# Fusion-Axis Companion File Spec (v1.0)

**Authority**: Operationalizes the FUSION lane (CLAUDE.md "Pipeline (4 lanes)" §3) at submission time.
**Status**: ACTIVE as of 2026-05-30. Enforced by `check_fusion_companion()` in `scripts/safe_aristotle_submit.py`. Triggered by `--fusion-lane`.
**Owner**: Fusion-lane infrastructure team, Agent I8 of the May 30 infrastructure series.

---

## Why

The FUSION lane invokes Aristotle's informal-reasoning subsystem (subsystem #2 per arXiv:2510.01346) by pairing a bare `.txt` sketch with a paired-LLM strategy dossier. The dossier captures the upstream research (literature, analogies, named techniques) that the MCGS formalizer alone cannot reach.

But that strategy content MUST NOT leak into the `.txt` sketch. The CLAUDE.md mission is unambiguous: "We do NOT develop proof strategies. We do NOT write step-by-step proof outlines." The .txt stays bare. The .fusion.json holds the strategy in machine-readable form, kept in an airlock, and surfaced only after human review.

This file specifies the on-disk artifact, the schema, the airlock pattern, and the gate behavior.

Per F3 (May 30 2026 finding): 87% of historical LLM consultations were meta-process, not math. The FUSION lane is the channel where structured math strategy work gets first-class treatment — without polluting the bare-gap discipline.

---

## File location and naming

For every sketch at `submissions/sketches/<name>.txt` on the FUSION lane, the companion file lives at:

```
submissions/sketches/<name>.fusion.json
```

Examples:
- `submissions/sketches/erdos_938.txt` -> `submissions/sketches/erdos_938.fusion.json`
- `submissions/sketches/slot999_erdos_938.txt` -> `submissions/sketches/slot999_erdos_938.fusion.json`

The gate computes this path by `input_file.with_suffix('.fusion.json')`. No nesting, no separate directory — the companion lives next to its sketch.

---

## File format

Strict JSON. Nine required top-level fields, no extra fields permitted. Total non-blank-line budget: ≤ **80 lines** (hard cap; gate rejects above).

```json
{
  "problem_id": "erdos_938",
  "stage_outputs": {
    "literature_path": "research_fusion/runs/erdos_938/01_literature.md",
    "analogies_path":  "research_fusion/runs/erdos_938/02_analogies.md",
    "techniques_path": "research_fusion/runs/erdos_938/03_techniques.md"
  },
  "named_technique": "Frey-Hellegouarch + Ribet level-lowering",
  "seminal_paper_arxiv": "https://arxiv.org/abs/0707.4035",
  "fit_score": 0.72,
  "bridge_lemma": "[1-3 sentence statement of the technical innovation needed]",
  "informal_proof_outline": "[<=500 word natural-language outline]",
  "candidate_lemmas": [
    "lemma1: ...",
    "lemma2: ...",
    "lemma3: ..."
  ],
  "honest_disclaimer": "[plain-language statement of what fusion-lane CAN/CANNOT deliver]"
}
```

### Field semantics

| Field | Type | Constraint | Purpose |
|---|---|---|---|
| `problem_id` | string | `^[a-z0-9_]+$` | Canonical problem id; must match the sketch's `OPEN GAP:` problem. |
| `stage_outputs` | object | 3 required string paths | Pointers to I6's Stage 1-3 markdown dossier (literature, analogies, techniques). Paths are relative to `MATH_DIR`. |
| `stage_outputs.literature_path` | string | `.md` path | Stage 1 — prior literature, known results. |
| `stage_outputs.analogies_path` | string | `.md` path | Stage 2 — cross-domain analogies. |
| `stage_outputs.techniques_path` | string | `.md` path | Stage 3 — named techniques shortlist. |
| `named_technique` | string | non-empty, ≤ 120 chars | The specific named technique selected (e.g. "Frey-Hellegouarch + Ribet level-lowering"). |
| `seminal_paper_arxiv` | string | URL or `"none"` | arXiv URL of the seminal paper for the technique, or the string `"none"` if not on arXiv. |
| `fit_score` | number | float in [0.0, 1.0] | Paired-LLM's confidence that the technique fits the problem. |
| `bridge_lemma` | string | 1-3 sentences, ≤ 600 chars | The technical innovation needed to bridge the technique to the problem. This is the SPECIFIC math claim; the proof outline below operationalizes it. |
| `informal_proof_outline` | string | ≤ 500 words, ≤ 4000 chars | The natural-language proof outline. Aristotle's informal reasoner consumes this. |
| `candidate_lemmas` | array[string] | 1-10 entries, each `"headline: detail"` | Discrete lemma statements suitable for `mk find` indexing. |
| `honest_disclaimer` | string | non-empty | Plain-language statement of what the FUSION lane can and cannot deliver. Forces the author to confront the F1 / F3 honesty problem. |

### Line budget

The companion must have at most **80 non-blank lines** total. Blank lines and lines that are exclusively whitespace do not count. The gate enforces this with `len([l for l in raw.splitlines() if l.strip()])`.

Rationale: 80 lines is enough to express the schema honestly (the example below is 13 non-blank lines minimum, including object braces). 80 lines is too small to smuggle in a full proof or to recapitulate research_fusion's Stage 1-3 outputs (those live at the `stage_outputs.*_path` references). The cap keeps the companion as METADATA pointing into the dossier, not the dossier itself.

---

## Airlock pattern

The FUSION lane's defining safety property is: **the .txt sketch must remain a bare-gap statement even when paired with a rich strategy dossier**. The airlock enforces this by scanning the .txt for any strategy term that appears in the companion.

The check is performed by `scripts/airlock_check.py` and called by the submission gate. It works in two layers:

1. **Static blocklist** — `scripts/airlock_blocklist.txt` is a curated list of famous named techniques (Frey curve, Iwasawa theory, polynomial method, etc.) and generic strategy keywords (Proof Strategy, Key Lemma, etc.). Any token from this list found in the .txt body causes a REJECT.

2. **Dynamic per-submission tokens** — From the companion `.fusion.json`, the airlock derives additional tokens:
   - `named_technique` (whole phrase)
   - First capitalised sub-word of `named_technique` (`Frey` from `Frey-Hellegouarch`)
   - First 6 words of `bridge_lemma`
   - First 6 words (or pre-colon headline) of each `candidate_lemmas` entry

Together these form the LEAK SET for that specific submission. The .txt is scanned with case-insensitive whole-word boundary matching. The metadata header lines (`OPEN GAP:`, `Source:`, `Domain:`, `Status:`) are excluded from scanning so they may reference the problem domain without false-positive matches.

### Example violation

`.fusion.json` says:
```json
{ "named_technique": "Frey curve modularity lift", ... }
```

`.txt` says:
```
OPEN GAP: Erdos 938
...
theorem erdos_938 : ∃ ... := by sorry

Status: Frey approach has been tried.
```

Airlock REJECTS:
```
airlock REJECT: token 'Frey curve modularity lift' leaked into bare .txt
  context: ...Status: [[FREY]] approach has been tried...
  fix: remove the strategy term from the .txt; keep it in <name>.fusion.json
```

Note: the static blocklist's "Frey curve" plus the dynamic token "Frey" (derived from the named technique) BOTH catch this. Either alone would suffice.

---

## Gate behavior (`check_fusion_companion`)

`scripts/safe_aristotle_submit.py` implements the gate as follows. Triggered ONLY when `--fusion-lane` is passed.

| Condition | Outcome |
|---|---|
| `--fusion-lane` not passed | Skip gate entirely; FUSION lane requires opt-in. |
| Companion file missing | REJECT — fusion lane requires the companion. |
| Companion invalid JSON | REJECT with parse error. |
| Companion missing required field | REJECT with schema error. |
| Companion has unexpected field | REJECT with schema error. |
| Companion has > 80 non-blank lines | REJECT with line-count error. |
| `fit_score` not in [0.0, 1.0] | REJECT with range error. |
| `informal_proof_outline` > 500 words | REJECT with length error. |
| `bridge_lemma` > 3 sentences | REJECT with length error. |
| Airlock detects strategy leak in .txt | REJECT with leak detail. |
| Companion is valid AND airlock clean | PASS — gate writes JSON to `submissions.fusion_json` and sets `lane='fusion'`. |

**No override.** Unlike the closure-axis gate (which has `--rubric-points` as an escape hatch), the FUSION gate is the strongest gate of all: the only way to bypass it is `--force`, which bypasses every gate and is reserved for the orchestrator pipeline.

Rationale: the airlock pattern is what protects bare-gap discipline. If you have strategy, it goes in the JSON. If the JSON is over-budget or the .txt leaks, the fix is in the author's hands. There is no operating procedure where "submit anyway" is correct.

---

## DB integration

When a FUSION submission succeeds, `safe_submit()` writes:

- `submissions.lane = 'fusion'`
- `submissions.informal_mode_used = 1` (fusion implicitly invokes the informal reasoner)
- `submissions.fusion_json = <full companion JSON, sorted-key serialized>`
- `submissions.paired_llm = <whatever --paired-llm passed>` (`codex`, `grok`, `gemini`, `mixed`, etc.)

Query examples:

```sql
-- All fusion-lane submissions in last 30 days
SELECT id, filename, paired_llm, json_extract(fusion_json, '$.named_technique') AS technique
  FROM submissions_audit
 WHERE lane = 'fusion'
   AND submitted_at >= date('now', '-30 days');

-- Fusion submissions grouped by named technique
SELECT json_extract(fusion_json, '$.named_technique') AS technique,
       COUNT(*) AS n,
       AVG(mathematical_content_score) AS avg_mcs
  FROM submissions_audit
 WHERE lane = 'fusion'
 GROUP BY technique
 ORDER BY n DESC;

-- Highest-confidence fusion shots
SELECT id, filename, json_extract(fusion_json, '$.fit_score') AS fit
  FROM submissions_audit
 WHERE lane = 'fusion'
 ORDER BY fit DESC NULLS LAST
 LIMIT 20;
```

---

## How to author a fusion submission end-to-end

1. **Stages 1-3 dossier** (I6's responsibility). The paired-LLM (Codex / Grok / Gemini) produces three markdown files under `research_fusion/runs/<problem_id>/`:
   - `01_literature.md` — prior literature, known results, recent papers
   - `02_analogies.md` — cross-domain analogies
   - `03_techniques.md` — named-technique shortlist with fit scores

2. **Select the top technique** from `03_techniques.md`. Note its arXiv seminal paper and fit_score.

3. **Write the bridge lemma** — the 1-3 sentence technical innovation needed to apply the technique to the problem.

4. **Write the informal proof outline** — ≤500 words of natural language explaining how the proof goes. Aristotle's informal reasoner will consume this.

5. **Extract 1-10 candidate lemmas** as `"headline: detail"` strings.

6. **Write the honest disclaimer** — what the fusion lane can deliver (paired-LLM dossier guidance, informal-reasoner activation), and what it cannot (it does NOT pre-validate the strategy; the technique fit may be wrong; Aristotle may still fail).

7. **Write the bare .txt sketch** in the usual ≤30 line bare-gap format. NO strategy in the .txt.

8. **Compose the .fusion.json companion** with all 9 required fields. Keep it ≤80 non-blank lines.

9. **Sanity check locally**:
   ```bash
   python3 scripts/airlock_check.py submissions/sketches/<name>.txt
   ```

10. **Submit**:
    ```bash
    python3 scripts/safe_aristotle_submit.py submissions/sketches/<name>.txt \
        --fusion-lane --paired-llm <codex|grok|gemini|mixed>
    ```

The gate runs `check_gap_targeting` → `check_literature_freshness` → `check_fusion_companion` (when `--fusion-lane`) → `check_closure_axis` → submission. The airlock runs as part of `check_fusion_companion`.

---

## Minimal valid example

`submissions/sketches/erdos_938.fusion.json` (illustrative):

```json
{
  "problem_id": "erdos_938",
  "stage_outputs": {
    "literature_path": "research_fusion/runs/erdos_938/01_literature.md",
    "analogies_path":  "research_fusion/runs/erdos_938/02_analogies.md",
    "techniques_path": "research_fusion/runs/erdos_938/03_techniques.md"
  },
  "named_technique": "Frey-Hellegouarch + Ribet level-lowering",
  "seminal_paper_arxiv": "https://arxiv.org/abs/0707.4035",
  "fit_score": 0.72,
  "bridge_lemma": "If a counterexample (a,b,c) exists with the required congruence conditions, the associated Frey curve y^2 = x(x-a^p)(x+b^p) is modular of conductor N divisible only by primes dividing 2abc, contradicting Ribet's level-lowering.",
  "informal_proof_outline": "Assume a counterexample (a,b,c) to the conjecture. Form the Frey curve E: y^2 = x(x-a^p)(x+b^p). By Wiles-Taylor modularity, E is modular of some level N. The conductor N divides 2abc up to small primes by a discriminant argument. Apply Ribet level-lowering to a newform of weight 2 and level dividing 2*rad(abc). The space of such newforms is empty for the level computed, contradiction. Result: no counterexample exists.",
  "candidate_lemmas": [
    "frey_modular: The Frey curve associated to (a,b,c) is modular of level dividing 2*rad(abc).",
    "ribet_lowering: A weight-2 newform at level 2N can be level-lowered to level 2.",
    "empty_newform_space: S_2(Gamma_0(2)) is trivial."
  ],
  "honest_disclaimer": "This dossier was produced by paired-LLM consultation (Codex + Grok, May 30 2026). The technique fit is the paired-LLM's best guess at 0.72 confidence; it has not been independently verified to apply to erdos_938. Aristotle's informal reasoner may still fail to assemble the proof, and the bridge_lemma may be unsound. The fusion lane CAN provide a structured strategy; it CANNOT pre-validate that strategy."
}
```

13 non-blank top-level fields; expands to ~25 non-blank lines when pretty-printed — well under the 80-line cap.

---

## Versioning

- **v1.0 (2026-05-30, this spec) — Initial.** 9 required fields. Airlock pattern with static blocklist + dynamic per-submission tokens. ≤80 line cap.
- **Future v1.1**: optional `secondary_techniques: [obj]` array for fallback techniques the paired-LLM ranked below the primary. Backward-compatible.
- **Future v2.0**: if Aristotle exposes a dedicated fusion-API endpoint distinct from the bare prompt+tar flow, the schema may grow an `api_target` field. Backward-incompatible.

---

## See also

- `docs/closure_axis_companion_spec.md` — parallel gate for the CLOSURE lane.
- `docs/infrastructure_changes_may30/I2_schema_unification.md` — DB columns added (`lane`, `fusion_json`, etc.).
- `docs/infrastructure_changes_may30/I4_literature_check.md` — sister gate (literature freshness).
- `docs/infrastructure_changes_may30/I8_fusion_lane.md` — gate implementation notes.
- `scripts/airlock_check.py` — airlock implementation.
- `scripts/airlock_blocklist.txt` — default static blocklist.
- `tests/fusion_gate/` — gate test fixtures.
