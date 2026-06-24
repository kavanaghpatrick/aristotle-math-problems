# I8 — FUSION Lane (May 30 2026)

**Status:** shipped 2026-05-30
**Owners:** I8 (infrastructure)
**Agent:** I8 of 10 in the May 30 2026 infrastructure series.
**Builds on:** I2 (added `lane`, `fusion_json`, `paired_llm` columns), I6 (Stages 1-3 dossier).
**Related:** I4 (literature-check gate), X2 (closure-axis gate), I9 (informal-mode routing).

## Why this exists

The FUSION lane is one of four lanes in the post-bare-gap pipeline (per CLAUDE.md §"Pipeline (4 lanes)"). It is the channel where a bare `.txt` sketch is paired with a paired-LLM strategy dossier — a companion `.fusion.json` produced from I6's Stage 1-3 outputs (literature, analogies, named techniques). This dossier captures the strategy that Aristotle's MCGS formalizer alone cannot reach, and (optionally, via I9) routes the submission through Aristotle's informal-reasoning subsystem.

But the bare-gap discipline must hold. CLAUDE.md is unambiguous: the `.txt` stays a bare conjecture statement. The strategy lives in the JSON companion, NOT in the .txt.

I8 enforces that invariant. It defines the companion schema, the airlock pattern (which keeps strategy in the JSON and out of the .txt), the submission gate, and the test fixtures that prove the gate behaves correctly. The fusion gate is the **strongest of the four submission gates**: no override (other than the global `--force` reserved for the orchestrator pipeline).

F3's audit (May 30 2026) found that 87% of historical LLM consultations were meta-process rather than math content. The FUSION lane is the channel where structured math strategy work gets first-class treatment — without polluting the bare-gap discipline that has driven the 1166 pre-May-30 submissions.

---

## The companion spec

Full spec: [`docs/fusion_axis_companion_spec.md`](../fusion_axis_companion_spec.md).

### Required fields (9)

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
  "candidate_lemmas": ["lemma1: ...", "lemma2: ...", "lemma3: ..."],
  "honest_disclaimer": "[plain-language statement of what fusion-lane CAN/CANNOT deliver]"
}
```

### Hard caps

| Field | Constraint |
|---|---|
| `problem_id` | regex `^[a-z0-9_]+$` |
| `fit_score` | float in `[0.0, 1.0]` |
| `named_technique` | ≤ 120 chars |
| `bridge_lemma` | ≤ 3 sentences AND ≤ 600 chars |
| `informal_proof_outline` | ≤ 500 words AND ≤ 4000 chars |
| `candidate_lemmas` | 1-10 entries, each a non-empty string |
| `stage_outputs` | exactly 3 keys: `literature_path`, `analogies_path`, `techniques_path` |
| total companion | ≤ 80 non-blank lines |

No extra top-level fields permitted. Schema is strict.

---

## Airlock pattern

The airlock is what keeps the FUSION lane honest. Strategy lives in the JSON, NOT the `.txt`. The airlock scans the .txt for strategy terms and REJECTS on any leak.

### Static blocklist + dynamic per-submission tokens

The airlock works in two layers:

**1. Static blocklist** — `scripts/airlock_blocklist.txt` lists famous techniques and generic strategy keywords. Excerpts:
- Famous named techniques: `Frey curve`, `Iwasawa theory`, `Selmer group`, `polynomial method`, `Szemeredi regularity`, etc.
- Generic strategy keywords: `Proof Strategy`, `Key Lemma`, `Proposed Approach`, `Step 1`, etc.

**2. Dynamic per-submission tokens** — From the companion `.fusion.json`, the airlock derives:
- `named_technique` (whole phrase)
- First capitalised sub-word of `named_technique` (`Frey` from `Frey-Hellegouarch`)
- First 6 words of `bridge_lemma`
- First 6 words (or pre-colon headline) of each `candidate_lemmas` entry

The merged set is the LEAK SET for that specific submission.

### Example violation

Companion declares `named_technique: "Frey curve"`. The author writes in the .txt:

```
Status: OPEN. Frey approach has been tried.
```

Airlock REJECT (verbatim output):
```
FAIL  airlock REJECT: token 'Frey curve' leaked into bare .txt
  file: tests/fusion_gate/sample_fusion_LEAKS.txt
  context: ...equation a^p + b^p = c^p. The [[FREY CURVE]] approach has been attempted h...
  fix: remove the strategy term from the .txt; keep it in
       sample_fusion_LEAKS.fusion.json (named_technique / bridge_lemma).
  reference: docs/fusion_axis_companion_spec.md
```

Both the static `Frey curve` and the dynamic `Frey` (from named_technique) catch this. Either alone would suffice. The error message shows the offending term and its context with `[[CAPITALIZED]]` highlights so the author can locate it quickly.

### Header lines excluded from scanning

The airlock excludes the metadata header lines (`OPEN GAP:`, `Source:`, `Domain:`, `Status:`) from scanning. This avoids false positives when a problem's domain name or source path happens to share a token with the blocklist (e.g. `Source: formal-conjectures/Erdos_modular.lean` should not trip on "modular" if a static blocklist token mentions modularity).

### Matching rules

- Case-insensitive
- Whole-word boundary: the matched token must not be preceded or followed by an ASCII letter or digit. So `Frey` matches `[[Frey]] approach` but not `Freydom`.
- Tokens with internal hyphens/spaces (`Frey-Hellegouarch`, `polynomial method`) are matched literally as phrases — the boundary rule applies only to the first/last character.

---

## Gate decision table

`check_fusion_companion(input_file)` in `scripts/safe_aristotle_submit.py`. Triggered ONLY when `--fusion-lane` is passed.

| Condition                                                | Outcome |
|---|---|
| `--fusion-lane` not passed                                | Skip gate; FUSION lane requires opt-in. |
| `--force` passed alongside `--fusion-lane`                | Bypass gate (orchestrator escape hatch). |
| Companion file missing                                    | REJECT — "FUSION lane requires a companion .fusion.json file." |
| Companion invalid JSON / not an object                    | REJECT with parse error. |
| Missing one of 9 required fields                          | REJECT, names missing field(s). |
| Extra unexpected top-level field                          | REJECT, names extra field(s). |
| `> 80` non-blank lines                                    | REJECT with line-count error. |
| `problem_id` not matching `^[a-z0-9_]+$`                  | REJECT. |
| `stage_outputs` missing literature/analogies/techniques   | REJECT. |
| `named_technique` empty or `> 120` chars                  | REJECT. |
| `seminal_paper_arxiv` not a string                        | REJECT. |
| `fit_score` not numeric or outside `[0.0, 1.0]`           | REJECT. |
| `bridge_lemma` empty, `> 3` sentences, or `> 600` chars   | REJECT. |
| `informal_proof_outline` empty, `> 500` words, or `> 4000` chars | REJECT. |
| `candidate_lemmas` not in 1-10 entries or has empty item  | REJECT. |
| `honest_disclaimer` empty                                 | REJECT. |
| Airlock detects strategy leak in .txt                     | REJECT with leak detail. |
| All checks pass                                           | PASS → `lane='fusion'`, `informal_mode_used=1` (via I9), `fusion_json` populated. |

**No override** other than `--force`. The fusion gate is the strongest of all four lane gates.

### Comparison with the closure-axis gate

| Aspect | Closure-axis gate | Fusion gate (I8) |
|---|---|---|
| Trigger | Always runs (warns if missing) | Only on `--fusion-lane` |
| Missing companion | WARN + allow (transition) | REJECT |
| `real_closure_candidate=false` | REJECT unless `--rubric-points` | n/a |
| Per-submission escape hatch | `--rubric-points` (logged) | none |
| Airlock | no | yes |
| Line budget | n/a | 80 non-blank |

---

## CLI integration

The `--fusion-lane` and `--paired-llm` flags already exist (added by I2). I8 wires them through to the new gate.

```bash
# Validate a fusion submission locally (no API call):
python3 scripts/airlock_check.py submissions/sketches/erdos_938.txt

# Full submit:
python3 scripts/safe_aristotle_submit.py submissions/sketches/erdos_938.txt \
    --fusion-lane --paired-llm codex
```

CLI help (excerpt):
```
  --fusion-lane        Tag this submission as research-fusion lane (DB.lane='fusion').
                       Triggers check_fusion_companion gate: validates the
                       sibling <name>.fusion.json (9 required fields, ≤80 lines)
                       and runs the airlock — REJECTS if strategy from the JSON
                       leaks into the bare .txt. NO override (other than --force).
                       See docs/fusion_axis_companion_spec.md,
                       docs/infrastructure_changes_may30/I8_fusion_lane.md.
```

---

## Test results

Test suite: `tests/fusion_gate/run_gate_test.py`. 5 test cases, all PASS.

```
$ python3 tests/fusion_gate/run_gate_test.py
   ✅ Fusion companion: sample_fusion.fusion.json (nblines=20/80, technique='Modularity lift via auxiliary elliptic curve', fit=0.72, airlock static=58 dynamic=7)
PASS  1. valid bare + valid companion passes
PASS  2. leaking .txt rejected by airlock
PASS  3. oversized companion rejected by line-budget
PASS  4. missing companion rejected
PASS  5. airlock standalone detects leak

All fusion-gate tests passed (5/5).
```

### Fixtures

| File | Purpose |
|---|---|
| `tests/fusion_gate/sample_fusion.txt` | Valid bare .txt (~7 non-blank lines) |
| `tests/fusion_gate/sample_fusion.fusion.json` | Valid companion (20 non-blank lines) |
| `tests/fusion_gate/sample_fusion_LEAKS.txt` | .txt mentions "Frey curve" → should REJECT |
| `tests/fusion_gate/sample_fusion_LEAKS.fusion.json` | Companion declares `named_technique: "Frey curve + Ribet level-lowering"` |
| `tests/fusion_gate/sample_fusion_OVERSIZED.fusion.json` | 89 non-blank lines → exceeds 80 cap → should REJECT |
| `tests/fusion_gate/sample_fusion_OVERSIZED.txt` | Valid bare .txt paired with oversized companion |
| `tests/fusion_gate/sample_fusion_MISSING.txt` | Valid bare .txt with NO companion file → should REJECT |

### Regression: closure-gate still passes

```
$ python3 tests/closure_gate/run_gate_test.py
PASS  real-candidate without flag passes
PASS  bounded-version without --rubric-points rejects
PASS  bounded-version with --rubric-points passes
PASS  missing companion allowed with warn
PASS  bad enum rejects
PASS  missing field rejects
All closure-gate tests passed.
```

I8's changes are additive — they leave the closure-axis gate, the literature-freshness gate, and the gap-targeting gate untouched.

---

## How to author a fusion submission end-to-end

1. **Get the Stage 1-3 dossier (I6).** The paired-LLM (Codex / Grok / Gemini) produces three markdown files under `research_fusion/runs/<problem_id>/`:
   - `01_literature.md` — prior literature, recent papers
   - `02_analogies.md` — cross-domain analogies
   - `03_techniques.md` — named-technique shortlist with fit scores

2. **Select the top technique** from `03_techniques.md`. Note its arXiv seminal paper and fit_score.

3. **Write the bridge lemma** — 1-3 sentence technical innovation needed to apply the technique to the problem.

4. **Write the informal proof outline** — ≤500 words. Aristotle's informal reasoner (I9 routing) will consume this.

5. **Extract 1-10 candidate lemmas** as `"headline: detail"` strings.

6. **Write the honest disclaimer** — what fusion can/cannot deliver. Forces the F1 / F3 honesty discipline.

7. **Write the bare `.txt` sketch** in the usual ≤30-line bare-gap format. **NO strategy in the .txt.**

8. **Compose the `.fusion.json` companion** with all 9 required fields. Keep it ≤80 non-blank lines.

9. **Sanity check locally** (no API call, no submission):
   ```bash
   python3 scripts/airlock_check.py submissions/sketches/<name>.txt
   ```
   This runs the airlock against the .txt and its companion. Exit 0 = clean; exit 1 = leak.

10. **Submit:**
    ```bash
    python3 scripts/safe_aristotle_submit.py submissions/sketches/<name>.txt \
        --fusion-lane --paired-llm <codex|grok|gemini|mixed>
    ```

Gate order at submission time:
- `check_gap_targeting` (always)
- `check_literature_freshness` (always; may need `--literature-ack`)
- `check_fusion_companion` (only on `--fusion-lane`) ← I8
- `check_closure_axis` (always; may need `--rubric-points`)
- I9 informal-mode routing (when `--fusion-lane` and companion has outline)
- Lockfile, duplicate, queue checks
- Submit

---

## DB integration

On successful submission, `safe_submit()` writes:

- `submissions.lane = 'fusion'` (or `'informal'` if I9 actually rewrote the prompt with the informal outline)
- `submissions.informal_mode_used = 1` (when I9 rewrote the prompt)
- `submissions.fusion_json = <full companion JSON, sorted-key serialized>`
- `submissions.paired_llm = <whatever --paired-llm passed>`

Query examples:

```sql
-- All fusion-lane submissions in last 30 days
SELECT id, filename, paired_llm,
       json_extract(fusion_json, '$.named_technique') AS technique
  FROM submissions_audit
 WHERE lane = 'fusion'
   AND submitted_at >= date('now', '-30 days');

-- Highest-confidence fusion shots
SELECT id, filename,
       CAST(json_extract(fusion_json, '$.fit_score') AS REAL) AS fit
  FROM submissions_audit
 WHERE lane = 'fusion'
 ORDER BY fit DESC NULLS LAST
 LIMIT 20;
```

---

## Files

**New files**

| Path | Purpose |
|---|---|
| `/Users/patrickkavanagh/math/docs/fusion_axis_companion_spec.md` | Companion file v1.0 schema spec |
| `/Users/patrickkavanagh/math/docs/infrastructure_changes_may30/I8_fusion_lane.md` | This document |
| `/Users/patrickkavanagh/math/scripts/airlock_check.py` | Airlock implementation (importable + CLI) |
| `/Users/patrickkavanagh/math/scripts/airlock_blocklist.txt` | Default static strategy-term blocklist |
| `/Users/patrickkavanagh/math/tests/fusion_gate/sample_fusion.txt` | Valid bare-gap fixture |
| `/Users/patrickkavanagh/math/tests/fusion_gate/sample_fusion.fusion.json` | Valid companion fixture |
| `/Users/patrickkavanagh/math/tests/fusion_gate/sample_fusion_LEAKS.txt` | Strategy-leak fixture |
| `/Users/patrickkavanagh/math/tests/fusion_gate/sample_fusion_LEAKS.fusion.json` | Companion for LEAKS fixture |
| `/Users/patrickkavanagh/math/tests/fusion_gate/sample_fusion_OVERSIZED.txt` | Sketch paired with oversized companion |
| `/Users/patrickkavanagh/math/tests/fusion_gate/sample_fusion_OVERSIZED.fusion.json` | >80-line companion |
| `/Users/patrickkavanagh/math/tests/fusion_gate/sample_fusion_MISSING.txt` | No companion fixture |
| `/Users/patrickkavanagh/math/tests/fusion_gate/run_gate_test.py` | Test driver |

**Modified files**

| Path | Change |
|---|---|
| `/Users/patrickkavanagh/math/scripts/safe_aristotle_submit.py` | Added `FusionCompanionError`, fusion schema constants, `_companion_fusion_path`, `_count_sentences`, `check_fusion_companion`. Wired into `safe_submit` between literature-freshness gate and closure-axis gate. Updated `--fusion-lane` CLI help. |

---

## Limitations / future work

- The airlock's static blocklist is curated by hand. A future enhancement: auto-derive it from the `research_fusion/runs/*/03_techniques.md` corpus.
- The airlock matches whole-word boundaries. It does NOT catch paraphrases (`Frey curve` vs. `the curve of Frey`). Adversarial obfuscation is out of scope.
- The line-budget cap is enforced before field validation. So an oversized file that ALSO has a schema error reports the line-budget error first. This is intentional — line budget is the primary discipline.
- `informal_proof_outline` length is char- and word-capped but not validated for content. The author's `honest_disclaimer` is the contract that this section was actually produced by a paired-LLM and not boilerplate.
- I9 routing is the consumer of `informal_proof_outline`. If I9 detects no outline (or an alias `strategy_outline` field), it falls back to BARE prompt and does NOT set `lane='informal'`. I8's gate does NOT depend on I9 being operational; the gate runs even when I9 is absent.
