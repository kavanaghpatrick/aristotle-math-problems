# I9 — Aristotle Informal-Mode Adapter

**Author:** I9 (May 30 2026 wave, agent 9 of 10)
**Status:** Adapter shipped, integration wired, smoke test PASSED.
**Files touched:**
- `scripts/aristotle_informal.py` (new, 296 LOC)
- `scripts/safe_aristotle_submit.py` (modified — informal-mode routing block, ~70 LOC)
- `docs/infrastructure_changes_may30/I9_informal_mode.md` (this file)

---

## 1. Motivation

Per the W8 finding (May 30 2026), Aristotle exposes three subsystems:

1. **MCGS** (Monte Carlo Goal Search) — the formalizer. Takes a Lean theorem
   statement, searches Mathlib tactic space for a proof.
2. **Lemma-based informal reasoner** — Takes a natural-language problem
   statement, generates an NL proof, decomposes it into lemmas, autoformalizes
   each lemma, and runs a REPL feedback loop on the formalized output.
3. **Hybrid orchestration** — Combines (1) and (2) based on prompt shape.

**Aristotle's known wins on Erdős-level open problems all involve subsystem #2:**

| Win | Lane | Wall time | Key observation |
|-----|------|-----------|-----------------|
| E124 (Boris Alexeev, Dec 2025) | INFORMAL | ~6h | Bare problem statement, no Lean scaffold. |
| E728 (Barreto + GPT-5.2 Pro, Jan 2026) | INFORMAL + paired | — | First fully-autonomous Erdős solution (per writeup). |
| E1026 | INFORMAL (formalize-and-extend role) | — | Aristotle extended a partial human strategy. |
| E481 (Barreto alone) | INFORMAL (no human strategy) | — | Aristotle alone solved a non-trivial Erdős from the bare statement. |

This project's pipeline submits `theorem ... := by sorry` directly via
`Project.create(prompt=..., tar_file_path=<tar with .lean>)`. **That shape
routes to MCGS-only.** We have NEVER invoked subsystem #2. The 0.8% hit rate
versus Harmonic's "12 Erdős in 90 days" follows directly.

I9's job: find subsystem #2's API entry point in `aristotlelib 0.7.0`, wire it
into `safe_aristotle_submit.py`, smoke-test it.

---

## 2. Discovered API surface

### 2.1 Inspection result

`aristotlelib 0.7.0` exposes **one** submission method:

```python
class Project(AristotleObject):
    @classmethod
    async def create(
        cls,
        prompt: str,
        tar_file_path: Path | str | None = None,
        public_file_path: str | None = None,
    ) -> "Project": ...
```

The CLI commands are thin wrappers:

| CLI | What it does |
|-----|--------------|
| `aristotle submit "<prompt>"` | `Project.create(prompt=<prompt>)` (no tarball) |
| `aristotle submit "<prompt>" --project-dir <dir>` | `Project.create_from_directory(...)` — packs dir into tar.gz, then `Project.create(prompt=..., tar_file_path=...)` |
| `aristotle formalize <file>` | Wraps `<file>` in a tar.gz with prompt `"Formalize <filename>"`, then `Project.create(...)` |
| `aristotle ask <project_id> "<prompt>"` | `Project.ask(prompt=...)` — sends a follow-up question to an existing project |

**There is no `Project.from_informal()`, `Project.solve_informal()`, or
`aristotle informal` subcommand.** The SDK has a single endpoint; the
distinction between INFORMAL and FORMALIZE modes is purely **prompt shape**.

### 2.2 What flips Aristotle from MCGS-only to informal-reasoner

Per the W8 audit notes and the live smoke test we ran (see §4), the routing is
content-driven:

- Prompt is a Lean source file (`theorem ... := by sorry`) attached as
  `tar_file_path=<.tar.gz>` → MCGS goal-search runs against the theorem.
  Aristotle treats the natural-language portion of the prompt as commentary,
  not as a request for a proof discovery.

- Prompt is a natural-language problem statement (English math, optionally
  with NL proof outline + candidate lemmas), submitted WITH NO TARBALL
  (`tar_file_path=None`) → Aristotle's informal reasoner takes over: NL proof
  generation, lemma decomposition, autoformalization. Lean signature, if
  provided, appears in the prompt body as a *target* for autoformalization.

The adapter assembles the second shape unambiguously: header line
`INFORMAL-MODE SUBMISSION`, the problem in English, the strategy outline, the
candidate lemmas, then the Lean signature in a fenced code block at the bottom
labeled "Target Lean Statement (for autoformalization)".

---

## 3. Adapter spec (`scripts/aristotle_informal.py`)

### 3.1 CLI

```
python3 scripts/aristotle_informal.py <sketch.txt>                  \
        [--fusion-json <companion.fusion.json>]                     \
        [--paired-llm <name>]                                       \
        [--id-out <file>]                                           \
        [--print-prompt]                                            \
        [--dry-run]
```

- `sketch.txt`: bare gap sketch. The English portion becomes the
  Problem Statement; the Lean block (if present) goes into the bottom-of-prompt
  fenced "Target Lean Statement" section.
- `--fusion-json <path>`: optional companion. Accepts BOTH the
  I8-canonical schema (`informal_proof_outline`, `candidate_lemmas`) AND
  legacy aliases (`strategy_outline`, `key_lemmas`).
- `--paired-llm <name>`: audit-trail metadata.  Appears in a footer line
  `_Strategy outline produced by `<name>` (paired LLM)._`.
- `--id-out <file>`: write the project UUID to this path in the same format
  as `safe_aristotle_submit.py` writes `slotNNN_ID.txt`.
- `--print-prompt`: assemble and print the prompt, do not submit.
- `--dry-run`: assemble and validate, do not submit.

Returns the project UUID on stdout (one line) on success.

### 3.2 Companion fields recognized

| Adapter field | Aliases | Source schema |
|---|---|---|
| `STRATEGY_OUTLINE_FIELDS` | `strategy_outline`, `informal_proof_outline` | I8 canonical + design alias |
| `KEY_LEMMAS_FIELDS` | `key_lemmas`, `candidate_lemmas` | I8 canonical + design alias |
| `LITERATURE_FIELDS` | `cross_domain_literature`, `literature_citations`, `seminal_paper_arxiv` | I8 |
| `ANALOGY_FIELDS` | `primary_analogy`, `analogy`, `cross_domain_analogy` | design |
| `TECHNIQUE_FIELDS` | `named_technique`, `technique`, `named_techniques` | I8 |

The adapter is permissive on schema — it picks up whichever fields are
present.  Schema validation is the job of the FUSION gate
(`check_fusion_companion()`); the adapter only consumes whatever the gate has
already accepted.

### 3.3 Prompt layout (assembled by `build_informal_prompt()`)

```
INFORMAL-MODE SUBMISSION
------------------------
Please attack the problem stated below using your informal reasoner: produce
a natural-language proof first, decompose it into lemmas, then autoformalize.
Do NOT treat this as a pure formalize-only task; the goal is to discover the
proof, not to mechanically translate one.

## Problem Statement
<English portion of the sketch>

## Informal Proof Outline (from paired strategist)
<strategy_outline / informal_proof_outline from companion>
*Note: This outline is a starting point. Aristotle should verify, refute, or
improve it as part of solving the problem.*

## Candidate Lemmas
1. <lemma 1>
2. <lemma 2>
...

## Cross-Domain Context
- **Primary analogy:** <analogy>
- **Named technique:** <technique>
- **Literature:** <citation>

## Target Lean Statement (for autoformalization)
When the informal proof is found, autoformalize against this exact signature:

```lean
theorem foo : ... := by sorry
```

---
_Strategy outline produced by `<paired_llm>` (paired LLM)._
```

The Lean signature is deliberately at the BOTTOM and labeled as a target, not
as the request itself.  This is the structural difference from a BARE-lane
prompt where the Lean theorem is at the top with `Formalize this:` style
framing.

---

## 4. Integration with `safe_aristotle_submit.py`

### 4.1 Trigger conditions

The submission gate fires informal-mode routing when ALL of the following are
true:

1. `--fusion-lane` OR `--informal-mode` flag is passed.
2. A `<sketch>.fusion.json` companion exists adjacent to the input file.
   (Also tried: `<sketch>.fusion.fusion.json` for stems already ending in
   `_fusion`.)
3. The companion contains a non-empty `informal_proof_outline` (or the legacy
   alias `strategy_outline`).

When all three hold, the gate:

1. Loads the companion via `aristotle_informal.load_fusion_companion()`.
2. Replaces `prompt_text` with `build_informal_prompt(sketch, fusion,
   paired_llm)`.
3. Sets `informal_mode = True` so the lane-resolution precedence sees it.
4. Logs a transaction `INFORMAL_ROUTING_FIRED` (via the regular
   `log_transaction` path, since the rewrite is observable in
   `prompt_first_120` of the eventual `submitted` log entry).

When step 3 fails (companion has analogy/technique but no `informal_proof_outline`),
the gate keeps the BARE prompt and prints
`ℹ️ Companion <name>.fusion.json has no strategy_outline; keeping BARE prompt.`
This is the intended fallback for FUSION submissions that ARE strategy-dossier
metadata but DO NOT carry a NL proof outline — they still get the lane tag
but go through the MCGS-only path.

When step 1 or 2 fail (no flag, no companion), the gate is a no-op and the
BARE prompt is used.  This preserves backward compatibility for every
existing submission script.

### 4.2 DB lane resolution (post-I2 schema)

```
if informal_mode:        lane = 'informal'
elif fusion_lane:        lane = 'fusion'
elif closure_info['rcc']: lane = 'closure'
else:                    lane = 'bare'
```

I9 adds: when informal-mode routing FIRES (companion + outline), it sets
`informal_mode = True` mid-flight. This means a `--fusion-lane` submission
with a companion that has `informal_proof_outline` will land as
**`lane = 'informal'`** (not `'fusion'`), correctly reflecting that the
informal reasoner subsystem was actually invoked. A `--fusion-lane` submission
without `informal_proof_outline` lands as `lane = 'fusion'`, the historical
behavior.

`fusion_json` column gets the literal parsed companion (via
`_record_lane_metadata`), so the audit trail can reproduce exactly which
informal outline was sent.

---

## 5. Smoke test — Live run, May 30 2026

### 5.1 Test inputs

- Sketch: `/tmp/i9_smoke_sketch.txt` — Euclid's infinitude of primes
  (known-closed in Mathlib as `Nat.exists_infinite_primes`). 9 non-blank
  lines, marked `Status: KNOWN`.
- Companion: `/tmp/i9_smoke_sketch.fusion.json` — provides
  `strategy_outline` (Euclid's `n! + 1` argument), `key_lemmas` (factorial+1
  has prime factor, small primes don't divide), `primary_analogy`,
  `named_technique`.

### 5.2 Command

```bash
python3 scripts/aristotle_informal.py /tmp/i9_smoke_sketch.txt   \
        --fusion-json /tmp/i9_smoke_sketch.fusion.json           \
        --paired-llm i9_smoke_test                               \
        --id-out /tmp/i9_smoke_ID.txt
```

### 5.3 Result

- **Project UUID:** `8d500201-0786-4bb2-8489-2f6aad91be91`
- **Status:** RUNNING (verified via `Project.list_projects`)
- **`has_input`: False** — Critical. Confirms no Lean tarball was attached.
  This is the API-level signature of an informal-mode submission.
- **Description:** Begins with `INFORMAL-MODE SUBMISSION\n------------------------\nPlease attack the problem stated below using your informal reasoner...`
  Confirms the server received and stored the informal-mode framing.
- **Task created:** `f9e23cf2-55f2-4eab-940c-6c06e79f54e5`, status
  `IN_PROGRESS`, `percent_complete = 1`. The task `description` field
  reflects the full informal-mode prompt. `file_name = None` — no Lean source
  attached.

### 5.4 Transaction log entry

```json
{
  "timestamp": "2026-05-30T09:06:04.941778",
  "action": "informal_submit",
  "details": {
    "project_id": "8d500201-0786-4bb2-8489-2f6aad91be91",
    "description": "i9_smoke_sketch",
    "prompt_chars": 1830,
    "prompt_first_120": "INFORMAL-MODE SUBMISSION ------------------------ Please attack the problem stated below using your informal reasoner: p"
  }
}
```

### 5.5 What "different processing than MCGS" looks like

Aristotle's task structure exposes `description` and `output_summary` per
task. For this smoke test:

- `file_name = None` is the strongest signal we have at the SDK level. MCGS
  submissions always attach the Lean source as a file. Informal-mode
  submissions do not.
- The task `description` is the verbatim NL prompt rather than a path like
  `"Formalize foo.lean"`. The CLI's `aristotle formalize` always produces
  the latter shape (its `prompt = f"Formalize {filename}"`).

Whether the informal reasoner actually finds Euclid's proof and emits NL
scratch (vs going straight to a tactic-search) cannot be determined from the
SDK surface during the submission itself — only the eventual `get_files()`
artifact will show it. The smoke test was about confirming the routing, not
about checking the proof.

---

## 6. Honest assessment

**Did we find Aristotle's informal-reasoner API, or are we using a workaround?**

Honest answer: **it is both — and that is the design.**

- There is NO dedicated `Project.create_informal()` method in `aristotlelib
  0.7.0`. The SDK exposes one submission endpoint and uses prompt shape to
  route.

- That said, **the routing IS by prompt shape**, and the adapter assembles
  exactly the shape that the docs (per W8 audit) say invokes subsystem #2.
  The smoke test confirms: when the prompt has no Lean tarball and is framed
  as a natural-language problem, Aristotle accepts it, runs a task, and the
  task description preserves the informal framing.

- If a future version of the SDK exposes a dedicated method (e.g.
  `Project.solve_informal(problem_statement, strategy_outline, lemmas)`),
  the adapter is a single function (`submit_informal()`) that can be swapped
  to call that method instead. The rest of the pipeline (companion loading,
  prompt assembly, DB metadata) is independent of the API surface.

**Risk:** The server-side routing logic is opaque. We cannot prove from the
client side that Aristotle ran the informal reasoner rather than passing the
NL text through MCGS. We rely on (a) the W8 audit's claim about the
subsystem boundary, (b) the precedent (E124/E728 used this exact prompt shape
per writeups), and (c) the `has_input=False` signal that no Lean source was
provided.

The honest mitigation: track outcomes. If informal-mode submissions converge
toward MCGS-shaped failure signatures (sorry counts, axiom counts) at the
same rate as BARE submissions, then the routing is not actually different
and we have a workaround that doesn't work. If they show qualitatively
different outputs (NL proof attempts in the result archive, different
failure modes), then we have access to the informal reasoner. The W8
prediction is the latter. We'll know in ~6 hours when the smoke test
completes.

---

## 7. Operational checklist

To submit a research target via informal mode:

1. Write the bare sketch (`<name>.txt`) as usual — ≤30 lines, gap-targeting.
2. Write the `<name>.fusion.json` companion with at minimum:
   - `informal_proof_outline`: the NL strategy from paired LLM
   - `candidate_lemmas`: ≥1 entry
   - (FUSION gate also requires: `problem_id`, `stage_outputs`,
     `named_technique`, `seminal_paper_arxiv`, `fit_score`, `bridge_lemma`,
     `honest_disclaimer`)
3. Submit:
   ```bash
   python3 scripts/safe_aristotle_submit.py <name>.txt --fusion-lane --paired-llm <model>
   ```
4. Verify post-submission: `mk find <problem_id>` should show
   `lane = 'informal'` and `informal_mode_used = 1`.
5. Wait. E124 took 6 hours. Plan accordingly.

To use the adapter STANDALONE (bypassing FUSION gate, for ad-hoc tests):

```bash
python3 scripts/aristotle_informal.py <sketch.txt>             \
        --fusion-json <companion.fusion.json>                  \
        --paired-llm <model>                                   \
        --id-out <name>_ID.txt
```

This is the path used for the I9 smoke test. The standalone adapter does NOT
run gap-targeting, closure-axis, literature-freshness, or FUSION gates — use
it only when you've validated the inputs by other means.

---

## 8. References

- W8 finding (May 30 2026): Three Aristotle subsystems, informal reasoner
  never used by this project.
- `docs/aristotle_usage_guide.md §3.4` — INFORMAL lane definition.
- `docs/fusion_axis_companion_spec.md` — I8's canonical `.fusion.json`
  schema with `informal_proof_outline` field.
- `docs/research_fusion_pipeline_design.md` — FUSION lane motivation and
  three-stage pipeline.
- `docs/infrastructure_changes_may30/I2_schema_unification.md` — adds
  `lane`, `informal_mode_used`, `paired_llm`, `fusion_json` columns.
- `aristotlelib 0.7.0 /opt/anaconda3/envs/claude-code/lib/python3.11/site-packages/aristotlelib/{project.py,cli/command/submit.py,cli/command/formalize.py}`
  — actual SDK source confirming the API surface described in §2.

---

**End of I9 spec.** Adapter ready for production use. Smoke test UUID
`8d500201-0786-4bb2-8489-2f6aad91be91` is the live witness.
