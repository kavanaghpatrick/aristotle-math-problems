# Feasibility Filter Rubric (v1.0)

**Authority**: Formalizes the May 30 2026 debate's "Novelty Gate" / "Feasibility Filter" as a mandatory pre-draft protocol. Hard rules from `CLAUDE.md` still bind. This rubric layers ON TOP of `check_gap_targeting()`; it does not replace it.

**Purpose**: Prevent the pipeline from manufacturing polished irrelevance on hard problems. The 5/5 batch (May 30) succeeded because every target had a concrete finite/computable core. On a structural-open target with no such core (e.g., Tuza ν=4 carcass), the same draft+audit machinery will produce formally clean fragments that do not engage the real combinatorial obstruction. The filter blocks that failure mode at submission time.

**Most important rule (single line)**: *No sketch may be submitted to Aristotle until it is labeled with one of the five Feasibility Categories AND the entry conditions for that category are met.* The mechanical default of "draft a bare gap and submit" is the path back to the 0.17% rate.

---

## The Five Categories

Every candidate target is classified as exactly one of:

1. `finite-verification` — Bounded universal claim; `native_decide` / `Finset.decide` / `interval_cases` can in principle discharge it.
2. `constructive-search` — Existence claim with a computable witness construction. The witness may be too large to fit in the sketch, but the construction is exhibited (CRT, greedy set cover, table lookup).
3. `mechanical-extension` — Same proof skeleton as a prior `compiled_advance`, applied to a wider parameter range or one new index. Reusable, low-novelty.
4. `structural-open` — Needs a genuine mathematical idea. No computable subclaim known. Submission ONLY after a fresh structural diagnostic exists.
5. `known-formalization` — Math is solved upstream in the literature. Submission is just porting to Lean. Excluded from active rotation per user prime directive ("novel, not formalization").

The May 30 debate proposed 4 categories. Empirically, slot736 (FT q ≤ 1500 extending slot720) was not the same animal as slot737 (E647 Cunningham narrowing — genuinely novel) nor slot738 (Brocard range bump with encoding refactor — half-novel). The fifth category `mechanical-extension` captures that distinct class so the rubric reflects what the pipeline actually produces.

---

## Decision Rules per Category

### `finite-verification`

**Criteria (ALL must hold)**:
- The claim binds all universal quantifiers to a finite explicit range (e.g., `∀ n, n ≤ N → ...` or `∀ n ∈ Finset.range N`).
- The predicate is `Decidable` in Lean. No `∀ x : ℝ`, no `∃ f : ℕ → ℕ`.
- A back-of-envelope `native_decide` budget exists: depth, fan-out, and per-cell work are bounded so the kernel can plausibly close it in ≤ 30 min CPU.

**Entry condition**: None beyond the criteria. Submit directly.

**Examples**: slot722 Brocard [2, 500]; slot738 Brocard [501, 1000]; bounded Cunningham residual cleanup.

**Failure mode to flag**: Kernel timeout. If the `native_decide` budget is questionable, the sketch must say so explicitly (e.g., "chunked over 10×50 with 8M heartbeats per chunk").

### `constructive-search`

**Criteria (ALL must hold)**:
- An existence claim: `∃ x, P x` or `∃ x, ∀ y, Q x y`.
- A concrete construction recipe is identifiable: CRT, greedy, set cover, witness table, explicit polynomial.
- The witness search is computationally bounded (NOT "find any covering system of ℤ²" — that's structural).

**Entry condition**: Either (a) the witness is already known and being formalized, OR (b) the search space is finite and the recipe is named in the sketch.

**Examples**: slot740 (greedy set cover over index-1 primes ≤ 500 to cover 8×8 grid); slot737 framed as "find σ₀ bounds 6 and 7 for the residual class".

**Failure mode to flag**: "Existence" sketches that hide a structural problem (e.g., `∃ infinitely many m`) — those belong in `structural-open` until the construction recipe is named.

### `mechanical-extension`

**Criteria (ALL must hold)**:
- A prior `compiled_advance` exists whose Lean proof skeleton transfers verbatim with the parameter swap.
- The new parameter range / index does not cross a known break point. Pre-scan must confirm.
- The contribution beyond the prior advance is bounded compute, not a new mathematical claim.

**Entry condition**:
- Cite the parent slot.
- Confirm no break point in the new range (e.g., FT q ≤ 2000 hits q=1583 where A(q) is prime — that's a break; STOP).
- Limit to one mechanical slot per batch (≤ 5). Two or more is metric-hacking the advance count.

**Examples**: slot736 (FT q ≤ 1000 → q ≤ 1500); slot738 (Brocard [2,500] → [501,1000]).

**Failure mode to flag**: Bound bumps past a known obstruction. Brocard [1001, 2000] is fine; FT q ≤ 2000 (which would include q=1583) is NOT — submit the diagnostic instead.

### `structural-open`

**Criteria (ANY of)**:
- No computable subclaim is currently known.
- The conjecture reduces to a famous open hard problem (Schinzel, Goldbach, even-perfect-number infinitude).
- Prior submissions all returned `compiled_no_advance` or `compile_failed` with no honest residual narrowed.

**Entry condition (MUST be satisfied before submission)**:
A **fresh structural diagnostic** exists. Concretely, the sketch must point to ONE of:
- A new finite-period quotient analysis showing partial cover (analysis/erdos203_quotient_lift_may30.md is the template).
- A new modular obstruction discovered since the last failed submission.
- A reduction to a subclaim that is itself either `finite-verification` or `constructive-search`.
- A debate transcript dated within the last 14 days specifically identifying a computable subclaim.

If none of these exist, the target is **HELD**, not submitted. The protocol is debate-only.

**Examples (HOLD)**: Tuza ν=4 carcass — falsified approaches list (apex bridge, 6-packing, LP duality, universal apex) is on record; no new diagnostic exists. Lehmer totient — no new computable subclaim.

**Failure mode to flag**: Sketches that resurrect a falsified approach (`mk failed <keywords>` would have shown) as if it were new.

### `known-formalization`

**Criteria**:
- The mathematics is solved in the literature (a citation exists, often pre-2020).
- The remaining novelty is purely the Lean port.
- formal-conjectures tag is `@[category research solved]` or equivalent.

**Entry condition**: **EXCLUDED from active rotation.** Per user prime directive ("we care about novel solutions, not formalization"), these belong in a benchmark/regression-test lane, not in batches.

**Examples**: slot739 (Leinster D₃ × C₅ nonabelian witness — Leinster 2001).

**Failure mode to flag**: Hiding the "known" status by relabeling. If a debate transcript or a formal-conjectures tag identifies the result as solved, the rubric blocks the slot regardless of how it is phrased.

---

## Pre-Draft Classification Stanza

Every sketch (or accompanying ID/metadata file) MUST contain this 3–5 line stanza BEFORE the `OPEN GAP:` header:

```
FEASIBILITY: <category>
PARENT_SLOTS: <slotXXX, slotYYY or N/A>
ENTRY_CONDITION: <satisfied because: 1-line citation>
NOVELTY_CLAIM: <novel | half-novel | mechanical | benchmark>
```

- `category` ∈ {finite-verification, constructive-search, mechanical-extension, structural-open, known-formalization}
- `PARENT_SLOTS` cites prior Aristotle work this builds on.
- `ENTRY_CONDITION` is a one-line justification. For `structural-open`, name the fresh diagnostic. For `mechanical-extension`, name the parent skeleton + confirm no break point.
- `NOVELTY_CLAIM` is the agent's honest assessment. The audit phase verifies it.

The stanza lives in the `_ID.txt` companion metadata file, NOT in the `.txt` sketch itself. The gate's C3 check counts every non-blank, non-separator line in the sketch toward the 30-line budget; placing the stanza in `_ID.txt` keeps the bare sketch ≤ 30 lines per Hard Rule #3. The `_ID.txt` is read by the audit agent and (in v1.1) by `check_feasibility_label()`.

---

## Examples from the May 30 Batch

| Slot | Sketch | Category | Reasoning |
|------|--------|----------|-----------|
| slot736 | FT p=3 q ≡ 71 mod 72, q ≤ 1500 | `mechanical-extension` | slot720 parent; range bump only; no break in q ≤ 1500. q ≤ 2000 would cross q=1583 break. |
| slot737 | E647 Sophie residue subclass | `constructive-search` | Discovers stronger σ₀ bounds (6, 7 vs 4) via independent witness construction. Genuinely novel. |
| slot738 | Brocard [501, 1000] | `mechanical-extension` (half-novel) | slot722 parent skeleton, but Aristotle independently invented the 10×50 chunked encoding. The encoding refactor was a side-effect novelty; the headline target is mechanical. |
| slot739 | Leinster D₃ × C₅ nonabelian witness | `known-formalization` | Leinster 2001 result. formal-conjectures tag `@[category research solved]`. Should NOT have been in active rotation under this rubric. |
| slot740 | E203 index-1 8×8 cover impossibility | `constructive-search` (in falsification mode) | Aristotle found a 22-prime greedy set cover with explicit m. The "impossibility" framing was the question, but the recipe is constructive search. Disproof is the high-value outcome. |

**Lesson**: Of 5 May 30 slots, only **1** was genuinely novel under this rubric (slot737). Slot740 became novel by disproof, but it would have classified ex-ante as `constructive-search`, not `structural-open`. Slot739 should have been blocked.

---

## Integration with `check_gap_targeting()`

The existing gate enforces:
- C1: `.txt` only
- C2: non-empty
- C3: ≤ 30 non-blank lines
- C4: no strategy keywords
- C5: ≤ 5 lines of Lean code
- C6: not `(P) ∨ ¬P` (em-tautology)

This rubric adds a soft pre-gate (label check) and an integration recommendation:

1. **No code change required in `safe_aristotle_submit.py` for v1.0.** The Feasibility stanza lives in `_ID.txt` (companion metadata file). The drafting agent populates it; the audit agent verifies it.
2. **v1.1 (future)**: Add a `check_feasibility_label()` function called immediately before `check_gap_targeting()`. It reads the companion `_ID.txt`, parses `FEASIBILITY:`, and rejects unlabeled or `known-formalization` / un-cleared `structural-open` sketches.
3. **Audit checklist (v1.0)**: The audit agent reads every sketch in a batch and produces a row per sketch with: claimed category, verified category, BATCH/HOLD/REWORK recommendation, and reasoning.

---

## Decision Procedure (5 steps per candidate)

1. **Identify**: What is the bare claim? Existence, universal, impossibility, or counterexample?
2. **Classify**: Apply the criteria above. If two categories seem to fit, pick the more conservative (structural-open over constructive-search; known-formalization over mechanical-extension).
3. **Check entry condition**: Does the category-specific entry condition hold? If `structural-open` with no fresh diagnostic, STOP.
4. **Check `mk failed`**: For `structural-open` and `constructive-search`, query the failed-approaches table. If the current approach matches a falsified pattern, STOP.
5. **Write the stanza, write the sketch, submit.**

---

## Failure Mode Glossary

- **Polished irrelevance**: Sketch passes `check_gap_targeting()`, compiles, even gets a `compiled_advance` verdict, but the underlying claim does not address the real open question. Slot739 (Leinster 2001) is the prototype.
- **Mechanical extension dressed as novel**: A bound bump or one-index extension marketed as a new result. Mitigated by `NOVELTY_CLAIM` honesty field + audit verification.
- **EM-tautology pathology**: Already blocked by C6. Listed here for completeness.
- **Smuggled falsified approach**: An approach previously documented in `failed_approaches` is rephrased as a "fresh structural diagnostic." Audit MUST cross-reference `mk failed <keywords>` before approving `structural-open`.
- **Bound bump past a break point**: Mechanical extension into a range containing a known counterexample to the current proof skeleton. FT q ≤ 2000 is the canonical case.

---

## When to Update This Rubric

- After each batch audit, append any new failure pattern observed.
- If a category proves redundant (e.g., `mechanical-extension` collapses into `finite-verification`), merge in v2.0.
- The 5-category structure is provisional; the May 30 debate explicitly used 4. If a future batch reveals that the `mechanical-extension` distinction does not matter for audit purposes, fold it back into `finite-verification` and document the reasoning.

---

## Authority Trail

- Original concept: Gemini Round 1, May 30 debate ("Feasibility Filter").
- 4-category split: Codex/GPT-5.2 Round 1, May 30 debate.
- 5th category (`mechanical-extension`): Agent #10 (audit role), based on empirical batch analysis (slot736 + slot738 vs slot737).
- Hard rules from `/Users/patrickkavanagh/math/CLAUDE.md` and prime directive from `~/.claude/projects/.../MEMORY.md` remain authoritative. This rubric is layered policy, not replacement.

---

## Addendum — Mathematical Content Score + Paired LLM Axis (added 2026-05-30, v1.1)

The F-team audit found that 57% of historical `compiled_advance` rows were brute-force bounded extensions, not real mathematical content. The closure-axis taxonomy detects this post-hoc; the rubric layer below detects it ex-ante.

### `mathematical_content_score` (0-10)

Drafter-populated, audit-verified. Scored on the **mathematical content of the closure mechanism**, not the polish of the Lean proof.

| Score | Meaning | Examples |
|---|---|---|
| 0-2 | No new math. Bounded extension by parameter swap, formalization-only port, or restatement. | slot736 (FT q ≤ 1500 range bump); slot739 (Leinster 2001 port) |
| 3-4 | Mechanical witness construction, minor encoding refactor, finite verification with kernel sweep. | slot738 (Brocard [501,1000] with chunked encoding); brute `native_decide` runs |
| 5-6 | Discovers a stronger bound, identifies a new residual subclass, or constructs a non-trivial witness via a recipe (CRT, greedy cover, table lookup). | slot737 (E647 stronger σ₀ bounds); slot740 (22-prime greedy cover) |
| 7-8 | Resolves a subclaim of an open problem, finds a counterexample to a published conjecture, or invents a useful auxiliary set / invariant. | E124 (Aristotle alone, 6 hours); E481 (Barreto's solo Aristotle solve) |
| 9-10 | Closes a previously open research-level conjecture in a way that adds to journal-publishable knowledge. | E728 (with GPT-5.2 Pro paired); reserved for genuinely novel proofs |

**Scoring rule for honesty**:
- Score is bound by the closure-axis CS axis. If CS = `bounded_version_closure` → score ≤ 4. If CS = `formalization_only` → score ≤ 2. The combined REAL-closure rule (CS in {full_closure, direction_closure, disproof_closure} ∧ HM = journal_clean) is required for score ≥ 5.
- The drafter writes the score in the companion JSON; the audit phase verifies and may downgrade.
- Score ≥ 5 + `real_closure_candidate=true` is the gate for the closure lane.

DB column: `submissions.mathematical_content_score` (INTEGER, NULL pre-2026-05-30). Audit-populated.

### `paired_llm` (string | NULL)

For the FUSION lane: which informal-reasoner model produced the strategy outline in the `.fusion.json` companion. NULL for the BARE and CLOSURE lanes.

Allowed values (string, lowercase, one of):
- `claude-opus-4.7`
- `claude-sonnet-4.7`
- `gpt-5.2-pro`
- `gpt-5.4`
- `gemini-2.5-pro`
- `grok-4`
- `codex-cli`
- `multi` (when the FUSION companion fused outputs from 2+ models)

DB column: `submissions.paired_llm` (TEXT, NULL by default).

W-team finding (W8): we have historically never used the informal-reasoner subsystem of Aristotle. The `paired_llm` column tracks our adoption of the FUSION lane and lets us audit hit rates per pairing.

### Closure vs Fusion vs Informal vs Bare lane decision criteria

Per the I2 schema unification (May 30 2026), four lanes are persisted in `submissions.lane`:

| Criterion | BARE | CLOSURE | FUSION | INFORMAL |
|---|---|---|---|---|
| `submissions.lane` value | `bare` | `closure` | `fusion` | `informal` |
| Companion file | none | `.closure.json` | `.fusion.json` + airlock | none required |
| Sketch budget | ≤30 lines | ≤30 lines | ≤30 lines (companion ≤80) | bare problem statement |
| CLI flag | (default) | (companion-driven) | `--fusion-lane` | `--informal-mode` |
| `check_gap_targeting()` | enforced | enforced | enforced | enforced |
| `check_closure_axis()` | warn-only | enforced; `real_closure_candidate=true` or `--rubric-points` | per companion | warn-only |
| `mathematical_content_score` target | ≥3 | ≥5 | ≥5 | ≥5 |
| `paired_llm` | `none` | `none` | required | optional |
| `informal_mode_used` | 0 | 0 | 0 | 1 |
| Aristotle subsystem invoked | MCGS only | MCGS only | MCGS + research dossier | informal reasoner FIRST, then MCGS |
| Typical hit rate (empirical) | 0.8% (long-tail Erdős) | ~2-5% (est.; new lane) | unknown; new lane | unknown; new lane |
| Prototype | slot737 (constructive-search); slot740 (disproof) | (new lane, May 30 2026) | E728 (paired GPT-5.2 Pro) | E124 (Boris Alexeev, ~6 hours) |

**Decision rule**:
1. First submission of a new problem → BARE lane.
2. Bare lane returned `compiled_no_advance` and closure mechanism is known → CLOSURE lane.
3. Bare lane returned `compiled_no_advance` and closure mechanism is unknown → FUSION lane (after literature check + paired-LLM debate).
4. Mechanical extension of a prior `compiled_advance` → CLOSURE lane with `--rubric-points` override + honest `mathematical_content_score ≤ 4`.

The FUSION lane is the lever for W8: it is how we start using Aristotle's informal-reasoning subsystem. It is also the answer to F3's finding that 87% of historical LLM consultations were meta-process, not math — the FUSION lane routes the LLM strategy work into a companion file that is part of the submission, not into chat.

### Authority for v1.1

- Mathematical content axis: F1 audit (57% brute force) + W7 finding (closure-axis taxonomy is post-hoc; an ex-ante score is needed).
- Paired-LLM axis: W8 finding (Aristotle's informal-reasoner subsystem has never been used by this project).
- Lane decision criteria: I5 synthesis of F-team + W-team + I-team outputs (May 30 2026).

---

## Addendum — Closure-Axis Gate (added 2026-05-30, v1.0)

Layered on top of this rubric is a **machine-enforced** closure-axis gate. The Feasibility Categories above are an honest pre-classification by the drafter; the closure axis is the runtime artifact that gates submission.

### Where it lives

- **Spec**: `docs/closure_axis_companion_spec.md`
- **Taxonomy**: `docs/closure_taxonomy_may30.md` (CS / CM / CR / HM, the four axes)
- **Implementation**: `check_closure_axis()` in `scripts/safe_aristotle_submit.py`
- **DB**: `submissions.closure_axis_json` (TEXT, JSON-serialized; added by `scripts/migrate_add_closure_axis.py`)
- **Tests**: `docs/closure_gate_test.md`, `tests/closure_gate/`

### How to populate the companion file

For every sketch at `submissions/sketches/<name>.txt`, create a paired JSON file at `submissions/sketches/<name>.closure.json`:

```json
{
  "CS": "<one of: full_closure | direction_closure | disproof_closure | bounded_version_closure | sub_claim_closure | formalization_only>",
  "CM": "<one of: explicit_witness | bounded_to_infinite_lift | structural_finite_reduction | disproof_construction | witness_table_chunked | density_sieve_closure | induction_template | none_known>",
  "CR": "<one of: clean_decidable | partial_result_only | iff_rfl_trap | witness_search_explosion | definition_mismatch | em_tautology | infrastructure_overgrowth | recursive_falsification>",
  "HM": "<one of: journal_clean | journal_partial | journal_subclaim | infrastructure_only>",
  "real_closure_candidate": <bool: true iff CS in {full_closure, direction_closure, disproof_closure} AND CM != none_known AND CR in {clean_decidable, witness_search_explosion} AND HM == journal_clean>,
  "rationale": "<one English sentence naming the parent slot / falsified pattern avoided / honest scope statement>"
}
```

All six fields are required. Enum values are exact strings from `closure_taxonomy_may30.md`. The drafter sets `real_closure_candidate` honestly per the taxonomy's combined REAL-closure rule; the gate trusts that boolean and audits separately.

### Gate behavior

| Companion file | `real_closure_candidate` | `--rubric-points` flag | Outcome |
|---|---|---|---|
| missing | n/a | n/a | WARN + log `MISSING_CLOSURE_AXIS` to `aristotle_submission_log.jsonl`; **allow** (transition period) |
| present, invalid JSON or bad schema | n/a | n/a | REJECT (`ClosureAxisError`) |
| present, valid | `true` | n/a | PASS |
| present, valid | `false` | absent | REJECT — pass `--rubric-points` to override |
| present, valid | `false` | present | PASS, log `RUBRIC_POINTS_OVERRIDE` for audit |

The `--force` flag (informal-proof orchestrator pipeline) also bypasses this gate, identical to its gap-targeting behavior. Use sparingly.

### Mapping from Feasibility Category to closure axis (typical)

| Feasibility category | Typical CS | Typical HM | Typical `real_closure_candidate` |
|---|---|---|---|
| `finite-verification` | `bounded_version_closure` | `journal_partial` | `false` (requires `--rubric-points`) |
| `constructive-search` (true existence proven) | `full_closure` or `disproof_closure` | `journal_clean` | `true` |
| `mechanical-extension` | `bounded_version_closure` | `journal_partial` | `false` (requires `--rubric-points`) |
| `structural-open` (when finally tractable) | `full_closure` | `journal_clean` | `true` |
| `known-formalization` | `formalization_only` | `infrastructure_only` | `false` (requires `--rubric-points`, but should not be in active rotation per prime directive) |

The mapping is a heuristic, not an inference. The drafter must classify both layers independently. The audit phase cross-checks them.

### DB column

`submissions.closure_axis_json` is populated by `safe_submit()` immediately after Aristotle accepts the project, keyed by `uuid`. Rows from before this gate landed (pre-2026-05-30) have `closure_axis_json = NULL`. No backfill is planned for v1.0.

Useful query — find any submission that was counted as `compiled_advance` but was honestly a bounded version:

```sql
SELECT id, filename, status,
       json_extract(closure_axis_json, '$.CS') AS cs,
       json_extract(closure_axis_json, '$.HM') AS hm
  FROM submissions
 WHERE status LIKE 'compiled_advance%'
   AND json_extract(closure_axis_json, '$.CS') = 'bounded_version_closure';
```

