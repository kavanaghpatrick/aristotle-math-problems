# E938 Fusion-Lane Validation Watch

Date: 2026-05-30
Slot: 752
Aristotle Project ID: `e561c214-eb4c-42a1-87ea-7b49ea0439c2`
Problem: erdos_938 — finite many 3-term APs of consecutive powerful numbers
Lane (DB): `informal` (informal-mode routing took precedence per I9, fusion identity preserved in `fusion_json`)
Paired LLM: `mixed` (F5 analysis + I7 Grok+Gemini+Codex debate)
Real closure candidate: `false` — submitted under `--rubric-points` override
Named technique: Frey-Hellegouarch curve + Ribet level-lowering with kernel control
Fit score: 0.3
Plausibility of full closure: F5=4/10, I7 Bayesian ~0.20 (Frey-Ribet alone)

## Purpose

This is the FIRST end-to-end fusion-lane submission. Per S10, it is the
kill/validate experiment for the entire research-fusion pipeline (S1-S10
component chain feeding paired-LLM companions into Aristotle's informal
reasoner).

Outcome interpretation:
- ANY ONE of the four criteria below firing in Aristotle's return = pivot
  validated, lane is real.
- ZERO criteria = the pipeline routed structured strategic content but
  Aristotle did not engage with it, and the lane is shelved.

## The Four Validation Criteria

When Aristotle's result returns (`/fetch 752` or
`python3 scripts/aristotle_fetch.py fetch 752`), check the summary, the
`.lean` file, and any reasoning trace for the following:

### Criterion 1: Bennett-Skinner / Frey-Hellegouarch citation
Look in Aristotle's natural-language summary / reasoning output for any
of:
- "Bennett-Skinner", "Bennett and Skinner", arXiv:math/0309108
- "Frey-Hellegouarch", "Frey curve", "Hellegouarch"
- "level-lowering", "Ribet's theorem", "Ribet level-lowering"
- "modularity theorem" applied to the specific curve
  `Y^2 = X(X - n_k)(X + delta)`

Verifies: companion JSON's `named_technique` and
`seminal_paper_arxiv` reached the reasoner's strategic context.

### Criterion 2: Mathlib `ModularForms.*` or `EllipticCurve.*` import
Inspect the returned `.lean` file's import block:
```bash
grep -E "^import Mathlib\.(NumberTheory\.ModularForms|AlgebraicGeometry\.EllipticCurve|NumberTheory\.LSeries|NumberTheory\.GaloisRepresentations)" submissions/nu4_final/slot752_result.lean
```
Any hit = Aristotle wired modular-form / elliptic-curve scaffolding into
the formal proof, not just pattern-matched powerful-number lemmas.

Verifies: structural Lean engagement with the bridge_lemma, not just a
top-level `sorry` or trivial reduction.

### Criterion 3: NL reasoning trace separate from Lean source
Check whether Aristotle returned a natural-language reasoning artifact
*distinct from* the `.lean` proof. Possibilities:
- A `.md` / `.txt` companion file alongside the result
- A "reasoning_trace" / "summary" / "strategy" field in the API response
- Comments inside the `.lean` file blocking out a multi-step strategy
  (Step 1, Step 2, ...)

Verifies: the informal-mode path (I9) produced a two-channel response —
formal Lean + informal strategic narrative — which is the canonical
fusion-lane payload signature.

### Criterion 4: Non-trivial `frey_conductor_bound` or `ribet_kernel_lowering` partial
Search the returned `.lean` for any of the named candidate lemmas from
the companion JSON:
- `frey_conductor_bound`
- `ribet_kernel_lowering`
- `empty_cusp_space_finite`
- `consecutive_square_gap`
- `chan_partial_bound`
- `bombieri_lang_finite_points`
- `pila_wilkie_residual_count`
- `general_type_surface`
- `frey_curve_attach`
- `powerful_density_asymptotic`

For ANY hit, also verify it is NOT a bare `sorry`:
```bash
grep -B 1 -A 10 "frey_conductor_bound\|ribet_kernel_lowering" submissions/nu4_final/slot752_result.lean
```
A lemma stub with a partial proof body (even a few `have` lines before a
remaining `sorry`) = the reasoner consumed and operated on the
candidate-lemma scaffold.

Verifies: structured fusion content drove decomposition, not just
shallow surface citation.

## Failure Modes to Watch For

- **Aristotle returns a trivial `sorry` over the original theorem
  statement**: companion JSON ignored, pipeline did NOT route content
  effectively. All four criteria zero.
- **Aristotle ignores the informal section and produces a `bare` style
  attempt**: informal-mode routing failed silently — check
  `informal_mode_used=1` was preserved and the prompt actually carried
  the 5943-char informal payload (logged at submission time).
- **Aristotle attempts the Frey curve but discharges with `decide` /
  `simp` / EM**: would also be a fail; the gate caught EM-tautology
  precisely to prevent this regression.

## Pivot Decision Rule (per S10)

| Criteria firing | Decision |
|-----------------|----------|
| 0 / 4 | Shelve fusion lane. Treat as too costly relative to bare-gap baseline. |
| 1 / 4 | Lane validated. Continue but tighten companion JSON; investigate which channel landed. |
| 2-3 / 4 | Lane strongly validated. Scale to additional problem_ids. |
| 4 / 4 | Pivot confirmed. Fusion is the new default for high-difficulty problems. |

## Operational Checks After Fetch

```bash
# 1. Fetch the result
python3 scripts/aristotle_fetch.py fetch 752

# 2. Inspect result file
ls -la submissions/nu4_final/slot752_*

# 3. Run criterion checks
grep -i "bennett\|frey\|hellegouarch\|level-lowering\|ribet\|modularity" submissions/nu4_final/slot752_result.lean submissions/nu4_final/slot752_*.md 2>/dev/null

grep -E "^import Mathlib\.(NumberTheory\.ModularForms|AlgebraicGeometry\.EllipticCurve|NumberTheory\.LSeries|NumberTheory\.GaloisRepresentations)" submissions/nu4_final/slot752_result.lean

grep -E "frey_conductor_bound|ribet_kernel_lowering|empty_cusp_space_finite|consecutive_square_gap|chan_partial_bound" submissions/nu4_final/slot752_result.lean

# 4. Audit gap-resolution
python3 scripts/audit_proven.py submissions/nu4_final/slot752_result.lean

# 5. Update DB with verdict
sqlite3 submissions/tracking.db "UPDATE submissions SET status=..., target_resolved=..., notes=... WHERE uuid='e561c214-eb4c-42a1-87ea-7b49ea0439c2';"
```

## Artifacts on Submission Side

- Sketch (txt): `submissions/sketches/erdos938_fusion.txt`
- Fusion companion: `submissions/sketches/erdos938_fusion.fusion.json`
- Closure axis: `submissions/sketches/erdos938_fusion.closure.json`
- ID file: `submissions/sketches/erdos938_fusion.ID.txt`
- Tracking ID file: `submissions/nu4_final/slot752_ID.txt`
- Submission hash: `73562808879abde8`
