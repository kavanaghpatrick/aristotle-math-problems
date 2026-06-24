# Failure DNA Catalog — compiled_no_advance Traps

**Date**: 2026-05-30
**Agent**: #3 of 10 (problems-database sweep)
**Sample**: 25 result files inspected across 24 distinct problem_ids; tuza_nu4 examined separately

## Sample Origin

Total `compiled_no_advance` in DB: **742**. tuza_nu4 alone: **216** (29%).

Top trap-prone problem_ids (excluding tuza_nu4):

| problem_id | no_advance count |
|------------|------------------|
| `<unlabeled>` | 13 |
| leinster | 8 |
| feit_thompson | 8 |
| sierpinski_5n | 7 |
| path4_tau_le_8 | 7 |
| erdos850 | 7 |
| tuza_nu3 | 6 |
| erdos_1 | 5 |
| tau_le_8 | 4 |
| agoh_giuga | 4 |

## Failure Modes (frequency in sample of 25)

### F1. Restate-and-define (Iff.rfl trap) — 11/25 (44%)

Open conjectures with non-decidable predicates. Aristotle defines `answer := <Statement>` then proves `theorem foo : answer ↔ Statement := by rfl` (or `Iff.rfl`, `bound`).

**Examples**: slot697 (erdos470 odd weird), slot696 (erdos412 iterated sigma), slot700 (erdos252 irrationality), slot684 (hadamard), slot682 (artin), slot681 (bunyakovsky), slot689 (jacobian), slot686 (HL1), slot679 (HL2), slot692 (erdos1052), slot700.

**Red flag**: Sketch RHS uses `Irrational`, `IsEquivalent`, `HasDensity`, `Tendsto`, `Set.Finite/Infinite` with no finite restriction.

**Diagnostic**: If you cannot turn the conjecture into `∀/∃ x ∈ Finset.range N, P x` with explicit N, the slot will produce a definitional tautology.

### F2. Excluded middle (P ∨ ¬P) tautology — 2/25 (8%)

Sketches phrased as "X exists OR no X exists" — Aristotle closes with `exact em _`.

**Examples**: slot717_erdos850_bare, slot719_erdos850_bare_then_ask.

**Red flag**: `∨ ¬ ∃` or `∨ ¬ ∀` in the theorem. Already documented in `feedback_em_tautology_antipattern.md`. Gate C6 blocks new submissions, but legacy ones slipped through.

### F3. Side-lemma proliferation without main target — 7/25 (28%)

Aristotle produces 30-100 helper lemmas (recurrences, modular periodicities, gcd analyses) for the structural problem but never closes the main theorem.

**Examples**:
- slot703_erdos672_ap: 1148 lines of Pell / SeqA / SeqB infrastructure
- slot698_erdos672: Pell periodicity mod 17, 8, 5 — main theorem unstated
- slot705_erdos850_smooth_diff: 15+ lemmas about smooth-difference, no main theorem
- slot691_arithmetic_sums: `S_eq_zero` for primes, `conj_1_1_false`, but never closes conj 4.3
- slot676, slot687, slot677

**Red flag**: Sketch contains "reduces to" or "follows from a well-known infinite descent / Pell / sieve" without naming the precise finite obstruction that closes it.

**Diagnostic**: If the conjecture requires an unbounded argument (infinitely many, asymptotic, "for all n") and NO parent slot has done the structural legwork, the result will be infrastructure-without-target.

### F4. Axiomatize-the-hard-part (exact?/sorry stubs) — 4/25 (16%)

Aristotle peppers proofs with `exact?` calls that fail silently (left in result file) or references undefined names. Effectively axiomatizes parts of the proof.

**Examples**: slot698 (multiple `exact?` after `have h_recurrence`), slot687 (`apply pell_valuation_mul_prime'` defined recursively as `exact?`), slot705 (`exact?` for `h_parity`, `h_mod_3`), slot650 (`apply lemoine_upto_1000_corrected` then `exact?`).

**Red flag**: Sketch references "classical" or "standard" facts without identifying the exact Mathlib name. Aristotle leaves an `exact?` hole that compiles to "tactic failed but typechecks" — silent axiom.

### F5. Counterexample disproves own scaffolding (recursive falsification) — 3/25 (12%)

On Tuza ν=4 family, Aristotle constructs a "witness" graph but the witness fails to satisfy a precondition, and the proof ends with a corollary that contradicts the original lemma's premise.

**Examples**:
- slot543_bad_bridge_counterexample: proves slot542's `bridge_has_apex_in_bridge` is FALSE on a concrete 11-vertex graph
- slot541_bridge_coverage_integration
- slot113_conservative_bound (cycle4 with diag-condition that already excludes the hard case)

**Red flag**: Sketch is about a specific apex / bridge / cycle sub-configuration of Tuza ν=4 with no fresh structural diagnostic.

### F6. Restate-with-sorry (target = sorry, scaffold compiled) — 4/25 (16%)

Tuza/path4 specifically. Aristotle file says "Aristotle took a wrong turn (reason code: 9)" or "Aristotle failed to find a proof.", then dumps the target theorem with `:= by sorry`, often with a multi-step plan in a comment.

**Examples**: slot327_tau_le_8_final (`tau_le_8 := by sorry`), all 7 `path4_tau_le_8` slots.

**Red flag**: Sketch is `tau_le_X` for a Tuza sub-case requiring 3+ unproved auxiliary lemmas not yet on any parent slot.

### F7. Bounded verification dressed as infinite claim — 3/25 (12%)

Aristotle proves a stronger bounded version (Lemoine for n ≤ 1000, Conj 4.3 for k ≤ 3135) instead of the unbounded conjecture. Compiles; gap unmoved.

**Examples**: slot650_lemoine (`lemoine_upto_1000_final`), slot676 (`conj_4_3_verified_3253/57/59`), slot669 (`conj_4_3_verified_3120_3130`).

**Red flag**: Sketch is unbounded `∀ n, P n` but prior context shows Aristotle solved small ranges. If GENUINELY unbounded with no known computable reduction, it's `structural-open` → HOLD.

### F8. Wrong direction or vacuous equivalence — 2/25 (8%)

Aristotle proves `A ↔ B` where one direction is trivial, or proves the conjecture is equivalent to its own definition.

**Examples**: slot697 (`erdos_470.part1 : answer ↔ ∃ n, n.Weird ∧ Odd n` via `rfl`), slot696 (`erdos_412 : answer ↔ ...` via `Iff.rfl`).

**Red flag**: LHS and RHS of the iff differ only by definitional unfolding. NEVER submit this shape.

### F9. Computational explosion (native_decide budget overrun) — 2/25 (8%)

Aristotle frames verification as `native_decide` that times out or proves a too-narrow range, leaving the open part untouched.

**Examples**: slot650_lemoine (settled for 1000 after attempting larger), slot684_hadamard (only k=0, k=1 — kernel exhausted on k=2 because 8x8 matrices).

**Red flag**: Decidable predicate has fan-out exceeding the per-cell budget (e.g., 4 nested `interval_cases` on 1000-element range).

### F10. Definition mismatch with formal-conjectures — 2/25 (8%)

Aristotle introduces its own `def IsX` that differs from the upstream Mathlib / formal-conjectures definition.

**Examples**: slot689_jacobian (custom `RegularFunction`, `jacobianDet` instead of Mathlib's `MvPolynomial.aeval`), slot688_regular_primes (custom `KummerCriterion`).

**Red flag**: Sketch defines new `Prop` from scratch instead of opening the formal-conjectures statement.

## Tuza ν=4 Dominant Mode (special call-out)

**Total**: 317 submissions, **216 compiled_no_advance** (68% no-advance rate).

**Dominant mode**: F5 + F6 combined — side-lemma proliferation plus restate-with-sorry, with frequent recursive falsification (slot543 disproving slot542).

**Structural diagnosis**:
- Tuza ν=4 has NO known computable subclaim
- MEMORY.md FALSIFIED list: "Apex-based bridge coverage, 6-packing, LP duality, universal apex" — all dead ends
- 317 submissions chased apex / bridge / cycle4 / path4 sub-configurations
- Each compiled some partial lemma; the main `tau_le_8 ∃ E, E.card ≤ 8 ∧ isTriangleCover G E` remained sorried (slot327) or was attacked via auxiliary defs that turned out to be falsifiable (slot543 disproved slot542's apex claim)
- The `feasibility_filter_rubric.md` classifies tuza_nu4 as `structural-open` with **HOLD** entry condition: "no new diagnostic exists"

**Lesson**: All 216 tuza_nu4 no_advance submissions retroactively confirm the rubric. Submitting without a fresh structural diagnostic on a falsified-approach-saturated problem produces polished irrelevance.

## Top 3 "Avoid These Problem Shapes" Rules

1. **No undecidable wrapper.** If the conjecture cannot be made `Decidable` over a finite range, do NOT submit a sketch that "defines `answer` and proves `answer ↔ Statement`". The submission will produce F1/F8 (Iff.rfl / answer-tautology). Examples: erdos412 (iterated sigma collision), erdos470 (odd weird), jacobian, hadamard general k, bunyakovsky, artin.

2. **No structural sub-lemma on falsified-approach problems.** If a structural conjecture has no computable subclaim AND prior submissions have left falsified-approach records, do NOT submit another structural sub-lemma. Examples: tuza_nu4, path4_tau_le_8, leinster, agoh_giuga. Result: F5/F6 (recursive falsification + restate-with-sorry). Per rubric: HOLD.

3. **No unbounded Pell / sieve / density without finite reduction.** If the conjecture involves Pell sequences, infinite descent, or unbounded universal quantification over an analytic predicate (asymptotic, density, irrationality), do NOT submit unless a parent slot has reduced it to a `Decidable` finite check. Otherwise Aristotle produces 1000-line infrastructure (F3) AND leaves `exact?` stubs (F4). Examples: erdos672 (Pell), erdos251, arithmetic_sums (conj 4.3), pell_primes, hardy_littlewood 1/2.

## Pre-Submission Red Flag Checklist

| Code | Pattern | Trigger Symptom |
|------|---------|-----------------|
| F1 | Restate-and-define | `Irrational`, `IsEquivalent`, `HasDensity`, `Tendsto`, `Set.Finite/Infinite` w/o finite restriction |
| F2 | EM tautology | `∨ ¬ ∃` or `∨ ¬ ∀` (gate C6 blocks; legacy slipped through) |
| F3 | Infrastructure overgrowth | "reduces to" / "by infinite descent / Pell / sieve" without explicit finite obstruction |
| F4 | Axiomatize-the-hard | "by classical X" / "follows from standard Y" without exact Mathlib lemma name |
| F5 | Recursive falsification | Apex / bridge / cycle sub-config of falsified-approach problem |
| F6 | Restate-with-sorry | `tau_le_X` for Tuza sub-case requiring 3+ unproved auxiliaries |
| F7 | Bounded leak | Unbounded universal that secretly accepts a 1000-range answer |
| F8 | Vacuous iff | `answer ↔ <verbatim definition>` |
| F9 | Compute explosion | `native_decide` fan-out ≥ 10^8 cells |
| F10 | Def mismatch | Sketch redefines `Prop` instead of importing formal-conjectures |
