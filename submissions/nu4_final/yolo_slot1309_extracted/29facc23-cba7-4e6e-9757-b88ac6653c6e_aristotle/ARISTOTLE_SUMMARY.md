# Summary of changes for run 29facc23-cba7-4e6e-9757-b88ac6653c6e
# Erdős Problem 1052 / Wall k=3 — Formalization Report

## What was accomplished

I created `RequestProject/Erdos1052.lean` containing a clean formalization of Erdős Problem 1052 (primitive divisors of Lehmer sequences at the Wall k=3 stratum).

### Definitions (fully formalized)
- **`LehmerSeq R Q n`**: The integer Lehmer sequence via the parity-dependent recurrence (computable, returns `ℤ`)
- **`lehmerTermComplex α β n`**: The complex closed-form Lehmer term (αⁿ−βⁿ)/(α−β) or (αⁿ−βⁿ)/(α²−β²)
- **`IsLehmerPair R Q`**: Structure encoding all Lehmer pair conditions
- **`IsPrimitiveDivisor R Q n q`**: Predicate for primitive divisors
- **`IsRootOfUnity z`**: Predicate for roots of unity in ℂ
- **`lehmer_term α β hR hQ n`**: Integer-valued Lehmer term from complex parameters

### Theorems proved (no sorry)
- Basic values: `LehmerSeq_zero`, `LehmerSeq_one`, `LehmerSeq_two`, `LehmerSeq_three`, `LehmerSeq_four`
- Recurrence relations: `LehmerSeq_even_succ_succ`, `LehmerSeq_odd_succ_succ`
- Algebraic identity: `pow_sub_pow_recurrence`
- Helper lemmas: `sum_ne_zero_of_sq_pos`, `sq_sub_sq_ne_zero`
- Complex recurrences: `lehmerTermComplex_even_recurrence`, `lehmerTermComplex_odd_recurrence`
- **`LehmerSeq_eq_lehmerTermComplex`**: The integer recurrence agrees with the complex closed form (proved by strong induction, decomposed into 4 helper lemmas)
- **`erdos_1052_wall_k3_of_bhv`**: The Wall k=3 case follows from the full BHV theorem

### Theorems stated but left as sorry (3 total)
- **`erdos_1052_wall_k3_int`** and **`erdos_1052_wall_k3`**: The main theorem in integer and complex formulations
- **`bilu_hanrot_voutier`**: The full Bilu-Hanrot-Voutier theorem (n > 30 implies primitive divisor exists)

## Why the main theorem remains open in Lean

The BHV theorem (2001) was proved using Baker's theory of linear forms in logarithms of algebraic numbers. This deep analytic number theory machinery is entirely absent from Mathlib. Formalizing it would require:
1. Baker's theory (effective lower bounds for |β₁ log α₁ + ... + βₙ log αₙ|)
2. Effective solutions of Thue-Mahler equations
3. Computational verification for finitely many exceptional cases
4. Cyclotomic polynomial divisibility theory

The suggested Heegner-point approach (via Gross-Zagier, Kolyvagin) is equally unformalizable and additionally contains a genuinely conjectural "bridge" step (connecting primitive-divisor-freeness to bounded Heegner heights) that has no published justification.

## Note on the target signature

The user's suggested signature had `α + β ∈ Set.range (Int.cast : ℤ → ℂ)`, but for a **Lehmer** pair, α + β = √R (not an integer), so the correct condition is `(α + β)² ∈ ℤ`. The formalization uses this corrected version. (The original condition would describe a **Lucas** pair instead.)