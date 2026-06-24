# Summary of changes for run 5fdd71fe-2d6c-4e1f-b209-4389478ac1f0
## Erdős 1052 / Wall k=3 — Formalization Summary

### What was accomplished

The file `RequestProject/Erdos1052.lean` contains a formalization of the Erdős 1052 / Wall k=3 primitive divisor theorem for Lehmer sequences.

**Definitions provided:**
- `IsRootOfUnity'` — predicate for complex roots of unity
- `lehmer_term_complex` / `lehmer_term` — the n-th Lehmer number U_n(α,β) as a complex number and as an integer
- `IsPrimitiveDivisor` — predicate for primitive prime divisors

**Fully proved lemmas (no sorry):**
- `lehmer_term_is_integer` — For a Lehmer pair, every Lehmer term is an algebraic integer. Proved by strong induction using the recurrence relation with integer coefficients.
- `lehmer_term_ne_zero` — If α/β is not a root of unity and αβ ≠ 0, then U_n ≠ 0 for all n ≥ 1. Proved by contrapositive, showing U_n = 0 implies α/β is a root of unity.

**Main theorem (`erdos_1052_wall_k3`):**
The reduction from the main theorem to the key lemma is fully verified — given `lehmer_primitive_part_nontrivial`, the main theorem follows by extracting a prime factor of the primitive part using `Int.exists_prime_and_dvd`.

### What remains (1 sorry)

**`lehmer_primitive_part_nontrivial`** — This is the core of the Bilu-Hanrot-Voutier (BHV) theorem: for n > 30, the "primitive part" Φ*_n(α,β) has absolute value > 1 and its prime factors are all primitive divisors of U_n.

This lemma requires **Baker's theory of linear forms in logarithms**, which is not currently available in Mathlib. Specifically, it needs:
1. The cyclotomic factorization of Lehmer numbers: U_n = ∏_{d|n} Φ*_d(α,β)
2. Baker-type lower bounds on |Φ*_n(α,β)| for large n
3. The arithmetic property that prime factors of Φ*_n don't divide Φ*_d for d &lt; n

### Note on the statement

The original target signature was modified to add the non-degeneracy hypothesis `hne : α * β ≠ 0`, which is part of the standard Lehmer pair definition (Q ≠ 0). Without this, α = β = 0 provides a trivial counterexample where all Lehmer terms are 0 and no primitive divisor exists.

### Mathematical context

The result is mathematically settled — it follows from the full BHV theorem (Bilu-Hanrot-Voutier, Crelle's Journal 539, 2001), which proves primitive divisors exist for ALL n > 30 (not just those divisible by 3). However, formalizing the proof requires building Baker's theory from scratch, which is a major formalization project in its own right.