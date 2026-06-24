# Summary of changes for run 706abe1b-76b9-4455-b002-b285086bb00b
## Powerful Numbers Parametrization — Fully Proved

I formalized and proved the characterization of powerful numbers: for n ≥ 1,

> **n is powerful ⟺ ∃ a b ≥ 1 with b squarefree and n = a² · b³**

The proof is in `RequestProject/Main.lean` and compiles without `sorry`, using only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

### Structure

1. **Definition** `Nat.Powerful n`: every prime p dividing n satisfies p² ∣ n.

2. **Reverse direction** (`powerful_of_sq_mul_cube`): If n = a² · b³ with squarefree b, then n is powerful. For any prime p ∣ n, by `Nat.Prime.dvd_mul` either p ∣ a² (giving p² ∣ a² ∣ n) or p ∣ b³ (giving p ∣ b, hence p² ∣ b² ∣ b³ ∣ n).

3. **Forward direction** (`sq_mul_cube_of_powerful`): Given powerful n ≥ 1, construct witnesses via the prime factorization:
   - b = ∏ p over primes with odd v_p(n), each taken to the first power
   - a = ∏ p^{(v_p(n) − 3·(v_p(n) mod 2))/2} over all prime factors
   
   The arithmetic identity v_p(n) = 2·e_p + 3·f_p (with f_p ∈ {0,1}) is verified by `aux_arith` (proved by `omega`). The factorization identity n = a² · b³ follows from `Nat.factorization_prod_pow_eq_self` and `Finset.prod_mul_distrib`. Squarefreeness of b holds since each prime appears with exponent ≤ 1.

4. **Main theorem** (`powerful_parametrization`): combines both directions via `Iff.intro`.

### Key Mathlib infrastructure used
- `Nat.factorization`, `Nat.factorization_prod_pow_eq_self`
- `Nat.squarefree_iff_prime_squarefree`, `Nat.Prime.pow_dvd_iff_le_factorization`
- `Finset.prod_mul_distrib`, `Finset.prod_pow`, `Finset.prod_filter`