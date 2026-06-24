# Summary of changes for run cee543e6-a30d-4bf6-b978-0c7cc370a6bb
## Result

I have formally proved in Lean 4 that there are infinitely many odd, squarefree Sierpinski numbers:

```lean
theorem squarefree_odd_sierpinski_infinite :
    {k : ℕ | Odd k ∧ Squarefree k ∧ ∀ n : ℕ, 0 < n → ¬ Nat.Prime (k * 2^n + 1)}.Infinite
```

The proof compiles without any `sorry`, using only standard axioms (`propext`, `Classical.choice`, `Lean.ofReduceBool`, `Lean.trustCompiler`, `Quot.sound`).

## Proof Strategy

Despite being listed as an open problem, the result follows from combining two classical ingredients:

### 1. Selfridge Covering System
The primes S = {3, 5, 7, 13, 17, 241} with multiplicative orders {2, 4, 3, 12, 8, 24} form a covering system of ℤ. By CRT, the residue k₀ = 2931991 (mod P = 5592405) satisfies: for every k ≡ k₀ (mod P) and every n ≥ 1, some prime p ∈ S divides k·2ⁿ+1. Since k > 241 ≥ p, this makes k·2ⁿ+1 composite, hence k is Sierpinski.

### 2. Dirichlet's Theorem on Primes in Arithmetic Progressions
Since gcd(k₀, P) = 1, Dirichlet's theorem (available in Mathlib as `Nat.infinite_setOf_prime_and_eq_mod`) gives infinitely many primes q ≡ k₀ (mod P). Each such prime q is:
- **Odd**: q > 241 > 2, so q ≠ 2
- **Squarefree**: primes are squarefree
- **Sierpinski**: by the covering system argument above

The key insight is that the BBMST 2022 obstruction (no covering system has all-odd-squarefree *moduli*) is irrelevant here — squarefreeness is required of k (the residue variable), not of the covering moduli.

## File Structure

- `RequestProject/CoveringFacts.lean`: Computational verification of the 24 covering cases using `norm_num`, plus divisibility and primality facts for the Selfridge primes.
- `RequestProject/Main.lean`: The main proof, structured as:
  - `pow_two_mod_period`: Periodicity of 2ⁿ mod p (since 2²⁴ ≡ 1)
  - `dvd_of_cover`: Lifting from base cases to all n and k in the AP
  - `exists_cover_dvd`: Combining the covering system
  - `not_prime_of_cover`: The Sierpinski property
  - `squarefree_odd_sierpinski_infinite`: The main theorem via Dirichlet