# Summary of changes for run 6e37aeee-7abb-48e6-bd90-4fd8d2775412
## Erdős Problem 942 — Limsup Variant

**Result:** Formalized the theorem `erdos_942.variants.limsup`:
```
atTop.limsup (((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ erdos_942.h)) = ⊤
```
where `h(n)` counts powerful (squarefull) integers in [n², (n+1)²).

### File: `RequestProject/Erdos942.lean`

**Proof strategy (Golomb + Kronecker):** For any target M, pick M distinct primes p₁,…,p_M. By Golomb's parametrization, a²pᵢ³ is powerful. The condition a²pᵢ³ ∈ [n², (n+1)²) reduces to a simultaneous Diophantine approximation problem. Besicovitch's theorem (Q-linear independence of square roots of distinct primes) combined with Kronecker's multi-dimensional approximation theorem guarantees infinitely many n satisfying all M conditions simultaneously, giving h(n) ≥ M for arbitrarily large M.

### What is proved (no sorry):
1. **`powerful_of_sq_mul_cube`** — a²p³ is powerful when a ≥ 1 and p is prime
2. **`sq_mul_cube_injective`** — a²p³ = b²q³ with p ≠ q prime implies contradiction (via p-adic valuation parity)
3. **`card_powerful_le_h`** — subset cardinality bound for h(n)
4. **`erdos_942.h_ge_of_approx`** — M distinct a_i²p_i³ in [n², (n+1)²) implies h(n) ≥ M, using (1)+(2) for powerfulness and distinctness
5. **`erdos_942.h_frequently_ge`** — for every M, ∃ᶠ n in atTop, M ≤ h(n) (uses the i-th prime enumeration `Nat.nth`)
6. **`erdos_942.variants.limsup`** — the main theorem, derived from (5)

### What remains sorry'd (1 sorry):
- **`simultaneous_approx_primes`** (line 110): The combined Besicovitch–Kronecker result — for any M distinct primes and any N, there exists n ≥ N with aᵢ ≥ 1 satisfying n² ≤ aᵢ²pᵢ³ < (n+1)² for all i. This encapsulates two classical results absent from Mathlib4:
  - **Besicovitch (1940):** Q-linear independence of {1, √p₁, …, √p_M} for distinct primes
  - **Kronecker's simultaneous approximation:** density of (nβ₁ mod 1, …, nβ_M mod 1) in [0,1)^M when 1, β₁, …, β_M are Q-linearly independent

Both are well-established mathematics (the limsup result is described as "not hard to prove" by Erdős; De Koninck–Luca–Shparlinski 2005 give the quantitative strengthening h(n) ≫ (log n)^{1/3+o(1)} i.o.), but formalizing them requires infrastructure for multi-variable equidistribution and algebraic number theory (field extension degrees) that Mathlib4 does not yet provide.

### Summary
The main theorem is **conditionally proved**: all mathematical reasoning is formalized except the Besicovitch–Kronecker step, which is a precisely identified and clearly documented Mathlib gap. The proof architecture (Golomb parametrization → counting → Kronecker density → limsup) is fully verified.