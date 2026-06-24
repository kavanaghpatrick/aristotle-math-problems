# Summary of changes for run 14531689-1485-45f2-80d8-6247306fdd02
## Erdős Problem 942: limsup of powerful-counts in [n², (n+1)²) is infinite

I formalized the proof of `erdos_942.variants.limsup : atTop.limsup ((fun n ↦ (n : ℕ∞)) ∘ erdos_942.h) = ⊤` in the file `RequestProject/Erdos942.lean`.

### What was proved

The proof establishes the following chain of lemmas, all fully proved except one:

1. **`sq_mul_cube_isPowerful`** ✅ — Any `u² · v³` with `u, v ≥ 1` is powerful. Uses a p-adic valuation case split: if `p | u` then `p² | u²`; if `p | v` then `p³ | v³`.

2. **`golomb_distinct`** ✅ — If `p₁ ≠ p₂` are primes and `u₁²p₁³ = u₂²p₂³`, contradiction. The `p₁`-adic valuation of the LHS is odd (2k+3) while the RHS is even (2k).

3. **`sqrt_witness`** ✅ — For `u > 0`, setting `n = Nat.sqrt(u²p³)` gives `n² ≤ u²p³ < (n+1)²`.

4. **`kronecker_construction`** ⚠️ **sorry** — For any finite set of distinct primes and any `N`, there exists `n ≥ N` with witnesses `u_i` such that `u_i²p_i³ ∈ [n², (n+1)²)` for each prime `p_i`. This requires Kronecker's theorem on simultaneous Diophantine approximation, which is not available in Mathlib.

5. **`h_ge_of_distinct_powerful`** ✅ — Given witnesses from the construction, proves `h(n) ≥ ps.card` by constructing an injection from the prime set into the filtered finset of powerful numbers.

6. **`exists_prime_finset`** ✅ — For any `M`, there exists a finset of `M` primes (using `Nat.nth`).

7. **`h_frequently_large`** ✅ — For any `M` and `N`, there exists `n ≥ N` with `h(n) ≥ M`. Combines lemmas 4, 5, and 6.

8. **`variants.limsup`** ✅ — The main theorem: `limsup h(n) = ⊤`. Uses `h_frequently_large` with `Filter.limsup_eq_iInf_iSup_of_nat` and `iInf_eq_top`.

### The remaining sorry

The sole sorry is `kronecker_construction`, which encapsulates the analytic number theory content: **Kronecker's theorem on simultaneous Diophantine approximation**. Specifically, it requires showing that for Q-linearly independent irrationals `β₁, …, β_M` (where `β_i = p_i^{-3/2}`), the fractional parts `{n·β_i}` simultaneously land in prescribed intervals for infinitely many `n ∈ ℕ`. This is a deep result that is mathematically well-known (proved by Kronecker in 1884, with quantitative strengthening by Weyl) but is not formalized in Mathlib. The required infrastructure (equidistribution on tori, Q-linear independence of radical expressions) would constitute a significant independent formalization effort.

### Project structure

- `RequestProject/Erdos942.lean` — Complete formalization (≈140 lines), compiles cleanly with one sorry warning.