# Summary of changes for run e32a4620-7495-4654-b680-0996c098bc9a
## Erdős Problem 672 (k=4, l=3) — Partial Formalization

### Problem
Prove that for any positive integers n and d with gcd(n, d) = 1, the product n(n+d)(n+2d)(n+3d) is never a perfect cube.

### Status: Partial progress — 2 sorry's remain

This is a known theorem (Hajdu-Tengely-Tijdeman 2009; Győry-Hajdu-Pintér 2009) but its proof requires deep number theory not yet available in Mathlib. The formalization makes substantial structural progress.

### What was proved (7 lemmas, all sorry-free):

1. **`ap_product_identity`**: The algebraic identity n(n+d)(n+2d)(n+3d) = (n²+3nd+d²)² - d⁴
2. **`ap_product_factor`**: Factorization as n(n+3d) · (n+d)(n+2d)
3. **`ap_factor_diff`**: The two halves differ by 2d²
4. **`prod_range_four`**: The Finset product simplifies to the explicit product
5. **`cube_sum_subst`**: The substitution identity (u+v)³ + (u-v)³ = 2u(u²+3v²)
6. **`flt_three_int`**: FLT for n=3 over ℤ (a³+b³ ≠ c³ for nonzero integers), proved by reducing to Mathlib's `fermatLastTheoremThree`
7. **`gcd_factor_dvd_two`**: When gcd(n,d)=1, the GCD of n(n+3d) and (n+d)(n+2d) divides 2
8. **`ap_prime_divides_atmost_one`**: For primes p ≥ 5 not dividing d, at most one AP term is divisible by p

### What remains sorry'd (2 lemmas):

1. **`sum_cubes_eq_double_cube`**: x³ + y³ = 2z³ implies x = y for positive naturals. This is the core number-theoretic obstacle. It is equivalent to the rank-0 property of the elliptic curve X³+Y³=2Z³ over ℚ, and requires descent in the Eisenstein integers ℤ[ω]. While Mathlib has FLT for n=3 (which uses ℤ[ω] internally), its key lemma `FermatLastTheoremForThreeGen` handles a³+b³ ≠ u·c³ only for **units** u in 𝒪_K. Since 2 is a **prime** (not a unit) in ℤ[ω], a separate descent argument is needed.

2. **`erdos_672_k4_l3`**: The main theorem, which depends on `sum_cubes_eq_double_cube` plus an extensive case analysis on the 2,3-valuations of the four AP terms.

### Proof architecture

The documented proof outline reduces the main theorem to `sum_cubes_eq_double_cube` via:
1. Factor the product as n(n+3d)·(n+d)(n+2d)
2. Show these factors have GCD dividing 2 (proved)
3. For p ≥ 5, each term has cube-free part involving only 2 and 3 (proved)
4. Case analysis on the 2,3-structure yields α³+δ³ = 2γ³
5. Apply the key lemma to get d = 0, contradiction

### File
All work is in `RequestProject/Main.lean`.