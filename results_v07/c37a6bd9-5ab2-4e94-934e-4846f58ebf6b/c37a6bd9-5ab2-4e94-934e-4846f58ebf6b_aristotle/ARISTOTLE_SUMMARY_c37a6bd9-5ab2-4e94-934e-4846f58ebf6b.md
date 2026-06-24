# Summary of changes
## Erdős Problem 672 — AP Products Not Perfect Cubes

**Status**: This is a known **open problem** in number theory. The product of 4 terms in arithmetic progression with coprime first term and common difference being a perfect cube (l=3 case) has not been resolved by mathematicians. The analogous l=2 (square) case was proved by Euler.

### File: `RequestProject/Erdos672.lean`

### What was accomplished

I developed a substantial proof infrastructure toward the main theorem, proving **6 helper lemmas** that form the building blocks of a complete proof strategy:

1. **`ap4_product_identity`** ✅ — The key algebraic identity: `n(n+d)(n+2d)(n+3d) + d⁴ = (n²+3nd+d²)²`

2. **`gcd_ap_terms_dvd`** ✅ — For coprime n, d: `gcd(n+id, n+jd)` divides `|i-j|`, showing that common prime factors of AP terms are bounded by 3.

3. **`not_cube_mod9`** ✅ — The mod 9 obstruction: `a⁶+3t²` cannot be a perfect cube when `3 ∤ a` and `3 ∤ t`. (Because `a⁶ ≡ 1` and `3t² ≡ 3` mod 9, giving sum ≡ 4, which is not a cube mod 9.)

4. **`not_square_a4_9a2_27`** ✅ — `a⁴+9a²+27` is never a perfect square. (Squeezed between `(a²+4)²` and `(a²+5)²` for |a| ≥ 3, checked explicitly for small values.)

5. **`no_solution_mod8`** ✅ — `u⁴+9a²u²+27a⁴ ≠ v²` when a is odd. (Mod 8, the LHS ≡ 3, 5, or 7, none of which are quadratic residues mod 8.)

6. **`coprime_product_implies_unit`** ✅ — If `P·Q = c·α⁴` with P, Q each coprime to α, then α is a unit (±1). This is the key coprimality argument used in the descent.

### Proof strategy (documented in the file)

The proof reduces to **Euler's result** (no 3 distinct positive cubes form an arithmetic progression) via:
- Coprime factorization of the four AP terms
- Case analysis on shared factors of 2 and 3
- Descent to the equation `a⁴+9a²α²+27α⁴ = β²`
- The coprimality argument forces |α| = 1
- Then `not_square_a4_9a2_27` provides the final contradiction (for the 3∤s case)

### Remaining sorry's (3 total)

1. **`not_square_27a4_9a2_1`** — `27a⁴+9a²+1 ≠ v²` for a ≠ 0. The mod 8 argument handles a odd and a ≡ 2 mod 4, but a ≡ 0 mod 4 appears to require deeper techniques (possibly elliptic curve rank computation).

2. **`no_three_cubes_in_ap`** — Euler's full result. The 3∤s case follows from the proved lemmas; the 3|s case needs the above.

3. **`erdos_672_l3`** — The main open theorem, which depends on the Euler result plus case analysis on shared factors of 2 and 3 among the four AP terms.