# Summary of changes
## Summary

I was unable to close the 3 remaining `sorry` statements in `Erdos672.lean`. These are genuinely deep results in number theory that require substantial formalization infrastructure.

### What was accomplished

**Two new proved helper lemmas were added:**

1. **`not_square_27a4_9a2_1_not_div4`** (line 147): Proves `27a⁴ + 9a² + 1 ≠ v²` when `a` is not divisible by 4. The proof uses a mod 8 argument: for such `a`, the expression is ≡ 5 mod 8, which is not a quadratic residue.

2. **`pell_identity_27`** (line 162): Proves the algebraic identity that if `27a⁴ + 9a² + 1 = v²`, then `(2v)² - 3·(6a² + 1)² = 1`, connecting the problem to the Pell equation `X² - 3Y² = 1`.

### What remains open (3 sorries)

1. **`not_square_27a4_9a2_1`** (line 165): The case `a ≡ 0 mod 4` requires Pell equation theory. I established computationally that the Pell sequence `Y_n` mod 1200 has period 120, and among valid values (Y ≡ 1 mod 6, Y ≥ 7), `(Y-1)/6` mod 200 is always a non-quadratic residue — but formalizing this in Lean requires building Pell equation infrastructure (using `Pell.Solution₁` and `Pell.IsFundamental` from Mathlib) which proved too complex for the available time.

2. **`no_three_cubes_in_ap`** (line 195): Euler's classical result that `x³ + y³ = 2z³` implies `x = y`. This requires either a full Euler descent formalization or a novel reduction to `fermatLastTheoremThree` (which is in Mathlib). The descent argument is essentially as complex as FLT3 itself and depends on `not_square_27a4_9a2_1`.

3. **`erdos_672_l3`** (line 211): The main theorem depends on `no_three_cubes_in_ap`.

### Why these are hard

- The `a ≡ 0 mod 4` case of `not_square_27a4_9a2_1` cannot be handled by any finite set of modular arithmetic checks alone (verified computationally). It genuinely requires Pell equation theory.
- `no_three_cubes_in_ap` is a deep theorem proved by Euler using infinite descent, comparable in difficulty to FLT3.
- Erdős Problem 672 itself is listed as an **open problem** in the Erdős problem database.

The file builds successfully with the 3 remaining sorry statements, and all previously proved lemmas (`ap4_product_identity`, `gcd_ap_terms_dvd`, `not_cube_mod9`, `not_square_a4_9a2_27`, `no_solution_mod8`, `coprime_product_implies_unit`) remain intact.