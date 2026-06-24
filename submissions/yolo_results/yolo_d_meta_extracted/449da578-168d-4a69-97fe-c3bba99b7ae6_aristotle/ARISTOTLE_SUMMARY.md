# Summary of changes for run 449da578-168d-4a69-97fe-c3bba99b7ae6
## Summary

I formalized the three-conjunct theorem about powerful numbers in `RequestProject/Main.lean`. Here is the status:

### What was proved (sorry-free):

**Part (a) — Pell pair infinitude:** There exists an injective function `f : ℕ → ℕ` such that both `8*(f k)²` and `8*(f k)² + 1` are powerful for all `k`. The proof constructs the Pell sequence for `x² - 8y² = 1` starting from (3,1), proves the recurrence satisfies the Pell equation by induction (`pell_eq`), and shows `pellY` is strictly monotone (hence injective). The key lemmas `Nat.Powerful.sq` (perfect squares are powerful) and `Nat.Powerful.eight_mul_sq` (`8y²` is always powerful) complete the proof.

**Part (b) — Mod-36 residue closure:** If `m, m+1, m+2` are all powerful, then `m % 36 ∈ {7, 27, 35}`. The proof uses two modular obstructions:
- Powerful numbers cannot be ≡ 2 mod 4 (prime 2 obstruction)
- Powerful numbers cannot be ≡ 3 or 6 mod 9 (prime 3 obstruction)

Applied to three consecutive integers, these force `m % 4 = 3` and `m % 9 ∈ {0, 7, 8}`, which combine via CRT to give `m % 36 ∈ {7, 27, 35}`.

**Part (c) — QR elimination of m%36=27:** When additionally `m + 1 = 8y²`, the residue `m % 36 = 27` is eliminated using a quadratic residue argument: `m % 9 = 0` would require `y² ≡ 8 mod 9`, but the quadratic residues mod 9 are `{0, 1, 4, 7}`, and 8 is not among them. This is proved as `pell_mod9_ne_zero`.

### What remains (`sorry`):

**`pell_mod9_ne_eight`** — The elimination of `m % 36 = 35` (equivalently, `m % 9 ≠ 8` when `m+1 = 8y²`). After extensive analysis, I determined that this is equivalent to showing that `72z² - 1` and `72z² + 1` cannot both be powerful simultaneously (where `y = 3z`). This is a special case of the **Erdős–Mollin–Walsh conjecture** (that no three consecutive integers are all powerful), which is a well-known open problem in number theory.

The proof outline provided with the problem suggested a simple mod-8 argument, but this argument is flawed: knowing `m % 36 = r` does not determine `m % 8 = r % 8` because `gcd(36, 8) = 4 ≠ 1`. The mod-8 trick only eliminates `m % 36 = 27` (which is already eliminated by the QR argument), not `m % 36 = 35`.

I computationally verified the claim for all `y ≤ 10000` with no counterexample found, confirming the statement is empirically true. The formal proof of this last step would likely require techniques from algebraic number theory or the resolution of the Erdős–Mollin–Walsh conjecture.