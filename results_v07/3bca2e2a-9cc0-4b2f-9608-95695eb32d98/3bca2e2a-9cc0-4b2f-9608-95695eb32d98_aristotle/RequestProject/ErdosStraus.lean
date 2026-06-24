import Mathlib

/-!
# Erdős-Straus Conjecture (Erdős Problem 242)

For every integer n ≥ 2, the equation 4/n = 1/x + 1/y + 1/z has a solution
in positive integers x, y, z.

**Status**: OPEN. Verified computationally to 10^17. No general proof known.

The formulation below clears denominators:
  4/n = 1/x + 1/y + 1/z  ⟺  4·x·y·z = n·(y·z + x·z + x·y)

## Partial results

We prove the conjecture for the following cases, which together cover all `n`
except those satisfying `n ≡ 1 (mod 4)` and `¬ 3 ∣ n`:

- `n` even: use `x = n/2, y = n, z = n`
- `n ≡ 3 (mod 4)`: use `x = n/4 + 2, y = (n/4 + 1)(n/4 + 2), z = n·(n/4 + 1)`
- `n ≡ 0 (mod 3)` (covers remaining `n ≡ 1 (mod 4)` with `3 ∣ n`):
  use `x = n/3 + 1, y = (n/3)·(n/3 + 1), z = n`
-/

/-- The Erdős-Straus conjecture for even `n`:
    if `n = 2m`, then `4/n = 1/m + 1/(2m) + 1/(2m)`. -/
theorem erdos_straus_even (n : ℕ) (hn : n ≥ 2) (heven : Even n) :
    ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = n * (y * z + x * z + x * y) := by
  obtain ⟨m, rfl⟩ := heven
  exact ⟨m, 2 * m, 2 * m, by linarith, by linarith, by linarith, by ring⟩

/-- The Erdős-Straus conjecture for `n ≡ 3 (mod 4)`:
    if `n = 4k + 3`, then `4/n = 1/(k+2) + 1/((k+1)(k+2)) + 1/(n(k+1))`. -/
theorem erdos_straus_3_mod_4 (n : ℕ) (hn : n ≥ 2) (hmod : n % 4 = 3) :
    ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = n * (y * z + x * z + x * y) := by
  set k := n / 4
  use k + 2, (k + 1) * (k + 2), n * (k + 1)
  exact ⟨Nat.succ_pos _, Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _), by nlinarith,
    by rw [show n = 4 * (n / 4) + 3 by omega]; ring⟩

/-- The Erdős-Straus conjecture for `n` divisible by 3:
    if `n = 3j`, then `4/n = 1/(j+1) + 1/(j(j+1)) + 1/(3j)`. -/
theorem erdos_straus_div_3 (n : ℕ) (hn : n ≥ 2) (hdiv : 3 ∣ n) :
    ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = n * (y * z + x * z + x * y) := by
  obtain ⟨j, rfl⟩ := hdiv
  exact ⟨j + 1, j * (j + 1), 3 * j, by linarith, by nlinarith, by linarith, by ring⟩

/-- **Erdős-Straus Conjecture** (Erdős Problem 242).
    For every integer `n ≥ 2`, the equation `4/n = 1/x + 1/y + 1/z` has a solution
    in positive integers `x, y, z`.

    **Status**: OPEN. Verified computationally to 10^17. No general proof known.
    The cases `n` even, `n ≡ 3 (mod 4)`, and `3 ∣ n` are proved above; the remaining
    open case is `n ≡ 1 (mod 4)` with `gcd(n, 6) = 1`. -/
theorem erdos_straus : ∀ n : ℕ, n ≥ 2 →
    ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = n * (y * z + x * z + x * y) := by
  sorry
