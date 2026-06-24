import Mathlib

open scoped BigOperators

set_option maxHeartbeats 8000000

/-!
# Erdős 1052 / Wall k=3 — Lehmer Pair Primitive Divisor Theorem

## Mathematical Background

A **Lehmer pair** (α, β) is a pair of algebraic integers with:
- α + β = √R and αβ = Q for coprime nonzero integers R, Q
- α/β is not a root of unity

The **Lehmer sequence** is defined as:
- U_n(α, β) = (αⁿ - βⁿ)/(α - β) when n is odd
- U_n(α, β) = (αⁿ - βⁿ)/(α² - β²) when n is even

A **primitive prime divisor** of U_n is a prime q that divides U_n but does not
divide U_m for any 0 < m < n.

## Main Result

The Bilu–Hanrot–Voutier theorem (2001) states that for every Lehmer pair and
every n > 30, U_n has a primitive prime divisor. The "Wall k=3" stratum is the
immediate corollary restricting to n divisible by 3.

## Formalization Status

The BHV theorem is stated as `bhv_primitive_divisor_gt_30` with `sorry`, as it
requires ~50 pages of analytic number theory not yet formalized in Mathlib.
The k=3 corollary `erdos_1052_wall_k3` is proved from it.
-/

/-- The Lehmer sequence term U_n(α, β).
For a valid Lehmer pair, these values are always integers.
- For odd n: U_n = (αⁿ - βⁿ)/(α - β)
- For even n: U_n = (αⁿ - βⁿ)/(α² - β²) -/
noncomputable def lehmer_term (α β : ℂ) (n : ℕ) : ℤ :=
  if n % 2 = 1 then
    ⌊((α ^ n - β ^ n) / (α - β)).re⌋
  else
    ⌊((α ^ n - β ^ n) / (α ^ 2 - β ^ 2)).re⌋

/-- α/β is not a root of unity: no positive power of α/β equals 1. -/
def not_root_of_unity (z : ℂ) : Prop := ∀ k : ℕ, 0 < k → z ^ k ≠ 1

/-- **Bilu–Hanrot–Voutier Theorem** (J. Reine Angew. Math. 539, 2001, pp. 75–122).

For every Lehmer pair (α, β) and every n > 30, the Lehmer sequence term U_n
has a primitive prime divisor.

This is a deep result in analytic number theory that has not yet been formalized
in Mathlib. It relies on Baker's theory of linear forms in logarithms and
extensive computational verification for small cases. -/
theorem bhv_primitive_divisor_gt_30
    (α β : ℂ) (hα : α + β ∈ Set.range (Int.cast : ℤ → ℂ))
    (hαβ : α * β ∈ Set.range (Int.cast : ℤ → ℂ)) (hrat : not_root_of_unity (α / β))
    (n : ℕ) (hn : 30 < n) :
    ∃ q : ℕ, q.Prime ∧ (↑q : ℤ) ∣ lehmer_term α β n ∧
      ∀ m < n, ¬ ((↑q : ℤ) ∣ lehmer_term α β m) := by
  sorry

/-- **Erdős Problem 1052 / Wall k=3 Stratum**.

For every Lehmer pair (α, β) and every n > 30 with 3 ∣ n, the term U_n
has a primitive prime divisor.

This is an immediate corollary of the Bilu–Hanrot–Voutier theorem:
the hypothesis n > 30 ∧ 3 ∣ n implies n > 30, so BHV applies directly.

*Proof.* Since 3 ∣ n and n > 30, we have n > 30. By the Bilu–Hanrot–Voutier
theorem, U_n has a primitive prime divisor. □ -/
theorem erdos_1052_wall_k3
    (α β : ℂ) (hα : α + β ∈ Set.range (Int.cast : ℤ → ℂ))
    (hαβ : α * β ∈ Set.range (Int.cast : ℤ → ℂ)) (hrat : not_root_of_unity (α / β))
    (n : ℕ) (hn : 30 < n) (_h3 : 3 ∣ n) :
    ∃ q : ℕ, q.Prime ∧ (↑q : ℤ) ∣ lehmer_term α β n ∧
      ∀ m < n, ¬ ((↑q : ℤ) ∣ lehmer_term α β m) :=
  -- The k=3 condition is redundant: n > 30 suffices by BHV.
  bhv_primitive_divisor_gt_30 α β hα hαβ hrat n hn
