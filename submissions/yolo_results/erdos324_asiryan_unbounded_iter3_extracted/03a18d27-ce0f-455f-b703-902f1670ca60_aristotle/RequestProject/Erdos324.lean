import Mathlib

/-!
# Erdős Problem 324 — Quintic Pair-Sum Distinctness

Erdős conjectured that all sums a⁵ + b⁵ with a < b (nonneg integers) are distinct:
there is no nontrivial collision a⁵ + b⁵ = c⁵ + d⁵ with {a,b} ≠ {c,d}.

## Status

This is an **open problem** in number theory. No counterexample is known
(numerical search to ~10¹¹ confirms zero pair collisions), but no proof exists either.

## What we prove here

1. `erdos_324_h_zero`: the "h = 0 slice" — if a⁵+b⁵ = c⁵+d⁵ **and** a+b = c+d,
   then (a,b) = (c,d). This follows by showing that the residual quadratic factor
   in the polynomial g(t) = t⁵+(s-t)⁵ - [a⁵+(s-a)⁵] (after dividing out the known
   roots t=a and t=s-a) has strictly negative discriminant, so no other integer roots
   exist.

2. `erdos_324_bounded_100`: verified computationally for all a,b,c,d < 100
   via `native_decide`.

The main unbounded theorem `erdos_324_quintic_pair_distinct` is stated but left as
`sorry` — it is a well-known open problem.
-/

set_option maxHeartbeats 800000

/-! ## The h = 0 slice -/

open Polynomial in
/-- If `a + b = c + d` and `a⁵ + b⁵ = c⁵ + d⁵` with `a < b`, `c < d`,
    then `a = c ∧ b = d`.

    Proof: Fix s = a+b = c+d. The polynomial f(t) = t⁵+(s-t)⁵ has degree 4.
    The difference f(t) - f(a) factors as 5s·(t-a)·(t-b)·q(t) where
    q(t) = t² - st + (s²-sa+a²) has discriminant Δ = -3s²+4sa-4a² < 0,
    so q has no real roots. Hence f(c) = f(a) forces c ∈ {a,b}, and
    the ordering constraints yield (c,d) = (a,b). -/
theorem erdos_324_h_zero (a b c d : ℕ) (hab : a < b) (hcd : c < d)
    (hsum : a + b = c + d)
    (hpow : a ^ 5 + b ^ 5 = c ^ 5 + d ^ 5) :
    a = c ∧ b = d := by
  wlog h_wlog : a < c generalizing a b c d
  · grind
  · set s := a + b
    set g : ℤ → ℤ := fun t => t ^ 5 + (s - t) ^ 5
    have h_root : (c - a : ℤ) * (c - b : ℤ) *
        (c ^ 2 - s * c + s ^ 2 - s * a + a ^ 2 : ℤ) = 0 := by
      have h_root : g c = g a := by grind
      simp +zetaDelta at *
      exact Classical.or_iff_not_imp_right.2 fun h =>
        Classical.or_iff_not_imp_left.2 fun h' =>
          mul_left_cancel₀ (sub_ne_zero_of_ne h) <|
            mul_left_cancel₀ (sub_ne_zero_of_ne h') <| by nlinarith
    simp_all +decide [sub_eq_iff_eq_add]
    exact absurd (h_root.resolve_left (by omega))
      (by nlinarith only [h_wlog, hcd, hsum])

/-! ## Bounded verification -/

/-- The Erdős 324 conjecture holds for all a, b, c, d < 100. -/
theorem erdos_324_bounded_100 :
    ∀ a b c d : Fin 100, a < b → c < d →
      a.val ^ 5 + b.val ^ 5 = c.val ^ 5 + d.val ^ 5 → a = c ∧ b = d := by
  native_decide

/-! ## The full conjecture (OPEN PROBLEM) -/

/-- **Erdős Problem 324** (OPEN). No nontrivial collision a⁵+b⁵ = c⁵+d⁵ with
    {a,b} ≠ {c,d} exists among nonneg integers.

    This is an open conjecture. No counterexample is known (verified
    computationally to ~10¹¹), but no proof exists in the mathematical literature.

    The "Asiryan 2026" reference cited in the problem brief does not correspond to
    any known publication; it appears to be fabricated. The genus-one fibration
    approach described in the brief, while mathematically plausible in structure,
    has not been carried out in any verified work.

    What IS known:
    - For k=3: fails (1729 = 1³+12³ = 9³+10³, Hardy-Ramanujan).
    - For k=4: fails (635318657 = 59⁴+158⁴ = 133⁴+134⁴, Euler).
    - For k=5: conjectured to hold (Erdős). No counterexample known. -/
theorem erdos_324_quintic_pair_distinct :
    ∀ a b c d : ℕ, a < b → c < d →
      a ^ 5 + b ^ 5 = c ^ 5 + d ^ 5 → a = c ∧ b = d := by
  sorry
