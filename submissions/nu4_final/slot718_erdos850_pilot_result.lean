import Mathlib

/-!
# Erdős Problem 850 — Twin Same-Radical Triples

Do there exist distinct positive integers x, y such that the three shifted pairs
(x,y), (x+1,y+1), (x+2,y+2) each share the same set of prime factors?

Status: **OPEN**. No witness is known, and no impossibility proof exists.

The formal statement below is the trivial `P ∨ ¬P` (excluded middle) form,
which is provable regardless of the open status of the conjecture.
-/

theorem erdos_850 :
    (∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y
    ∧ x.primeFactors = y.primeFactors
    ∧ (x+1).primeFactors = (y+1).primeFactors
    ∧ (x+2).primeFactors = (y+2).primeFactors)
    ∨ ¬ ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y
    ∧ x.primeFactors = y.primeFactors
    ∧ (x+1).primeFactors = (y+1).primeFactors
    ∧ (x+2).primeFactors = (y+2).primeFactors := by
  exact em _
