import Mathlib

/--
OPEN GAP: Erdos 850 — Three consecutive same-radical pairs

Do there exist distinct positive x, y such that rad(x)=rad(y),
rad(x+1)=rad(y+1), and rad(x+2)=rad(y+2)?

Status: OPEN. No witness or impossibility proof known.

The disjunction P ∨ ¬P is provable by the law of excluded middle,
without resolving the underlying open problem.
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
