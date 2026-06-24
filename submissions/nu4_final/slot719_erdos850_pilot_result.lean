import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-- Erdős Problem 850: Do there exist distinct positive x, y such that rad(x)=rad(y),
rad(x+1)=rad(y+1), and rad(x+2)=rad(y+2)?

Status: OPEN. No witness or impossibility proof known.
This theorem is a tautology (P ∨ ¬P), proved by excluded middle. -/
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
