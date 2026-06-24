import Mathlib

/-!
# Definitions for Erdős Problem 938

We define powerful numbers and the radical function needed for the
abc-conditional sandwich theorem on consecutive powerful 3-APs.
-/

open scoped BigOperators

set_option maxHeartbeats 800000

/-- A natural number `n` is **powerful** if every prime dividing `n` divides it
    with exponent at least 2 (i.e., `p ∣ n → p² ∣ n`), and `n > 0`. -/
def Nat.Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- The **radical** of a natural number is the product of its distinct prime factors. -/
noncomputable def ABC.radical (n : ℕ) : ℕ :=
  n.primeFactors.prod id

/-- Every perfect square of a positive number is powerful. -/
lemma powerful_sq (m : ℕ) (hm : 0 < m) : Nat.Powerful (m ^ 2) :=
  ⟨by positivity, fun p hp hpd => pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hpd) 2⟩

/-- The set of powerful numbers is infinite. -/
lemma powerful_infinite : (setOf Nat.Powerful).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n => (n + 1) ^ 2)
  · intro a b hab
    have := Nat.pow_left_injective (by omega : (2 : ℕ) ≠ 0) hab
    omega
  · intro n
    exact powerful_sq (n + 1) (by omega)

/-- 1 is powerful. -/
lemma powerful_one : Nat.Powerful 1 :=
  ⟨by omega, fun p hp hpd => by
    have := hp.one_lt
    have := Nat.le_of_dvd (by omega) hpd
    omega⟩
