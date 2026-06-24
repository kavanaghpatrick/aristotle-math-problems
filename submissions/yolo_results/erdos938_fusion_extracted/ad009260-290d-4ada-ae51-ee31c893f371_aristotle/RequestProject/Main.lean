import Mathlib

open scoped BigOperators

set_option maxHeartbeats 8000000

/-!
# Erdős Problem 938 — Finitely many 3-term APs of consecutive powerful numbers

A natural number `n` is **powerful** (also called *squarefull* or *full*) if every prime
factor of `n` appears with exponent at least 2. Equivalently, `n` can be written as
`a² b³` with `a, b ∈ ℕ`.

**Conjecture (Erdős 938).** There are only finitely many indices `k` such that the three
consecutive powerful numbers `n_k < n_{k+1} < n_{k+2}` form an arithmetic progression.

## Status

This is an **open problem**. It is closely related to the Erdős–Mollin–Walsh conjecture
(that there are no three consecutive powerful integers). Chan (2022, arXiv:2210.00281) gave
conditional lower bounds on the common difference under the abc-conjecture, but the full
conjecture remains open.
-/

namespace Nat

/-- A natural number `n` is *powerful* if `n ≥ 1` and for every prime `p` dividing `n`,
    `p²` also divides `n`. This is also known as *squarefull*. -/
def Powerful (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

end Nat

namespace Set

/-- A set `S` is an arithmetic progression of length `k` if there exist `a` and nonzero `d`
    such that `S = {a, a + d, a + 2d, …, a + (k-1)·d}`. -/
def IsAPOfLength {α : Type*} [AddCommMonoid α] (S : Set α) (k : ℕ) : Prop :=
  ∃ a d, d ≠ 0 ∧ S = {x | ∃ i : ℕ, i < k ∧ x = a + i • d}

end Set

/-! ## Auxiliary: The set of powerful numbers is infinite -/

/-
Every perfect square `n² ≥ 1` is powerful.
-/
lemma sq_powerful {n : ℕ} (hn : 1 ≤ n) : Nat.Powerful (n ^ 2) := by
  exact ⟨ Nat.one_le_pow _ _ hn, fun p pp dp => by simpa only [ sq ] using pow_dvd_pow_of_dvd ( pp.dvd_of_dvd_pow dp ) 2 ⟩

/-
The set of powerful numbers is infinite (it contains all perfect squares).
-/
lemma powerful_infinite : (setOf Nat.Powerful).Infinite := by
  exact Set.infinite_of_forall_exists_gt fun n => ⟨ ( n + 2 ) ^ 2, sq_powerful ( by nlinarith ), by nlinarith ⟩

/-! ## Main conjecture -/

/-- **Erdős Problem 938** (Open Conjecture): There are only finitely many three-term
arithmetic progressions among consecutive powerful numbers. That is, the set of Finsets
`{n_k, n_{k+1}, n_{k+2}}` (consecutive in the enumeration of powerful numbers) that
also form a 3-term AP is finite. -/
theorem erdos_938 :
    {P : Finset ℕ | Set.IsAPOfLength P.toSet 3 ∧ ∃ k,
      P = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1),
           Nat.nth Nat.Powerful (k+2)}}.Finite := by
  sorry