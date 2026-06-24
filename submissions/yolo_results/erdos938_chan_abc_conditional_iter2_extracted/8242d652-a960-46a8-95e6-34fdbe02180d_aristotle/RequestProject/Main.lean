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

/-!
# Erdős Problem 938: Finitely many 3-term APs of consecutive powerful numbers

A natural number n ≥ 1 is **powerful** if p | n implies p² | n for every prime p.
Equivalently, n can be written as a²b³ with b squarefree.

**Problem (Erdős 938):** Are there only finitely many indices k such that the
three consecutive powerful numbers n_k, n_{k+1}, n_{k+2} form an arithmetic progression?

**Status:** OPEN. This is closely tied to the Erdős–Mollin–Walsh conjecture.
Chan (2022, arXiv:2210.00281) shows conditionally on abc that the common difference
of any such AP satisfies d ≫_ε N^{1/2-ε}, which combined with the upper bound
d ≤ 2√N + O(N^{1/4}) confines d to a narrow window, but does not rule out
infinitely many solutions.
-/

/-- A natural number is **powerful** if it is at least 1 and every prime dividing it
divides it with multiplicity at least 2. -/
def Nat.Powerful (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- A set of natural numbers is an arithmetic progression of length `len` if there exist
`a` and `d > 0` such that the set equals {a, a+d, a+2d, ..., a+(len-1)d}. -/
def Set.IsAPOfLength (S : Set ℕ) (len : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ S = {n | ∃ i < len, n = a + i * d}

/-
Every perfect square ≥ 1 is powerful.
-/
lemma sq_powerful {n : ℕ} (hn : 1 ≤ n) : Nat.Powerful (n ^ 2) := by
  exact ⟨ by nlinarith, fun p pp dp => by exact pow_dvd_pow_of_dvd ( pp.dvd_of_dvd_pow dp ) 2 ⟩

/-
The set of powerful numbers is infinite (since it contains all perfect squares).
-/
lemma powerful_infinite : (setOf Nat.Powerful).Infinite := by
  exact Set.infinite_of_forall_exists_gt ( fun n => ⟨ ( n+1 ) ^ 2, sq_powerful <| Nat.succ_pos n, by nlinarith ⟩ )

/-- **Erdős 938**: There are only finitely many 3-term arithmetic progressions
formed by three consecutive powerful numbers.

This is an **open problem**. The proof below is left as `sorry`. -/
theorem erdos_938 :
    {P : Finset ℕ | Set.IsAPOfLength (P : Set ℕ) 3 ∧ ∃ k,
      P = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1),
           Nat.nth Nat.Powerful (k+2)}}.Finite := by sorry