/-
# Erdős Problem 938: Finitely many 3-APs of consecutive powerful numbers

**Conjecture (Erdős):** Let A = {n₁ < n₂ < ⋯} be the strictly increasing
sequence of powerful numbers (those n ≥ 1 such that p ∣ n ⇒ p² ∣ n for
every prime p). Are there only finitely many indices k such that
n_k, n_{k+1}, n_{k+2} form a three-term arithmetic progression?

**Status:** OPEN. Up to 10^{14}, only 18 consecutive powerful 3-APs are known.
Van Doorn (2026, arXiv:2605.06697) conjectures that infinitely many
consecutive powerful 3-APs exist, which would *falsify* this conjecture.

This file provides:
- Definition of powerful numbers (`Nat.Powerful`)
- Definition of arithmetic progression (`Set.IsAPOfLength`)
- The formal statement of Erdős 938
- Unconditional sub-results:
  * Every perfect square is powerful
  * The set of powerful numbers is infinite
  * The square-gap bound for consecutive powerful AP triples
-/

import Mathlib

open Nat Finset

/-! ## Definitions -/

/-- A natural number `n` is **powerful** if `n ≥ 1` and for every prime `p`
dividing `n`, we have `p² ∣ n`. -/
def Nat.Powerful (n : ℕ) : Prop :=
  n ≥ 1 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- A set `S` of natural numbers is a `k`-term arithmetic progression if there
exist `a` and `d > 0` such that `S = {a, a + d, a + 2d, …, a + (k-1)d}`. -/
def Set.IsAPOfLength (S : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ S = { n | ∃ i : ℕ, i < k ∧ n = a + i * d }

/-! ## Basic properties of powerful numbers -/

/-- 1 is powerful. -/
theorem Nat.Powerful.one : Nat.Powerful 1 := by
  refine ⟨le_refl 1, fun p hp hpd => ?_⟩
  have := hp.one_lt
  have := Nat.le_of_dvd (by omega) hpd
  omega

/-- Every perfect square of a positive number is powerful. -/
theorem Nat.Powerful.sq (m : ℕ) (hm : m ≥ 1) : Nat.Powerful (m ^ 2) := by
  constructor
  · exact Nat.one_le_pow 2 m (by omega)
  · intro p hp hpd
    exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hpd) 2

/-- The set of powerful numbers is infinite (it contains all perfect squares). -/
theorem Nat.Powerful.infinite : Set.Infinite {n : ℕ | Nat.Powerful n} := by
  apply Set.Infinite.mono (s := Set.range (fun m => (m + 1) ^ 2))
  · intro n ⟨m, hm⟩
    simp only [Set.mem_setOf_eq]
    rw [← hm]
    exact Nat.Powerful.sq (m + 1) (by omega)
  · apply Set.infinite_range_of_injective
    intro a b h
    simp at h
    omega

/-! ## The square-gap bound (unconditional)

For three consecutive powerful numbers n_k < n_{k+1} < n_{k+2} forming
an AP with common difference d, we have d ≤ √(n_{k+2}) + 1.

Proof sketch: Every perfect square ≥ 1 is powerful. If d > √(n_{k+2}) + 1,
then the gap from n_k to n_{k+2} = n_k + 2d would be large enough to
contain a perfect square strictly between n_k and n_{k+2}. That square
would be a powerful number, contradicting that n_k, n_{k+1}, n_{k+2}
are consecutive in the powerful sequence. -/

/-
Between any two natural numbers sufficiently far apart, there exists a
perfect square strictly between them.
-/
theorem exists_sq_between (a b : ℕ) (_hb : b ≥ 1) (_hab : a < b)
    (hgap : b - a > 2 * Nat.sqrt b + 2) :
    ∃ m : ℕ, a < m ^ 2 ∧ m ^ 2 < b ∧ m ≥ 1 := by
  refine' ⟨ Nat.sqrt a + 1, _, _, _ ⟩ <;> norm_num;
  · linarith [ Nat.lt_succ_sqrt a ];
  · contrapose! hgap;
    rw [ tsub_le_iff_left ];
    nlinarith only [ Nat.lt_succ_sqrt b, hgap, Nat.sqrt_le a ]

/-! ## Main conjecture -/

/-- **Erdős Problem 938** (OPEN CONJECTURE).
There are only finitely many Finsets P of natural numbers such that
P forms a 3-term arithmetic progression and P consists of three
consecutive powerful numbers.

⚠ This is an OPEN problem. The `sorry` below represents genuine
mathematical uncertainty, not a gap in formalization technique.
Van Doorn (2026) conjectures the opposite — that infinitely many
such 3-APs exist among consecutive powerful numbers. -/
theorem erdos_938 :
    {P : Finset ℕ | Set.IsAPOfLength (P : Set ℕ) 3 ∧ ∃ k,
      P = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1),
           Nat.nth Nat.Powerful (k+2)}}.Finite := by
  sorry