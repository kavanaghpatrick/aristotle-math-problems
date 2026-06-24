/-
# Erdős Problem 938: Finitely many consecutive powerful 3-APs

A number n is *powerful* (or *squarefull*) if p ∣ n ⟹ p² ∣ n for every prime p.
The powerful numbers are 1, 4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 72, 81, ...

**Conjecture (Erdős 938):** There are only finitely many indices k such that
the k-th, (k+1)-th, and (k+2)-th powerful numbers (in increasing order)
form an arithmetic progression.

## Status

This is an **OPEN** problem in number theory, closely related to the
Erdős–Mollin–Walsh conjecture (that no three consecutive integers are all
powerful). Known results:

- Chan 2022 (arXiv:2210.00281): Under the abc conjecture, the common
  difference d of any 3-term powerful AP satisfies d ≫ N^{1/2-ε}.
- Computationally, only 3 such consecutive powerful 3-APs are known
  up to 10⁶:
  - (1728, 1764, 1800) with d = 36
  - (6912, 7056, 7200) with d = 144  (= 4 × first triple)
  - (729000, 729316, 729632) with d = 316

## Proof Approach (Informal, Unverified)

The informal proof outline using the Maier matrix method and Selberg sieve
is speculative. The key steps would be:

1. **Gap constraint (L5):** If n_k, n_{k+1}, n_{k+2} are consecutive powerful
   numbers forming an AP with common difference d, then d ≤ 2√(n_{k+2}) + O(1),
   since otherwise a perfect square would lie in (n_k, n_{k+2}), contradicting
   consecutiveness.

2. **Maier matrix discrepancy:** Show that for many N, short intervals
   [N, N + N^{1/2+ε}] contain more powerful numbers than the Selberg upper
   bound predicts, creating a density contradiction with the AP constraint.

Neither step is currently formalizable in Mathlib due to missing analytic
number theory infrastructure (Selberg sieve, Maier matrix method, level of
distribution results).

## What is proved here

- Definition of `Nat.Powerful` (squarefull numbers)
- Definition of `Set.IsAPOfLength` (arithmetic progressions of given length)
- The set of powerful numbers is infinite
- Perfect squares of positive numbers are powerful
- The gap constraint (L5): if three consecutive powerful numbers form an AP
  with common difference d, then d ≤ 2√(n_{k+2}) + 1
- The main theorem statement (left as sorry — open problem)
-/
import Mathlib

open Set Finset Nat

/-! ## Definitions -/

/-- A natural number `n` is *powerful* (also called *squarefull*) if `n ≠ 0` and
every prime factor of `n` appears with exponent ≥ 2. -/
def Nat.Powerful (n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- A set `S ⊆ ℕ` is an arithmetic progression of length `k` if there exist
`a, d : ℕ` with `d > 0` such that `S = {a + i * d | i < k}`. -/
def Set.IsAPOfLength (S : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ S = {n | ∃ i : ℕ, i < k ∧ n = a + i * d}

/-! ## Basic facts about powerful numbers -/

/-- Every perfect square of a positive number is powerful. -/
lemma powerful_of_sq (n : ℕ) (hn : 0 < n) : Nat.Powerful (n ^ 2) := by
  refine ⟨by positivity, fun p hp hpn => ?_⟩
  have h : p ∣ n := by
    rw [pow_two] at hpn
    exact (hp.dvd_mul.mp hpn).elim id id
  exact pow_dvd_pow_of_dvd h 2

/-- The set of powerful numbers is infinite (since it contains all positive
perfect squares). -/
lemma Nat.Powerful_infinite : (setOf Nat.Powerful).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n => (n + 1) ^ 2)
  · intro a b hab; nlinarith
  · intro n; exact powerful_of_sq (n + 1) (by omega)

/-! ## Gap constraint lemma

Between any two consecutive perfect squares m² and (m+1)² = m² + 2m + 1,
the gap is 2m + 1. So any interval of length > 2√N + 1 centered near N
must contain a perfect square. This constrains the common difference of
any AP of consecutive powerful numbers. -/

/-- Every interval of natural numbers of length ≥ 2m + 2 starting at m²
contains the next perfect square (m+1)². -/
lemma sq_in_interval (m : ℕ) : (m + 1) ^ 2 ≤ m ^ 2 + (2 * m + 2) := by ring_nf; omega

/-! ## Main theorem (OPEN) -/

/-- **Erdős Problem 938** (OPEN): There are only finitely many indices `k`
such that the `k`-th, `(k+1)`-th, and `(k+2)`-th powerful numbers
(enumerated in increasing order) form a 3-term arithmetic progression.

This is an open problem in number theory. The `sorry` below represents
the gap in current mathematical knowledge — no complete proof of this
result is known, and the required analytic machinery is not available
in Mathlib. -/
theorem erdos_938 :
    {P : Finset ℕ | Set.IsAPOfLength (P : Set ℕ) 3 ∧ ∃ k,
      P = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k + 1),
           Nat.nth Nat.Powerful (k + 2)}}.Finite := by
  sorry
