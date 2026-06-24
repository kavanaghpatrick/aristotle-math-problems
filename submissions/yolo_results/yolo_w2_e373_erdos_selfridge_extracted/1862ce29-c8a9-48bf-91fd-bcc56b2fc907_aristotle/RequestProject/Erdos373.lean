import Mathlib

/-!
# Erdős Problem 373

The conjecture (open since the 1960s) states that the only solution to
`n! = a! * b!` with `1 < b ≤ a` and `a + 1 ≠ n` is `(n, a, b) = (10, 7, 6)`.

## Results proved sorry-free

1. **Forward direction**: `(10, 7, 6)` satisfies all constraints.
2. **Corridor bounds**: Any solution satisfies `a + 2 ≤ n` and `n < 2 * a`.
3. **Witness prime lemma**: If there exists a prime `p` with `a < p ≤ n` and
   `n < 2 * p`, then `n! ≠ a! * b!` for `b ≤ a`. Since `n < 2a`, any prime `p`
   in `(a, n]` satisfies `n < 2p`, so any prime in the interval `(a, n]` rules out
   a solution.
4. **Bounded verification**: For `a ≤ 200`, the only solution is `(10, 7, 6)`
   (direct `native_decide` on the mathematical statement).
5. **Computational check to 1000**: An efficient decision procedure confirms
   no other solutions for `a ≤ 1000`.

## Status

This is an open problem (Surányi's conjecture). The main theorem retains a single
`sorry` for the case `a > 200` — equivalently, for showing that no pair `(a, n)` with
`a > 200`, `a + 2 ≤ n < 2a`, and no prime in `(a, n]` satisfies
`(a+1)(a+2)⋯n = b!` for any `b ≤ a`.
-/

open scoped Nat
namespace Erdos373

/-! ## Forward direction -/

/-- `10! = 7! · 6!` -/
theorem solution_check : (10 : ℕ).factorial = (7 : ℕ).factorial * (6 : ℕ).factorial := by
  native_decide

/-- `(10, 7, 6)` is in the solution set. -/
theorem mem_solution_set :
    (10, 7, 6) ∈ {(n, a, b) : ℕ × ℕ × ℕ | n ! = a ! * b ! ∧ 1 < n ∧ 1 < a ∧ 1 < b
      ∧ b ≤ a ∧ a + 1 ≠ n} := by
  refine ⟨?_, by omega, by omega, by omega, by omega, by omega⟩
  native_decide

/-! ## Corridor bounds -/

/-- If `n! = a! * b!` with `1 < b ≤ a` and `a + 1 ≠ n`, then `n > a`. -/
theorem n_gt_a {n a b : ℕ} (hfact : n ! = a ! * b !)
    (_hn : 1 < n) (_ha : 1 < a) (hb : 1 < b) (_hba : b ≤ a) (_hne : a + 1 ≠ n) :
    a < n := by
  exact lt_of_not_ge fun h => by
    nlinarith [Nat.factorial_pos a, Nat.factorial_le h, Nat.self_le_factorial b]

/-- Lower corridor bound: `a + 2 ≤ n`. -/
theorem corridor_lower {n a b : ℕ} (hfact : n ! = a ! * b !)
    (hn : 1 < n) (ha : 1 < a) (hb : 1 < b) (hba : b ≤ a) (hne : a + 1 ≠ n) :
    a + 2 ≤ n := by
  by_cases h_eq : n = a + 1
  · omega
  · exact lt_of_le_of_ne
      (Nat.succ_le_of_lt (n_gt_a hfact hn ha hb hba hne))
      (Ne.symm h_eq)

/-- Upper corridor bound: `n < 2 * a`.

The key idea is that `(2a)! > (a!)²`, so if `n ≥ 2a` then
`b! = n!/a! ≥ (2a)!/a! > a! ≥ b!`, a contradiction. -/
theorem corridor_upper {n a b : ℕ} (hfact : n ! = a ! * b !)
    (_hn : 1 < n) (ha : 1 < a) (_hb : 1 < b) (hba : b ≤ a) (_hne : a + 1 ≠ n) :
    n < 2 * a := by
  have h_fact : (2 * a)! > (a !) ^ 2 := by
    refine Nat.le_induction ?_ ?_ a ha <;> intros <;>
      simp_all +decide [Nat.factorial, Nat.mul_succ, sq]
    nlinarith [sq ‹_›]
  contrapose! h_fact
  exact le_trans (Nat.factorial_le h_fact) (by nlinarith [Nat.factorial_le hba])

/-! ## Witness prime lemma -/

/-- If there is a prime `p` with `a < p ≤ n` and `b ≤ a`, then `n! ≠ a! * b!`.

Since `p` is prime and `p ≤ n`, we have `p ∣ n!`. Since `a < p`, we have `p ∤ a!`.
By Euclid's lemma, `p ∣ b!`. But `b ≤ a < p`, so `p ∤ b!` — contradiction. -/
theorem witness_prime_kills {n a b p : ℕ} (hp : Nat.Prime p)
    (hap : a < p) (hpn : p ≤ n) (_hn2p : n < 2 * p) (hba : b ≤ a)
    (hfact : n ! = a ! * b !) : False := by
  have hp_dvd_nfact : p ∣ n ! := Nat.dvd_factorial hp.pos hpn
  have hp_not_dvd_afact : ¬(p ∣ a !) := by
    rw [Nat.Prime.dvd_factorial] <;> omega
  rw [hfact] at hp_dvd_nfact
  rcases hp.dvd_mul.mp hp_dvd_nfact with h | h
  · exact hp_not_dvd_afact h
  · exact absurd (hp.dvd_factorial.mp h) (by omega)

/-! ## Bounded verification -/

set_option maxRecDepth 8000 in
/-- For `a ≤ 200`, the only solution is `(n, a, b) = (10, 7, 6)`.
This is verified by exhaustive computation via `native_decide`. -/
theorem bounded_200 :
    ∀ a ∈ Finset.range 201, ∀ n ∈ Finset.Ico (a + 2) (2 * a),
    ∀ b ∈ Finset.Ico 2 (a + 1),
    n.factorial = a.factorial * b.factorial → (n, a, b) = (10, 7, 6) := by
  native_decide

/-- Efficient decision procedure for checking all `(a, n)` pairs in the corridor. -/
private def isFactorialProd (a n : ℕ) : Bool := Id.run do
  if n ≤ a + 1 then return false
  let mut P : Nat := 1
  for i in [:n - a] do
    P := P * (a + 1 + i)
  let mut bfact : Nat := 1
  for b in [:a + 1] do
    bfact := if b == 0 then 1 else bfact * b
    if b ≥ 2 && bfact == P then return true
    if bfact > P then return false
  return false

/-- Check all corridor pairs with `a ≤ K`, excluding the known solution `(10, 7)`. -/
private def checkBound (K : ℕ) : Bool := Id.run do
  for a in [:K + 1] do
    if a < 2 then continue
    for n in [:2 * a] do
      if n < a + 2 then continue
      if isFactorialProd a n && !(n == 10 && a == 7) then return false
  return true

/-- Computational verification that no solution exists for `2 ≤ a ≤ 1000`
other than `(n, a) = (10, 7)`. -/
theorem checkBound_1000 : checkBound 1000 = true := by native_decide

/-! ## Auxiliary lemma: any prime in `(a, n]` with `n < 2a` is a witness -/

/-- Combined lemma: if there exists a prime in `(a, n]` and `n < 2a`,
then no solution `n! = a! * b!` with `b ≤ a` can exist. -/
theorem prime_in_interval_kills {n a b : ℕ} (hba : b ≤ a) (hnu : n < 2 * a)
    (hfact : n ! = a ! * b !)
    (hp : ∃ p, Nat.Prime p ∧ a < p ∧ p ≤ n) : False := by
  obtain ⟨p, hp_prime, hap, hpn⟩ := hp
  exact witness_prime_kills hp_prime hap hpn (by omega) hba hfact

/-! ## Partial proof of the backward direction -/

/-- For `a ≤ 200`, any solution must be `(10, 7, 6)`. This combines
the corridor bounds with the bounded computational check. -/
theorem uniqueness_bounded {n a b : ℕ}
    (hfact : n ! = a ! * b !) (hn : 1 < n) (ha : 1 < a) (hb : 1 < b)
    (hba : b ≤ a) (hne : a + 1 ≠ n) (ha_bound : a ≤ 200) :
    (n, a, b) = (10, 7, 6) := by
  have hcl := corridor_lower hfact hn ha hb hba hne
  have hcu := corridor_upper hfact hn ha hb hba hne
  exact bounded_200 a (Finset.mem_range.mpr (by omega)) n
    (Finset.mem_Ico.mpr ⟨hcl, hcu⟩) b (Finset.mem_Ico.mpr ⟨hb, by omega⟩) hfact

/-! ## Main theorem -/

/-- **Erdős Problem 373** (Surányi's conjecture, open since the 1960s).

The unique solution to `n! = a! · b!` with `1 < b ≤ a` and `a + 1 ≠ n`
is `(n, a, b) = (10, 7, 6)`, i.e., `10! = 7! · 6! = 3,628,800`.

**Status**: Open problem. The proof has a single sorry for the unbounded case
(`a > 200`). All structural lemmas (corridor bounds, witness prime elimination)
and the bounded case (`a ≤ 200`) are proved sorry-free. The result is additionally
computationally verified for `a ≤ 1000`.
-/
theorem erdos_373_target :
    {(n, a, b) : ℕ × ℕ × ℕ | n ! = a ! * b ! ∧ 1 < n ∧ 1 < a ∧ 1 < b
      ∧ b ≤ a ∧ a + 1 ≠ n} = {(10, 7, 6)} := by
  ext ⟨n, a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hfact, hn, ha, hb, hba, hne⟩
    by_cases ha_bound : a ≤ 200
    · have := uniqueness_bounded hfact hn ha hb hba hne ha_bound
      exact ⟨congr_arg (·.1) this, congr_arg (·.2.1) this, congr_arg (·.2.2) this⟩
    · -- Open problem: case a > 200
      -- By corridor_upper, n < 2 * a. By corridor_lower, a + 2 ≤ n.
      -- By witness_prime_kills, if any prime exists in (a, n], we get a contradiction.
      -- The remaining cases (no prime in (a, n]) are finite for each a but
      -- infinite in total, and showing they all fail to satisfy n!/a! = b!
      -- for any b ≤ a is the open part of Surányi's conjecture.
      sorry
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨solution_check, by omega, by omega, by omega, by omega, by omega⟩

end Erdos373
