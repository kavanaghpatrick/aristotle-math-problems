import Mathlib

open scoped Nat

namespace Erdos373

/-!
# Erdős Problem 373 (Surányi's Conjecture)

The equation n! = a! · b! with 1 < b ≤ a and a + 1 ≠ n has exactly one solution:
(n, a, b) = (10, 7, 6), since 10! = 7! · 6! = 3628800.

## Proof Strategy

1. **Witness verification**: 10! = 7! · 6! (computational).
2. **Corridor bounds**: Any solution satisfies a + 2 ≤ n < 2a, hence a ≥ 3.
3. **No-prime lemma**: There is no prime in the interval (a, n].
4. **Finite verification**: Combine bounds with computational checking.

## Status
This is an open problem (Surányi's conjecture, 1960s). We prove it for a ≤ 275
using machine-verified computation, and reduce the full conjecture to an upper
bound on `a` (`a_upper_bound`).
-/

-- Helper: the witness (10, 7, 6) satisfies all conditions
lemma witness_mem :
    (10 : ℕ).factorial = (7 : ℕ).factorial * (6 : ℕ).factorial ∧
    1 < (10 : ℕ) ∧ 1 < (7 : ℕ) ∧ 1 < (6 : ℕ) ∧ (6 : ℕ) ≤ 7 ∧ (7 : ℕ) + 1 ≠ 10 := by
  native_decide

-- Helper: n > a when n! = a! * b! and b > 1
lemma n_gt_a {n a b : ℕ} (h : n ! = a ! * b !) (hb : 1 < b) : a < n := by
  contrapose! h
  exact ne_of_lt (lt_of_le_of_lt (Nat.factorial_le h)
    (lt_mul_of_one_lt_right (Nat.factorial_pos _)
      (by linarith [Nat.self_le_factorial b])))

-- Helper: n ≥ a + 2 under the full conditions
lemma n_ge_a_plus_two {n a b : ℕ} (h : n ! = a ! * b !) (hb : 1 < b)
    (hne : a + 1 ≠ n) : a + 2 ≤ n := by
  have h_n_ge_a_plus_1 : a + 1 ≤ n :=
    Nat.succ_le_of_lt (n_gt_a h hb)
  exact h_n_ge_a_plus_1.lt_of_ne hne

-- Helper: n < 2 * a (corridor upper bound)
lemma n_lt_two_a {n a b : ℕ} (h : n ! = a ! * b !) (ha : 1 < a)
    (_hb : 1 < b) (hba : b ≤ a) : n < 2 * a := by
  by_contra h_contra
  have h_ge : (2 * a)! ≤ a ! * a ! := by
    exact le_trans (Nat.factorial_le (le_of_not_gt h_contra))
      (h.le.trans (Nat.mul_le_mul_left _ (Nat.factorial_le hba)))
  contrapose! h_ge
  rcases a with (_ | _ | a) <;> simp_all +arith +decide [Nat.factorial]
  ring_nf
  nlinarith only [show 0 < a ! ^ 2 by positivity,
    show a ! ^ 2 ≤ (a * 2)! from by
      rw [sq]
      exact Nat.le_of_dvd (Nat.factorial_pos _) <|
        Nat.factorial_mul_factorial_dvd_factorial_add _ _ |> dvd_trans <| by ring_nf; norm_num,
    pow_nonneg (Nat.zero_le a) 3, pow_nonneg (Nat.zero_le a) 4]

/-
Helper: a ≥ 3 for any solution
-/
lemma a_ge_three {n a b : ℕ} (h : n ! = a ! * b !) (ha : 1 < a) (hb : 1 < b)
    (hba : b ≤ a) (hne : a + 1 ≠ n) : 3 ≤ a := by
  by_contra! H;
  interval_cases a ; interval_cases b ; simp_all +decide;
  have : n ≤ 4 := Nat.le_of_lt_succ ( Nat.lt_succ_of_le ( by { exact le_trans ( Nat.self_le_factorial _ ) h.le } ) ) ; interval_cases n <;> trivial;

-- Key structural lemma: no prime exists in (a, n] when n! = a! * b! with b ≤ a
lemma no_prime_in_interval {n a b : ℕ} (h : n ! = a ! * b !) (hba : b ≤ a)
    (p : ℕ) (hp : Nat.Prime p) (hpa : a < p) (hpn : p ≤ n) : False := by
  have h_div_n : p ∣ n.factorial := Nat.dvd_factorial hp.pos hpn
  have h_not_div_a : ¬(p ∣ a.factorial) := by
    rw [Nat.Prime.dvd_factorial] <;> aesop
  simp_all +decide [Nat.Prime.dvd_mul]
  exact absurd (hp.dvd_factorial.mp h_div_n) (by linarith)

/-
Connection: n! = a! * ∏ i in Icc (a+1) n, i
-/
lemma factorial_eq_mul_prod {n a : ℕ} (h : a ≤ n) :
    n ! = a ! * (Finset.Icc (a + 1) n).prod id := by
  induction h <;> simp_all +decide [ Nat.factorial_succ, mul_comm, mul_left_comm, Finset.prod_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ]

-- Computational check for a ∈ [3, 275] using the product form
lemma computational_check :
    ∀ a ∈ Finset.Icc 3 275,
      ∀ n ∈ Finset.Icc (a + 2) (2 * a - 1),
        ∀ b ∈ Finset.Icc 2 a,
          (Finset.Icc (a + 1) n).prod id = Nat.factorial b →
          n = 10 ∧ a = 7 ∧ b = 6 := by native_decide

/-- The core open bound: any solution to the factorial equation has a ≤ 275.
This is the key open part of Surányi's conjecture.

**Structural argument** (proved above):
- Any solution satisfies a + 2 ≤ n < 2a (corridor bounds).
- There is no prime in the interval (a, n].
- By Bertrand's postulate, the prime gap after a is less than a.

**What remains open**: showing that for a > 275, the products (a+1)·...·n
cannot equal any factorial b! with b ≤ a, for all valid n in the corridor.
This is related to Brocard-type problems about when products of consecutive
integers can be factorials. -/
lemma a_upper_bound {n a b : ℕ} (h : n ! = a ! * b !)
    (hn : 1 < n) (ha : 1 < a) (hb : 1 < b) (hba : b ≤ a) (hne : a + 1 ≠ n) :
    a ≤ 275 := by
  sorry

-- The main theorem
theorem erdos_373_suranyi :
    {(n, a, b) : ℕ × ℕ × ℕ | n ! = a ! * b ! ∧ 1 < n ∧ 1 < a ∧ 1 < b
      ∧ b ≤ a ∧ a + 1 ≠ n} = {(10, 7, 6)} := by
  ext ⟨n, a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · intro ⟨heq, hn, ha, hb, hba, hne⟩
    -- Structural bounds
    have h_ge := n_ge_a_plus_two heq hb hne
    have h_lt := n_lt_two_a heq ha hb hba
    have h_a3 := a_ge_three heq ha hb hba hne
    -- The open bound
    have h_bound := a_upper_bound heq hn ha hb hba hne
    -- Convert to product form
    have h_an : a ≤ n := by omega
    have h_prod := factorial_eq_mul_prod h_an
    -- n! = a! * b! and n! = a! * product, so product = b!
    have h_prod_eq : (Finset.Icc (a + 1) n).prod id = b ! := by
      have h_pos : 0 < a ! := Nat.factorial_pos _
      exact mul_left_cancel₀ (Nat.pos_iff_ne_zero.mp h_pos) (h_prod.symm.trans heq)
    -- Apply computational check
    have h_mem_a : a ∈ Finset.Icc 3 275 := by
      simp [Finset.mem_Icc]; omega
    have h_mem_n : n ∈ Finset.Icc (a + 2) (2 * a - 1) := by
      simp [Finset.mem_Icc]; omega
    have h_mem_b : b ∈ Finset.Icc 2 a := by
      simp [Finset.mem_Icc]; omega
    exact computational_check a h_mem_a n h_mem_n b h_mem_b h_prod_eq
  · rintro ⟨rfl, rfl, rfl⟩
    exact witness_mem

end Erdos373