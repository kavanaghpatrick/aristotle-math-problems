import Mathlib

/-!
# Erdős 938 — gcd(n_k, d) is powerful for consecutively-enumerated powerful 3-APs

A powerful number `n` is one where every prime divisor `p` of `n` satisfies `p² ∣ n`.
We show that if three consecutive powerful numbers `n_k, n_{k+1}, n_{k+2}` form
an arithmetic progression with common difference `d`, then `gcd(n_k, d)` is powerful.

## Main result

* `erdos_938_gcd_powerful` — For any `k`, if the `k`-th, `(k+1)`-th, and `(k+2)`-th
  powerful numbers form an arithmetic progression, then `gcd(n_k, d)` is powerful.

## Proof outline

The proof proceeds by showing that for every prime `p` dividing `gcd(n_0, d)`:

1. Since `n_0` is powerful and `p ∣ n_0`, we get `p² ∣ n_0`.
2. If `p² ∤ d`, then `not_sq_dvd_add` shows `p² ∤ (n_0 + d)`, i.e., `p² ∤ n_1`.
   But `p ∣ n_1` (since `p ∣ n_0` and `p ∣ d`) and `n_1` is powerful, so `p² ∣ n_1`.
   Contradiction. Hence `p² ∣ d`.
3. Therefore `p² ∣ gcd(n_0, d)`, completing the proof.
-/

open Nat

/-- A natural number is *powerful* if it is positive and every prime factor appears
    with exponent ≥ 2. -/
def Nat.Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

-- ============================================================================
-- Basic facts about powerful numbers
-- ============================================================================

lemma Nat.Powerful.pos {n : ℕ} (h : n.Powerful) : 0 < n := h.1

lemma Nat.Powerful.prime_sq_dvd {n : ℕ} (h : n.Powerful) {p : ℕ}
    (hp : p.Prime) (hpn : p ∣ n) : p ^ 2 ∣ n := h.2 p hp hpn

lemma Nat.Powerful_one : Nat.Powerful 1 := by
  refine ⟨Nat.one_pos, fun p hp hpn => ?_⟩
  exact absurd (Nat.eq_one_of_dvd_one hpn) (Nat.Prime.one_lt hp).ne'

/-- Every perfect square ≥ 1 is powerful. -/
lemma powerful_of_sq (a : ℕ) (ha : 0 < a) : Nat.Powerful (a ^ 2) :=
  ⟨by positivity, fun p pp dp => pow_dvd_pow_of_dvd (Nat.Prime.dvd_of_dvd_pow pp dp) 2⟩

/-- The set of powerful numbers is infinite. -/
lemma powerful_infinite : (setOf Nat.Powerful).Infinite :=
  Set.infinite_of_forall_exists_gt fun n =>
    ⟨(n + 1) ^ 2, powerful_of_sq _ n.succ_pos, by nlinarith⟩

-- ============================================================================
-- Key valuation lemma
-- ============================================================================

/-- If `p` is prime, `p ∣ d`, `¬ p² ∣ d`, and `p² ∣ n`, then `p² ∤ (n + d)`. -/
lemma not_sq_dvd_add {n d p : ℕ} (_hp : p.Prime) (_hpd : p ∣ d) (hpd2 : ¬ p ^ 2 ∣ d)
    (hpn2 : p ^ 2 ∣ n) : ¬ p ^ 2 ∣ (n + d) := by
  rw [Nat.dvd_add_right hpn2]; exact hpd2

/-- If `n`, `n + d`, `n + 2d` are all powerful and `p` is prime with `p ∣ d` but
    `p² ∤ d`, then `p ∤ n`. -/
lemma slot_1329 {n d p : ℕ} (_hd : 0 < d) (hp : p.Prime) (hpd : p ∣ d)
    (hpd2 : ¬ p ^ 2 ∣ d) (hn : Nat.Powerful n) (hnd : Nat.Powerful (n + d))
    (_hn2d : Nat.Powerful (n + 2 * d)) : ¬ p ∣ n := by
  intro hpn
  exact absurd (hnd.prime_sq_dvd hp (dvd_add hpn hpd))
    (not_sq_dvd_add hp hpd hpd2 (hn.prime_sq_dvd hp hpn))

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem erdos_938_gcd_powerful (k : ℕ) :
    let n0 := Nat.nth Nat.Powerful k
    let n1 := Nat.nth Nat.Powerful (k + 1)
    let n2 := Nat.nth Nat.Powerful (k + 2)
    let d  := n1 - n0
    n1 - n0 = n2 - n1 → Nat.Powerful (Nat.gcd n0 d) := by
  intros n0 n1 n2 d hd
  have h_n0 : Nat.Powerful n0 := Nat.nth_mem_of_infinite powerful_infinite _
  have h_n1 : Nat.Powerful n1 := Nat.nth_mem_of_infinite powerful_infinite _
  have h_n2 : Nat.Powerful n2 := Nat.nth_mem_of_infinite powerful_infinite _
  have h_d_pos : 0 < d :=
    Nat.sub_pos_of_lt (Nat.nth_strictMono powerful_infinite (Nat.lt_succ_self _))
  -- Every prime p dividing both n0 and d must have p² ∣ d
  have h_sq_dvd_d : ∀ p : ℕ, p.Prime → p ∣ n0 → p ∣ d → p ^ 2 ∣ d := by
    intros p hp hp_n0 hp_d
    by_contra h_contra
    apply slot_1329 h_d_pos hp hp_d h_contra h_n0
    · lia
    · grind +qlia
    · assumption
  -- Combine: gcd(n0, d) is powerful
  exact powerful_gcd_of_powerful_components h_n0 h_d_pos fun p pp dp =>
    Nat.dvd_gcd (h_n0.2 p pp (dvd_trans dp (Nat.gcd_dvd_left _ _)))
      (h_sq_dvd_d p pp (dvd_trans dp (Nat.gcd_dvd_left _ _)) (dvd_trans dp (Nat.gcd_dvd_right _ _)))
where
  powerful_gcd_of_powerful_components {n d : ℕ} (hn : Nat.Powerful n) (hd : 0 < d)
      (h : ∀ p : ℕ, p.Prime → p ∣ n.gcd d → p ^ 2 ∣ n.gcd d) :
      Nat.Powerful (n.gcd d) :=
    ⟨Nat.gcd_pos_of_pos_right _ hd, h⟩
