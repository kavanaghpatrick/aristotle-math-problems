import Mathlib

open scoped BigOperators
open Finset Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

/-- A natural number is powerful if every prime dividing it does so with multiplicity ≥ 2. -/
def IsPowerful (a : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ a → p ^ 2 ∣ a

/-! ## Foundational lemmas about factorials and powerfulness -/

/-- For n ≥ 4, there exists a prime q with n/2 < q ≤ n such that q appears
    exactly once in the factorization of n! (Bertrand's postulate application) -/
lemma exists_prime_single_factor (n : ℕ) (hn : 4 ≤ n) :
    ∃ q : ℕ, q.Prime ∧ q ∣ n ! ∧ ¬ (q ^ 2 ∣ n !) := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, Nat.Prime q ∧ n / 2 < q ∧ q ≤ n := by
    exact Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega) |>
      fun ⟨q, hq₁, hq₂⟩ => ⟨q, hq₁, by omega, by omega⟩
  refine ⟨q, hq.1, Nat.dvd_factorial hq.1.pos hq.2.2, ?_⟩
  have hq_sq_gt_n : q ^ 2 > n := by
    nlinarith [Nat.div_add_mod n 2, Nat.mod_lt n two_pos]
  rw [Nat.Prime.pow_dvd_factorial_iff] <;> norm_num [hq.1]
  any_goals exact Nat.lt_succ_self _
  rw [Finset.sum_eq_single 1] <;> norm_num
  · exact Nat.div_lt_of_lt_mul <| by nlinarith [Nat.div_add_mod n 2, Nat.mod_lt n two_pos]
  · exact fun b hb₁ hb₂ hb => Or.inr <| lt_of_lt_of_le hq_sq_gt_n <|
      Nat.pow_le_pow_right hq.1.pos <| Nat.lt_of_le_of_ne hb₁ <| Ne.symm hb
  · exact fun h => absurd (h hq.2.2) (not_le_of_gt hq.1.one_lt)

/-- n! is not powerful for n ≥ 2 -/
lemma factorial_not_powerful (n : ℕ) (hn : 2 ≤ n) : ¬ IsPowerful (n !) := by
  by_contra h_contra
  obtain ⟨p, hp_prime, hp_div⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ! ∧ ¬(p ^ 2 ∣ n !) := by
    by_cases h₂ : n < 4
    · interval_cases n <;> exact ⟨2, by decide, by decide, by decide⟩
    · exact exists_prime_single_factor n (le_of_not_gt h₂)
  exact hp_div.right (h_contra p hp_prime hp_div.left)

/-- The set of powerful factorials is finite (equals {1}) -/
lemma powerful_factorial_finite :
    {a : ℕ | (∃ n : ℕ, a = n !) ∧ IsPowerful a}.Finite := by
  refine Set.Finite.subset (Set.finite_singleton 1) ?_
  rintro a ⟨⟨n, rfl⟩, ha⟩
  rcases n with (_ | _ | n) <;> simp_all +decide
  exact factorial_not_powerful _ le_add_self ha

/-! ## Key structural lemma: isolated minimum forces non-powerfulness -/

/-
If a finset S = {n} ∪ T where n ≥ 4, n ∉ T, q is a Bertrand prime of n,
    and all elements of T are ≥ 2q, then ∑ s! over S is not powerful.
    This is because v_q(n!) = 1 while v_q(t!) ≥ 2 for all t ∈ T.
-/
lemma single_low_element_not_powerful (n : ℕ) (hn : 4 ≤ n) (T : Finset ℕ)
    (q : ℕ) (hq_prime : q.Prime) (hq_range : n / 2 < q ∧ q ≤ n)
    (hT : ∀ t ∈ T, 2 * q ≤ t) (hn_notin : n ∉ T) :
    ¬ IsPowerful (∑ s ∈ insert n T, s !) := by
      -- First, we show that q � divides the sum. All elements are ≥ q (n ≥ q by hq_range.2, elements of T ≥ 2q ≥ q), so q | s! for each s, hence q | sum.
      have hq_divides_sum : q ∣ ∑ s ∈ insert n T, s ! := by
        exact Finset.dvd_sum fun x hx => Nat.dvd_factorial hq_prime.pos ( by cases Finset.mem_insert.mp hx <;> [ linarith; linarith [ hT _ ‹_› ] ] );
      -- Next, we show that q² divides all terms of the sum except n!. For each t � ∈� T, t ≥ 2q, so t! contains both q and 2q as factors, giving v_q(t!) ≥ 2 �.� Use that q! � *� q! | (2q)! (by Nat.factorial_mul_factorial_dvd_factorial_add) and (2q)! | t! (by Nat.factorial_dvd_factorial).
      have hq2_divides_T : ∀ t ∈ T, q^2 ∣ t ! := by
        -- Since $q$ is prime and $t \geq 2q$, $ �t�!$ contains both $q$ and $2q$ as factors, giving $v_q(t!) \geq 2$.
        intros t ht
        have hq_factorial : q ! * q ! ∣ t ! := by
          exact Nat.factorial_mul_factorial_dvd_factorial_add _ _ |> dvd_trans <| Nat.factorial_dvd_factorial <| by linarith [ hT t ht ] ;
        exact dvd_trans ( by rw [ sq ] ; exact mul_dvd_mul ( Nat.dvd_factorial ( Nat.pos_of_ne_zero hq_prime.ne_zero ) ( by linarith ) ) ( Nat.dvd_factorial ( Nat.pos_of_ne_zero hq_prime.ne_zero ) ( by linarith ) ) ) hq_factorial;
      -- By Nat.dvd_add_left (since q² |_T t!), q² | sum ↔ q² | n!. Since q² n!, � q�² sum.
      have hq2_divides_sum_iff : q^2 ∣ ∑ s ∈ insert n T, s ! ↔ q^2 ∣ n ! := by
        rw [ Finset.sum_insert hn_notin ];
        rw [ Nat.dvd_add_left ( Finset.dvd_sum hq2_divides_T ) ];
      -- Since q² n!, we have q²� s ∈ insert n T, s !.
      have hq2_not_divides_sum : ¬(q^2 ∣ n !) := by
        rw [ Nat.Prime.pow_dvd_factorial_iff ] <;> norm_num [ hq_prime ];
        rotate_right;
        exact 2;
        · exact Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.div_add_mod n 2, Nat.mod_lt n two_pos ] ;
        · exact Nat.log_lt_of_lt_pow ( by linarith ) ( by nlinarith [ Nat.div_add_mod n 2, Nat.mod_lt n two_pos, Nat.pow_le_pow_left hq_prime.two_le 2 ] );
      exact fun h => hq2_not_divides_sum <| hq2_divides_sum_iff.mp <| h q hq_prime hq_divides_sum

/-! ## Reduction: bounding max(S) implies finiteness -/

/-
If powerful factorial sums with support ≤ K have bounded maximum element,
    then the set of such sums is finite.
-/
lemma finite_of_max_bounded (K : ℕ) (N₀ : ℕ)
    (h_bound : ∀ S : Finset ℕ, S.card ≤ K →
      (∀ p : ℕ, p.Prime → p ∣ ∑ n ∈ S, n ! → p ^ 2 ∣ ∑ n ∈ S, n !) →
      ∀ n ∈ S, n < N₀) :
    {a : ℕ | (∃ S : Finset ℕ, S.card ≤ K ∧ a = ∑ n ∈ S, n.factorial) ∧
             (∀ p : ℕ, p.Prime → p ∣ a → p ^ 2 ∣ a)}.Finite := by
               refine Set.Finite.subset ( Set.toFinite ( Finset.image ( fun S : Finset ℕ => ∑ n ∈ S, n ! ) ( Finset.powerset ( Finset.range N₀ ) |> Finset.filter ( fun S => S.card ≤ K ) ) ) ) ?_;
               grind +extAll

/-- Open conjecture: for each K, there exists a bound N₀ such that any powerful
    sum of ≤ K distinct factorials has all summand indices below N₀.

    This is the core open content of Erdős Problem 1108 (bounded-support sub-claim).
    For K = 1, N₀ = 4 suffices (by `factorial_not_powerful` and Bertrand's postulate).
    For K ≥ 2, this is open unconditionally; known results are abc-conditional
    (Luca–Sárközy 1996, Bolvardizadeh–Yavari 2025).

    The lemma `single_low_element_not_powerful` establishes a key partial result:
    if the minimum element of S is "isolated" (no other element in [q, 2q) for a
    Bertrand prime q), the sum cannot be powerful. The full conjecture additionally
    requires handling the case where elements cluster in [min, 2·min). -/
lemma max_element_bounded (K : ℕ) :
    ∃ N₀ : ℕ, ∀ S : Finset ℕ, S.card ≤ K →
      (∀ p : ℕ, p.Prime → p ∣ ∑ n ∈ S, n ! → p ^ 2 ∣ ∑ n ∈ S, n !) →
      ∀ n ∈ S, n < N₀ := by sorry

/-- Main theorem: for every fixed K, the set of powerful sums of ≤ K distinct
    factorials is finite.

    This follows from `max_element_bounded` (which bounds the indices in any
    powerful factorial sum) and `finite_of_max_bounded` (which derives finiteness
    from the bound). The open content is entirely in `max_element_bounded`. -/
theorem bounded_card_powerful_factorial_sums (K : ℕ) :
    {a : ℕ | (∃ S : Finset ℕ, S.card ≤ K ∧ a = ∑ n ∈ S, n.factorial) ∧
             (∀ p : ℕ, p.Prime → p ∣ a → p ^ 2 ∣ a)}.Finite := by
  obtain ⟨N₀, hN₀⟩ := max_element_bounded K
  exact finite_of_max_bounded K N₀ hN₀

end