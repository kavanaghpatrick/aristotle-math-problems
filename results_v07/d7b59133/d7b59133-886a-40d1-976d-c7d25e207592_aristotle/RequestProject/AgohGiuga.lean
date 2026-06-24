import Mathlib

/-!
# Agoh-Giuga Conjecture

The Agoh-Giuga conjecture (Giuga 1950, Agoh 1995) states that no composite
number n satisfies ∑_{a=1}^{n-1} a^{n-1} ≡ -1 (mod n).

**Status**: This is an OPEN conjecture. Any counterexample must have ≥ 4771
prime factors and exceed 10^{19907} (Borwein-Maitland-Skerritt, 2013).

## Approach

We establish the known equivalence: if n is composite and satisfies the sum
condition, then n must simultaneously be a Carmichael number and a Giuga number.
The final step — showing no composite number is both Carmichael and Giuga — is
the hard open part.
-/

open Finset

/-- The power sum S(n) = ∑_{a=0}^{n-1} a^{n-1} -/
noncomputable def powerSum (n : ℕ) : ℕ := ∑ a ∈ Finset.range n, a ^ (n - 1)

/-- A number n is a Giuga number if for every prime p dividing n,
    p divides (n/p - 1). -/
def IsGiuga (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ (n / p - 1)

/-- Key lemma: if n > 1 is composite and n ∣ (powerSum n + 1), then n is squarefree. -/
lemma giuga_squarefree (n : ℕ) (hn : n > 1) (hcomp : ¬ Nat.Prime n)
    (hdvd : n ∣ (powerSum n + 1)) : Squarefree n := by
  refine' Nat.squarefree_iff_prime_squarefree.mpr _;
  intro p pp dp;
  have hp_div : p ∣ (powerSum n + 1) := by
    exact dvd_trans ( dvd_of_mul_left_dvd dp ) hdvd;
  have hsum_mod_p : (∑ a ∈ Finset.range n, a ^ (n - 1)) ≡ (∑ a ∈ Finset.range p, a ^ (n - 1)) * (n / p) [MOD p] := by
    have hsum_mod_p : ∀ k : ℕ, (∑ a ∈ Finset.range (k * p), a ^ (n - 1)) ≡ (∑ a ∈ Finset.range p, a ^ (n - 1)) * k [MOD p] := by
      intro k; induction k <;> simp_all +decide [ Nat.succ_mul, ← ZMod.natCast_eq_natCast_iff, Finset.sum_range_add ] ; ring;
    convert hsum_mod_p ( n / p ) using 1 ; rw [ Nat.div_mul_cancel ( dvd_of_mul_left_dvd dp ) ];
  have hp_div_np : p ∣ (n / p) := by
    exact Nat.dvd_div_of_mul_dvd dp;
  simp_all +decide [ Nat.ModEq, Nat.dvd_iff_mod_eq_zero ];
  simp_all +decide [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd ];
  unfold powerSum at *; simp_all +decide ;

/-- Key lemma: if n > 1 and n ∣ (powerSum n + 1), then for every prime p | n,
    we have (p-1) | (n-1) (Korselt/Carmichael condition). -/
lemma giuga_korselt (n : ℕ) (hn : n > 1)
    (hdvd : n ∣ (powerSum n + 1)) (p : ℕ) (hp : Nat.Prime p) (hpn : p ∣ n) :
    (p - 1) ∣ (n - 1) := by
  by_contra h_contra
  obtain ⟨p, hp_prime, hp_div, hp_not_div⟩ : ∃ p, Nat.Prime p ∧ p ∣ n ∧ ¬(p - 1) ∣ (n - 1) := by
    use p;
  have h_sum_mod_p : (∑ a ∈ Finset.range n, a ^ (n - 1)) % p = (∑ a ∈ Finset.range p, a ^ (n - 1)) * (n / p) % p := by
    have h_split_sum : ∑ a ∈ Finset.range (p * (n / p)), a ^ (n - 1) = ∑ k ∈ Finset.range (n / p), ∑ a ∈ Finset.range p, (a + p * k) ^ (n - 1) := by
      induction' n / p with k hk;
      · norm_num;
      · rw [ Nat.mul_succ, Finset.sum_range_add, hk ];
        simp +arith +decide [ add_comm, Finset.sum_range_succ ];
    rw [ Nat.mul_div_cancel' hp_div ] at h_split_sum; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff', mul_comm ] ;
  have h_sum_zero_mod_p : (∑ a ∈ Finset.range p, a ^ (n - 1)) % p = 0 := by
    haveI := Fact.mk hp_prime; simp +decide [ ← ZMod.val_natCast, Nat.add_mod, Nat.pow_mod, Finset.sum_nat_mod ] ;
    obtain ⟨g, hg⟩ : ∃ g : ZMod p, orderOf g = p - 1 := by
      obtain ⟨ g, hg ⟩ := IsCyclic.exists_generator ( α := ( ZMod p )ˣ );
      exact ⟨ g, by rw [ orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg ] ; simp +decide [ Nat.totient_prime hp_prime ] ⟩;
    have h_sum_ga : ∑ a ∈ Finset.range p, (g * a) ^ (n - 1) = ∑ a ∈ Finset.range p, a ^ (n - 1) := by
      have h_sum_ga : Finset.image (fun a : ZMod p => g * a) (Finset.univ : Finset (ZMod p)) = Finset.univ := by
        refine' Finset.eq_of_subset_of_card_le ( Finset.subset_univ _ ) _;
        rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ ( show g ≠ 0 from by rintro rfl; rw [ eq_comm ] at hg; rcases p with ( _ | _ | p ) <;> simp_all +decide ) hxy ];
      have h_sum_ga : ∑ a ∈ Finset.univ, (g * a) ^ (n - 1) = ∑ a ∈ Finset.univ, a ^ (n - 1) := by
        conv_rhs => rw [ ← h_sum_ga, Finset.sum_image ( Finset.card_image_iff.mp <| by aesop ) ] ;
      simp_all +decide [ Finset.sum_range, ZMod.natCast_eq_zero_iff ];
      rcases p with ( _ | _ | p ) <;> simp_all +decide [ Fin.sum_univ_succ, ZMod ];
    have h_g_ne_one : g ^ (n - 1) ≠ 1 := by
      exact fun h => hp_not_div <| hg.symm ▸ orderOf_dvd_iff_pow_eq_one.mpr h;
    simp_all +decide [ mul_pow, Finset.mul_sum _ _ _ ];
    rw [ ← Finset.mul_sum _ _ _ ] at h_sum_ga ; exact mul_left_cancel₀ ( sub_ne_zero_of_ne h_g_ne_one ) <| by linear_combination' h_sum_ga;
  obtain ⟨ k, hk ⟩ := hdvd; replace hk := congr_arg ( · % p ) hk; simp_all +decide [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd ] ;
  unfold powerSum at hk; aesop;

/-- Key lemma: if n > 1 and n ∣ (powerSum n + 1), then for every prime p | n,
    we have p | (n/p - 1) (Giuga condition). -/
lemma giuga_condition (n : ℕ) (hn : n > 1)
    (hdvd : n ∣ (powerSum n + 1)) (p : ℕ) (hp : Nat.Prime p) (hpn : p ∣ n) :
    p ∣ (n / p - 1) := by
  have hkorselt : (p - 1) ∣ (n - 1) := giuga_korselt n hn hdvd p hp hpn
  have hsum_mod_p : (∑ a ∈ Finset.range n, a ^ (n - 1)) ≡ (∑ a ∈ Finset.range p, a ^ (n - 1)) * (n / p) [MOD p] := by
    have hsum_split : ∑ a ∈ Finset.range (p * (n / p)), a ^ (n - 1) ≡ (∑ a ∈ Finset.range p, a ^ (n - 1)) * (n / p) [MOD p] := by
      induction' n / p with k hk;
      · rfl;
      · simp_all +decide [ Nat.mul_succ, ← ZMod.natCast_eq_natCast_iff, Finset.sum_range_add ];
    rwa [ Nat.mul_div_cancel' hpn ] at hsum_split;
  have hsum_mod_p_prime : (∑ a ∈ Finset.range p, a ^ (n - 1)) ≡ p - 1 [MOD p] := by
    have h_fermat : ∀ a ∈ Finset.Ico 1 p, a ^ (n - 1) ≡ 1 [MOD p] := by
      intro a ha; have := Nat.totient_prime hp; rw [ ← Nat.mul_div_cancel' hkorselt ] ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, pow_mul ] ;
      haveI := Fact.mk hp; rw [ ZMod.pow_card_sub_one_eq_one ( by rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ha.1 ha.2 ) ] ; norm_num;
    simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
    rw [ ← Finset.sum_range_add_sum_Ico _ hp.pos ];
    rw [ Finset.sum_congr rfl fun x hx => h_fermat x ( Finset.mem_Ico.mp hx |>.1 ) ( Finset.mem_Ico.mp hx |>.2 ) ] ; norm_num [ hp.pos ];
    rw [ zero_pow ( Nat.sub_ne_zero_of_lt hn ) ];
  have hsum_mod_p_final : (∑ a ∈ Finset.range n, a ^ (n - 1)) ≡ - (n / p) [ZMOD p] := by
    simp_all +decide [ ← Int.natCast_modEq_iff ];
    simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, hp.pos ];
  have hdiv_p : (p : ℤ) ∣ (∑ a ∈ Finset.range n, a ^ (n - 1)) + 1 :=
    Int.natCast_dvd_natCast.mpr (dvd_trans hpn hdvd)
  rw [ ← Int.natCast_dvd_natCast ] ; cases le_total ( n / p ) 1 <;> simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_eq_intCast_iff ] ;
  linear_combination' -hdiv_p

/-
PROBLEM
Two-prime-factor case: no product of two distinct primes can satisfy the
    Giuga conditions. If p < q are primes, then p | (q-1) and q | (p-1)
    is impossible since q > p implies q cannot divide p-1 < q.

PROVIDED SOLUTION
Since q | (p - 1) and q is prime with q > p ≥ 2, we have q ≤ p - 1 < p < q, contradiction.
-/
lemma no_giuga_two_factors (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hgiuga_p : p ∣ (q - 1)) (hgiuga_q : q ∣ (p - 1)) : False := by
  linarith [ Nat.le_of_dvd ( Nat.sub_pos_of_lt hp.one_lt ) hgiuga_q, Nat.sub_add_cancel hp.pos, Nat.sub_add_cancel hq.pos ]

/-- No composite number is simultaneously Carmichael and Giuga.
    THIS IS THE OPEN PART OF THE CONJECTURE.

    Known results (Borwein-Maitland-Skerritt 2013): any such number must have
    ≥ 4771 prime factors and exceed 10^{19907}. No proof that none exists is known. -/
lemma no_carmichael_giuga (n : ℕ) (hn : n > 1) (hcomp : ¬ Nat.Prime n)
    (hsqfree : Squarefree n)
    (hkorselt : ∀ p : ℕ, Nat.Prime p → p ∣ n → (p - 1) ∣ (n - 1))
    (hgiuga : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ (n / p - 1)) :
    False := by
  sorry

theorem agoh_giuga (n : ℕ) (hn : n > 1) (hcomp : ¬ Nat.Prime n) :
    ¬ (n ∣ (∑ a ∈ Finset.range n, a ^ (n - 1) + 1)) := by
  intro hdvd
  have hdvd' : n ∣ (powerSum n + 1) := hdvd
  exact no_carmichael_giuga n hn hcomp
    (giuga_squarefree n hn hcomp hdvd')
    (giuga_korselt n hn hdvd')
    (giuga_condition n hn hdvd')