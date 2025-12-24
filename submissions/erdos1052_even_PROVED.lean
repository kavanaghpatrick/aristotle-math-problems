/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 95bd192a-e505-4a0f-8aa5-0479a0d8de86

The following was proved by Aristotle:

- theorem even_of_isUnitaryPerfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n
-/

/-
Erdős Problem #1052 - Unitary Perfect Numbers
OPEN: Are there only finitely many unitary perfect numbers?

SELF-CONTAINED definitions (same as FormalConjectures):
- properUnitaryDivisors: d | n with gcd(d, n/d) = 1 and d < n
- IsUnitaryPerfect: sum of proper unitary divisors = n
-/

import Mathlib


set_option maxHeartbeats 400000

namespace Erdos1052

/-- Proper unitary divisors of n: divisors d of n such that
    gcd(d, n/d) = 1 and d < n.
    This is the EXACT definition from FormalConjectures. -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

/-- n is a unitary perfect number if the sum of its proper
    unitary divisors equals n, and n > 0.
    This is the EXACT definition from FormalConjectures. -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n

/- Aristotle took a wrong turn (reason code: 8). Please try again. -/
/-- OPEN: Are there only finitely many unitary perfect numbers?

    Known facts:
    - 5 examples exist: 6, 60, 90, 87360, 146361946186458562560000
    - All are even (no odd unitary perfect numbers) -/
theorem erdos_1052 : Set.Finite {n | IsUnitaryPerfect n} ↔ sorry := by
  sorry

/-- SOLVED: All unitary perfect numbers are even. -/
theorem even_of_isUnitaryPerfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n := by
  -- If $n$ is a unitary perfect number, then $f(n) = 2n$.
  have h_unitary_perfect : (∑ i ∈ Nat.divisors n, if Nat.Coprime i (n / i) then i else 0) = 2 * n := by
    unfold Erdos1052.IsUnitaryPerfect at hn; aesop;
    -- The sum of all unitary divisors, both proper and improper, is given by $\sum_{d \mid n, \gcd(d, n/d) = 1} d$.
    have h_divisors : ∑ i ∈ Nat.divisors n, (if Nat.Coprime i (n / i) then i else 0) = ∑ i ∈ properUnitaryDivisors n ∪ {n}, i := by
      rw [ ← Finset.sum_filter ] ; congr ; ext x ; aesop;
      · exact Classical.or_iff_not_imp_left.2 fun h => Finset.mem_filter.2 ⟨ Finset.mem_Ico.2 ⟨ Nat.pos_of_dvd_of_pos left_1 right, lt_of_le_of_ne ( Nat.le_of_dvd right left_1 ) h ⟩, left_1, right_1 ⟩;
      · exact Finset.mem_filter.mp h_1 |>.2.1;
      · exact Finset.mem_filter.mp h_1 |>.2.2;
    rw [ h_divisors, Finset.sum_union ] <;> aesop ; linarith;
    exact absurd ( Finset.mem_Ico.mp ( Finset.mem_filter.mp a |>.1 ) ) ( by aesop );
  -- If $n$ is odd, then $f(n) \equiv 2 \pmod{4}$, which contradicts $f(n) = 2n$.
  by_cases h_odd : Odd n;
  · -- If $n$ is odd, then each term in the sum $\sum_{i=0}^m (1 + p_i^{a_i})$ is even, making the entire sum divisible by $2^{m+1}$.
    have h_div : 2 ^ (Nat.primeFactors n).card ∣ (∑ i ∈ Nat.divisors n, if Nat.Coprime i (n / i) then i else 0) := by
      -- Let $n = \prod_{i=0}^m p_i^{a_i}$ be the prime factorization of $n$.
      set ps := Nat.primeFactors n with hps
      have h_prime_factors : (∑ i ∈ Nat.divisors n, if Nat.Coprime i (n / i) then i else 0) = ∏ i ∈ ps, (1 + i ^ (Nat.factorization n i)) := by
        -- By definition of coprimality, a divisor $d$ of $n$ is unitary if and only if $d$ is a product of distinct prime factors of $n$.
        have h_unitary_divisors : Finset.filter (fun d => Nat.Coprime d (n / d)) (Nat.divisors n) = Finset.image (fun s => ∏ i ∈ s, i ^ (Nat.factorization n i)) (Finset.powerset ps) := by
          ext; aesop;
          · refine' ⟨ Nat.primeFactors a, Nat.primeFactors_mono left right_1, _ ⟩;
            conv_rhs => rw [ ← Nat.factorization_prod_pow_eq_self ( Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos left ( Nat.pos_of_ne_zero right_1 ) ) ) ] ;
            refine' Finset.prod_congr _ _ <;> aesop;
            cases left ; aesop;
            rw [ Nat.factorization_eq_zero_of_not_dvd ( show ¬ x ∣ w from fun h => by have := Nat.dvd_gcd left_2 h; aesop ) ] ; aesop;
          · conv_rhs => rw [ ← Nat.factorization_prod_pow_eq_self h_odd.pos.ne' ];
            apply_rules [ Finset.prod_dvd_prod_of_subset ];
          · -- Since $w \subseteq ps$, we have $n = \prod_{i \in w} i^{Nat.factorization n i} \cdot \prod_{i \in ps \setminus w} i^{Nat.factorization n i}$.
            have h_factorization : n = (∏ i ∈ w, i ^ (Nat.factorization n i)) * (∏ i ∈ ps \ w, i ^ (Nat.factorization n i)) := by
              rw [ ← Finset.prod_union ( Finset.disjoint_sdiff ), Finset.union_sdiff_of_subset left ];
              exact Eq.symm ( Nat.factorization_prod_pow_eq_self h_odd.pos.ne' );
            rw [ show n / ∏ i ∈ w, i ^ ( n.factorization i ) = ∏ i ∈ ps \ w, i ^ ( n.factorization i ) from Nat.div_eq_of_eq_mul_left ( Finset.prod_pos fun i hi => pow_pos ( Nat.pos_of_mem_primeFactors ( left hi ) ) _ ) <| by linarith ];
            refine' Nat.Coprime.prod_left fun i hi => Nat.Coprime.prod_right fun j hj => _;
            exact Nat.coprime_pow_primes _ _ ( Nat.prime_of_mem_primeFactors ( left hi ) ) ( Nat.prime_of_mem_primeFactors ( Finset.mem_sdiff.mp hj |>.1 ) ) ( by rintro rfl; exact Finset.mem_sdiff.mp hj |>.2 hi );
        rw [ ← Finset.sum_filter, h_unitary_divisors, Finset.sum_image ];
        · simp +decide [ add_comm, Finset.prod_add ];
          rw [ ← Finset.sum_bij ( fun s _ => ps \ s ) ];
          · simp +contextual [ Finset.mem_powerset ];
          · intro a₁ a₂ ha₁ ha₂ h; rw [ Finset.sdiff_eq_sdiff_iff_inter_eq_inter ] at h; aesop;
            rw [ Finset.inter_eq_right.mpr a₂, Finset.inter_eq_right.mpr ha₂ ] at h ; aesop;
          · exact fun s hs => ⟨ ps \ s, by aesop ⟩;
          · exact?;
        · intro s hs t ht h_eq; apply_fun fun x => x.primeFactors at h_eq; simp_all +decide [ Finset.subset_iff, Nat.primeFactors_prod ] ;
          -- Since the prime factors of the product of elements in s and t are the same, and each element in s and t is a prime factor of n, it follows that s and t must be equal.
          have h_prime_factors_eq : ∀ {s : Finset ℕ}, (∀ x ∈ s, Nat.Prime x ∧ x ∣ n) → (∏ i ∈ s, i ^ (Nat.factorization n i)).primeFactors = s := by
            intros s hs; induction s using Finset.induction <;> simp_all +decide [ Nat.primeFactors_mul, Finset.prod_insert ] ;
            rw [ Nat.primeFactors_mul, Nat.primeFactors_pow ] <;> simp_all +decide [ Nat.Prime.ne_zero, Finset.prod_eq_zero_iff ];
            rw [ Nat.factorization_eq_zero_iff ] ; aesop;
          rw [ h_prime_factors_eq fun x hx => ⟨ hs hx |>.1, hs hx |>.2.1 ⟩, h_prime_factors_eq fun x hx => ⟨ ht hx |>.1, ht hx |>.2.1 ⟩ ] at h_eq ; aesop;
      -- Since each term in the product $\prod_{i=0}^m (1 + p_i^{a_i})$ is even, the entire product is divisible by $2^{m+1}$.
      have h_even_terms : ∀ i ∈ ps, 2 ∣ (1 + i ^ (Nat.factorization n i)) := by
        intro i hi; rw [ ← even_iff_two_dvd ] ; simp_all +decide [ parity_simps ] ;
        exact fun h => absurd ( h_odd.of_dvd_nat hi.2.1 ) ( by simp +decide [ h, hi.1.even_iff ] );
      exact h_prime_factors.symm ▸ dvd_trans ( by norm_num ) ( Finset.prod_dvd_prod_of_dvd _ _ h_even_terms );
    rcases k : n.primeFactors.card with ( _ | _ | k ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_dvd_mul_iff_left ];
    · cases k <;> simp_all ( config := { decide := Bool.true } ) [ Erdos1052.IsUnitaryPerfect ];
    · -- If $n$ has exactly one prime factor $p$, then $n = p^a$.
      obtain ⟨p, a, hp, rfl⟩ : ∃ p a : ℕ, Nat.Prime p ∧ n = p^a := by
        rw [ Finset.card_eq_one ] at k ; aesop;
        exact ⟨ w, Nat.prime_of_mem_primeFactors <| h.symm ▸ Finset.mem_singleton_self _, n.factorization w, by nth_rw 1 [ ← Nat.factorization_prod_pow_eq_self h_odd.pos.ne' ] ; rw [ Finsupp.prod ] ; aesop ⟩;
      rcases a with ( _ | _ | a ) <;> simp_all +decide [ Nat.divisors_prime_pow ];
      · rcases p with ( _ | _ | p ) <;> simp_all +arith +decide;
      · rw [ Finset.sum_range_succ ] at h_unitary_perfect ; simp_all +decide [ Nat.Coprime, Nat.gcd_comm ];
        simp_all +decide [ Nat.pow_succ', Nat.mul_div_mul_left, hp.pos ];
        rw [ Finset.sum_eq_single 0 ] at h_unitary_perfect <;> simp_all +decide [ Nat.pow_succ', Nat.mul_div_assoc, hp.pos ];
        · nlinarith [ hp.two_le, pow_pos hp.pos a, pow_pos hp.pos 2 ];
        · intro b hb hb' hb''; rcases b with ( _ | _ | b ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_div_assoc, hp.pos ] ;
          simp_all ( config := { decide := Bool.true } ) [ Nat.mul_div_mul_left, hp.pos ];
          exact absurd ( hb''.symm ▸ Nat.dvd_gcd ( dvd_mul_right _ _ ) ( Nat.dvd_div_of_mul_dvd ( pow_dvd_pow _ hb ) ) ) ( by aesop );
    · exact even_iff_two_dvd.mpr ( dvd_trans ( dvd_mul_right _ _ ) h_div );
  · simpa using h_odd

/-- Test case: 6 is unitary perfect.
    Proper unitary divisors of 6: 1, 2, 3 (all coprime to their complement)
    1 + 2 + 3 = 6 ✓ -/
theorem isUnitaryPerfect_6 : IsUnitaryPerfect 6 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

/-- Test case: 60 is unitary perfect. -/
theorem isUnitaryPerfect_60 : IsUnitaryPerfect 60 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

/-- Test case: 90 is unitary perfect. -/
theorem isUnitaryPerfect_90 : IsUnitaryPerfect 90 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

end Erdos1052