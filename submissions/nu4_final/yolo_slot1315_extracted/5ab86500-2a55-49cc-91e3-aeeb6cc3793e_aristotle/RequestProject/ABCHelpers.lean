import Mathlib
import RequestProject.Definitions

/-!
# Helper lemmas for the abc lower bound

These lemmas support the abc-conditional lower bound on the common difference
of consecutive powerful 3-APs.
-/

open scoped BigOperators Real
open Classical

set_option maxHeartbeats 8000000

noncomputable instance : DecidablePred Nat.Powerful := inferInstance

/-! ## Arithmetic identity for APs -/

/-- The AP identity: if n1 = n0 + d and n2 = n0 + 2d, then n1^2 = n0 * n2 + d^2. -/
lemma ap_identity (n0 d : ℕ) :
    (n0 + d) ^ 2 = n0 * (n0 + 2 * d) + d ^ 2 := by
  ring

/-
Coprime reduction for a + b = c implies pairwise coprime of {a, b, c}.
-/
lemma coprime_sum_pairwise {a b : ℕ} (hab : Nat.Coprime a b) :
    ({a, b, a + b} : Set ℕ).Pairwise Nat.Coprime := by
  simp +decide [Set.Pairwise];
  simp_all +decide [ Nat.Coprime, Nat.gcd_comm ]

/-! ## abc finiteness implies a bound -/

/-
From finiteness of the abc-exception set, extract a bound on the third component.
-/
lemma abc_finite_to_bound (ε : ℝ) (_hε : 0 < ε)
    (hfin : {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧
      ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧ a + b = c ∧
      (ABC.radical (a * b * c) : ℝ) ^ (1 + ε) < c}.Finite) :
    ∃ C : ℕ, ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      ({a, b, c} : Set ℕ).Pairwise Nat.Coprime → a + b = c →
      c > C → (ABC.radical (a * b * c) : ℝ) ^ (1 + ε) ≥ c := by
  cases' hfin.bddAbove with C hC;
  exact ⟨ C.2.2, fun a b c ha hb hc hab hbc hc' => not_lt.1 fun h => not_lt_of_ge ( @hC ( a, b, c ) ⟨ ha, hb, hc, hab, hbc, h ⟩ |>.2.2 ) hc' ⟩

/-! ## Radical properties -/

/-
The radical of a powerful number n satisfies rad(n)^2 ≤ n.
-/
lemma radical_sq_le_of_powerful (n : ℕ) (hn : Nat.Powerful n) :
    ABC.radical n ^ 2 ≤ n := by
  -- By definition of `Nat.PrimeFactors`, we know that `n.primeFactors.prod id` is the product of the distinct prime factors of `n`.
  have h_prime_factors : (∏ p ∈ n.primeFactors, p) ^ 2 ∣ n := by
    have h_each_prime : ∀ p ∈ n.primeFactors, p ^ 2 ∣ n := by
      exact fun p hp => hn.2 p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp );
    rw [ ← Finset.prod_pow ];
    have h_prod_prime_factors : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → (∀ p ∈ S, p ^ 2 ∣ n) → (∏ p ∈ S, p ^ 2) ∣ n := by
      intros S hS_prime hS_div
      induction' S using Finset.induction with p S hS ih;
      · norm_num;
      · rw [ Finset.prod_insert hS ];
        refine' Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ _;
        · exact Nat.Coprime.prod_right fun q hq => Nat.Coprime.pow _ _ <| hS_prime p ( Finset.mem_insert_self _ _ ) |> Nat.Prime.coprime_iff_not_dvd |>.2 fun h => hS <| by have := Nat.prime_dvd_prime_iff_eq ( hS_prime p ( Finset.mem_insert_self _ _ ) ) ( hS_prime q ( Finset.mem_insert_of_mem hq ) ) ; aesop;
        · exact hS_div p ( Finset.mem_insert_self _ _ );
        · exact ih ( fun q hq => hS_prime q ( Finset.mem_insert_of_mem hq ) ) ( fun q hq => hS_div q ( Finset.mem_insert_of_mem hq ) );
    exact h_prod_prime_factors ( fun p hp => Nat.prime_of_mem_primeFactors hp ) h_each_prime;
  exact Nat.le_of_dvd hn.1 h_prime_factors

/-
The radical is submultiplicative: rad(a * b) ≤ rad(a) * rad(b).
-/
lemma radical_mul_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ABC.radical (a * b) ≤ ABC.radical a * ABC.radical b := by
  -- By definition of prime factors, we know that the prime factors of $a * b$ are the union of the prime factors of $a$ and $b$.
  have h_prime_factors : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := by
    exact Nat.primeFactors_mul ha.ne' hb.ne';
  unfold ABC.radical;
  rw [ h_prime_factors, ← Finset.prod_union_inter ];
  exact le_mul_of_one_le_right ( Finset.prod_nonneg fun _ _ => Nat.zero_le _ ) ( Nat.one_le_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun x hx => Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors <| Finset.mem_of_mem_inter_left hx )

/-
The radical of a square equals the radical of the base.
-/
lemma radical_sq (a : ℕ) (_ha : 0 < a) :
    ABC.radical (a ^ 2) = ABC.radical a := by
  unfold ABC.radical;
  rw [ Nat.primeFactors_pow ] ; aesop

/-
The radical of a positive number is positive.
-/
lemma radical_pos (n : ℕ) (_hn : 0 < n) : 0 < ABC.radical n := by
  exact Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors hp

/-
rad(n) ≤ n for positive n.
-/
lemma radical_le (n : ℕ) (hn : 0 < n) : ABC.radical n ≤ n :=
  Nat.le_of_dvd hn <| Nat.prod_primeFactors_dvd _