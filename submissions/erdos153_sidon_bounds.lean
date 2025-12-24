/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 765f6fea-01cd-4291-ba88-9c34c2b1cdcd
-/

/-
ITERATION 1 for Erdős #153 v4 - Sidon Set Squared Gaps
Project ID: 8c02ea36-ee21-40fc-a52d-ed81584b8fcb

Complete this proof. Fill the hole at line 137.

The answer is: sumset_subset_interval hA_nonempty
(This lemma is already defined at line 100-106 in the same file!)

Constraints:
- Do not modify theorem statements
- Focus only on filling the hole
- The lemma signature is:
  theorem sumset_subset_interval {A : Finset ℕ} (hA : A.Nonempty) :
    sumset A ⊆ Finset.Icc (2 * A.min' hA) (2 * A.max' hA)
-/

import Mathlib


set_option linter.mathlibStandardSet false

open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

def IsSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → ({a, b} : Set ℕ) = {c, d}

def avg_squared_gap (S : Finset ℕ) : ℝ :=
  let sorted := S.sort (·≤·)
  let gaps := List.zipWith (·-·) sorted.tail sorted
  (gaps.map (fun g => (g : ℝ)^2)).sum / (S.card - 1 : ℝ)

def sumset (A : Finset ℕ) : Finset ℕ := A + A

def solutions_diff_k (A : Finset ℕ) (k : ℕ) : ℕ :=
  (A.filter (fun x => x + k ∈ A)).card

def count_gaps_eq (S : Finset ℕ) (k : ℕ) : ℕ :=
  let sorted := S.sort (·≤·)
  let gaps := List.zipWith (·-·) sorted.tail sorted
  gaps.count k

theorem card_sumset_sidon {A : Finset ℕ} (hA : IsSidon A) :
  (sumset A).card = A.card * (A.card + 1) / 2 := by
    have h_inj : Finset.card (Finset.image (fun (p : ℕ × ℕ) => p.1 + p.2) (Finset.filter (fun p => p.1 ≤ p.2) (A ×ˢ A))) = (A.card * (A.card + 1)) / 2 := by
      rw [ Finset.card_image_of_injOn, Nat.div_eq_of_eq_mul_left ];
      · grind;
      · have h_pairs : Finset.card (Finset.filter (fun p => p.1 ≤ p.2) (A ×ˢ A)) = Finset.card (Finset.filter (fun p => p.1 < p.2) (A ×ˢ A)) + Finset.card (Finset.filter (fun p => p.1 = p.2) (A ×ˢ A)) := by
          rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
          simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x hx => by split_ifs <;> omega;
        have h_pairs_lt : Finset.card (Finset.filter (fun p => p.1 < p.2) (A ×ˢ A)) = Finset.card (Finset.offDiag A) / 2 := by
          have h_pairs_lt : Finset.card (Finset.filter (fun p => p.1 < p.2) (A ×ˢ A)) = Finset.card (Finset.filter (fun p => p.1 > p.2) (A ×ˢ A)) := by
            rw [ Finset.card_filter, Finset.card_filter ];
            rw [ Finset.sum_product, Finset.sum_product ];
            rw [ Finset.sum_comm ];
          have h_pairs_lt : Finset.card (Finset.filter (fun p => p.1 < p.2) (A ×ˢ A)) + Finset.card (Finset.filter (fun p => p.1 > p.2) (A ×ˢ A)) = Finset.card (Finset.offDiag A) := by
            rw [ ← Finset.card_union_of_disjoint ];
            · congr with p ; aesop;
            · exact Finset.disjoint_filter.mpr fun _ _ _ _ => lt_asymm ‹_› ‹_›;
          rw [ Nat.div_eq_of_eq_mul_left ] <;> linarith;
        simp_all +decide [ Finset.offDiag_card ];
        rw [ show { p ∈ A ×ˢ A | p.1 = p.2 } = Finset.image ( fun x => ( x, x ) ) A by ext ⟨ x, y ⟩ ; aesop ] ; rw [ Finset.card_image_of_injective _ fun x y hxy => by aesop ] ; linarith [ Nat.sub_add_cancel ( show A.card ≤ A.card * A.card from Nat.le_mul_self _ ), Nat.div_mul_cancel ( show 2 ∣ A.card * A.card - A.card from even_iff_two_dvd.mp <| by rw [ Nat.even_sub <| Nat.le_mul_self _ ] ; simp +arith +decide [ mul_add, parity_simps ] ) ];
      · intro p hp q hq; specialize hA p.1 ( by aesop ) p.2 ( by aesop ) q.1 ( by aesop ) q.2 ( by aesop ) ; aesop;
        · grind;
        · grind;
    convert h_inj using 2 ; ext ; aesop;
    · cases' Finset.mem_add.mp a_1 with x hx ; cases' hx with y hy ; aesop;
      cases le_total x w <;> [ exact ⟨ x, w, ⟨ ⟨ y, left ⟩, by linarith ⟩, rfl ⟩ ; exact ⟨ w, x, ⟨ ⟨ left, y ⟩, by linarith ⟩, by linarith ⟩ ];
    · exact Finset.add_mem_add left right_2

theorem sidon_diff_count_le_one {A : Finset ℕ} (hA : IsSidon A) {k : ℕ} (hk : k ≠ 0) :
  solutions_diff_k A k ≤ 1 := by
    by_contra h_contra
    obtain ⟨x, hx₁, hx₂⟩ : ∃ x ∈ A, x + k ∈ A ∧ ∃ y ∈ A, y + k ∈ A ∧ x ≠ y := by
      obtain ⟨ x, hx ⟩ := Finset.one_lt_card.mp ( not_le.mp h_contra ) ; obtain ⟨ y, hy ⟩ := Finset.exists_ne_of_one_lt_card ( not_le.mp h_contra ) x; use x, by aesop, by aesop, y; aesop;
    have h_eq : ({x + k, hx₂.right.choose} : Set ℕ) = ({hx₂.right.choose + k, x} : Set ℕ) := by
      apply hA;
      · aesop;
      · exact hx₂.2.choose_spec.1;
      · exact hx₂.2.choose_spec.2.1;
      · aesop;
      · ring;
    norm_num [ Set.Subset.antisymm_iff, Set.subset_def ] at h_eq;
    exact hx₂.2.choose_spec.2.2 ( h_eq.1.1.resolve_right hk ▸ rfl )

theorem sumset_subset_interval {A : Finset ℕ} (hA : A.Nonempty) :
  sumset A ⊆ Finset.Icc (2 * A.min' hA) (2 * A.max' hA) := by
    intro x hx
    rw [sumset] at hx
    obtain ⟨a, b, ha, hb, hx_eq⟩ : ∃ a b, a ∈ A ∧ b ∈ A ∧ x = a + b := by
      simpa [ eq_comm ] using Finset.mem_add.mp hx;
    exact Finset.mem_Icc.mpr ⟨ by linarith [ Finset.min'_le _ _ ha, Finset.min'_le _ _ hb ], by linarith [ Finset.le_max' _ _ ha, Finset.le_max' _ _ hb ] ⟩

def avg_gap (S : Finset ℕ) : ℝ :=
  let sorted := S.sort (·≤·)
  let gaps := List.zipWith (fun a b => (a - b : ℕ)) sorted.tail sorted
  (gaps.map (fun g => (g : ℝ))).sum / (S.card - 1 : ℝ)

theorem avg_squared_gap_ge_sq_avg_gap {S : Finset ℕ} (hS : S.card > 1) :
  avg_squared_gap S ≥ (avg_gap S) ^ 2 := by
    set N := S.card - 1
    set gaps := List.zipWith (fun a b => (a - b : ℕ)) (S.sort (· ≤ ·)).tail (S.sort (· ≤ ·));
    have h_cauchy_schwarz : ∀ (g : List ℕ), (List.sum (List.map (fun g => (g : ℝ)) g))^2 ≤ (g.length : ℝ) * (List.sum (List.map (fun g => (g : ℝ)^2) g)) := by
      intro g; induction g <;> aesop;
      rcases tail <;> aesop;
      have := sq_nonneg ( ( head : ℝ ) * ( tail.length + 1 ) - ( head_1 + List.sum ( List.map ( fun g : ℝ => ( g : ℝ ) ) tail ) ) ) ; ( norm_num at * ; nlinarith; );
    unfold avg_gap avg_squared_gap;
    have := h_cauchy_schwarz gaps; rcases S with ⟨ ⟨ l, hl ⟩ ⟩ <;> aesop;
    rw [ div_pow, div_le_div_iff₀ ] <;> first | positivity | nlinarith;

def IsSidonFinset (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → ({a, b} : Finset ℕ) = {c, d}

theorem sidon_max_ge_card_sq {A : Finset ℕ} (hA : IsSidon A) (hA_nonempty : A.Nonempty) (hA_subset : A ⊆ Finset.range (A.max' hA_nonempty + 1)) :
  (A.max' hA_nonempty : ℝ) ≥ (A.card : ℝ) ^ 2 / 4 - (A.card : ℝ) / 4 := by
    have h_bound : (A.max' hA_nonempty : ℝ) ≥ Polynomial.eval (Finset.card A : ℝ) (Polynomial.C (1 / 4) * Polynomial.X ^ 2 - Polynomial.C (1 / 4) * Polynomial.X) := by
      have h_bound : (A.card * (A.card + 1) : ℝ) / 2 ≤ 2 * (A.max' hA_nonempty : ℝ) + 1 := by
        have h_bound : (sumset A).card ≤ 2 * (A.max' hA_nonempty : ℝ) + 1 := by
          have h_bound : (sumset A).card ≤ Finset.card (Finset.Icc (2 * (A.min' hA_nonempty)) (2 * (A.max' hA_nonempty))) := by
            refine Finset.card_le_card ?_;
            exact sumset_subset_interval hA_nonempty;
          exact_mod_cast h_bound.trans ( by norm_num );
        convert h_bound using 1;
        rw [ card_sumset_sidon hA ];
        norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_two_of_bodd ];
      norm_num; nlinarith;
    convert h_bound using 1 ; norm_num ; ring