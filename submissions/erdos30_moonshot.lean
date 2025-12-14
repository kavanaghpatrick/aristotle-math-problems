/-
ERDŐS PROBLEM #30 - $1000 PRIZE ATTEMPT
Target: Prove h(N) = N^{1/2} + O_ε(N^ε) for every ε > 0

Current best known: h(N) ≤ N^{1/2} + 0.98183·N^{1/4} + O(1) [Carter-Hunter-O'Bryant 2025]

STRATEGY: Use proven scaffolding to attempt improvement on error term.
We provide all known lemmas and ask Aristotle to find a tighter bound.

PROVEN SCAFFOLDING:
1. IsSidon definition
2. card_sumset_sidon: |A+A| = |A|(|A|+1)/2
3. sumset_subset_interval: A+A ⊆ [2·min(A), 2·max(A)]
4. sidon_max_ge_card_sq: max(A) ≥ |A|²/4 - |A|/4

GOAL: Improve the N^{1/4} error term toward O_ε(N^ε)
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

/-! ## Definitions -/

def IsSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → ({a, b} : Set ℕ) = {c, d}

def sumset (A : Finset ℕ) : Finset ℕ := A + A

/-- h(N) is the maximum size of a Sidon set in {1,...,N} -/
def sidon_max_size (N : ℕ) : ℕ :=
  Finset.sup (Finset.univ.filter (fun A : Finset ℕ => A ⊆ Finset.range (N + 1) ∧ IsSidon ↑A)) Finset.card

/-! ## PROVEN LEMMAS (Scaffolding) -/

/-- For Sidon sets, |A+A| = |A|(|A|+1)/2 -/
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

/-- A+A is contained in the interval [2·min(A), 2·max(A)] -/
theorem sumset_subset_interval {A : Finset ℕ} (hA : A.Nonempty) :
  sumset A ⊆ Finset.Icc (2 * A.min' hA) (2 * A.max' hA) := by
    intro x hx
    rw [sumset] at hx
    obtain ⟨a, b, ha, hb, hx_eq⟩ : ∃ a b, a ∈ A ∧ b ∈ A ∧ x = a + b := by
      simpa [ eq_comm ] using Finset.mem_add.mp hx;
    exact Finset.mem_Icc.mpr ⟨ by linarith [ Finset.min'_le _ _ ha, Finset.min'_le _ _ hb ], by linarith [ Finset.le_max' _ _ ha, Finset.le_max' _ _ hb ] ⟩

/-- Classical Erdős-Turán 1941 bound: max(A) ≥ |A|²/4 - |A|/4 -/
theorem sidon_max_ge_card_sq {A : Finset ℕ} (hA : IsSidon A) (hA_nonempty : A.Nonempty) :
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

/-! ## TARGET: Improved Bound -/

/--
PRIZE TARGET: Prove that for every ε > 0, there exists C_ε such that
h(N) ≤ N^{1/2} + C_ε · N^ε

Equivalently: For a Sidon set A in {1,...,N}, |A| ≤ √N + O_ε(N^ε)

Current best: |A| ≤ √N + 0.98183·N^{1/4} + O(1)

APPROACH HINTS FOR ARISTOTLE:
1. The sumset A+A has |A|(|A|+1)/2 elements
2. These must fit in an interval of length ≤ 2N
3. By pigeonhole, there must be clustering/collisions
4. The Sidon property prevents collisions, forcing spread
5. Can we get a better density estimate than N^{1/4}?

Alternative approaches:
- Fourier analysis on indicator functions
- Energy methods (additive energy of Sidon sets is |A|)
- Probabilistic deletion to thin dense subsets
- Graph-theoretic interpretation via sum graphs
-/

-- Attempt 1: Direct improvement on error term
theorem erdos_30_improved_bound (ε : ℝ) (hε : 0 < ε) (hε_small : ε < 1/4) :
    ∀ N : ℕ, ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) → IsSidon ↑A → A.Nonempty →
    (A.card : ℝ) ≤ Real.sqrt N + N ^ ε := by
  sorry

-- Attempt 2: Specific constant improvement (beat 0.98183)
theorem erdos_30_better_constant {A : Finset ℕ} (hA : IsSidon A) (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ Finset.range (A.max' hA_nonempty + 1)) :
    (A.card : ℝ) ≤ Real.sqrt (A.max' hA_nonempty) + 0.97 * (A.max' hA_nonempty : ℝ) ^ (1/4 : ℝ) + 2 := by
  sorry

-- Attempt 3: Intermediate - Better sumset density bound
theorem improved_sumset_density {A : Finset ℕ} (hA : IsSidon A) (hA_nonempty : A.Nonempty) :
    let N := A.max' hA_nonempty
    let k := A.card
    -- The sumset density (elements per unit interval) must satisfy certain constraints
    (k * (k + 1) / 2 : ℝ) ≤ 2 * N - 2 * (A.min' hA_nonempty) + 1 := by
  -- This is just restating the interval bound, but maybe we can extract more
  sorry

-- Attempt 4: Structure theorem - Sidon sets can't be too dense in any subinterval
theorem sidon_subinterval_sparse {A : Finset ℕ} (hA : IsSidon A) (a b : ℕ) (hab : a < b) :
    let A_sub := A.filter (fun x => a ≤ x ∧ x ≤ b)
    (A_sub.card : ℝ) ≤ Real.sqrt (b - a + 1) + 1 := by
  sorry

end
