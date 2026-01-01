/-
PROVEN SCAFFOLDING from Slot 63 (UUID: 3d31b863)
These lemmas are FULLY PROVEN by Aristotle - copy directly into new submissions.

PROVEN LEMMAS:
1. M_edge_in_exactly_one - edges in packing are disjoint
2. triangle_shares_edge_with_packing - maximality
3. M_char_is_fractional - M-char is valid fractional packing
4. M_char_weight_eq_card - weight equals |M|
5. M_char_weight_eq_4 - weight = 4 for ν=4
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ M' : Finset (Finset V), isTrianglePacking G M' → M'.card ≤ M.card

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧
    (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card = n}

def isFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) : Prop :=
  (∀ t, w t ≥ 0) ∧
  (∀ t, t ∉ G.cliqueFinset 3 → w t = 0) ∧
  (∀ e ∈ G.edgeFinset, ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2), w t ≤ 1)

def packingWeight (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : ℝ :=
  ∑ t ∈ G.cliqueFinset 3, w t

def M_char (M : Finset (Finset V)) : Finset V → ℝ :=
  fun t => if t ∈ M then 1 else 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA 1: M_edge_in_exactly_one
-- ══════════════════════════════════════════════════════════════════════════════

/-- Each edge in a triangle packing appears in exactly one triangle. -/
lemma M_edge_in_exactly_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
  intro m' hm' hne he'
  rw [Finset.mem_sym2_iff] at he he'
  obtain ⟨u, v, huv, hu_m, hv_m, rfl⟩ := he
  obtain ⟨u', v', _, hu'_m', hv'_m', heq⟩ := he'
  simp only [Sym2.eq, Sym2.rel_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h_card : (m ∩ m').card ≥ 2 := by
      have hsub : ({u, v} : Finset V) ⊆ m ∩ m' := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hu_m, hu'_m'⟩
        · exact Finset.mem_inter.mpr ⟨hv_m, hv'_m'⟩
      calc 2 = ({u, v} : Finset V).card := (Finset.card_pair huv).symm
        _ ≤ (m ∩ m').card := Finset.card_le_card hsub
    have := hM.2 hm hm' hne.symm
    omega
  · have h_card : (m ∩ m').card ≥ 2 := by
      have hsub : ({u, v} : Finset V) ⊆ m ∩ m' := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hu_m, hv'_m'⟩
        · exact Finset.mem_inter.mpr ⟨hv_m, hu'_m'⟩
      calc 2 = ({u, v} : Finset V).card := (Finset.card_pair huv).symm
        _ ≤ (m ∩ m').card := Finset.card_le_card hsub
    have := hM.2 hm hm' hne.symm
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA 2: triangle_shares_edge_with_packing
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle shares ≥2 vertices with some M-element (maximality). -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ m ∈ M, (t ∩ m).card ≥ 2 := by
  obtain ⟨hM_triangle_packing, hM_max⟩ := hM
  contrapose! hM_max
  refine ⟨insert t M, ?_, ?_⟩
  · simp only [isTrianglePacking, Finset.subset_iff, Set.Pairwise] at *
    constructor
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact ht
      · exact hM_triangle_packing.1 hx
    · intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact (hxy rfl).elim
      · exact Nat.le_of_lt_succ (hM_max y hy)
      · rw [Finset.inter_comm]; exact Nat.le_of_lt_succ (hM_max x hx)
      · exact hM_triangle_packing.2 hx hy hxy
  · rw [Finset.card_insert_of_not_mem]
    · omega
    · intro ht_in_M
      specialize hM_max t ht_in_M
      have := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
      omega

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA 3: M_char_is_fractional
-- ══════════════════════════════════════════════════════════════════════════════

/-- M_char is a valid fractional packing. -/
lemma M_char_is_fractional (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    isFractionalPacking G (M_char M) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun t => by unfold M_char; split_ifs <;> norm_num
  · exact fun t ht => if_neg fun h => ht (hM.1 h)
  · intro e he
    have h_disjoint : ∀ t1 t2 : Finset V, t1 ∈ M → t2 ∈ M → e ∈ t1.sym2 → e ∈ t2.sym2 → t1 = t2 := by
      intro t1 t2 ht1 ht2 ht1e ht2e
      by_contra hne
      exact M_edge_in_exactly_one G M hM e t1 ht1 ht1e t2 ht2 hne ht2e
    have h_sum : ∑ t ∈ G.cliqueFinset 3, (if t ∈ M ∧ e ∈ t.sym2 then 1 else 0) ≤ 1 := by
      simp only [← Finset.filter_filter]
      have h_card : ((G.cliqueFinset 3).filter (fun t => t ∈ M ∧ e ∈ t.sym2)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro x hx y hy
        simp only [Finset.mem_filter] at hx hy
        exact h_disjoint x y hx.2.1 hy.2.1 hx.2.2 hy.2.2
      calc ∑ t ∈ (G.cliqueFinset 3).filter (fun t => t ∈ M ∧ e ∈ t.sym2), (1 : ℝ)
          = ((G.cliqueFinset 3).filter (fun t => t ∈ M ∧ e ∈ t.sym2)).card := by simp
        _ ≤ 1 := by exact_mod_cast h_card
    simp only [M_char]
    convert h_sum using 2
    ext t
    simp only [ite_and]
    split_ifs <;> simp_all

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA 4: M_char_weight_eq_card
-- ══════════════════════════════════════════════════════════════════════════════

/-- M_char weight equals |M| for ANY packing. -/
lemma M_char_weight_eq_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    packingWeight G (M_char M) = M.card := by
  have h_sum : packingWeight G (M_char M) = ∑ t ∈ M, (1 : ℝ) := by
    unfold packingWeight M_char
    rw [← Finset.sum_subset hM.1]
    · congr 1
      ext t
      simp only [ite_eq_left_iff, one_ne_zero]
      tauto
    · intro t _ ht
      simp only [if_neg ht]
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h_sum
  rw [h_sum]
  simp

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA 5: M_char_weight_eq_4
-- ══════════════════════════════════════════════════════════════════════════════

/-- For ν = 4, M_char weight = 4. -/
lemma M_char_weight_eq_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (h_card : M.card = 4) :
    packingWeight G (M_char M) = 4 := by
  rw [M_char_weight_eq_card G M hM, h_card]
  norm_num

end
