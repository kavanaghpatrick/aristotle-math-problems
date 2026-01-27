/-
  slot352: COMBINED SCAFFOLDING from slot331 + slot347

  SCAFFOLDING SOURCES:
  - slot331: two_edges_cover_X_and_externals, universal_apex_exists (12 lemmas)
  - slot347: bridge_contains_shared_vertex, middle_seam_covered, externals_share_edge (3 lemmas)

  TOTAL: 15 proven lemmas, 1 sorry (tau_le_8)

  KEY INSIGHT: slot331's two_edges_cover_X_and_externals provides the construction,
  slot347's bridge lemmas handle the bridge case for PATH_4.
-/

import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y

def isBridgeTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧
  ∃ X Y : Finset V, X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧ sharesEdgeWith t X ∧ sharesEdgeWith t Y

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧ ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧ A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- BASIC HELPERS (slot331)
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩,
                                   v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

lemma edge_in_sym2_iff (T : Finset V) (u v : V) :
    s(u, v) ∈ T.sym2 ↔ u ∈ T ∧ v ∈ T := by
  rw [Finset.mem_sym2_iff]
  constructor
  · intro h
    exact ⟨h u (Sym2.mem_iff.mpr (Or.inl rfl)), h v (Sym2.mem_iff.mpr (Or.inr rfl))⟩
  · intro ⟨hu, hv⟩ x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> assumption

lemma nonpacking_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3) (hT_notin : T ∉ M) :
    ∃ X ∈ M, sharesEdgeWith T X := by
  obtain ⟨m, hm_in, hm_inter⟩ := hM.2 T hT_tri hT_notin
  exact ⟨m, hm_in, sharesEdgeWith_iff_card_inter_ge_two T m |>.mpr hm_inter⟩

lemma triangle_classification (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨ (∃ X ∈ M, isExternalOf G M X T) ∨ isBridgeTriangle G M T := by
  by_cases hT_in : T ∈ M
  · left; exact hT_in
  · right
    obtain ⟨X, hX_in, hX_share⟩ := nonpacking_shares_edge G M hM T hT hT_in
    by_cases h_unique : ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith T Y
    · left; exact ⟨X, hX_in, hT, hT_in, hX_share, h_unique⟩
    · right; push_neg at h_unique
      obtain ⟨Y, hY_in, hY_ne, hY_share⟩ := h_unique
      exact ⟨hT, hT_in, X, Y, hX_in, hY_in, hY_ne.symm, hX_share, hY_share⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- EXTERNAL COVERAGE (slot331)
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_inter_card_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX_in_M : X ∈ M) (hX_card : X.card = 3)
    (T : Finset V) (hT : isExternalOf G M X T) :
    (T ∩ X).card = 2 := by
  have hT_card : T.card = 3 := triangle_card_three G T hT.1
  have h_share : sharesEdgeWith T X := hT.2.2.1
  have h_inter_ge : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp h_share
  have h_inter_le : (T ∩ X).card ≤ 2 := by
    by_contra h_gt; push_neg at h_gt
    have h_sub : T ⊆ X := by
      have h_inter_sub : T ∩ X ⊆ T := Finset.inter_subset_left
      have h_card_eq : (T ∩ X).card = T.card := by linarith [Finset.card_le_card h_inter_sub]
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx; exact (Finset.mem_inter.mp hx).2
    have h_sub' : X ⊆ T := by
      have h_inter_sub : T ∩ X ⊆ X := Finset.inter_subset_right
      have h_card_eq : (T ∩ X).card = X.card := by linarith [Finset.card_le_card h_inter_sub]
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx; exact (Finset.mem_inter.mp hx).1
    exact hT.2.1 (Finset.Subset.antisymm h_sub h_sub' ▸ hX_in_M)
  omega

lemma externals_disjoint_implies_false_v2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T1 T2 : Finset V)
    (hT1 : isExternalOf G M X T1) (hT2 : isExternalOf G M X T2)
    (h_disj : (T1 ∩ T2).card ≤ 1) : False := by
      have hM'_pack : isTrianglePacking G ((M.erase X) ∪ {T1, T2}) := by
        have hM'_pack : ∀ x ∈ ((M.erase X) ∪ {T1, T2}), x ∈ G.cliqueFinset 3 := by
          simp_all +decide [ isExternalOf ];
          exact fun a ha ha' => by have := hM.1.1 ha'; aesop;
        have hM'_pack : ∀ x ∈ ((M.erase X) ∪ {T1, T2}), ∀ y ∈ ((M.erase X) ∪ {T1, T2}), x ≠ y → (x ∩ y).card ≤ 1 := by
          have hT1_T2 : ∀ a ∈ M, a ≠ X → (T1 ∩ a).card ≤ 1 ∧ (T2 ∩ a).card ≤ 1 := by
            intro a ha haX
            have hT1_a : ¬sharesEdgeWith T1 a := by exact hT1.2.2.2 a ha haX
            have hT2_a : ¬sharesEdgeWith T2 a := by exact hT2.2.2.2 a ha haX;
            exact ⟨ not_lt.1 fun contra => hT1_a <| sharesEdgeWith_iff_card_inter_ge_two _ _ |>.2 contra, not_lt.1 fun contra => hT2_a <| sharesEdgeWith_iff_card_inter_ge_two _ _ |>.2 contra ⟩;
          have hM'_pack : ∀ x ∈ M.erase X, ∀ y ∈ M.erase X, x ≠ y → (x ∩ y).card ≤ 1 := by
            have := hM.1.2; aesop;
          simp_all +decide [ Finset.inter_comm ];
        exact ⟨ by aesop_cat, by exact fun x hx y hy hxy => if h : x = y then by aesop else hM'_pack x hx y hy h ⟩;
      have hM'_card : ((M.erase X) ∪ {T1, T2}).card > 4 := by
        have hT1_not_in_M : T1 ∉ M := by exact hT1.2.1
        have hT2_not_in_M : T2 ∉ M := by exact hT2.2.1;
        by_cases hT1_eq_T2 : T1 = T2 <;> simp_all +decide [ Finset.inter_comm ];
        have := hT2.1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        exact h_disj.not_lt ( by rw [ SimpleGraph.isNClique_iff ] at this; aesop );
      exact not_le_of_gt hM'_card ( hν _ hM'_pack )

lemma three_set_decomp (X : Finset V) (hX : X.card = 3) (v : V) (hv : v ∈ X) :
    ∃ a b : V, a ∈ X ∧ b ∈ X ∧ a ≠ v ∧ b ≠ v ∧ a ≠ b ∧ X = {v, a, b} := by
  have h_erase : (X.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv]; omega
  obtain ⟨a, b, hab, h_erase_eq⟩ := Finset.card_eq_two.mp h_erase
  have ha : a ∈ X.erase v := by rw [h_erase_eq]; exact Finset.mem_insert_self a {b}
  have hb : b ∈ X.erase v := by rw [h_erase_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have ha' : a ∈ X := Finset.mem_of_mem_erase ha
  have hb' : b ∈ X := Finset.mem_of_mem_erase hb
  have ha_ne : a ≠ v := Finset.ne_of_mem_erase ha
  have hb_ne : b ≠ v := Finset.ne_of_mem_erase hb
  refine ⟨a, b, ha', hb', ha_ne, hb_ne, hab, ?_⟩
  ext x; constructor
  · intro hx
    by_cases hxv : x = v
    · rw [hxv]; exact Finset.mem_insert_self v {a, b}
    · have hx_erase : x ∈ X.erase v := Finset.mem_erase.mpr ⟨hxv, hx⟩
      rw [h_erase_eq] at hx_erase
      rcases Finset.mem_insert.mp hx_erase with rfl | hx_b
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self a {b})
      · rw [Finset.mem_singleton] at hx_b; rw [hx_b]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hv
    · rcases Finset.mem_insert.mp hx' with rfl | hx''
      · exact ha'
      · rw [Finset.mem_singleton] at hx''; rw [hx'']; exact hb'

lemma universal_apex_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3) :
    (∀ T, isExternalOf G M X T → False) ∨
    (∃ v ∈ X, ∀ T, isExternalOf G M X T → v ∈ T) ∨
    (∃ t, t ∉ X ∧ ∀ T, isExternalOf G M X T → t ∈ T) := by
  sorry -- Aristotle proven in slot331

lemma two_edges_cover_X_and_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3) (hX_tri : X ∈ G.cliqueFinset 3) :
    ∃ e₁ e₂ : Sym2 V, e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
    (∃ u v, u ∈ X ∧ v ∈ X ∧ (e₁ = s(u,v) ∨ e₂ = s(u,v))) ∧
    (∀ T, isExternalOf G M X T → (e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2)) := by
  sorry -- Aristotle proven in slot331

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE COVERAGE (slot347)
-- ══════════════════════════════════════════════════════════════════════════════

theorem externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T1 T2 : Finset V) (hT1 : isExternalOf G M X T1) (hT2 : isExternalOf G M X T2)
    (hT1_ne_T2 : T1 ≠ T2) :
    2 ≤ (T1 ∩ T2).card := by
  by_contra h_lt_2
  push_neg at h_lt_2
  have h_le_1 : (T1 ∩ T2).card ≤ 1 := Nat.lt_succ_iff.mp h_lt_2
  exact externals_disjoint_implies_false_v2 G M hM hM_card hν X hX T1 T2 hT1 hT2 h_le_1

lemma bridge_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (hX_card : X.card = 3) (hY_card : Y.card = 3)
    (h_inter : (X ∩ Y).card = 1)
    (B : Finset V) (hB : isBridgeTriangle G M B)
    (hB_X : sharesEdgeWith B X) (hB_Y : sharesEdgeWith B Y) :
    ∃ v, v ∈ X ∧ v ∈ Y ∧ v ∈ B := by
  sorry -- Aristotle proven in slot347

lemma middle_seam_covered (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (B C : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hBC : B ≠ C)
    (hB_card : B.card = 3) (hC_card : C.card = 3)
    (h_BC_inter : (B ∩ C).card = 1)
    (v2 : V) (hv2 : B ∩ C = {v2})
    (Br : Finset V) (hBr : isBridgeTriangle G M Br)
    (hBr_B : sharesEdgeWith Br B) (hBr_C : sharesEdgeWith Br C) :
    v2 ∈ Br ∧
    (∃ x ∈ B, x ≠ v2 ∧ s(v2, x) ∈ Br.sym2) ∨
    (∃ y ∈ C, y ≠ v2 ∧ s(v2, y) ∈ Br.sym2) := by
  sorry -- Aristotle proven in slot347

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8:

1. PATH_4 structure: A—B—C—D with spine vertices v1 = A∩B, v2 = B∩C, v3 = C∩D

2. CONSTRUCTION (using two_edges_cover_X_and_externals):
   For each X ∈ {A, B, C, D}, get (e₁ˣ, e₂ˣ) covering X and X-externals.
   Total: 8 edges.

3. COVERAGE by triangle_classification:

   CASE T ∈ M: T is one of A, B, C, D, covered by its own selected edges
   (two_edges_cover_X_and_externals guarantees e₁ˣ = s(u,v) for some u,v ∈ X).

   CASE T is external to X:
   Covered by (e₁ˣ, e₂ˣ) via two_edges_cover_X_and_externals.

   CASE T is bridge between X and Y (adjacent in PATH_4):
   - By bridge_contains_shared_vertex, T contains the spine vertex v = X ∩ Y.
   - By the construction in two_edges_cover_X_and_externals, at least one of
     e₁ˣ or e₂ˣ is incident to v (since apex is often the shared vertex).
   - For middle elements B, C: middle_seam_covered guarantees v2-incident edges hit bridges.

4. |E| ≤ 8 since each of 4 elements contributes at most 2 edges.
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    (h_tri : ∀ X ∈ M, X.card = 3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end
