/-
  slot342: COMBINED SCAFFOLDING from 3 Aristotle outputs

  SYNTHESIS OF PROVEN LEMMAS:
  - From slot332: bridge_inter_nonempty (B ∩ X ∩ Y ≠ ∅)
  - From slot331: two_edges_cover_X_and_externals, universal_apex_exists
  - From slot330: bridge_covered_by_some_m_edge

  KEY INSIGHT FOR BRIDGES:
  bridge_inter_nonempty proves: Every bridge B has vertex v ∈ X ∩ Y.
  For PATH_4, these shared vertices are the SPINE: v_ab, v_bc, v_cd.

  If we ensure the apex-based selection includes spine vertices,
  then ALL bridges are automatically covered!

  PROOF STRATEGY:
  1. For each X ∈ M, universal_apex_exists gives an apex
  2. two_edges_cover_X_and_externals shows 2 edges cover X + externals
  3. For bridges: bridge_inter_nonempty says B contains shared vertex v
  4. If X's apex is the shared vertex v, X's edges hit B
  5. If not, show another M-element's apex IS on B (using ν≤4)
-/

import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators Classical
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════ DEFINITIONS ═══════════════════

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

-- ═══════════════════ PROVEN HELPERS (Aristotle verified) ═══════════════════

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

-- CRITICAL: Bridge intersection is nonempty (from slot332)
lemma bridge_inter_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (B X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (hBX : sharesEdgeWith B X) (hBY : sharesEdgeWith B Y)
    (hB_card : B.card = 3) :
    (B ∩ X ∩ Y).Nonempty := by
  by_contra h_empty
  rw [Finset.not_nonempty_iff_eq_empty] at h_empty
  have hBX_ge : (B ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two B X |>.mp hBX
  have hBY_ge : (B ∩ Y).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two B Y |>.mp hBY
  have h_disj : Disjoint (B ∩ X) (B ∩ Y) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    convert h_empty using 1; ext v; simp [Finset.mem_inter]
  have h_union_card : ((B ∩ X) ∪ (B ∩ Y)).card ≥ 4 := by
    rw [Finset.card_union_of_disjoint h_disj]; omega
  have h_sub : (B ∩ X) ∪ (B ∩ Y) ⊆ B := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv' | hv'
    · exact Finset.mem_of_mem_inter_left hv'
    · exact Finset.mem_of_mem_inter_left hv'
  have := Finset.card_le_card h_sub
  omega

-- Bridge covered by some M-edge (from slot330)
lemma bridge_covered_by_some_m_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T : Finset V) (hT : isBridgeTriangle G M T) :
    ∃ X ∈ M, ∃ u v : V, u ≠ v ∧ u ∈ X ∧ v ∈ X ∧ s(u, v) ∈ T.sym2 := by
  obtain ⟨_, _, X, _, hX_in, _, _, hX_share, _⟩ := hT
  obtain ⟨u, v, huv, hu_T, hv_T, hu_X, hv_X⟩ := hX_share
  exact ⟨X, hX_in, u, v, huv, hu_X, hv_X, edge_in_sym2_iff T u v |>.mpr ⟨hu_T, hv_T⟩⟩

-- ═══════════════════ KEY LEMMAS FROM slot331 ═══════════════════

-- Externals disjoint implies packing contradiction (ν≤4 key!)
lemma externals_disjoint_implies_false (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T1 T2 : Finset V)
    (hT1 : isExternalOf G M X T1) (hT2 : isExternalOf G M X T2)
    (h_disj : (T1 ∩ T2).card ≤ 1) : False := by
  have hM'_pack : isTrianglePacking G ((M.erase X) ∪ {T1, T2}) := by
    have h_in_clique : ∀ x ∈ ((M.erase X) ∪ {T1, T2}), x ∈ G.cliqueFinset 3 := by
      intro x hx
      simp only [mem_union, mem_erase, mem_insert, mem_singleton] at hx
      rcases hx with ⟨_, hx'⟩ | rfl | rfl
      · exact hM.1.1 hx'
      · exact hT1.1
      · exact hT2.1
    have h_pairwise : Set.Pairwise (((M.erase X) ∪ {T1, T2}) : Set (Finset V))
        (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
      intro a ha b hb hab
      simp only [coe_union, coe_erase, coe_insert, coe_singleton,
                 Set.mem_union, Set.mem_diff, Set.mem_singleton_iff,
                 Set.mem_insert_iff] at ha hb
      rcases ha with ⟨ha1, ha2⟩ | rfl | rfl <;> rcases hb with ⟨hb1, hb2⟩ | rfl | rfl
      · exact hM.1.2 ha1 hb1 hab
      · have := hT1.2.2.2 a ha1 (Ne.symm ha2)
        exact Nat.lt_one_iff.mp (Nat.not_le.mp (mt (sharesEdgeWith_iff_card_inter_ge_two T1 a).mpr this))
      · have := hT2.2.2.2 a ha1 (Ne.symm ha2)
        exact Nat.lt_one_iff.mp (Nat.not_le.mp (mt (sharesEdgeWith_iff_card_inter_ge_two T2 a).mpr this))
      · have := hT1.2.2.2 b hb1 (Ne.symm hb2)
        rw [inter_comm]; exact Nat.lt_one_iff.mp (Nat.not_le.mp (mt (sharesEdgeWith_iff_card_inter_ge_two T1 b).mpr this))
      · exact hab.elim rfl
      · exact h_disj
      · have := hT2.2.2.2 b hb1 (Ne.symm hb2)
        rw [inter_comm]; exact Nat.lt_one_iff.mp (Nat.not_le.mp (mt (sharesEdgeWith_iff_card_inter_ge_two T2 b).mpr this))
      · rw [inter_comm]; exact h_disj
      · exact hab.elim rfl
    exact ⟨fun x hx => h_in_clique x hx, h_pairwise⟩
  have hM'_card : ((M.erase X) ∪ {T1, T2}).card > 4 := by
    have hT1_notin : T1 ∉ M := hT1.2.1
    have hT2_notin : T2 ∉ M := hT2.2.1
    have hT1_ne_T2 : T1 ≠ T2 := by
      intro h_eq
      rw [h_eq] at h_disj
      have := triangle_card_three G T2 hT2.1
      simp only [inter_self] at h_disj
      omega
    simp only [card_union_of_disjoint, card_erase_of_mem hX, card_insert_of_not_mem,
               card_singleton, hM_card]
    · omega
    · simp [hT1_ne_T2]
    · simp only [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
      intro x hx
      simp only [mem_inter, mem_erase, mem_insert, mem_singleton] at hx
      rcases hx.2 with rfl | rfl
      · exact hT1_notin hx.1.2
      · exact hT2_notin hx.1.2
  exact Nat.not_lt.mpr (hν _ hM'_pack) hM'_card

-- ═══════════════════ MAIN THEOREM ═══════════════════

/-
PROOF SKETCH for tau_le_8:

1. For each X ∈ M, two_edges_cover_X_and_externals gives 2 edges
2. Total: 4 × 2 = 8 edges

COVERAGE ARGUMENT:
- M-elements: Each X covered by its own 2 edges (one is an X-edge)
- Externals: Covered by two_edges_cover_X_and_externals
- Bridges: By bridge_inter_nonempty, every bridge B has v ∈ X ∩ Y
  - If X's apex is v, X's edges hit B (they're incident to v)
  - If Y's apex is v, Y's edges hit B
  - Key: At least one of X, Y has apex on the shared vertex!

  Why? If neither X nor Y has apex on v = X ∩ Y:
  - X's apex is some x ∉ {v} ∩ externals
  - Y's apex is some y ∉ {v} ∩ externals
  - But B shares edge with both, so B contains v plus one vertex from each
  - This forces B to have 4+ vertices, contradiction!

  Actually simpler: B ∩ X = {v, u} and B ∩ Y = {v, w}.
  B = {v, u, w}. X's selection covers triangles containing X's apex.
  If apex ∈ {v, u}, edges incident to apex include v-adjacent edges hitting B.
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end
