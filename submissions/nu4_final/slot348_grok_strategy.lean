/-
  slot348: GROK STRATEGY - Use selection_compatible for bridge coverage

  STRATEGY (Grok Option 3):
  Each bridge is covered by SOME M-element's selection:
  - A-B bridges → covered by A (its only bridge type, per path4_A_bridges_only_to_B)
  - B-C bridges → covered by B or C (choose strategically)
  - C-D bridges → covered by D (its only bridge type, per path4_D_bridges_only_to_C)

  KEY PROVEN LEMMAS:
  1. two_edges_cover_X_externals_and_bridge: 2 edges cover X + externals + ONE bridge
  2. selection_compatible: apex-based edges cover bridges (apex ∈ B, or other M covers)
  3. externals_share_edge: All X-externals share an edge
  4. bridge_inter_nonempty: Bridges contain shared spine vertex
  5. path4_A_bridges_only_to_B, path4_D_bridges_only_to_C: endpoint bridge constraints

  PROOF SKETCH:
  For PATH_4 A—B—C—D:
  - A contributes 2 edges covering A + A-externals + all A-B bridges
  - B contributes 2 edges covering B + B-externals + B-C bridges (choose B-C)
  - C contributes 2 edges covering C + C-externals (B-C already covered by B)
  - D contributes 2 edges covering D + D-externals + all C-D bridges
  Total: 8 edges, all triangles covered by selection_compatible argument
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

def isBridgeOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X Y B : Finset V) : Prop :=
  B ∈ G.cliqueFinset 3 ∧ B ∉ M ∧ X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧
  sharesEdgeWith B X ∧ sharesEdgeWith B Y

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧ ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧ A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (All Aristotle-verified)
-- ══════════════════════════════════════════════════════════════════════════════

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

-- Bridges contain shared spine vertex (from slot342)
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

-- All X-externals share an edge (from slot344)
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
  let M' := (M.erase X) ∪ {T1, T2}
  have hM'_pack : isTrianglePacking G M' := by
    constructor
    · intro t ht
      simp only [mem_union, mem_erase, mem_insert, mem_singleton] at ht
      rcases ht with ⟨_, ht'⟩ | rfl | rfl
      · exact hM.1.1 ht'
      · exact hT1.1
      · exact hT2.1
    · intro a ha b hb hab
      simp only [coe_union, coe_erase, coe_insert, coe_singleton,
                 Set.mem_union, Set.mem_diff, Set.mem_singleton_iff,
                 Set.mem_insert_iff] at ha hb
      rcases ha with ⟨ha1, ha2⟩ | rfl | rfl <;> rcases hb with ⟨hb1, hb2⟩ | rfl | rfl
      · exact hM.1.2 ha1 hb1 hab
      · have hT1_not_a := hT1.2.2.2 a ha1 (Ne.symm ha2)
        exact Nat.lt_one_iff.mp (Nat.not_le.mp (mt (sharesEdgeWith_iff_card_inter_ge_two T1 a).mpr hT1_not_a))
      · have hT2_not_a := hT2.2.2.2 a ha1 (Ne.symm ha2)
        exact Nat.lt_one_iff.mp (Nat.not_le.mp (mt (sharesEdgeWith_iff_card_inter_ge_two T2 a).mpr hT2_not_a))
      · have hT1_not_b := hT1.2.2.2 b hb1 (Ne.symm hb2)
        rw [inter_comm]
        exact Nat.lt_one_iff.mp (Nat.not_le.mp (mt (sharesEdgeWith_iff_card_inter_ge_two T1 b).mpr hT1_not_b))
      · exact hab.elim rfl
      · exact h_le_1
      · have hT2_not_b := hT2.2.2.2 b hb1 (Ne.symm hb2)
        rw [inter_comm]
        exact Nat.lt_one_iff.mp (Nat.not_le.mp (mt (sharesEdgeWith_iff_card_inter_ge_two T2 b).mpr hT2_not_b))
      · rw [inter_comm]; exact h_le_1
      · exact hab.elim rfl
  have hM'_card : M'.card > 4 := by
    have hT1_notin : T1 ∉ M := hT1.2.1
    have hT2_notin : T2 ∉ M := hT2.2.1
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
  exact Nat.not_lt.mpr (hν M' hM'_pack) hM'_card

-- 2 edges cover X + externals + ONE bridge (from slot343)
lemma two_edges_cover_X_externals_and_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X Y B : Finset V) (hBridge : isBridgeOf G M X Y B)
    (hX_card : X.card = 3) :
    ∃ e1 e2 : Sym2 V, e1 ∈ G.edgeFinset ∧ e2 ∈ G.edgeFinset ∧
    (∃ u ∈ X, ∃ v ∈ X, u ≠ v ∧ (e1 = s(u,v) ∨ e2 = s(u,v))) ∧
    (∀ T, isExternalOf G M X T → e1 ∈ T.sym2 ∨ e2 ∈ T.sym2) ∧
    (e1 ∈ B.sym2 ∨ e2 ∈ B.sym2) := by
  sorry  -- Proven by Aristotle in slot343

-- Selection compatible: apex-based edges cover bridges (from slot346)
lemma selection_compatible (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (apex : V) (h_apex_in_X : apex ∈ X)
    (h_apex_universal : ∀ T, isExternalOf G M X T → apex ∈ T)
    (a b : V) (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b) (ha_ne : a ≠ apex) (hb_ne : b ≠ apex)
    (B : Finset V) (hB : isBridgeTriangle G M B)
    (hB_X : sharesEdgeWith B X) :
    s(apex, a) ∈ B.sym2 ∨ s(apex, b) ∈ B.sym2 ∨
    ∃ Y ∈ M, Y ≠ X ∧ sharesEdgeWith B Y := by
  sorry  -- Proven by Aristotle in slot346

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8 (Grok Strategy - Option 3):

1. EDGE CONSTRUCTION:
   For each X ∈ M = {A, B, C, D}:
   - Find apex vertex (universal for X-externals)
   - X = {apex, a, b}
   - Select edges e₁ = {apex, a}, e₂ = {apex, b}
   Total: 4 × 2 = 8 edges

2. COVERAGE BY triangle_classification:

   CASE T ∈ M:
   - T's own 2 edges cover it (both endpoints in T)

   CASE T is external to X:
   - apex ∈ T (by h_apex_universal)
   - T shares edge with X → T ∩ X has vertex besides apex
   - So {apex, a} or {apex, b} ∈ T.sym2

   CASE T is bridge between X and Y:
   - By selection_compatible:
     (a) X's apex-based edges hit T, OR
     (b) T shares edge with Y → Y's edges hit T
   - Either way, SOME M-element's edges cover T

3. BRIDGE ASSIGNMENT (PATH_4 specific):
   - A-B bridges: A covers (its only bridge type)
   - B-C bridges: B covers (choosing B-C as B's "one" bridge)
   - C-D bridges: D covers (its only bridge type)
   - No "leftover" bridges since selection_compatible ensures coverage

4. |E| ≤ 8: Each X contributes 2 edges, |M| = 4
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end
