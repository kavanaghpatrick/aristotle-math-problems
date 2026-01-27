/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e98605df-48e3-4c1c-acd4-a039c307546e
-/

/-
  slot347: BRIDGE COORDINATION FIX for τ ≤ 8

  DEBATE CONSENSUS (Gemini + Codex + Grok):
  The "middle seam" problem - B and C can't both satisfy their outer neighbors
  with a single apex each. Fix: Use v2 (shared B∩C vertex) as apex for BOTH.

  KEY INSIGHT:
  - A uses apex = v1 (covers A + A-externals + A-B bridges)
  - B uses apex = v2 (covers B + B-externals + B-C bridges!)
  - C uses apex = v2 (covers C + C-externals + B-C bridges!)
  - D uses apex = v3 (covers D + D-externals + C-D bridges)

  The B-C bridges contain v2 (by bridge_inter_nonempty).
  Since BOTH B and C select edges incident to v2, B-C bridges are covered!

  PROVEN SCAFFOLDING INCLUDED:
  - externals_share_edge (slot344)
  - triangle_classification (slot329)
  - middle_seam_covered (new - uses bridge_inter_nonempty)
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
-- PROVEN HELPERS
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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: externals_share_edge (Aristotle - slot344)
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

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY: Bridge contains shared vertex (spine vertex is in bridge)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for bridge_contains_shared_vertex:
A bridge B shares edges with BOTH X and Y.
- B ∩ X has ≥ 2 elements (shares edge with X)
- B ∩ Y has ≥ 2 elements (shares edge with Y)
- |B| = 3, |X| = 3, |Y| = 3
- In PATH_4, |X ∩ Y| = 1 (spine vertex v)

Since B shares edge with X, let B ∩ X = {u, w} for some u, w ∈ X.
Since B shares edge with Y, let B ∩ Y = {p, q} for some p, q ∈ Y.
Now |B| = 3, so B has at most 3 vertices total.

If v ∉ B, then:
  - B ∩ X ⊆ X \ {v} (2 elements from the 2 non-spine vertices of X)
  - B ∩ Y ⊆ Y \ {v} (2 elements from the 2 non-spine vertices of Y)
  - But X \ {v} and Y \ {v} are DISJOINT (since X ∩ Y = {v})
  - So B has at least 4 vertices (2 from X, 2 from Y, disjoint)
  - Contradiction with |B| = 3!

Therefore v ∈ B.
-/
lemma bridge_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (hX_card : X.card = 3) (hY_card : Y.card = 3)
    (h_inter : (X ∩ Y).card = 1)
    (B : Finset V) (hB : isBridgeTriangle G M B)
    (hB_X : sharesEdgeWith B X) (hB_Y : sharesEdgeWith B Y) :
    ∃ v, v ∈ X ∧ v ∈ Y ∧ v ∈ B := by
  -- Get the unique shared vertex v
  obtain ⟨v, hv, hv_unique⟩ := Finset.card_eq_one.mp h_inter
  have hv_X : v ∈ X := by simp only [mem_inter] at hv; exact hv.1
  have hv_Y : v ∈ Y := by simp only [mem_inter] at hv; exact hv.2
  -- Assume v ∉ B and derive contradiction
  by_contra h_not
  push_neg at h_not
  -- B ∩ X has ≥ 2 elements, all in X \ {v}
  have hBX_card : (B ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two B X |>.mp hB_X
  have hBY_card : (B ∩ Y).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two B Y |>.mp hB_Y
  -- B ∩ X ⊆ X \ {v} and B ∩ Y ⊆ Y \ {v}
  have hBX_sub : B ∩ X ⊆ X.erase v := by
    intro x hx
    simp only [mem_inter] at hx
    simp only [mem_erase]
    constructor
    · intro hxv; subst hxv
      have : v ∈ B := hx.1
      exact h_not v hv_X hv_Y this
    · exact hx.2
  have hBY_sub : B ∩ Y ⊆ Y.erase v := by
    intro x hx
    simp only [mem_inter] at hx
    simp only [mem_erase]
    constructor
    · intro hxv; subst hxv
      have : v ∈ B := hx.1
      exact h_not v hv_X hv_Y this
    · exact hx.2
  -- X.erase v and Y.erase v are disjoint
  have h_disj : Disjoint (X.erase v) (Y.erase v) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext x
    simp only [mem_inter, mem_erase, not_mem_empty, iff_false, not_and, and_imp]
    intro hx_ne hx_X _ hx_Y
    have : x ∈ X ∩ Y := mem_inter.mpr ⟨hx_X, hx_Y⟩
    rw [hv_unique] at this
    simp only [mem_singleton] at this
    exact hx_ne this
  -- B ∩ X and B ∩ Y are disjoint (since subsets of disjoint sets)
  have hBXY_disj : Disjoint (B ∩ X) (B ∩ Y) := by
    exact Disjoint.mono hBX_sub hBY_sub h_disj
  -- B has at least 4 elements
  have hB_card_ge : (B ∩ X ∪ B ∩ Y).card ≥ 4 := by
    rw [Finset.card_union_of_disjoint hBXY_disj]
    omega
  -- But B ∩ X ∪ B ∩ Y ⊆ B
  have hB_sub : B ∩ X ∪ B ∩ Y ⊆ B := by
    intro x hx
    simp only [mem_union, mem_inter] at hx
    rcases hx with ⟨hxB, _⟩ | ⟨hxB, _⟩ <;> exact hxB
  -- B has 3 elements
  have hB_card : B.card = 3 := by
    have := hB.1
    exact (SimpleGraph.mem_cliqueFinset_iff.mp this).2
  -- Contradiction: B has at least 4 elements but also has 3
  have : (B ∩ X ∪ B ∩ Y).card ≤ B.card := Finset.card_le_card hB_sub
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MIDDLE SEAM LEMMA: B-C bridges are covered by v2-incident edges
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for middle_seam_covered:
For PATH_4 A—B—C—D, let v2 be the unique vertex in B ∩ C.

Any B-C bridge contains v2 (by bridge_contains_shared_vertex).
So if we select edges {v2, b1} and {v2, b2} from B (where B = {v2, b1, b2}),
and edges {v2, c1} and {v2, c2} from C (where C = {v2, c1, c2}),
then any B-C bridge is hit by one of these 4 edges.

Actually, the bridge B shares edge with B: B ∩ Bridge has 2 vertices, one of which is v2.
So B ∩ Bridge = {v2, x} for some x ∈ B.
If our edge selection includes {v2, x}, the bridge is hit.
Since we select BOTH edges incident to v2 in B, we hit the bridge.
-/
lemma middle_seam_covered (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (B C : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hBC : B ≠ C)
    (hB_card : B.card = 3) (hC_card : C.card = 3)
    (h_BC_inter : (B ∩ C).card = 1)
    (v2 : V) (hv2 : B ∩ C = {v2})
    (Br : Finset V) (hBr : isBridgeTriangle G M Br)
    (hBr_B : sharesEdgeWith Br B) (hBr_C : sharesEdgeWith Br C) :
    -- The bridge Br contains v2, so v2-incident edges from B or C hit it
    v2 ∈ Br ∧
    (∃ x ∈ B, x ≠ v2 ∧ s(v2, x) ∈ Br.sym2) ∨
    (∃ y ∈ C, y ≠ v2 ∧ s(v2, y) ∈ Br.sym2) := by
  -- Get that v2 ∈ Br
  have ⟨v, hv_B, hv_C, hv_Br⟩ := bridge_contains_shared_vertex G M hM B C hB hC hBC hB_card hC_card h_BC_inter Br hBr hBr_B hBr_C
  have hv_eq : v = v2 := by
    have : v ∈ B ∩ C := mem_inter.mpr ⟨hv_B, hv_C⟩
    rw [hv2] at this
    exact mem_singleton.mp this
  subst hv_eq
  constructor
  · exact hv_Br
  · -- Br shares edge with B, so Br ∩ B = {v2, x} for some x
    have hBrB_card : (Br ∩ B).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two Br B |>.mp hBr_B
    obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hBrB_card
    have hu_Br : u ∈ Br := mem_of_mem_inter_left hu
    have hu_B : u ∈ B := mem_of_mem_inter_right hu
    have hw_Br : w ∈ Br := mem_of_mem_inter_left hw
    have hw_B : w ∈ B := mem_of_mem_inter_right hw
    -- At least one of u, w is different from v2
    by_cases hu_v2 : u = v2
    · -- u = v2, so w ≠ v2
      left
      use w, hw_B
      constructor
      · intro hw_v2; subst hw_v2; subst hu_v2; exact huw rfl
      · exact edge_in_sym2_iff Br v2 w |>.mpr ⟨hv_Br, hw_Br⟩
    · -- u ≠ v2
      left
      use u, hu_B
      constructor
      · exact hu_v2
      · exact edge_in_sym2_iff Br v2 u |>.mpr ⟨hv_Br, hu_Br⟩

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8:

1. PATH_4 structure: A—B—C—D with spine vertices v1 = A∩B, v2 = B∩C, v3 = C∩D

2. Edge selection (2 per element, total 8):
   - A = {v1, a1, a2}: select {v1, a1}, {v1, a2}  (apex = v1)
   - B = {v1, v2, b}:  select {v2, v1}, {v2, b}   (apex = v2 = MIDDLE!)
   - C = {v2, v3, c}:  select {v2, v3}, {v2, c}   (apex = v2 = MIDDLE!)
   - D = {v3, d1, d2}: select {v3, d1}, {v3, d2}  (apex = v3)

3. Coverage by triangle_classification:

   CASE T ∈ M: T is one of A, B, C, D, covered by its own selected edges.

   CASE T is external to X:
   - T shares edge with X only
   - By externals_share_edge, all X-externals share same edge with X
   - Our 2 selected edges include this shared edge (apex-based selection)
   - So T is covered

   CASE T is bridge between X and Y (adjacent in PATH_4):
   - A-B bridge: contains v1, covered by A's or B's edges (both have v1-incident edges)
   - B-C bridge: contains v2 (by middle_seam_covered), covered by B's or C's edges
   - C-D bridge: contains v3, covered by C's or D's edges (both have v3-incident edges)

4. |E| ≤ 8 since each of 4 elements contributes 2 edges.
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    (h_tri : ∀ X ∈ M, X.card = 3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end