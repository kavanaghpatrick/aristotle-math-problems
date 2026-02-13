/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 45b096db-a4a0-4d8f-9f78-ff08f832bc26

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot552_base_edge_cant_bridge_adjacent.lean

  KEY STRUCTURAL LEMMA FOR PATH_4 BOTH-ENDPOINTS CASE:

  In PATH_4 (A —[v1]— B —[v2]— C —[v3]— D), a base-edge external
  of endpoint A (a triangle T using {a1,a2} without v1) CANNOT be a
  bridge to the adjacent element B. That is, |T ∩ B| ≤ 1.

  PROOF: A∩B = {v1}, so a1 ∉ B and a2 ∉ B. Since also v1 ∉ T,
  we get T ∩ B ⊆ {x} ∩ B for the third vertex x of T, giving |T∩B| ≤ 1.

  COROLLARIES:
  1. Base-edge externals are pure externals — never bridges to adjacent.
  2. Every bridge between adjacent elements A,B contains the shared vertex.
  3. Bridges between A and B have form {v1, a_i, b_j} (a_i ∈ A\B, b_j ∈ B\A).

  SORRY COUNT: 0
  AXIOM COUNT: 0
  TIER: 1 (elementary set theory)
-/

import Mathlib


set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════════
-- DEFINITIONS (matching slot548/551 conventions)
-- ═══════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  2 ≤ (t ∩ S).card

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y

def isBridgeOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X Y : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧ sharesEdgeWith t Y ∧ X ≠ Y

-- ═══════════════════════════════════════════════════════════════════════
-- HELPER: membership exclusion from singleton intersection
-- ═══════════════════════════════════════════════════════════════════════

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

/-- If A ∩ B = {v}, then any a ∈ A with a ≠ v satisfies a ∉ B. -/
lemma not_mem_of_inter_eq_singleton (A B : Finset V) (v a : V)
    (hAB : A ∩ B = {v}) (ha_A : a ∈ A) (ha_ne : a ≠ v) :
    a ∉ B := by
  intro ha_B
  have : a ∈ A ∩ B := mem_inter.mpr ⟨ha_A, ha_B⟩
  rw [hAB] at this
  exact ha_ne (mem_singleton.mp this)

/-- Singleton intersection implies card 1. -/
lemma inter_singleton_card (A B : Finset V) (v : V) (hAB : A ∩ B = {v}) :
    (A ∩ B).card = 1 := by
  rw [hAB, card_singleton]

/-- If two elements of T are not in B, then |T ∩ B| ≤ |T| - 2.
    Proof: T ∩ B ⊆ T \ {a1,a2}, and |T \ {a1,a2}| = |T| - 2. -/
lemma inter_card_le_of_two_not_mem (T B : Finset V) (a1 a2 : V)
    (ha1 : a1 ∈ T) (ha2 : a2 ∈ T) (h_ne : a1 ≠ a2)
    (ha1_notin : a1 ∉ B) (ha2_notin : a2 ∉ B) :
    (T ∩ B).card ≤ T.card - 2 := by
  -- T ∩ B ⊆ T \ {a1, a2}: any x ∈ T ∩ B has x ∈ B, but a1 ∉ B, a2 ∉ B
  have h_TB_sub : T ∩ B ⊆ T \ {a1, a2} := by
    intro x hx
    rw [mem_inter] at hx
    rw [mem_sdiff]
    refine ⟨hx.1, ?_⟩
    simp only [mem_insert, mem_singleton]
    push_neg
    exact ⟨fun h => ha1_notin (h ▸ hx.2), fun h => ha2_notin (h ▸ hx.2)⟩
  -- {a1, a2} ⊆ T
  have h_pair_sub : ({a1, a2} : Finset V) ⊆ T := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  -- |T \ {a1,a2}| = |T| - |{a1,a2}| = |T| - 2
  have h_pair_card : ({a1, a2} : Finset V).card = 2 := by
    rw [card_insert_of_not_mem (by simpa using h_ne), card_singleton]
  have h_sdiff_card := card_sdiff h_pair_sub
  -- Combine: |T ∩ B| ≤ |T \ {a1,a2}| = |T| - 2
  calc (T ∩ B).card ≤ (T \ {a1, a2}).card := card_le_card h_TB_sub
    _ = T.card - ({a1, a2} : Finset V).card := h_sdiff_card
    _ = T.card - 2 := by rw [h_pair_card]

-- ═══════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Base-edge external cannot bridge to adjacent element
-- ═══════════════════════════════════════════════════════════════════════

/-- MAIN LEMMA: If A = {v1, a1, a2} and A ∩ B = {v1}, and T is a
    triangle containing a1 and a2 but not v1 (a base-edge external),
    then T does not share an edge with B (|T ∩ B| ≤ 1).

    This proves base-edge externals are always pure externals of A,
    never bridges to the adjacent element B. -/
theorem base_edge_external_not_bridge_adjacent
    (A B T : Finset V) (v1 a1 a2 : V)
    (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (hAB_inter : A ∩ B = {v1})
    (hT_card : T.card = 3)
    (ha1_T : a1 ∈ T) (ha2_T : a2 ∈ T) (hv1_notin_T : v1 ∉ T) :
    ¬sharesEdgeWith T B := by
  unfold sharesEdgeWith
  push_neg
  -- a1 ∉ B and a2 ∉ B since A ∩ B = {v1}
  have ha1_A : a1 ∈ A := by rw [hA_eq]; simp
  have ha2_A : a2 ∈ A := by rw [hA_eq]; simp [h12, h13]
  have ha1_notin_B := not_mem_of_inter_eq_singleton A B v1 a1 hAB_inter ha1_A h12.symm
  have ha2_notin_B := not_mem_of_inter_eq_singleton A B v1 a2 hAB_inter ha2_A h13.symm
  -- |T ∩ B| ≤ |T| - 2 = 3 - 2 = 1
  have := inter_card_le_of_two_not_mem T B a1 a2 ha1_T ha2_T h23 ha1_notin_B ha2_notin_B
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- COROLLARY 1: Bridge between adjacent elements contains shared vertex
-- ═══════════════════════════════════════════════════════════════════════

/-- If T shares an edge with both A = {v1,a1,a2} and B, where A∩B = {v1},
    then v1 ∈ T.

    Contrapositive of: v1 ∉ T → |T∩B| ≤ 1 (from main theorem).
    If v1 ∉ T and |T∩A| ≥ 2 with A = {v1,a1,a2}, then T∩A ⊆ {a1,a2},
    so |T∩A| = 2 means {a1,a2} ⊆ T, and then |T∩B| ≤ 1. -/
theorem bridge_adjacent_contains_shared_vertex
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B T : Finset V) (v1 a1 a2 : V)
    (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (hAB_inter : A ∩ B = {v1})
    (hT_tri : T ∈ G.cliqueFinset 3)
    (hT_share_A : sharesEdgeWith T A)
    (hT_share_B : sharesEdgeWith T B) :
    v1 ∈ T := by
  by_contra hv1
  have hT_card := triangle_card_three G T hT_tri
  -- v1 ∉ T, so T ∩ A ⊆ {a1, a2}
  have hT_A_sub : T ∩ A ⊆ {a1, a2} := by
    intro x hx
    rw [mem_inter] at hx
    rw [hA_eq] at hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 hv1
    · exact mem_insert_self a1 {a2}
    · exact mem_insert_of_mem a1 (mem_singleton.mpr rfl)
  -- |T ∩ A| ≥ 2 and T ∩ A ⊆ {a1, a2} which has card 2
  have hpair_card : ({a1, a2} : Finset V).card = 2 := by
    rw [card_insert_of_not_mem (by simpa using h23), card_singleton]
  have hTA_card : (T ∩ A).card = 2 := by
    have h_ge : (T ∩ A).card ≥ 2 := hT_share_A
    have h_le := card_le_card hT_A_sub
    omega
  have hTA_eq : T ∩ A = {a1, a2} :=
    eq_of_subset_of_card_le hT_A_sub (by omega)
  -- So a1 ∈ T and a2 ∈ T
  have ha1_T : a1 ∈ T := by
    have : a1 ∈ T ∩ A := hTA_eq ▸ mem_insert_self a1 {a2}
    exact mem_of_mem_inter_left this
  have ha2_T : a2 ∈ T := by
    have : a2 ∈ T ∩ A := hTA_eq ▸ mem_insert_of_mem a1 (mem_singleton.mpr rfl)
    exact mem_of_mem_inter_left this
  -- Apply main theorem: ¬sharesEdgeWith T B
  exact base_edge_external_not_bridge_adjacent A B T v1 a1 a2
    hA_eq h12 h13 h23 hAB_inter hT_card ha1_T ha2_T hv1 hT_share_B

-- ═══════════════════════════════════════════════════════════════════════
-- COROLLARY 2: Bridge form characterization
-- ═══════════════════════════════════════════════════════════════════════

/-- A bridge between adjacent A = {v1,a1,a2} and B with A∩B = {v1}
    contains v1 plus one vertex from A\B and shares ≥2 vertices with B
    including v1. So the bridge has form {v1, a_i, y} where a_i ∈ {a1,a2}
    and y ∈ B \ A. -/
theorem bridge_adjacent_has_base_vertex
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B T : Finset V) (v1 a1 a2 : V)
    (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (hAB_inter : A ∩ B = {v1})
    (hT_tri : T ∈ G.cliqueFinset 3)
    (hT_share_A : sharesEdgeWith T A)
    (hT_share_B : sharesEdgeWith T B) :
    v1 ∈ T ∧ (a1 ∈ T ∨ a2 ∈ T) := by
  have hv1_T := bridge_adjacent_contains_shared_vertex G A B T v1 a1 a2
    hA_eq h12 h13 h23 hAB_inter hT_tri hT_share_A hT_share_B
  refine ⟨hv1_T, ?_⟩
  -- |T ∩ A| ≥ 2 and v1 ∈ T, so at least one of a1, a2 is in T
  have hT_card := triangle_card_three G T hT_tri
  have h_ge : (T ∩ A).card ≥ 2 := hT_share_A
  by_contra h; push_neg at h
  obtain ⟨ha1, ha2⟩ := h
  -- T ∩ A ⊆ {v1}
  have : T ∩ A ⊆ {v1} := by
    intro x hx
    rw [mem_inter] at hx
    rw [hA_eq] at hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx.2 with rfl | rfl | rfl
    · exact mem_singleton.mpr rfl
    · exact absurd hx.1 ha1
    · exact absurd hx.1 ha2
  have : (T ∩ A).card ≤ 1 := le_trans (card_le_card this) (card_singleton v1).le
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- COROLLARY 3: Spoke edge from v1 covers the bridge
-- ═══════════════════════════════════════════════════════════════════════

lemma edge_in_sym2 (T : Finset V) (a b : V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 := by
  rw [Finset.mk_mem_sym2_iff]; exact ⟨ha, hb⟩

/-- Every bridge between adjacent A and B is hit by a spoke edge from v1.
    Specifically: v1 ∈ T and (a1 ∈ T ∨ a2 ∈ T), so s(v1,a1) or s(v1,a2)
    is in T.sym2. -/
theorem bridge_hit_by_spoke
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B T : Finset V) (v1 a1 a2 : V)
    (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (hAB_inter : A ∩ B = {v1})
    (hT_tri : T ∈ G.cliqueFinset 3)
    (hT_share_A : sharesEdgeWith T A)
    (hT_share_B : sharesEdgeWith T B) :
    s(v1, a1) ∈ T.sym2 ∨ s(v1, a2) ∈ T.sym2 := by
  obtain ⟨hv1, ha⟩ := bridge_adjacent_has_base_vertex G A B T v1 a1 a2
    hA_eq h12 h13 h23 hAB_inter hT_tri hT_share_A hT_share_B
  rcases ha with ha1 | ha2
  · left; exact edge_in_sym2 T v1 a1 hv1 ha1
  · right; exact edge_in_sym2 T v1 a2 hv1 ha2

-- ═══════════════════════════════════════════════════════════════════════
-- APPLICATION: Combined coverage for both-endpoints case
--
-- When apex_A ≠ v1 (i.e., A has base-edge externals and apex = a1 or a2),
-- A's 2-edge cover is {apex_A, v1} and {apex_A, other_base}.
-- Bridges to B contain v1 and one of {a1,a2}, so they are hit by
-- {apex_A, v1} if apex_A ∈ {a1,a2} (which it is by hypothesis).
-- Wait — not necessarily. If apex = a1, cover = {a1,v1}, {a1,a2}.
-- Bridge {v1, a2, b_j}: Does {a1,v1} hit it? Only if a1 ∈ T, but
-- a1 may not be in this particular bridge. The bridge has a2.
-- So {a1,a2} must hit it — but {a1,a2} hits T iff a1 ∈ T ∧ a2 ∈ T.
-- Since the bridge is {v1,a2,b_j}, a1 ∉ T. So neither cover edge hits.
--
-- HOWEVER: B's cover can catch it. B's cover includes some spoke from B.
-- This is the slot551 approach. The key new fact from THIS file is:
-- bridges always go through v1, which constrains them to specific forms,
-- enabling coordinated cover selection.
-- ═══════════════════════════════════════════════════════════════════════

/-- If A's apex is a1 (cover = {a1,v1}, {a1,a2}), then bridges {v1,a1,b_j}
    ARE covered by {a1,v1}. Only bridges {v1,a2,b_j} are potentially missed
    by A's cover. But these satisfy v1 ∈ T and b_j ∈ T ∩ B, so B's spoke
    edge {v1,b_j} covers them if v1 is B's apex. -/
theorem bridge_a1_covered_by_a1_spoke
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B T : Finset V) (v1 a1 a2 : V)
    (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (hAB_inter : A ∩ B = {v1})
    (hT_tri : T ∈ G.cliqueFinset 3)
    (hT_share_A : sharesEdgeWith T A)
    (hT_share_B : sharesEdgeWith T B)
    (ha1_T : a1 ∈ T) : -- bridge goes through a1
    s(a1, v1) ∈ T.sym2 := by
  have hv1_T := bridge_adjacent_contains_shared_vertex G A B T v1 a1 a2
    hA_eq h12 h13 h23 hAB_inter hT_tri hT_share_A hT_share_B
  exact edge_in_sym2 T a1 v1 ha1_T hv1_T

-- ═══════════════════════════════════════════════════════════════════════
-- SYMMETRIC VERSION: Same result for endpoint D
-- ═══════════════════════════════════════════════════════════════════════

/-- Same lemma for the other endpoint D = {v3,d1,d2} with D∩C = {v3}. -/
theorem base_edge_external_not_bridge_adjacent_D
    (C D T : Finset V) (v3 d1 d2 : V)
    (hD_eq : D = {v3, d1, d2})
    (h12 : v3 ≠ d1) (h13 : v3 ≠ d2) (h23 : d1 ≠ d2)
    (hDC_inter : D ∩ C = {v3})
    (hT_card : T.card = 3)
    (hd1_T : d1 ∈ T) (hd2_T : d2 ∈ T) (hv3_notin_T : v3 ∉ T) :
    ¬sharesEdgeWith T C :=
  base_edge_external_not_bridge_adjacent D C T v3 d1 d2
    hD_eq h12 h13 h23 hDC_inter hT_card hd1_T hd2_T hv3_notin_T

end