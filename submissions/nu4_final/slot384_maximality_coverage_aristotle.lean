/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f36dcc8c-1b8b-40f0-905d-2bd9aba3e9f9
-/

/-
Tuza ν=4 Strategy - Slot 384: Maximality Implies Coverage

DEBATE CONSENSUS (Grok):
  "This is purely a maximality argument. If T shares NO edge with ANY e ∈ M,
  then M ∪ {T} is a larger triangle packing. This contradicts ν(G) = 4 = |M|."

THEOREM:
  For a maximal packing M with |M| = ν(G) = 4:
  Every triangle T shares edge with some e ∈ M.

CONSEQUENCE:
  All triangles are in ∪_{e∈M} S_e (the union of edge-sharing sets).
  Combined with τ(S_e) ≤ 2, we get τ ≤ 4 × 2 = 8.

TIER: 2 (Maximality argument - structural, not computational)
-/

import Mathlib


set_option maxHeartbeats 800000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle packing: edge-disjoint triangles -/
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  ∀ e f : Finset V, e ∈ M → f ∈ M → e ≠ f → (e ∩ f).card ≤ 1

/-- Triangle packing number ν(G) -/
noncomputable def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup { n | ∃ M : Finset (Finset V), isTrianglePacking G M ∧ M.card = n }

/-- M is a maximal packing: no triangle can be added -/
def isMaximalPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ e ∈ M, (T ∩ e).card ≥ 2

/-- T shares edge with e: at least 2 common vertices -/
def sharesEdgeWith (T e : Finset V) : Prop := (T ∩ e).card ≥ 2

/-- S_e: triangles sharing edge with e -/
def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) : Finset (Finset V) :=
  G.cliqueFinset 3 |>.filter (fun T => (T ∩ e).card ≥ 2)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles share edge with themselves -/
lemma sharesEdgeWith_self (T : Finset V) (hT : T.card = 3) : sharesEdgeWith T T := by
  simp [sharesEdgeWith, inter_self]
  omega

/-- M-element is in S_M (trivially) -/
lemma M_element_in_own_S (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V)
    (hM : isTrianglePacking G M) (he : e ∈ M) :
    e ∈ trianglesSharingEdge G e := by
  simp [trianglesSharingEdge, mem_filter]
  constructor
  · exact hM.1 he
  · have h := G.mem_cliqueFinset_iff.mp (hM.1 he)
    simp [sharesEdgeWith_self, inter_self]
    exact le_of_eq h.2

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Maximality implies all triangles share edge with some M-element
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH (from Grok):
1. Let T be any triangle in G, T ∉ M
2. By maximality of M: T shares edge with some e ∈ M
3. Therefore T ∈ trianglesSharingEdge G e for some e ∈ M

For T ∈ M:
4. T shares edge with itself (trivially)
5. Therefore T ∈ trianglesSharingEdge G T

QED: all triangles are in ∪_{e∈M} trianglesSharingEdge G e
-/

/-- Every triangle shares edge with some M-element (maximality) -/
theorem triangle_shares_edge_with_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, sharesEdgeWith T e := by
  by_cases hTM : T ∈ M
  · -- T is in M, shares edge with itself
    exact ⟨T, hTM, sharesEdgeWith_self T (G.mem_cliqueFinset_iff.mp hT).2⟩
  · -- T not in M, use maximality
    obtain ⟨e, he, h_share⟩ := hM.2 T hT hTM
    exact ⟨e, he, h_share⟩

/-- All triangles are in union of S_e sets -/
theorem all_triangles_in_union_S (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M) :
    ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ M, T ∈ trianglesSharingEdge G e := by
  intro T hT
  obtain ⟨e, he, h_share⟩ := triangle_shares_edge_with_M G M hM T hT
  exact ⟨e, he, mem_filter.mpr ⟨hT, h_share⟩⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: Coverage by union of S_e
-- ══════════════════════════════════════════════════════════════════════════════

/-- For 4-element packing {A,B,C,D}, all triangles in S_A ∪ S_B ∪ S_C ∪ S_D -/
theorem triangles_covered_by_union_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (A B C D : Finset V) (hABCD : M = {A, B, C, D}) :
    G.cliqueFinset 3 ⊆
      trianglesSharingEdge G A ∪ trianglesSharingEdge G B ∪
      trianglesSharingEdge G C ∪ trianglesSharingEdge G D := by
  intro T hT
  obtain ⟨e, he, hTe⟩ := all_triangles_in_union_S G M hM T hT
  rw [hABCD] at he
  simp only [mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact mem_union_left _ (mem_union_left _ (mem_union_left _ hTe))
  · exact mem_union_left _ (mem_union_left _ (mem_union_right _ hTe))
  · exact mem_union_left _ (mem_union_right _ hTe)
  · exact mem_union_right _ hTe

-- ══════════════════════════════════════════════════════════════════════════════
-- OPTIMALITY PACKING (ν(G) = 4)
-- ══════════════════════════════════════════════════════════════════════════════

/-- If M achieves ν(G) = 4, then M is maximal -/
lemma optimal_packing_is_maximal (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM_pack : isTrianglePacking G M)
    (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4) :
    isMaximalPacking G M := by
  constructor
  · exact hM_pack
  · intro T hT hTM
    -- Suppose T shares no edge with any e ∈ M
    by_contra h_no_share
    push_neg at h_no_share
    -- Then M ∪ {T} would be a valid packing
    have h_new_pack : isTrianglePacking G (insert T M) := by
      constructor
      · intro x hx
        simp at hx
        rcases hx with rfl | hx
        · exact hT
        · exact hM_pack.1 hx
      · intro e f he hf hef
        simp at he hf
        rcases he with rfl | he <;> rcases hf with rfl | hf
        · exact absurd rfl hef
        · have := h_no_share f hf
          simp [sharesEdgeWith] at this
          exact Nat.lt_succ_iff.mp this
        · have := h_no_share e he
          simp [sharesEdgeWith, inter_comm] at this
          exact Nat.lt_succ_iff.mp this
        · exact hM_pack.2 e f he hf hef
    -- But |M ∪ {T}| = 5 > 4, contradicting ν = 4
    have h_card : (insert T M).card = 5 := by
      rw [card_insert_of_not_mem hTM, hM_card]
    have := hν (insert T M) h_new_pack
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN APPLICATION: τ ≤ 8 structure
-- ══════════════════════════════════════════════════════════════════════════════

/-- For ν = 4 packing, all triangles are in union of 4 S_e sets -/
theorem nu4_triangles_in_4_sets (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM_pack : isTrianglePacking G M)
    (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B C D : Finset V) (hABCD : M = {A, B, C, D}) :
    G.cliqueFinset 3 ⊆
      trianglesSharingEdge G A ∪ trianglesSharingEdge G B ∪
      trianglesSharingEdge G C ∪ trianglesSharingEdge G D := by
  have hM_max := optimal_packing_is_maximal G M hM_pack hM_card hν
  exact triangles_covered_by_union_4 G M hM_max A B C D hABCD

end