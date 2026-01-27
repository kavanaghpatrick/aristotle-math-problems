/-
  slot520_bridge_bound.lean

  CRITICAL LEMMA: At most 2 bridges assigned to each M-element

  PROVEN building blocks (from slot506, slot512):
  - tau_le_8_from_Se'_partition: τ ≤ 8 IF bridge bound holds
  - constrained_selection_exists: 2 edges cover S_e' IF bridge bound holds
  - two_edges_cover_Se: 2 edges cover S_e (exclusive externals)

  WHAT WE NEED TO PROVE:
  ∀ e ∈ M, (S_e' G M e idx \ S_e G M e).card ≤ 2

  PROOF STRATEGY (6-packing argument):
  1. Bridge T in S_e' \ S_e shares edge with e AND some f (idx(f) > idx(e))
  2. If e has ≥3 bridges using all 3 edge-types of e:
     - These bridges are pairwise edge-disjoint (proven lemma)
     - Together with e, that's 4 edge-disjoint triangles
     - Plus f (some other M-element) → 5 triangles
     - But bridges share with f... need careful counting
  3. Alternative: bound via "each bridge pair (e,f) has ≤1 bridge"

  TIER: 2 (6-packing + counting)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧ ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

def sharesEdgeWith (M : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  M.filter (fun e => 2 ≤ (T ∩ e).card)

def S_e' (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V)
    (idx : Finset V → ℕ) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧
    (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅)

/-- Bridges assigned to e: triangles in S_e' but not S_e -/
def bridgesOf (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) 
    (e : Finset V) (idx : Finset V → ℕ) : Finset (Finset V) :=
  S_e' G M e idx \ S_e G M e

-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA 1: Bridge shares with at least 2 M-elements
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridge_shares_multiple (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (idx : Finset V → ℕ)
    (T : Finset V) (hT : T ∈ bridgesOf G M e idx) :
    2 ≤ (sharesEdgeWith M T).card := by
  simp only [bridgesOf, S_e', S_e, mem_sdiff, mem_filter] at hT
  -- T is in S_e' but not S_e
  -- Not in S_e means: ∃ f ∈ M, f ≠ e ∧ 2 ≤ (T ∩ f).card
  push_neg at hT
  obtain ⟨⟨_, hTe_inter, _⟩, hT_notSe⟩ := hT
  -- T shares edge with e
  have he_shares : e ∈ sharesEdgeWith M T := by
    sorry -- need e ∈ M
  -- T shares edge with some f ≠ e
  obtain ⟨f, hfM, hfe, hf_inter⟩ := hT_notSe (by sorry) hTe_inter
  have hf_shares : f ∈ sharesEdgeWith M T := by
    simp only [sharesEdgeWith, mem_filter]
    exact ⟨hfM, hf_inter⟩
  -- e ≠ f and both in sharesEdgeWith
  have hef : e ≠ f := hfe.symm
  rw [two_le_card]
  exact ⟨e, he_shares, f, hf_shares, hef⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA 2: Bridges using different edge-types are edge-disjoint
-- ══════════════════════════════════════════════════════════════════════════════

/-- Edge-type: which 2 vertices of e = {a,b,c} does T use? -/
def edgeType (T e : Finset V) : Finset V := T ∩ e

lemma bridges_different_types_disjoint (T₁ T₂ e : Finset V)
    (he3 : e.card = 3)
    (hT1_inter : (T₁ ∩ e).card = 2) (hT2_inter : (T₂ ∩ e).card = 2)
    (hT1_card : T₁.card = 3) (hT2_card : T₂.card = 3)
    (h_diff_type : edgeType T₁ e ≠ edgeType T₂ e) :
    (T₁ ∩ T₂).card ≤ 1 := by
  -- T₁ ∩ e and T₂ ∩ e are different 2-element subsets of e
  -- e has 3 vertices, so different 2-subsets share exactly 1 vertex
  -- T₁ and T₂ each have a third vertex outside e
  -- So T₁ ∩ T₂ ⊆ (T₁ ∩ e) ∩ (T₂ ∩ e), which has ≤1 element
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA 3: Three bridges with 3 types → 6-packing contradiction
-- ══════════════════════════════════════════════════════════════════════════════

lemma three_bridges_six_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hM4 : M.card = 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3)
    (T₁ T₂ T₃ : Finset V)
    (hT1 : T₁ ∈ G.cliqueFinset 3) (hT2 : T₂ ∈ G.cliqueFinset 3) (hT3 : T₃ ∈ G.cliqueFinset 3)
    (h1e : 2 ≤ (T₁ ∩ e).card) (h2e : 2 ≤ (T₂ ∩ e).card) (h3e : 2 ≤ (T₃ ∩ e).card)
    (h_distinct_types : edgeType T₁ e ≠ edgeType T₂ e ∧ 
                        edgeType T₂ e ≠ edgeType T₃ e ∧ 
                        edgeType T₁ e ≠ edgeType T₃ e)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4) :
    False := by
  -- T₁, T₂, T₃ are pairwise edge-disjoint (different types)
  -- {e, T₁, T₂, T₃} would be 4 pairwise edge-disjoint triangles
  -- But T₁, T₂, T₃ ∉ M (they're bridges), so with any f ∈ M \ {e},
  -- we'd have 5 edge-disjoint triangles... unless T_i shares with f
  -- Actually: {T₁, T₂, T₃} ∪ (M \ {e}) could give 6 triangles
  -- But some T_i share edges with elements of M
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: At most 2 bridges per M-element
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Suppose e has ≥3 bridges T₁, T₂, T₃
2. Each T_i uses some edge-type of e (2-element intersection)
3. e has only 3 edge-types, so by pigeonhole, either:
   a) Two bridges use same type → combine analysis
   b) All 3 types used → 6-packing contradiction (three_bridges_six_packing)
4. Case (b) is impossible, so at most 2 distinct edge-types populated
5. Each edge-type can have at most 1 bridge (or similar argument)
6. Therefore ≤2 bridges total
-/
theorem bridge_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (hM4 : M.card = 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3)
    (idx : Finset V → ℕ) :
    (bridgesOf G M e idx).card ≤ 2 := by
  by_contra h
  push_neg at h
  -- e has ≥3 bridges
  rw [Nat.succ_le_iff, Finset.two_lt_card] at h
  obtain ⟨T₁, hT1, T₂, hT2, T₃, hT3, h12, h13, h23⟩ := h
  -- Each T_i is a bridge using some edge-type of e
  have hT1_tri : T₁ ∈ G.cliqueFinset 3 := by
    simp only [bridgesOf, S_e', mem_sdiff, mem_filter] at hT1
    exact hT1.1.1
  have hT2_tri : T₂ ∈ G.cliqueFinset 3 := by
    simp only [bridgesOf, S_e', mem_sdiff, mem_filter] at hT2
    exact hT2.1.1
  have hT3_tri : T₃ ∈ G.cliqueFinset 3 := by
    simp only [bridgesOf, S_e', mem_sdiff, mem_filter] at hT3
    exact hT3.1.1
  -- 3 edge-types, 3 bridges → some pair uses same type OR all different
  -- If all different → 6-packing contradiction
  sorry

end
