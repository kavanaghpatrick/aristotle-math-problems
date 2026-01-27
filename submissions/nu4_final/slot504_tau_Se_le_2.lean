/-
  slot504_tau_Se_le_2.lean

  BRIDGING FILE: From slot412's proven `not_all_three_edge_types` to τ(S_e) ≤ 2

  STATUS:
  - slot412 PROVES: `not_all_three_edge_types` (0 sorry, 12 theorems)
  - This file: Uses that to prove τ(S_e) ≤ 2

  PROOF SKETCH:
  By slot412, at most 2 of 3 edge-types of any M-element e = {a,b,c} have externals.
  WLOG, edges {a,b} and {b,c} can have externals, but {a,c} cannot.
  Cover = {s(a,b), s(b,c)} has 2 edges and covers all of S_e.
  Therefore τ(S_e) ≤ 2 for all packing elements.
  4 elements × 2 edges = 8 edges total → τ ≤ 8.

  TIER: 1-2 (case analysis + straightforward cover construction)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical
open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (same as slot412 for compatibility)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => t ≠ e ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def S_e_edge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (a b c : V) : Finset (Finset V) :=
  (S_e G M {a, b, c}).filter (fun T => a ∈ T ∧ b ∈ T ∧ c ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- IMPORT: not_all_three_edge_types from slot412 (PROVEN - 0 sorry)
-- ══════════════════════════════════════════════════════════════════════════════

/-- From slot412: At most 2 of 3 edge-types can have externals.

This is PROVEN in slot412_6packing_proof_aristotle.lean with 0 sorry.
Key insight: If all 3 edge-types had externals, we'd get a 6-packing, contradicting ν=4.
-/
axiom not_all_three_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ {a, b, c}) (hC_ne : C ≠ {a, b, c}) (hD_ne : D ≠ {a, b, c})
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hB_tri : B ∈ G.cliqueFinset 3) (hC_tri : C ∈ G.cliqueFinset 3) (hD_tri : D ∈ G.cliqueFinset 3) :
    ¬((S_e_edge G M a b c).Nonempty ∧
      (S_e_edge G M b c a).Nonempty ∧
      (S_e_edge G M a c b).Nonempty)

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Every element of S_e uses one of the 3 edges of e
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every T ∈ S_e shares ≥2 vertices with e, hence uses at least one edge of e -/
lemma S_e_uses_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (T : Finset V) (hT : T ∈ S_e G M {a, b, c}) :
    (a ∈ T ∧ b ∈ T) ∨ (b ∈ T ∧ c ∈ T) ∨ (a ∈ T ∧ c ∈ T) := by
  simp only [S_e, trianglesSharingEdge, mem_filter] at hT
  obtain ⟨⟨_, h_inter⟩, _, _⟩ := hT
  -- T ∩ {a,b,c} has ≥2 elements, so T contains ≥2 of {a,b,c}
  -- Case analysis on which pair
  have h_exists : ∃ x y : V, x ≠ y ∧ x ∈ T ∩ {a, b, c} ∧ y ∈ T ∩ {a, b, c} := by
    have h_nonempty : (T ∩ {a, b, c}).Nonempty := by rw [← card_pos]; omega
    obtain ⟨x, hx⟩ := h_nonempty
    have h_card' : ((T ∩ {a, b, c}).erase x).card ≥ 1 := by rw [card_erase_of_mem hx]; omega
    have h_nonempty' : ((T ∩ {a, b, c}).erase x).Nonempty := by rw [← card_pos]; omega
    obtain ⟨y, hy⟩ := h_nonempty'
    simp only [mem_erase] at hy
    exact ⟨x, y, hy.1.symm, hx, hy.2⟩
  obtain ⟨x, y, hxy, hx, hy⟩ := h_exists
  simp only [mem_inter, mem_insert, mem_singleton] at hx hy
  rcases hx.2 with rfl | rfl | rfl <;> rcases hy.2 with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hxy
    | left; exact ⟨hx.1, hy.1⟩
    | left; exact ⟨hy.1, hx.1⟩
    | right; left; exact ⟨hx.1, hy.1⟩
    | right; left; exact ⟨hy.1, hx.1⟩
    | right; right; exact ⟨hx.1, hy.1⟩
    | right; right; exact ⟨hy.1, hx.1⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA: τ(S_e) ≤ 2 when at most 2 edge-types have externals
-- ══════════════════════════════════════════════════════════════════════════════

/-- If at most 2 of 3 edges have externals, we can cover S_e with 2 edges from e -/
theorem tau_Se_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM4 : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hE_tri : {a, b, c} ∈ G.cliqueFinset 3) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ G.edgeFinset ∧
      ∀ T ∈ S_e G M {a, b, c}, ∃ e ∈ E', e ∈ T.sym2 := by
  /-
  PROOF SKETCH:
  By not_all_three_edge_types, at least one edge-type is empty.
  Case 1: {a,c}-edge type empty → use E' = {s(a,b), s(b,c)}
  Case 2: {b,c}-edge type empty → use E' = {s(a,b), s(a,c)}
  Case 3: {a,b}-edge type empty → use E' = {s(b,c), s(a,c)}

  In each case, any T ∈ S_e uses one of the 2 available edge-types,
  so T is covered by E'.
  -/
  sorry -- Aristotle: case analysis + cover construction

-- ══════════════════════════════════════════════════════════════════════════════
-- ASSEMBLING: τ ≤ 8 from τ(S_e) ≤ 2 for all packing elements
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle is in S_e ∪ {e} for some e ∈ M (by maximality) -/
lemma triangle_in_some_Se_or_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hM_max : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ e ∈ M, (T ∩ e).card ≥ 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨ ∃ e ∈ M, T ∈ S_e G M e := by
  by_cases hT_M : T ∈ M
  · left; exact hT_M
  · right
    obtain ⟨e, he, h_inter⟩ := hM_max T hT hT_M
    use e, he
    simp only [S_e, trianglesSharingEdge, mem_filter]
    have hT_ne_e : T ≠ e := by intro h; rw [h] at hT_M; exact hT_M he
    refine ⟨⟨hT, h_inter⟩, hT_ne_e, ?_⟩
    -- T is edge-disjoint from other M-elements (shares with only e)
    intro f hf hf_ne
    -- If T shared ≥2 with both e and f, then... need to pick the right one
    -- For simplicity, we assume T was assigned to its unique sharing element
    sorry -- Aristotle: T shares with exactly one M-element

/-- MAIN THEOREM: τ ≤ 8 when ν = 4 -/
theorem tau_le_8_from_Se_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM4 : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hM_max : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ e ∈ M, (T ∩ e).card ≥ 2)
    (hM_tri : ∀ e ∈ M, e ∈ G.cliqueFinset 3) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 8 ∧ E' ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ T.sym2 := by
  /-
  PROOF SKETCH:
  1. For each e ∈ M, by tau_Se_le_2, get E_e with |E_e| ≤ 2 covering S_e
  2. Let E' = ⋃_{e ∈ M} E_e
  3. |E'| ≤ 4 × 2 = 8
  4. For any triangle T:
     - By triangle_in_some_Se_or_M, T ∈ M or T ∈ S_e for some e
     - If T ∈ M, then T = e for some e, and E_e contains an edge of T
     - If T ∈ S_e, then E_e covers T
     - So E' covers T
  -/
  sorry -- Aristotle: construct union of S_e covers

-- ══════════════════════════════════════════════════════════════════════════════
-- SUMMARY
-- ══════════════════════════════════════════════════════════════════════════════

/-
FILE STATUS:

PROVEN (from slot412):
- not_all_three_edge_types: At most 2 of 3 edge-types have externals (0 sorry)

PROVEN (this file):
- S_e_uses_edge: Every T ∈ S_e uses at least one edge of e

REMAINING SORRIES (3):
1. tau_Se_le_2: Case analysis to construct 2-edge cover
2. triangle_in_some_Se_or_M: T shares with exactly one M-element (pigeonhole)
3. tau_le_8_from_Se_bound: Assembly of union of covers

NEXT STEPS:
- Submit to Aristotle for proof completion
- Once tau_Se_le_2 is proven, tau_le_8_from_Se_bound should follow
-/

end
