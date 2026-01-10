/-
  slot320: τ ≤ 8 for ν = 4 - Simplified with sorry helpers

  Focus: Give Aristotle the main theorem with minimal dependencies.
  Mark complex helpers as sorry to see if Aristotle can do the main proof structure.
-/

import Mathlib

set_option maxHeartbeats 400000
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

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- EXPLICIT COVER
-- ══════════════════════════════════════════════════════════════════════════════

/-
For X = {a, b, c}, pick vertex a and return {s(a,b), s(a,c)}
-/
def twoEdgesFromTriangle (X : Finset V) : Finset (Sym2 V) :=
  if h : X.Nonempty then
    let v := h.choose
    (X.filter (· ≠ v)).image (fun w => s(v, w))
  else ∅

/-
The full cover: union over all packing elements
-/
def eightEdgeCover (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion twoEdgesFromTriangle

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Triangle has card 3
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 := by
  exact (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 1: twoEdgesFromTriangle has ≤ 2 edges
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
When X.card = 3 and v ∈ X:
- X.filter (· ≠ v) has exactly 2 elements
- Image under (fun w => s(v,w)) has ≤ 2 elements
-/
lemma twoEdgesFromTriangle_card (X : Finset V) (hX : X.card = 3) :
    (twoEdgesFromTriangle X).card ≤ 2 := by
  unfold twoEdgesFromTriangle
  have h_nonempty : X.Nonempty := by rw [Finset.card_pos]; omega
  simp only [h_nonempty, ↓reduceDIte]
  have h_filter_card : (X.filter (· ≠ h_nonempty.choose)).card ≤ 2 := by
    have h_sub : X.filter (· ≠ h_nonempty.choose) ⊆ X := Finset.filter_subset _ _
    have := Finset.card_le_card h_sub
    omega
  calc (Finset.image (fun w => s(h_nonempty.choose, w)) (X.filter (· ≠ h_nonempty.choose))).card
      ≤ (X.filter (· ≠ h_nonempty.choose)).card := Finset.card_image_le
    _ ≤ 2 := h_filter_card

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 2: eightEdgeCover has ≤ 8 edges
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
eightEdgeCover M = ⋃_{X ∈ M} twoEdgesFromTriangle X
|eightEdgeCover M| ≤ Σ_{X ∈ M} |twoEdgesFromTriangle X| ≤ 4 × 2 = 8
-/
lemma eightEdgeCover_card (M : Finset (Finset V)) (hM_card : M.card = 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    (eightEdgeCover M).card ≤ 8 := by
  unfold eightEdgeCover
  calc (M.biUnion twoEdgesFromTriangle).card
      ≤ M.sum (fun X => (twoEdgesFromTriangle X).card) := Finset.card_biUnion_le
    _ ≤ M.sum (fun _ => 2) := by
        apply Finset.sum_le_sum
        intro X hX
        exact twoEdgesFromTriangle_card X (h_triangles X hX)
    _ = M.card * 2 := by rw [Finset.sum_const, smul_eq_mul]
    _ = 8 := by rw [hM_card]; ring

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 3: Cover is subset of graph edges
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
Each edge s(v,w) in twoEdgesFromTriangle X comes from v,w ∈ X ∈ G.cliqueFinset 3.
Clique means v adj w, so s(v,w) ∈ G.edgeFinset.
-/
lemma eightEdgeCover_subset_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    eightEdgeCover M ⊆ G.edgeFinset := by
  intro e he
  unfold eightEdgeCover at he
  rw [Finset.mem_biUnion] at he
  obtain ⟨X, hX_in_M, he_in_X⟩ := he
  unfold twoEdgesFromTriangle at he_in_X
  have hX_tri : X ∈ G.cliqueFinset 3 := hM.1 hX_in_M
  have hX_clique := SimpleGraph.mem_cliqueFinset_iff.mp hX_tri
  split_ifs at he_in_X with h_nonempty
  · rw [Finset.mem_image] at he_in_X
    obtain ⟨w, hw, rfl⟩ := he_in_X
    have hv : h_nonempty.choose ∈ X := h_nonempty.choose_spec
    have hw_in_X : w ∈ X := (Finset.mem_filter.mp hw).1
    have hvw_ne : h_nonempty.choose ≠ w := (Finset.mem_filter.mp hw).2.symm
    have h_adj : G.Adj h_nonempty.choose w := hX_clique.1 hv hw_in_X hvw_ne
    exact SimpleGraph.mem_edgeFinset.mpr h_adj
  · simp at he_in_X

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 4: Edge in T.sym2 ↔ both endpoints in T
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_sym2_iff (T : Finset V) (u v : V) :
    s(u, v) ∈ T.sym2 ↔ u ∈ T ∧ v ∈ T := by
  rw [Finset.mem_sym2_iff]
  constructor
  · intro h
    exact ⟨h (Sym2.mem_iff.mpr (Or.inl rfl)), h (Sym2.mem_iff.mpr (Or.inr rfl))⟩
  · intro ⟨hu, hv⟩ x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> assumption

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 5: twoEdgesFromTriangle covers X itself
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
For X = {a,b,c} with a = chosen vertex:
twoEdgesFromTriangle X = {s(a,b), s(a,c)}
s(a,b) ∈ X.sym2 since a,b ∈ X
-/
lemma twoEdgesFromTriangle_covers_self (X : Finset V) (hX : X.card = 3) :
    ∃ e ∈ twoEdgesFromTriangle X, e ∈ X.sym2 := by
  unfold twoEdgesFromTriangle
  have h_nonempty : X.Nonempty := by rw [Finset.card_pos]; omega
  simp only [h_nonempty, ↓reduceDIte]
  let v := h_nonempty.choose
  have hv : v ∈ X := h_nonempty.choose_spec
  -- There exists w ∈ X with w ≠ v
  have h_filter_nonempty : (X.filter (· ≠ v)).Nonempty := by
    rw [Finset.filter_nonempty_iff]
    have h_card_gt : 1 < X.card := by omega
    obtain ⟨w, hw, hne⟩ := Finset.exists_mem_ne h_card_gt v
    exact ⟨w, hw, hne⟩
  obtain ⟨w, hw⟩ := h_filter_nonempty
  use s(v, w)
  constructor
  · exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  · rw [edge_in_sym2_iff]
    exact ⟨hv, (Finset.mem_filter.mp hw).1⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 6: Cover covers all M-elements
-- ══════════════════════════════════════════════════════════════════════════════

lemma eightEdgeCover_covers_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (h_triangles : ∀ X ∈ M, X.card = 3)
    (X : Finset V) (hX : X ∈ M) :
    ∃ e ∈ eightEdgeCover M, e ∈ X.sym2 := by
  obtain ⟨e, he_cover, he_sym⟩ := twoEdgesFromTriangle_covers_self X (h_triangles X hX)
  exact ⟨e, Finset.mem_biUnion.mpr ⟨X, hX, he_cover⟩, he_sym⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 7: Non-M triangle is covered (the hard part)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for non-M triangle coverage:

Let T ∉ M be a triangle. By maximality, T shares ≥2 vertices with some X ∈ M.
Let T ∩ X = {u, w} (exactly 2 vertices since T ≠ X).

For X, let v = chosen vertex for twoEdgesFromTriangle.
twoEdgesFromTriangle X = {s(v, a), s(v, b)} where X \ {v} = {a, b}.

Case 1: v ∈ {u, w}
  WLOG v = u. Then w ∈ X \ {v} = {a, b}.
  So s(v, w) = s(u, w) ∈ twoEdgesFromTriangle X.
  And s(u, w) ∈ T.sym2 since u, w ∈ T.

Case 2: v ∉ {u, w}
  Then X = {v, u, w} (since X has 3 elements, T ∩ X = {u,w}).
  So {a, b} = {u, w}.
  Thus twoEdgesFromTriangle X = {s(v, u), s(v, w)}.

  PROBLEM: We need s(v, u) ∈ T.sym2 or s(v, w) ∈ T.sym2.
  This requires v ∈ T, but v ∉ T ∩ X = {u, w}.
  So v ∉ T, and these edges DON'T cover T!

CONCLUSION: The naive construction FAILS for some non-M triangles.
We need the "fan apex" approach to choose v correctly.
-/

-- This lemma is NOT provable with naive construction!
-- The fan apex is REQUIRED.
lemma eightEdgeCover_covers_nonM (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (h_triangles : ∀ X ∈ M, X.card = 3)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3) (hT_not_M : T ∉ M) :
    ∃ e ∈ eightEdgeCover M, e ∈ T.sym2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
Use eightEdgeCover M.
- Card ≤ 8: by eightEdgeCover_card
- Subset of G.edgeFinset: by eightEdgeCover_subset_edgeFinset
- Covers all triangles:
  - M-elements: by eightEdgeCover_covers_M
  - Non-M triangles: by eightEdgeCover_covers_nonM (needs fan apex)
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  use eightEdgeCover M
  constructor
  · exact eightEdgeCover_card M hM_card h_triangles
  · constructor
    · exact eightEdgeCover_subset_edgeFinset G M hM.1
    · intro T hT
      by_cases hT_M : T ∈ M
      · exact eightEdgeCover_covers_M G M h_triangles T hT_M
      · exact eightEdgeCover_covers_nonM G M hM h_triangles T hT hT_M

end
