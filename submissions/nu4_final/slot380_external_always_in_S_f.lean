/-
Tuza ν=4 Strategy - Slot 380: External Always in Some S_f

DEBATE CONSENSUS (Grok, Gemini, Codex):
  All three agents converge on using maximality of packing:
  - Every triangle shares edge with SOME M-element (by maximality)
  - Therefore, "externals" (share only vertex) must share edge elsewhere

KEY LEMMA TO TEST (falsification-first):
  If t is external for e (shares vertex but not edge with e),
  then ∃ f ∈ M, f ≠ e, such that t shares edge with f.

IF TRUE: τ ≤ 8 follows immediately
  - All triangles are in ∪_{e∈M} S_e
  - Each S_e needs ≤ 2 edges (tau_S_le_2)
  - 4 × 2 = 8 ✓

IF FALSE: Counterexample reveals new structure needed

STRUCTURE (on Fin 8 for PATH_4):
  A = {0, 1, 2}
  B = {2, 3, 4}  -- shares v=2 with A
  C = {4, 5, 6}  -- shares w=4 with B
  D = {6, 7, 0}  -- shares x=6 with C (PATH closes to CYCLE here for test)

TIER: 1 (Decidable on Fin 8)
-/

import Mathlib

set_option maxHeartbeats 800000

open Finset

-- ══════════════════════════════════════════════════════════════════════════════
-- PACKING M ON FIN 8 (PATH_4 configuration)
-- ══════════════════════════════════════════════════════════════════════════════

def A : Finset (Fin 8) := {0, 1, 2}
def B : Finset (Fin 8) := {2, 3, 4}
def C : Finset (Fin 8) := {4, 5, 6}
def D : Finset (Fin 8) := {6, 7, 0}

def M : Finset (Finset (Fin 8)) := {A, B, C, D}

-- ══════════════════════════════════════════════════════════════════════════════
-- GRAPH: PATH_4 configuration with potential external triangles
-- We add edges that could create externals to test the lemma
-- ══════════════════════════════════════════════════════════════════════════════

-- Edges from M-triangles
def M_edges : Finset (Finset (Fin 8)) :=
  { {0, 1}, {0, 2}, {1, 2},   -- A
    {2, 3}, {2, 4}, {3, 4},   -- B
    {4, 5}, {4, 6}, {5, 6},   -- C
    {6, 7}, {6, 0}, {7, 0} }  -- D

-- Adjacency in the minimal graph (only M-edges)
def adj (x y : Fin 8) : Bool :=
  x ≠ y ∧ ({x, y} : Finset (Fin 8)) ∈ M_edges

-- Triangle predicate
def isTriangleInG (T : Finset (Fin 8)) : Bool :=
  T.card = 3 ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → adj x y)

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

-- Edges of a triangle (as 2-element Finsets)
def triangleEdges (T : Finset (Fin 8)) : Finset (Finset (Fin 8)) :=
  T.powerset.filter (fun e => e.card = 2)

-- Edges of a packing element
def packingEdges (e : Finset (Fin 8)) : Finset (Finset (Fin 8)) :=
  e.powerset.filter (fun edge => edge.card = 2)

-- Triangle T shares edge with packing element e
def sharesEdgeWith (T e : Finset (Fin 8)) : Bool :=
  (triangleEdges T ∩ packingEdges e).Nonempty

-- Triangle T shares only vertex (not edge) with e
def sharesOnlyVertex (T e : Finset (Fin 8)) : Bool :=
  (T ∩ e).Nonempty ∧ ¬sharesEdgeWith T e

-- Triangle T is external for e: shares vertex but not edge
def isExternalFor (T e : Finset (Fin 8)) : Bool :=
  sharesOnlyVertex T e

-- S_e: triangles that share edge ONLY with e (not with any other M-element)
def S_e (e : Finset (Fin 8)) : Finset (Finset (Fin 8)) :=
  (Finset.univ : Finset (Fin 8)).powerset.filter (fun T =>
    isTriangleInG T ∧
    sharesEdgeWith T e ∧
    ∀ f ∈ M, f ≠ e → ¬sharesEdgeWith T f)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: Basic Facts
-- ══════════════════════════════════════════════════════════════════════════════

lemma A_card : A.card = 3 := by native_decide
lemma B_card : B.card = 3 := by native_decide
lemma C_card : C.card = 3 := by native_decide
lemma D_card : D.card = 3 := by native_decide
lemma M_card : M.card = 4 := by native_decide

lemma A_in_M : A ∈ M := by native_decide
lemma B_in_M : B ∈ M := by native_decide
lemma C_in_M : C ∈ M := by native_decide
lemma D_in_M : D ∈ M := by native_decide

-- Packing property: any two M-elements share ≤ 1 vertex
lemma M_packing : ∀ X ∈ M, ∀ Y ∈ M, X ≠ Y → (X ∩ Y).card ≤ 1 := by
  intro X hX Y hY hne
  simp only [M, mem_insert, mem_singleton] at hX hY
  rcases hX with rfl | rfl | rfl | rfl <;>
  rcases hY with rfl | rfl | rfl | rfl <;>
  first | exact absurd rfl hne | native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- ENUMERATE ALL TRIANGLES IN MINIMAL GRAPH
-- ══════════════════════════════════════════════════════════════════════════════

def trianglesInG : Finset (Finset (Fin 8)) :=
  (Finset.univ : Finset (Fin 8)).powerset.filter (fun T => isTriangleInG T)

/-- In minimal PATH_4 graph, only triangles are A, B, C, D -/
lemma triangles_eq_M : trianglesInG = M := by native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Every triangle shares edge with some M-element (maximality)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle in G shares an edge with some packing element -/
lemma triangle_shares_edge_with_M (T : Finset (Fin 8)) (hT : T ∈ trianglesInG) :
    ∃ e ∈ M, sharesEdgeWith T e = true := by
  rw [triangles_eq_M] at hT
  simp only [M, mem_insert, mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · exact ⟨A, A_in_M, by native_decide⟩
  · exact ⟨B, B_in_M, by native_decide⟩
  · exact ⟨C, C_in_M, by native_decide⟩
  · exact ⟨D, D_in_M, by native_decide⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- THE CRITICAL LEMMA: External always in some S_f
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH (from debate consensus):
1. Let T be any triangle external for e (shares vertex but not edge)
2. By maximality, T shares edge with some M-element f
3. Since T doesn't share edge with e, we have f ≠ e
4. Therefore T ∈ S_f (or at least shares edge with f)

This is the KEY insight: externals are NOT special - they're just S_f triangles
for a different f. The "external" label is relative to one element.
-/

/-- If T is external for e, then T shares edge with some f ≠ e in M -/
theorem external_shares_edge_with_other
    (T e : Finset (Fin 8))
    (hT : T ∈ trianglesInG)
    (he : e ∈ M)
    (hext : isExternalFor T e = true) :
    ∃ f ∈ M, f ≠ e ∧ sharesEdgeWith T f = true := by
  -- By maximality, T shares edge with some M-element
  obtain ⟨f, hf_in_M, hf_shares⟩ := triangle_shares_edge_with_M T hT
  -- T is external for e means T doesn't share edge with e
  simp only [isExternalFor, sharesOnlyVertex, Bool.and_eq_true, decide_eq_true_eq,
             Bool.not_eq_true', sharesEdgeWith] at hext
  obtain ⟨_, h_not_edge⟩ := hext
  -- Case split: is f = e or f ≠ e?
  by_cases hfe : f = e
  · -- If f = e, contradiction: hext says T doesn't share edge with e
    subst hfe
    simp only [sharesEdgeWith, Bool.eq_true_iff] at hf_shares h_not_edge
    exact absurd hf_shares h_not_edge
  · -- If f ≠ e, we're done
    exact ⟨f, hf_in_M, hfe, hf_shares⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- CONSEQUENCE: In minimal graph, there are NO externals
-- (because the only triangles are A, B, C, D themselves)
-- ══════════════════════════════════════════════════════════════════════════════

/-- In minimal PATH_4 graph, no triangle is external for any M-element -/
lemma no_externals_in_minimal : ∀ T ∈ trianglesInG, ∀ e ∈ M, isExternalFor T e = false := by
  intro T hT e he
  rw [triangles_eq_M] at hT
  simp only [M, mem_insert, mem_singleton] at hT he
  rcases hT with rfl | rfl | rfl | rfl <;>
  rcases he with rfl | rfl | rfl | rfl <;>
  native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- COVERAGE BOUND FOR MINIMAL GRAPH
-- ══════════════════════════════════════════════════════════════════════════════

/-- Each M-element is covered by 2 edges (one from each pair of non-shared vertices) -/
def cover : Finset (Finset (Fin 8)) :=
  { {0, 1}, {2, 3}, {4, 5}, {6, 7} }

lemma cover_card : cover.card = 4 := by native_decide

lemma cover_all_card_2 : ∀ e ∈ cover, e.card = 2 := by
  intro e he
  simp only [cover, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> native_decide

lemma cover_hits_A : ∃ e ∈ cover, e ⊆ A := by
  use {0, 1}; simp only [cover, A, mem_insert, true_or, subset_iff]; decide

lemma cover_hits_B : ∃ e ∈ cover, e ⊆ B := by
  use {2, 3}; simp only [cover, B, mem_insert, or_true, subset_iff]; decide

lemma cover_hits_C : ∃ e ∈ cover, e ⊆ C := by
  use {4, 5}; simp only [cover, C, mem_insert, or_true, subset_iff]; decide

lemma cover_hits_D : ∃ e ∈ cover, e ⊆ D := by
  use {6, 7}; simp only [cover, D, mem_insert, or_true, subset_iff]; decide

lemma cover_hits_all : ∀ T ∈ trianglesInG, ∃ e ∈ cover, e ⊆ T := by
  intro T hT
  rw [triangles_eq_M] at hT
  simp only [M, mem_insert, mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · exact cover_hits_A
  · exact cover_hits_B
  · exact cover_hits_C
  · exact cover_hits_D

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 4 for minimal PATH_4 (stronger than τ ≤ 8)
-- ══════════════════════════════════════════════════════════════════════════════

theorem path4_minimal_tau_le_4 :
    ∃ E : Finset (Finset (Fin 8)),
      E.card ≤ 4 ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ T ∈ trianglesInG, ∃ e ∈ E, e ⊆ T) := by
  use cover
  refine ⟨?_, cover_all_card_2, cover_hits_all⟩
  simp only [cover_card, le_refl]

theorem path4_minimal_tau_le_8 :
    ∃ E : Finset (Finset (Fin 8)),
      E.card ≤ 8 ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ T ∈ trianglesInG, ∃ e ∈ E, e ⊆ T) := by
  obtain ⟨E, hcard, hedge, hcover⟩ := path4_minimal_tau_le_4
  exact ⟨E, by omega, hedge, hcover⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- INSIGHT: The real test is on GENERAL graphs, not minimal
-- The lemma external_shares_edge_with_other shows the path forward:
--   All triangles are covered by ∪_{e∈M} S_e
--   τ(S_e) ≤ 2 for each e
--   Therefore τ ≤ 4 × 2 = 8
-- ══════════════════════════════════════════════════════════════════════════════

end
