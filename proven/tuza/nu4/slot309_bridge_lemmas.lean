/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ba39e952-3f21-4f5a-9a16-46f1fc5abf2c
-/

/-
  slot309: τ ≤ 8 for ν = 4 - WITH BRIDGE TRIANGLE HANDLING

  PROVEN FOUNDATION (slot306, UUID: 1658ed6d-db63-42b1-9118-2911c7a06975):
  - All X-externals share a common vertex
  - 2 edges cover X and all its X-externals

  GAP IDENTIFIED (Gemini review):
  - Bridge triangles (sharing edges with MULTIPLE packing elements) are NOT covered
    by the two_edges_cover_all_externals approach

  THIS FILE:
  - Proves bridge triangles ARE covered by the 8-edge union
  - Key insight: Bridge T={x,c,y} passes through shared vertex c
  - If common vertex for X or Y is c, then T is covered
  - We prove at least one must have c as common vertex

  PROOF STRATEGY:
  1. Define bridge triangles precisely
  2. Show bridge triangle T={x,c,y} is covered if c is common vertex for X or Y
  3. Prove: for any shared vertex c, at least one adjacent element has c as common vertex
  4. Combine with two_edges_cover_all_externals for complete τ ≤ 8
-/

import Mathlib


set_option maxHeartbeats 400000

set_option linter.mathlibStandardSet false

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

-- NEW: Bridge triangle definition
def isBridgeTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧
  ∃ X Y : Finset V, X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧ sharesEdgeWith t X ∧ sharesEdgeWith t Y

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING FROM SLOT306 (0 sorry - copied verbatim)
-- ══════════════════════════════════════════════════════════════════════════════

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.2 ⟨u, by aesop, v, by aesop⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE TRIANGLE PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH: Bridge triangle passes through shared vertex

If T shares edges with X and Y (both in M), and X ∩ Y = {c} (edge-disjoint packing):
- T ∩ X has ≥ 2 vertices (shares edge)
- T ∩ Y has ≥ 2 vertices (shares edge)
- T has 3 vertices
- X ∩ Y has 1 vertex (edge-disjoint)

Let T = {a, b, c'} where the shared edge with X is {a, b} ⊆ X.
For T to also share edge with Y, that edge must be {?, ?} ⊆ Y ∩ T.
Since X ∩ Y = {c}, and T ∩ X = {a, b}, the shared vertex c must be in T.
Actually, if a ∈ X \ Y and b ∈ X \ Y, then T ∩ Y ⊆ {c'}.
For T ∩ Y to have ≥ 2 vertices, we need c' ∈ Y and one of a, b ∈ Y.
But a, b ∈ X \ Y, contradiction unless c' = c and exactly one of a, b is in Y.

More carefully: Let X = {x1, x2, c}, Y = {y1, y2, c} with X ∩ Y = {c}.
T shares edge with X: either {x1, x2}, {x1, c}, or {x2, c}.
T shares edge with Y: either {y1, y2}, {y1, c}, or {y2, c}.

Case: T shares {x1, c} with X and {y1, c} with Y.
Then T ⊇ {x1, c, y1}, and since T has 3 vertices, T = {x1, c, y1}.
So c ∈ T. ✓

Case: T shares {x1, x2} with X (not involving c).
Then T ⊇ {x1, x2}, and T must share edge with Y.
T ∩ Y ≥ 2, so at least 2 of T's vertices are in Y = {y1, y2, c}.
Since {x1, x2} ⊆ X and X ∩ Y = {c}, we have x1, x2 ∉ Y (unless x1 or x2 = c, contradiction).
So T's third vertex must provide 2 vertices in Y. Impossible (only 1 third vertex).
So this case is impossible: T cannot share edge {x1, x2} (avoiding c) with X.

Therefore, any bridge triangle between X and Y contains the shared vertex c.
-/
lemma bridge_triangle_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (hX_card : X.card = 3) (hY_card : Y.card = 3)
    (h_inter : (X ∩ Y).card = 1)  -- Edge-disjoint implies ≤ 1; we assume exactly 1 shared vertex
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3)
    (hT_share_X : sharesEdgeWith T X) (hT_share_Y : sharesEdgeWith T Y) :
    ∃ c, c ∈ X ∧ c ∈ Y ∧ c ∈ T := by
  -- The shared vertex c is the unique element of X ∩ Y
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h_inter
  use c
  constructor
  · exact Finset.mem_inter.mp (hc ▸ Finset.mem_singleton_self c) |>.1
  constructor
  · exact Finset.mem_inter.mp (hc ▸ Finset.mem_singleton_self c) |>.2
  · -- Show c ∈ T
    -- T shares edge with X, so |T ∩ X| ≥ 2
    -- T shares edge with Y, so |T ∩ Y| ≥ 2
    -- T has 3 vertices, X ∩ Y = {c}
    -- If c ∉ T, then T ∩ X ⊆ X \ {c} and T ∩ Y ⊆ Y \ {c}
    -- |X \ {c}| = 2, |Y \ {c}| = 2, and (X \ {c}) ∩ (Y \ {c}) = ∅
    -- So T has ≥ 2 vertices from X \ {c} and ≥ 2 from Y \ {c}, disjoint
    -- That's ≥ 4 vertices, but T has only 3. Contradiction.
    by_contra hc_notin_T
    have h_TX : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp hT_share_X
    have h_TY : (T ∩ Y).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T Y |>.mp hT_share_Y
    have hT_card : T.card = 3 := by
      simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT_tri
      exact hT_tri.2.2
    -- T ∩ X ⊆ X \ {c} since c ∉ T
    have h1 : T ∩ X ⊆ X \ {c} := by
      intro v hv
      simp only [Finset.mem_inter] at hv
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact hv.2
      · intro hvc
        rw [hvc] at hv
        exact hc_notin_T hv.1
    -- Similarly T ∩ Y ⊆ Y \ {c}
    have h2 : T ∩ Y ⊆ Y \ {c} := by
      intro v hv
      simp only [Finset.mem_inter] at hv
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact hv.2
      · intro hvc
        rw [hvc] at hv
        exact hc_notin_T hv.1
    -- (X \ {c}) ∩ (Y \ {c}) = ∅ since X ∩ Y = {c}
    have h3 : (X \ {c}) ∩ (Y \ {c}) = ∅ := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton, Finset.not_mem_empty,
                 iff_false, not_and, not_not]
      intro ⟨hvX, hvc⟩ ⟨hvY, _⟩
      -- v ∈ X ∩ Y, so v ∈ {c}, so v = c
      have : v ∈ X ∩ Y := Finset.mem_inter.mpr ⟨hvX, hvY⟩
      rw [hc] at this
      exact hvc (Finset.mem_singleton.mp this)
    -- T ∩ X and T ∩ Y are disjoint subsets of T
    have h4 : Disjoint (T ∩ X) (T ∩ Y) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      have : (T ∩ X) ∩ (T ∩ Y) ⊆ (X \ {c}) ∩ (Y \ {c}) := by
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        constructor
        · exact h1 (Finset.mem_inter.mpr ⟨hv.1.1, hv.1.2⟩)
        · exact h2 (Finset.mem_inter.mpr ⟨hv.2.1, hv.2.2⟩)
      exact Finset.eq_empty_of_subset_empty (h3 ▸ this)
    -- |T ∩ X| + |T ∩ Y| ≤ |T| since they're disjoint subsets
    have h5 : (T ∩ X).card + (T ∩ Y).card ≤ T.card := by
      have : (T ∩ X) ∪ (T ∩ Y) ⊆ T := by
        intro v hv
        cases Finset.mem_union.mp hv with
        | inl h => exact Finset.mem_inter.mp h |>.1
        | inr h => exact Finset.mem_inter.mp h |>.1
      calc (T ∩ X).card + (T ∩ Y).card
          = ((T ∩ X) ∪ (T ∩ Y)).card := by rw [Finset.card_union_eq_card_add_card h4]
        _ ≤ T.card := Finset.card_le_card this
    -- But |T ∩ X| ≥ 2 and |T ∩ Y| ≥ 2, so sum ≥ 4 > 3 = |T|
    omega

/-
PROOF SKETCH: Bridge triangle is covered if shared vertex is common vertex

If T = {x, c, y} with edges {x,c}, {c,y}, {x,y}, and:
- c is the common vertex for X's externals (so X's 2 edges are incident to c)
- Then one of X's edges is {c, x} (since x ∈ X and c ∈ X)
- Edge {c, x} = {x, c} is in T

Similarly if c is common vertex for Y.
-/
lemma bridge_covered_if_shared_is_common (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (c : V) (hc : c ∈ X)
    (e₁ e₂ : Sym2 V) (he₁ : e₁ ∈ G.edgeFinset) (he₂ : e₂ ∈ G.edgeFinset)
    (h_incident : ∃ u w : V, u ∈ X ∧ w ∈ X ∧ u ≠ c ∧ w ≠ c ∧ u ≠ w ∧
                  e₁ = Sym2.mk (c, u) ∧ e₂ = Sym2.mk (c, w))
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hT_share_X : sharesEdgeWith T X) (hc_in_T : c ∈ T) :
    e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
  -- T shares edge with X, so T ∩ X has ≥ 2 elements
  -- c ∈ T and c ∈ X, so c ∈ T ∩ X
  -- Let the other element of T ∩ X be v ∈ X, v ≠ c
  -- Then {c, v} is an edge of T (since T is a triangle containing c and v)
  -- e₁ = {c, u} or e₂ = {c, w} where u, w are the other two vertices of X
  -- If v = u, then {c, v} = {c, u} = e₁ ∈ T.sym2
  -- If v = w, then {c, v} = {c, w} = e₂ ∈ T.sym2
  -- If v ∉ {u, w}, then v = c, contradiction
  obtain ⟨u, w, hu_X, hw_X, hu_ne_c, hw_ne_c, huw, he₁_eq, he₂_eq⟩ := h_incident
  have h_TX : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp hT_share_X
  have hc_inter : c ∈ T ∩ X := Finset.mem_inter.mpr ⟨hc_in_T, hc⟩
  -- Get another element v ∈ T ∩ X, v ≠ c
  obtain ⟨v, hv_inter, hv_ne_c⟩ : ∃ v ∈ T ∩ X, v ≠ c := by
    have : 1 < (T ∩ X).card := by linarith
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp this
    by_cases hac : a = c
    · exact ⟨b, hb, fun h => hab (hac ▸ h.symm)⟩
    · exact ⟨a, ha, hac⟩
  have hv_T : v ∈ T := Finset.mem_inter.mp hv_inter |>.1
  have hv_X : v ∈ X := Finset.mem_inter.mp hv_inter |>.2
  -- v ∈ X and v ≠ c, so v ∈ {u, w} (since X = {c, u, w})
  have hX_form : X = {c, u, w} := by
    rw [Finset.card_eq_three] at hX_card
    obtain ⟨a, b, d, hab, had, hbd, hX_eq⟩ := hX_card
    -- c, u, w ∈ X = {a, b, d}, all distinct
    have hc_in : c ∈ ({a, b, d} : Finset V) := hX_eq ▸ hc
    have hu_in : u ∈ ({a, b, d} : Finset V) := hX_eq ▸ hu_X
    have hw_in : w ∈ ({a, b, d} : Finset V) := hX_eq ▸ hw_X
    -- c, u, w are distinct
    have hcu : c ≠ u := hu_ne_c.symm
    have hcw : c ≠ w := hw_ne_c.symm
    -- So {c, u, w} = {a, b, d}
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      rcases hx with rfl | rfl | rfl
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hc_in; tauto
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hu_in; tauto
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hw_in; tauto
    · intro hx
      rw [← hX_eq]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> [exact hc; exact hu_X; exact hw_X]
  -- v ∈ X = {c, u, w} and v ≠ c, so v = u or v = w
  have hv_uw : v = u ∨ v = w := by
    rw [hX_form] at hv_X
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv_X
    rcases hv_X with rfl | rfl | rfl
    · exact absurd rfl hv_ne_c
    · left; rfl
    · right; rfl
  -- {c, v} is an edge of T
  have hT_card : T.card = 3 := by
    simp only [SimpleGraph.cliqueFinset, Finset.mem_filter] at hT
    exact hT.2.2
  have hcv_edge : Sym2.mk (c, v) ∈ T.sym2 := by
    -- T is a 3-clique containing c and v with c ≠ v
    simp only [Finset.mem_sym2_iff]
    constructor
    · exact hc_in_T
    · exact hv_T
  -- Conclude
  cases hv_uw with
  | inl hvu =>
    left
    rw [he₁_eq, ← hvu]
    exact hcv_edge
  | inr hvw =>
    right
    rw [he₂_eq, ← hvw]
    exact hcv_edge

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8:
1. For each X ∈ M, use two_edges_cover_all_externals to get 2 edges
2. These 8 edges cover:
   - All elements of M (each covered by its own 2 edges)
   - All triangles external to exactly one element
3. For bridge triangles T sharing edges with X and Y:
   - By bridge_triangle_contains_shared_vertex, T contains the shared vertex c
   - If c is the common vertex for X, X's edges cover T (by bridge_covered_if_shared_is_common)
   - If c is the common vertex for Y, Y's edges cover T
   - We need to prove: for each shared vertex c, at least one adjacent element uses c
4. The key insight: if neither X nor Y has c as common vertex, we can MODIFY the choice
   to use c for one of them without increasing total edges

ALTERNATIVE: Direct construction using shared vertices as apexes.
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  /-
  PROOF SKETCH:
  1. Every triangle T is either in M, external to one element, or a bridge triangle
  2. Triangles in M and externals are covered by two_edges_cover_all_externals (slot306)
  3. Bridge triangles pass through shared vertices of M-elements
  4. Choose edges incident to shared vertices to cover bridge triangles
  5. Total: ≤ 8 edges

  Key observation: In a 4-packing, there are at most 3 pairs of elements sharing vertices.
  Each shared vertex c needs edges to cover bridge triangles passing through c.
  By choosing c as the "common vertex" for at least one adjacent element,
  the 2 edges for that element cover all bridge triangles at c.
  -/
  sorry

end