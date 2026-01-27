/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 45b44abe-931d-4ab1-86b9-d0ddd754e2f3

The following was proved by Aristotle:

- lemma bridge_covered_by_adjacent (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3)
    (B : Finset V) (hB : isBridgeTriangle G M B) :
    ∃ X ∈ M, ∃ e1 e2 : Sym2 V, e1 ∈ G.edgeFinset ∧ e2 ∈ G.edgeFinset ∧
      e1 ∈ X.sym2 ∧ e2 ∈ X.sym2 ∧ (e1 ∈ B.sym2 ∨ e2 ∈ B.sym2)
-/

/-
  slot349: τ ≤ 8 via biUnion Construction

  MINIMAL VERSION: Focus Aristotle on the ONE key gap.

  PROVEN SCAFFOLDING:
  - triangle_classification: Every triangle is in M, external, or bridge
  - biUnion_card_bound: Union of 4 sets of ≤2 elements has ≤8 elements
  - sharesEdgeWith_iff_card_inter_ge_two: Edge sharing ↔ intersection ≥ 2

  KEY LEMMA (for Aristotle to prove):
  two_edges_cover_X_and_externals: ∃ 2 X-edges covering X + all X-externals

  PROOF STRATEGY:
  1. For each X ∈ M, get 2 edges covering X + X-externals
  2. biUnion has ≤ 8 edges
  3. Coverage: M-elements by own edges, externals by parent's edges,
     bridges by one of their adjacent M-elements' edges
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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
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
  · intro h; exact ⟨h u (Sym2.mem_iff.mpr (Or.inl rfl)), h v (Sym2.mem_iff.mpr (Or.inr rfl))⟩
  · intro ⟨hu, hv⟩ x hx; simp only [Sym2.mem_iff] at hx; rcases hx with rfl | rfl <;> assumption

lemma triangle_classification (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨ (∃ X ∈ M, isExternalOf G M X T) ∨ isBridgeTriangle G M T := by
  by_cases hT_in : T ∈ M
  · left; exact hT_in
  · right
    obtain ⟨X, hX_in, hX_share⟩ := hM.2 T hT hT_in
    have hX_share' : sharesEdgeWith T X := sharesEdgeWith_iff_card_inter_ge_two T X |>.mpr hX_share
    by_cases h_ext : ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith T Y
    · left; exact ⟨X, hX_in, hT, hT_in, hX_share', h_ext⟩
    · right; push_neg at h_ext
      obtain ⟨Y, hY_in, hY_ne, hY_share⟩ := h_ext
      exact ⟨hT, hT_in, X, Y, hX_in, hY_in, hY_ne.symm, hX_share', hY_share⟩

theorem biUnion_card_bound {α β : Type*} [DecidableEq β]
    (M : Finset α) (hM : M.card = 4)
    (f : α → Finset β) (hf : ∀ x ∈ M, (f x).card ≤ 2) :
    (M.biUnion f).card ≤ 8 := by
  calc (M.biUnion f).card
      ≤ M.sum (fun x => (f x).card) := Finset.card_biUnion_le
    _ ≤ M.sum (fun _ => 2) := Finset.sum_le_sum (fun x hx => hf x hx)
    _ = 2 * M.card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
    _ = 2 * 4 := by rw [hM]
    _ = 8 := by decide

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Two edges cover X + externals
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for two_edges_cover_X_and_externals:

1. X = {a, b, c} has 3 vertices and 3 edges: {a,b}, {a,c}, {b,c}
2. Each X-external shares EXACTLY ONE edge with X (by ν=4 constraint)
3. KEY: All X-externals share the SAME edge with X
   - If external T1 shares {a,b} and T2 shares {a,c}, we could form a 5-packing
   - Contradiction with ν = 4
4. So pick e1 = the common edge, e2 = any other X-edge
5. e1 covers all externals, e1 ∪ e2 covers X
-/
lemma two_edges_cover_X_and_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3) :
    ∃ e1 e2 : Sym2 V, e1 ∈ G.edgeFinset ∧ e2 ∈ G.edgeFinset ∧
    e1 ∈ X.sym2 ∧ e2 ∈ X.sym2 ∧
    ∀ T, isExternalOf G M X T → e1 ∈ T.sym2 ∨ e2 ∈ T.sym2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE COVERAGE: Bridges share edge with 2 M-elements, one covers it
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for bridge_covered_by_adjacent:

A bridge B shares edges with X and Y in M.
B ∩ X ≥ 2 and B ∩ Y ≥ 2, but B.card = 3.

Let B = {u, v, w}.
B ∩ X = at least 2 of {u, v, w}
B ∩ Y = at least 2 of {u, v, w}

Since M is a packing, X ∩ Y ≤ 1 vertex.
So B ∩ X and B ∩ Y share at most 1 vertex.

CASE: B ∩ X = {u, v}, B ∩ Y = {u, w} (share vertex u)
- X's 2-edge selection includes 2 edges of X = {u, v, x}
- At least one of X's edges is incident to u or v
- If that edge is {u, v}, it's in B
- Otherwise, X picked edges {u, x} and {v, x}, missing {u, v}
- But then Y's selection for edge {u, w}: if Y = {u, w, y}, Y picks 2 edges
- At least one contains u or w. If {u, w}, it's in B. ✓

By pigeonhole, at least one of X or Y's selections hits B.
-/
lemma bridge_covered_by_adjacent (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3)
    (B : Finset V) (hB : isBridgeTriangle G M B) :
    ∃ X ∈ M, ∃ e1 e2 : Sym2 V, e1 ∈ G.edgeFinset ∧ e2 ∈ G.edgeFinset ∧
      e1 ∈ X.sym2 ∧ e2 ∈ X.sym2 ∧ (e1 ∈ B.sym2 ∨ e2 ∈ B.sym2) := by
  rcases hB with ⟨ hB₁, hB₂, X, Y, hX, hY, hXY, hB₃ ⟩;
  obtain ⟨ u, v, huv, hu, hv, huX, hvX ⟩ := hB₃.1;
  use X, hX;
  use s(u, v), s(u, v);
  have := Finset.mem_coe.2 ( Finset.mem_coe.1 <| Finset.mem_coe.2 <| Finset.mem_coe.1 <| Finset.mem_coe.1 hB₁ ) ; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
  exact hB₁.1 hu hv huv

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8:

CONSTRUCTION:
- For each X ∈ M, let (e1_X, e2_X) = two_edges_cover_X_and_externals
- Let E = ⋃_{X ∈ M} {e1_X, e2_X}

CARDINALITY:
- Each set has ≤ 2 elements
- |M| = 4
- |E| ≤ 4 × 2 = 8 by biUnion_card_bound

COVERAGE (by triangle_classification):
1. T ∈ M: T's own selection covers T (e1_T ∈ T.sym2)
2. T external to X: two_edges_cover_X_and_externals guarantees e1_X or e2_X in T.sym2
3. T is bridge: bridge_covered_by_adjacent guarantees some M-element's selection hits T

EDGE VALIDITY:
All edges from two_edges_cover_X_and_externals are in G.edgeFinset.
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end