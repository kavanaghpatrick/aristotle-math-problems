/-
Tuza ν=4 Portfolio - Slot 30: Vertex Partition Reduction

TARGET: If packing splits into vertex-disjoint blocks, reduce to smaller ν

KEY INSIGHT (from Gemini + Codex consultation 2024-12-23):
When the 4 packing elements can be partitioned into vertex-disjoint groups:
- Group A with k elements has ν = k
- Group B with 4-k elements has ν = 4-k
- Apply Parker's bound to each: τ(A) ≤ 2k, τ(B) ≤ 2(4-k)
- Total: τ ≤ 2k + 2(4-k) = 8

This handles all "disconnected" sharing graphs:
- Empty (all 4 isolated): 4 groups of 1, each τ ≤ 2, total ≤ 8
- Single edge: one pair + two isolated
- Matching: two pairs
- P3 + isolated: one triple + one isolated

SCAFFOLDING:
- tau_union_le_sum (proven in slot16)
- tau_S_le_2 (proven in slot6)
- Parker's inductive bound for ν ≤ 3
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

-- Union of all triangles sharing edges with elements in A
def triangleUnionOf (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V)) : Finset (Finset V) :=
  A.biUnion (trianglesSharingEdge G)

-- Vertex set of a collection of triangles
def vertexSetOf (A : Finset (Finset V)) : Finset V :=
  A.biUnion id

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry

-- Parker's bound for ν ≤ 2: τ ≤ 4
lemma parker_nu_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card ≤ 2) :
    triangleCoveringNumber G ≤ 4 := by
  sorry

-- Parker's bound for ν = 1: τ ≤ 2
lemma parker_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 1) :
    triangleCoveringNumber G ≤ 2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Vertex-disjoint blocks don't interact
-- ══════════════════════════════════════════════════════════════════════════════

-- If A and B are vertex-disjoint, their triangle neighborhoods don't share triangles
lemma vertex_disjoint_triangles_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V))
    (h_disj : Disjoint (vertexSetOf A) (vertexSetOf B)) :
    Disjoint (triangleUnionOf G A) (triangleUnionOf G B) := by
  -- A triangle sharing an edge with some a ∈ A has 2 vertices from a
  -- A triangle sharing an edge with some b ∈ B has 2 vertices from b
  -- If A and B are vertex-disjoint, no triangle can do both
  sorry

-- τ of disjoint union equals sum
lemma tau_disjoint_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V))
    (h_disj : Disjoint (triangleUnionOf G A) (triangleUnionOf G B)) :
    triangleCoveringNumberOn G (triangleUnionOf G A ∪ triangleUnionOf G B) =
    triangleCoveringNumberOn G (triangleUnionOf G A) + triangleCoveringNumberOn G (triangleUnionOf G B) := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Vertex Partition Theorem
-- ══════════════════════════════════════════════════════════════════════════════

-- Two vertex-disjoint groups
theorem tau_le_8_vertex_partition_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B : Finset (Finset V))
    (hAB : A ∪ B = M) (hAB_disj : Disjoint A B)
    (hA_card : A.card = 2) (hB_card : B.card = 2)
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B)) :
    triangleCoveringNumber G ≤ 8 := by
  -- Each group has ν = 2, so τ ≤ 4 each
  -- Vertex-disjoint means no interaction
  -- Total: τ ≤ 4 + 4 = 8
  sorry

-- 3+1 partition
theorem tau_le_8_vertex_partition_3_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset (Finset V)) (b : Finset V)
    (hAb : A ∪ {b} = M) (hb_not_in_A : b ∉ A)
    (hA_card : A.card = 3)
    (h_vertex_disj : Disjoint (vertexSetOf A) (b : Set V)) :
    triangleCoveringNumber G ≤ 8 := by
  -- A has ν = 3, so τ ≤ 6 by Parker
  -- {b} has ν = 1, so τ ≤ 2
  -- Vertex-disjoint means no interaction
  -- Total: τ ≤ 6 + 2 = 8
  sorry

-- General partition (any split of vertex-disjoint groups)
theorem tau_le_8_vertex_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B : Finset (Finset V))
    (hAB : A ∪ B = M) (hAB_disj : Disjoint A B)
    (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty)
    (h_vertex_disj : Disjoint (vertexSetOf A) (vertexSetOf B)) :
    triangleCoveringNumber G ≤ 8 := by
  -- |A| + |B| = 4, both nonempty
  -- τ ≤ 2|A| + 2|B| = 8
  sorry

-- Corollary: Disconnected sharing graph implies τ ≤ 8
theorem tau_le_8_disconnected (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    -- Sharing graph is disconnected: exists partition with no shared vertices
    (h_disconnected : ∃ (A B : Finset (Finset V)),
      A ∪ B = M ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
      ∀ a ∈ A, ∀ b ∈ B, Disjoint (a : Set V) (b : Set V)) :
    triangleCoveringNumber G ≤ 8 := by
  obtain ⟨A, B, hAB, hAB_disj, hA_ne, hB_ne, h_all_disj⟩ := h_disconnected
  -- The pairwise disjointness implies vertex set disjointness
  sorry

end
