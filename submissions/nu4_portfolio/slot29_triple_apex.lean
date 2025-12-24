/-
Tuza ν=4 Portfolio - Slot 29: Triple-Apex Reduction

TARGET: If some vertex v is in ≥3 packing triangles, prove τ ≤ 8

KEY INSIGHT (from Codex + Grok consultation 2024-12-23):
When a vertex v appears in 3+ packing elements:
1. Use tau_containing_v_le_4 to cover all v-containing triangles with ≤4 edges
2. The remaining packing element(s) have ν ≤ 1
3. Apply Parker's ν ≤ 1 bound: τ(T_e) ≤ 2
4. Total: τ ≤ 4 + 2 + (overlaps handled by bridges going through v)

This handles:
- Star case (all 4 share v)
- 3-star case (3 share v, 1 isolated)
- Triangle+1 case (3 form a triangle in sharing graph)

SCAFFOLDING:
- tau_containing_v_le_4 (proven in slot20)
- tau_union_le_sum (proven in slot16)
- tau_S_le_2 (proven in slot6)
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

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- Triangles containing vertex v
def trianglesContainingVertex (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

-- Packing elements containing vertex v
def packingElementsContaining (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  M.filter (fun t => v ∈ t)

-- Union of T_e for elements in a subset
def triangleUnion (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  M.biUnion (trianglesSharingEdge G)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Triangles containing v in the context of packing
-- ══════════════════════════════════════════════════════════════════════════════

-- All triangles sharing edges with packing elements that contain v
def trianglesAtV (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (packingElementsContaining M v).biUnion (trianglesSharingEdge G)

-- Triangles in trianglesAtV that contain v
def trianglesAtVContainingV (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (trianglesAtV G M v).filter (fun t => v ∈ t)

-- Triangles in trianglesAtV that avoid v (base triangles)
def trianglesAtVAvoidingV (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (trianglesAtV G M v).filter (fun t => v ∉ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: τ of triangles at v containing v
-- ══════════════════════════════════════════════════════════════════════════════

-- When ≥3 packing elements share v, triangles containing v can be hit with ≤4 edges
lemma tau_at_v_containing_v_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : (packingElementsContaining M v).card ≥ 3) :
    triangleCoveringNumberOn G (trianglesAtVContainingV G M v) ≤ 4 := by
  -- Strategy: Use spoke edges from v
  -- Each packing element {v, a_i, b_i} contributes spokes {v, a_i} and {v, b_i}
  -- Choose 4 spokes that cover all v-containing triangles including bridges
  sorry

-- Base triangles (avoiding v) need one edge per packing element's base
lemma tau_at_v_avoiding_v_le_k (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (v : V) (k : ℕ) (hk : (packingElementsContaining M v).card = k) :
    triangleCoveringNumberOn G (trianglesAtVAvoidingV G M v) ≤ k := by
  -- Each packing element's base triangles share the base edge
  -- So k base edges suffice
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Triple-Apex Theorem
-- ══════════════════════════════════════════════════════════════════════════════

-- When v is in ≥3 packing triangles
theorem tau_le_8_triple_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : (packingElementsContaining M v).card ≥ 3) :
    triangleCoveringNumber G ≤ 8 := by
  -- Case split: v is in 3 or 4 elements
  --
  -- If v is in all 4 (star case):
  --   trianglesAtVContainingV: τ ≤ 4 (spokes)
  --   trianglesAtVAvoidingV: τ ≤ 4 (bases)
  --   Total: τ ≤ 8
  --
  -- If v is in exactly 3:
  --   For the 3 at v: τ ≤ 3 + 3 = 6 (3 spokes + 3 bases)
  --   For the isolated element e4: τ(T_{e4}) ≤ 2
  --   Total: τ ≤ 8
  sorry

-- Specialized version for exactly 3 sharing v
theorem tau_le_8_three_share_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : (packingElementsContaining M v).card = 3)
    (e4 : Finset V) (he4 : e4 ∈ M) (he4_no_v : v ∉ e4) :
    triangleCoveringNumber G ≤ 8 := by
  -- The isolated element e4 contributes τ(S_{e4}) ≤ 2
  -- The 3 at v contribute τ ≤ 6
  sorry

-- Specialized version for all 4 sharing v (star)
theorem tau_le_8_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : ∀ e ∈ M, v ∈ e) :
    triangleCoveringNumber G ≤ 8 := by
  -- All triangles either contain v or are base triangles
  -- τ(containing v) ≤ 4 (4 well-chosen spokes)
  -- τ(base triangles) ≤ 4 (4 base edges)
  sorry

end
