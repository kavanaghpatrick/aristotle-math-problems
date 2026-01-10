/-
  slot304: {v1,b} Externals Are Constrained

  GOAL: Prove that B-externals using edge {v1,b} share a vertex in B
  with any other B-external. This follows directly from slot303.

  CONTEXT:
  PATH_4: A = {v1,a1,a2}, B = {v1,v2,b}, C = {v2,v3,c}, D = {v3,d1,d2}

  By slot303 (middle_fan_apex_in_B): Any two B-externals share a vertex in B.

  IMPLICATION: ALL B-externals share a common vertex x ∈ B (the fan apex).
  Therefore 2 edges from B incident to x cover B + all B-externals.
-/

import Mathlib

set_option maxHeartbeats 400000
set_option linter.mathlibStandardSet false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

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

-- Externals using specific edge
def isExternalUsingEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (u v : V) (t : Finset V) : Prop :=
  isExternalOf G M X t ∧ u ∈ t ∧ v ∈ t

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREMS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Key lemma: B-externals using {v1,b} share a vertex in B with any other B-external.

By slot303 (middle_fan_apex_in_B), any two B-externals share a vertex in B.
-/
theorem v1b_externals_share_B_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (B : Finset V) (hB : B ∈ M) (hB_3 : B.card = 3)
    (v1 b : V) (hv1 : v1 ∈ B) (hb : b ∈ B) (hv1_ne_b : v1 ≠ b)
    (T : Finset V) (hT : isExternalUsingEdge G M B v1 b T)
    (T' : Finset V) (hT' : isExternalOf G M B T')
    (h_ne : T ≠ T') :
    ∃ x ∈ T ∩ T', x ∈ B := by
  -- This follows from slot303: any two B-externals share a vertex in B
  -- T is a B-external (using edge {v1,b})
  -- T' is a B-external
  -- By slot303, they share a vertex in B
  sorry

/-- All B-externals share a common vertex in B (the fan apex) -/
theorem B_externals_share_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (B : Finset V) (hB : B ∈ M) (hB_3 : B.card = 3) :
    ∃ x ∈ B, ∀ T, isExternalOf G M B T → x ∈ T := by
  -- By slot303, any two B-externals share an edge containing a B-vertex
  -- This shared vertex is consistent across all pairs (fan structure)
  -- Therefore all B-externals share a common vertex in B
  sorry

/-- Corollary: 2 edges from B incident to fan apex cover B and all B-externals -/
theorem two_edges_cover_B_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (B : Finset V) (hB : B ∈ M) (hB_3 : B.card = 3)
    (x y z : V) (hB_eq : B = {x, y, z}) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx_apex : ∀ T, isExternalOf G M B T → x ∈ T) :
    ∀ T, (T ∈ G.cliqueFinset 3 ∧ (T = B ∨ isExternalOf G M B T)) →
         (∃ u v, s(u, v) ∈ ({s(x, y), s(x, z)} : Finset (Sym2 V)) ∧ u ∈ T ∧ v ∈ T) := by
  -- For T = B: B = {x,y,z} contains both {x,y} and {x,z}
  -- For T external: x ∈ T by apex property, and T shares edge with B
  --   T ∩ B has ≥ 2 vertices, one of which is x
  --   So T contains {x, w} for some w ∈ {y, z}
  sorry

end
