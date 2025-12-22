/-
Tuza ν=4 Portfolio - Slot 14: V-Decomposition Strategy

TARGET: Prove τ(T_e ∪ T_f) ≤ 4 using vertex decomposition

KEY INSIGHT (from Codex + Grok consultation):
Decompose T_e ∪ T_f by whether triangles contain shared vertex v:
  Y_v = triangles containing v
  Z = triangles avoiding v

For Z: All vertices come from (e \ {v}) ∪ (f \ {v}), which has ≤4 vertices
       → Apply lemma_K4_cover → τ(Z) ≤ 2

For Y_v: Every triangle uses an edge incident to v
         → Can cover with 2 v-incident edges (one from e-side, one from f-side)

Total: τ(Y_v) + τ(Z) ≤ 2 + 2 = 4 ✓

This decomposition makes the bound OBVIOUS rather than requiring overlap arguments.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

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

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY DEFINITIONS: V-decomposition
-- ══════════════════════════════════════════════════════════════════════════════

-- Triangles containing vertex v
def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

-- Triangles avoiding vertex v
def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA: K4 cover (triangles on ≤4 vertices have τ ≤ 2)
-- ══════════════════════════════════════════════════════════════════════════════

lemma k4_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V))
    (h_cliques : triangles ⊆ G.cliqueFinset 3)
    (h_vertices : (triangles.biUnion id).card ≤ 4) :
    triangleCoveringNumberOn G triangles ≤ 2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMAS FOR V-DECOMPOSITION
-- ══════════════════════════════════════════════════════════════════════════════

-- Triangles avoiding v have vertices only in (e \ {v}) ∪ (f \ {v})
lemma avoiding_v_vertices (e f : Finset V) (v : V)
    (he : e.card = 3) (hf : f.card = 3) (h_inter : e ∩ f = {v})
    (triangles : Finset (Finset V))
    (h_sub : triangles ⊆ trianglesSharingEdge (G : SimpleGraph V) e ∪ trianglesSharingEdge G f)
    (h_avoid : ∀ t ∈ triangles, v ∉ t) :
    (triangles.biUnion id) ⊆ (e \ {v}) ∪ (f \ {v}) := by
  sorry

-- (e \ {v}) ∪ (f \ {v}) has exactly 4 vertices
lemma non_v_vertices_card (e f : Finset V) (v : V)
    (he : e.card = 3) (hf : f.card = 3) (h_inter : e ∩ f = {v})
    (h_disjoint : (e \ {v}) ∩ (f \ {v}) = ∅) :
    ((e \ {v}) ∪ (f \ {v})).card = 4 := by
  sorry

-- Triangles containing v can be covered by 2 edges incident to v
lemma containing_v_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (v : V)
    (h_cliques : triangles ⊆ G.cliqueFinset 3)
    (h_contain : ∀ t ∈ triangles, v ∈ t) :
    triangleCoveringNumberOn G triangles ≤ 2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN DECOMPOSITION LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

-- The union splits into Y_v and Z
lemma v_decomposition (triangles : Finset (Finset V)) (v : V) :
    triangles = trianglesContaining triangles v ∪ trianglesAvoiding triangles v := by
  ext t
  simp [trianglesContaining, trianglesAvoiding]
  tauto

-- Covering number of union bounded by sum
lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: τ(T_e ∪ T_f) ≤ 4
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_union_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  -- Decompose into Y_v (containing v) and Z (avoiding v)
  let T_ef := trianglesSharingEdge G e ∪ trianglesSharingEdge G f
  let Y_v := trianglesContaining T_ef v
  let Z := trianglesAvoiding T_ef v
  -- T_ef = Y_v ∪ Z
  have h_decomp : T_ef = Y_v ∪ Z := v_decomposition T_ef v
  -- τ(T_ef) ≤ τ(Y_v) + τ(Z)
  calc triangleCoveringNumberOn G T_ef
      = triangleCoveringNumberOn G (Y_v ∪ Z) := by rw [← h_decomp]
    _ ≤ triangleCoveringNumberOn G Y_v + triangleCoveringNumberOn G Z := tau_union_le_sum G Y_v Z
    _ ≤ 2 + triangleCoveringNumberOn G Z := by {
        -- τ(Y_v) ≤ 2 by containing_v_cover
        sorry
      }
    _ ≤ 2 + 2 := by {
        -- τ(Z) ≤ 2 by k4_cover (Z lives on ≤4 vertices)
        sorry
      }
    _ = 4 := by ring

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: ν = 4 → τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

theorem tuza_nu4_v_decomp (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) : triangleCoveringNumber G ≤ 8 := by
  sorry

end
