/-
Tuza ν=4 Portfolio - Slot 31: Link Graph Vertex Cover (Star Case)

TARGET: In star configuration, reduce to vertex cover on link graph

KEY INSIGHT (from Gemini consultation 2024-12-23):
In the star case where all 4 packing elements share vertex v:
- M = {e1, e2, e3, e4} with ei = {v, ai, bi}
- Triangles containing v correspond to edges in the link graph L_v
- L_v has vertices = neighbors of v, edges = {u,w} where {v,u,w} is a triangle
- Covering triangles at v with edges incident to v ≡ Vertex Cover in L_v

The link graph structure:
- 8 outer vertices: a1, b1, a2, b2, a3, b3, a4, b4
- Packing edges: {ai, bi} for i=1,2,3,4 (a perfect matching)
- Bridge edges: connect ai or bi to aj or bj for i ≠ j

KEY LEMMA: Bridges form a matching on outer vertices (from bridges_inter_card_eq_one).
So bridge edges in L_v are also vertex-disjoint.

2-SAT INSIGHT: Choosing one spoke per packing element to cover all bridges
is a 2-SAT problem, which is always satisfiable when bridges form a matching.

SCAFFOLDING:
- bridges_contain_v (proven in slot6)
- bridges_inter_card_eq_one (proven in slot6)
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

def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

def allBridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  M.biUnion (bridges G M)

-- Outer vertices (vertices in packing minus v)
def outerVertices (M : Finset (Finset V)) (v : V) : Finset V :=
  (M.biUnion id).filter (· ≠ v)

-- Link graph at v: edges are {u,w} where {v,u,w} is a triangle
-- We represent edges as Sym2 V
def linkGraphEdges (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Sym2 V) :=
  ((G.cliqueFinset 3).filter (fun t => v ∈ t)).image (fun t =>
    let others := t.filter (· ≠ v)
    if h : others.card = 2 then
      let l := others.toList
      s(l.head!, l.tail.head!)
    else s(v, v)) -- fallback, shouldn't happen for triangles

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridges_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ bridges G M e) (ht_f : (t ∩ f).card ≥ 2) :
    v ∈ t := by
  sorry

lemma bridges_inter_card_eq_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ allBridges G M) (ht2 : t2 ∈ allBridges G M) (hne : t1 ≠ t2) :
    (t1 ∩ t2).card = 1 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- LINK GRAPH PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

-- In star configuration, packing triangles correspond to a matching in L_v
lemma packing_forms_matching_in_link (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (h_star : ∀ e ∈ M, v ∈ e) :
    ∃ (matching : Finset (Sym2 V)), matching.card = 4 ∧
      (∀ e ∈ matching, e ∈ linkGraphEdges G v) ∧
      (∀ e1 ∈ matching, ∀ e2 ∈ matching, e1 ≠ e2 → Disjoint (e1 : Set V) (e2 : Set V)) := by
  sorry

-- Bridges also form a matching on outer vertices
lemma bridges_form_matching (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (h_star : ∀ e ∈ M, v ∈ e) :
    ∀ t1 ∈ allBridges G M, ∀ t2 ∈ allBridges G M, t1 ≠ t2 →
      Disjoint ((t1.filter (· ≠ v)) : Set V) (t2.filter (· ≠ v)) := by
  -- From bridges_inter_card_eq_one: t1 ∩ t2 = {v}
  -- So the outer vertices (non-v vertices) are disjoint
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY THEOREM: Spoke Selection via 2-SAT
-- ══════════════════════════════════════════════════════════════════════════════

-- There exists a choice of 4 spokes (one per packing element) covering all bridges
theorem spoke_cover_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (h_star : ∀ e ∈ M, v ∈ e) :
    ∃ (spokes : Finset (Sym2 V)), spokes.card ≤ 4 ∧
      (∀ e ∈ M, ∃ s ∈ spokes, s ∈ (e : Finset V).image (fun u => s(v, u))) ∧
      (∀ b ∈ allBridges G M, ∃ s ∈ spokes, s ∈ (b : Finset V).image (fun u => s(v, u))) := by
  -- 2-SAT formulation:
  -- For each packing element e = {v, a, b}, we choose s(v,a) OR s(v,b)
  -- For each bridge b = {v, x, y} between e_i and e_j, we need s(v,x) OR s(v,y)
  -- Since bridges form a matching on outer vertices, no contradiction is possible
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Star Case via Link Graph
-- ══════════════════════════════════════════════════════════════════════════════

-- τ for triangles containing v in star case
lemma tau_containing_v_star_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (h_star : ∀ e ∈ M, v ∈ e) :
    triangleCoveringNumberOn G ((G.cliqueFinset 3).filter (fun t => v ∈ t)) ≤ 4 := by
  -- Use spoke_cover_exists: 4 spokes hit all packing and all bridges
  -- Triangles containing v are either packing, bridges, or in some S_e
  -- S_e triangles containing v share a spoke with e
  sorry

-- τ for triangles avoiding v (base triangles)
lemma tau_avoiding_v_star_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (h_star : ∀ e ∈ M, v ∈ e) :
    triangleCoveringNumberOn G ((G.cliqueFinset 3).filter (fun t => v ∉ t ∧
      ∃ e ∈ M, (t ∩ e).card ≥ 2)) ≤ 4 := by
  -- Base triangles share edge {a_i, b_i} with packing element e_i
  -- 4 base edges suffice
  sorry

-- Main theorem: Star case
theorem tau_le_8_star_link_graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (h_star : ∀ e ∈ M, v ∈ e) :
    triangleCoveringNumber G ≤ 8 := by
  -- Decompose all triangles into:
  -- 1. Containing v: τ ≤ 4 (by tau_containing_v_star_le_4)
  -- 2. Avoiding v but sharing edge with M: τ ≤ 4 (by tau_avoiding_v_star_le_4)
  -- All triangles fall into one of these categories
  sorry

end
