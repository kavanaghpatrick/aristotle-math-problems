/-
  slot223_external_common_edge.lean

  KEY LEMMA: All externals of M-element X share a common edge

  FROM 3-ROUND MULTI-AGENT DEBATE (Jan 3, 2026):
  Grok, Gemini, Codex all agreed this is the critical lemma for τ ≤ 8.

  STATEMENT:
  In cycle_4 with ν = 4, all externals of the same M-element X share a
  SINGLE common edge e_X.

  WHY THIS ISN'T JUST HELLY:
  Pattern 18 shows Helly fails for triangles (pairwise edge-sharing ≠ common edge).
  BUT the ν = 4 constraint adds EXTRA structure:

  PROOF STRATEGY (5-packing contradiction):
  1. Suppose externals T₁, T₂, T₃ of X use all 3 different edges of X
  2. By slot182, any two share an edge - they share the fan apex x
  3. T₁ = {a,b,x}, T₂ = {b,c,x}, T₃ = {a,c,x} where X = {a,b,c}
  4. If any two (say T₁, T₂) are edge-disjoint in the COVERING sense...
  5. Wait - they share edge {b,x}. So they're NOT edge-disjoint.

  REFINED INSIGHT:
  The key is that slot182 FORCES a common apex x for all externals.
  With apex x, the common edge is one of {a,x}, {b,x}, {c,x}.

  But which one? The 5-packing argument:
  - If T₁ uses {a,b} from X and T₂ uses {b,c} from X
  - They share apex x, so they share edge {b,x}
  - Actually ALL triangles containing x and any vertex of X share this structure

  CONCLUSION:
  Externals of X form a FAN around apex x. They share vertex x AND they share
  one of {a,x}, {b,x}, {c,x}. The question is which one.

  Actually, they share VERTEX x, but may use different spokes. However:
  - To COVER all externals, we need the spokes {a,x}, {b,x}, {c,x}
  - That's 3 edges per M-element × 4 M-elements = 12 edges
  - But this matches τ ≤ 12, not τ ≤ 8!

  ALTERNATIVE APPROACH (Link Graph):
  The τ ≤ 8 bound comes from König's theorem on the link graph, not from
  a common edge per M-element.

  At shared vertex v:
  - L_v has 4 vertices (M-neighbors of v)
  - α(L_v) ≥ 2 because ν = 4 (too many triangles → 5-packing)
  - Any 4-vertex graph with α ≥ 2 has τ ≤ 2
  - 4 vertices × 2 edges = 8

  DIFFICULTY: 5/5
  SUCCESS PROBABILITY: 50% (this is genuinely hard)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (standard)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 CONFIGURATION
-- ══════════════════════════════════════════════════════════════════════════════

structure Cycle4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  hM_card : M.card = 4
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  hAC : A ∩ C = ∅
  hBD : B ∩ D = ∅

-- ══════════════════════════════════════════════════════════════════════════════
-- LINK GRAPH DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- M-neighbors of v: vertices adjacent to v that are in some M-element containing v -/
def M_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset V :=
  M.biUnion (fun X => if v ∈ X then X.erase v else ∅)

/-- Link graph at v: edges between M-neighbors that form triangles with v -/
def linkGraphAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) (u w : V) : Prop :=
  u ∈ M_neighbors G M v ∧ w ∈ M_neighbors G M v ∧ u ≠ w ∧
  {v, u, w} ∈ G.cliqueFinset 3

/-- The link graph as a SimpleGraph -/
def linkGraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : SimpleGraph V where
  Adj := fun u w => linkGraphAdj G M v u w
  symm := by
    intro u w ⟨hu, hw, hne, ht⟩
    exact ⟨hw, hu, hne.symm, by rwa [Finset.insert_comm u, Finset.insert_comm v] at ht⟩
  loopless := by intro u ⟨_, _, hne, _⟩; exact hne rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: α(L_v) ≥ 2
-- ══════════════════════════════════════════════════════════════════════════════

/-- At shared vertex v in cycle_4, the link graph has at most 4 vertices -/
lemma link_graph_small (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V)) :
    (M_neighbors G M v).card ≤ 4 := by
  -- At each shared vertex, exactly 2 M-elements meet
  -- Each M-element contributes 2 other vertices
  -- Total: at most 4 M-neighbors
  sorry

/-- The link graph has independent set of size ≥ 2
    Proof: If α = 1, L_v = K₄, giving 6 triangles through v.
    This enables a 5-packing, contradicting ν = 4. -/
lemma link_graph_independence_ge_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V)) :
    ∃ u w, u ∈ M_neighbors G M v ∧ w ∈ M_neighbors G M v ∧ u ≠ w ∧
           ¬(linkGraph G M v).Adj u w := by
  -- Suppose not: every pair of M-neighbors forms a triangle with v
  -- This gives C(4,2) = 6 triangles through v
  -- At most 2 are M-elements, so at least 4 are externals
  -- Too many externals enables 5-packing by slot182 analysis
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- GRAPH THEORY LEMMA: 4-vertex graph with α ≥ 2 has τ ≤ 2
-- ══════════════════════════════════════════════════════════════════════════════

/-- Any graph on at most 4 vertices with independence number ≥ 2 has
    vertex cover number at most 2. -/
lemma four_vertex_cover (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (hS : S.card ≤ 4)
    (h_ind : ∃ u w, u ∈ S ∧ w ∈ S ∧ u ≠ w ∧ ¬H.Adj u w) :
    ∃ C : Finset V, C.card ≤ 2 ∧ C ⊆ S ∧ ∀ e ∈ H.edgeFinset, ∃ v ∈ C, v ∈ e := by
  -- If S has 4 vertices and α ≥ 2, it's not K₄
  -- Every non-K₄ on 4 vertices has τ ≤ 2
  -- Cases: path, cycle, star, etc. - all have 2-vertex cover
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- FROM VERTEX COVER TO EDGE COVER
-- ══════════════════════════════════════════════════════════════════════════════

/-- A vertex cover of L_v corresponds to an edge cover of triangles at v -/
lemma vertex_cover_to_edge_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V)
    (C : Finset V) (hC : C ⊆ M_neighbors G M v)
    (h_cover : ∀ u w, u ∈ M_neighbors G M v → w ∈ M_neighbors G M v → u ≠ w →
               {v, u, w} ∈ G.cliqueFinset 3 → u ∈ C ∨ w ∈ C) :
    ∀ t ∈ G.cliqueFinset 3, v ∈ t → ∃ u ∈ C, Sym2.mk (v, u) ∈ t.sym2 := by
  -- If t is a triangle containing v, its other vertices u, w are M-neighbors
  -- The vertex cover C contains u or w
  -- So edge {v,u} or {v,w} is in t
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN CONSTRUCTION: 8-EDGE COVER
-- ══════════════════════════════════════════════════════════════════════════════

/-- Construct 2-edge cover at each shared vertex -/
noncomputable def twoEdgeCoverAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V)) :
    Finset (Sym2 V) :=
  let C := (link_graph_independence_ge_2 G M hM hν cfg v hv).choose
  let u := C
  -- Select 2 vertices from M-neighbors that form a vertex cover
  -- Return edges {v, u}, {v, w}
  sorry

/-- The 8-edge cover construction -/
noncomputable def eightEdgeCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (cfg : Cycle4 G M) : Finset (Sym2 V) :=
  twoEdgeCoverAt G M hM hν cfg cfg.v_ab (by simp) ∪
  twoEdgeCoverAt G M hM hν cfg cfg.v_bc (by simp) ∪
  twoEdgeCoverAt G M hM hν cfg cfg.v_cd (by simp) ∪
  twoEdgeCoverAt G M hM hν cfg cfg.v_da (by simp)

-- ══════════════════════════════════════════════════════════════════════════════
-- COVERAGE LEMMA: Every triangle contains a shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle shares an edge with some M-element -/
axiom triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, sharesEdgeWith t X

/-- In cycle_4, every triangle contains at least one shared vertex -/
lemma triangle_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V), v ∈ t := by
  -- By maximality, t shares edge with some M-element X
  -- The shared edge contains vertices of X
  -- In cycle_4, each X contains exactly 2 shared vertices
  -- The shared edge must use at least one of them
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- MAIN THEOREM: τ ≤ 8 for cycle_4
    Proof via Link Graph + König approach from 3-round debate -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- Step 1: Build 8-edge cover
  let E := eightEdgeCover G M hM hν cfg

  -- Step 2: Show |E| ≤ 8
  have hE_card : E.card ≤ 8 := by
    -- Each vertex contributes ≤ 2 edges, 4 vertices total
    -- With possible overlap, still ≤ 8
    sorry

  -- Step 3: Show E covers all triangles
  have hE_covers : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
    intro t ht
    -- t contains some shared vertex v
    obtain ⟨v, hv_shared, hv_in_t⟩ := triangle_contains_shared_vertex G M hM cfg t ht
    -- twoEdgeCoverAt at v covers all triangles containing v
    sorry

  -- Step 4: Extract minimum
  sorry

end
