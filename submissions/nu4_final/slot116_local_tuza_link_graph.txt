/-- Submission timestamp: 20251226_164343 --/
/-
Tuza ν=4 Strategy - Slot 116: Local Tuza via Link Graph Reduction

DEBATE BREAKTHROUGH (Gemini + Grok + Codex unanimous):
This is THE KEY LEMMA that makes cycle_4 work.

For any vertex v and the set of triangles T_v containing v:
  τ(T_v) ≤ 2 · ν(T_v)

PROOF IDEA (Link Graph Reduction):
1. Each triangle in T_v has form {v, x, y} where {x, y} is an edge
2. Define the "link graph" L_v = edges {x, y} such that {v, x, y} is a triangle
3. KEY OBSERVATION:
   - Disjoint triangles in T_v ↔ Disjoint edges in L_v (a matching)
   - Edge cover for T_v ↔ Vertex cover for L_v
4. By standard graph theory: |Vertex Cover| ≤ 2 × |Maximum Matching|
5. Therefore: τ(T_v) ≤ 2 · ν(T_v)

WHY THIS IS SAFER THAN PRIOR APPROACHES:
- Does NOT assume local_cover_le_2 (which is FALSE)
- Does NOT assume diagonal exclusion
- Uses a GENERAL graph theory result, not cycle_4-specific assumptions
- The 2× factor comes from VC ≤ 2M, a well-known theorem

RISK: LOW/MEDIUM - depends on Mathlib support for VC ≤ 2M
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

noncomputable def trianglePackingOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  triangles.powerset.filter (fun S =>
    S ⊆ triangles ∧
    Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1))
    |>.image Finset.card |>.max |>.getD 0

def trianglesContainingVertex (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- LINK GRAPH DEFINITION
-- ══════════════════════════════════════════════════════════════════════════════

/-- The link graph of v: edges between neighbors of v that form triangles with v -/
def linkGraph (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ G.Adj v x ∧ G.Adj v y ∧ x ≠ y ∧ x ≠ v ∧ y ≠ v
  symm := by
    intro x y ⟨hxy, hvx, hvy, hne, hxv, hyv⟩
    exact ⟨hxy.symm, hvy, hvx, hne.symm, hyv, hxv⟩
  loopless := by
    intro x ⟨_, _, _, hne, _, _⟩
    exact hne rfl

/-- Link graph has decidable adjacency -/
instance linkGraphDecidableRel (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    DecidableRel (linkGraph G v).Adj := by
  intro x y
  unfold linkGraph
  infer_instance

-- ══════════════════════════════════════════════════════════════════════════════
-- CORRESPONDENCE: Triangles at v ↔ Edges in Link Graph
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles containing v correspond bijectively to edges in the link graph -/
def triangleToLinkEdge (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (hv : v ∈ t) :
    (linkGraph G v).edgeSet := by
  -- t = {v, x, y} for some x, y with {x, y} an edge in link graph
  sorry

/-- Disjoint triangles at v ↔ Disjoint edges in link graph (matching) -/
lemma disjoint_triangles_iff_matching (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (t1 t2 : Finset V) (ht1 : t1 ∈ trianglesContainingVertex G v)
    (ht2 : t2 ∈ trianglesContainingVertex G v) (hne : t1 ≠ t2) :
    (t1 ∩ t2).card ≤ 1 ↔ ∃ (e1 e2 : Sym2 V), e1 ∈ (linkGraph G v).edgeSet ∧
      e2 ∈ (linkGraph G v).edgeSet ∧ Disjoint e1 e2 := by
  -- Key: t1 = {v, a, b}, t2 = {v, c, d}
  -- (t1 ∩ t2).card ≤ 1 ⟺ t1 ∩ t2 = {v} ⟺ {a,b} ∩ {c,d} = ∅
  -- which means edges {a,b} and {c,d} in link graph are disjoint
  sorry

/-- Edge cover for triangles at v ↔ Vertex cover in link graph -/
lemma edge_cover_iff_vertex_cover (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (E' : Finset (Sym2 V)) :
    (∀ t ∈ trianglesContainingVertex G v, ∃ e ∈ E', e ∈ t.sym2) ↔
    ∀ e ∈ (linkGraph G v).edgeFinset, ∃ x ∈ (E'.image Sym2.toFinset).biUnion id, x ∈ e := by
  -- Key: Each triangle {v, a, b} contains edge {a,b}
  -- E' covers triangle ⟺ E' contains an edge of {v, a, b}
  -- This translates to hitting vertex a or b (the endpoints of {a,b} in link graph)
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- STANDARD GRAPH THEORY: Vertex Cover ≤ 2 × Maximum Matching
-- ══════════════════════════════════════════════════════════════════════════════

/-- Vertex cover number of a graph -/
noncomputable def vertexCoverNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ : Finset V).powerset.filter (fun S =>
    ∀ e ∈ G.edgeFinset, ∃ v ∈ S, v ∈ e)
    |>.image Finset.card |>.min |>.getD 0

/-- Maximum matching size of a graph -/
noncomputable def maxMatchingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun M =>
    Set.Pairwise (M : Set (Sym2 V)) fun e1 e2 => Disjoint e1 e2)
    |>.image Finset.card |>.max |>.getD 0

/-- STANDARD RESULT: Minimum vertex cover ≤ 2 × maximum matching -/
theorem vertex_cover_le_two_matching (G : SimpleGraph V) [DecidableRel G.Adj] :
    vertexCoverNumber G ≤ 2 * maxMatchingNumber G := by
  -- Standard proof: Take maximum matching M
  -- The endpoints of M form a vertex cover of size ≤ 2|M|
  -- Any edge not covered by endpoints of M would extend M (contradiction)
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: LOCAL TUZA VIA LINK GRAPH
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangle packing at v = Matching in link graph -/
lemma packing_at_v_eq_matching (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    trianglePackingOn G (trianglesContainingVertex G v) = maxMatchingNumber (linkGraph G v) := by
  -- Bijection: disjoint triangles at v ↔ matching in link graph
  sorry

/-- Triangle cover at v = Vertex cover of link graph + at most 1 (for v-incident edges) -/
lemma cover_at_v_le_vertex_cover (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    triangleCoveringNumberOn G (trianglesContainingVertex G v) ≤ vertexCoverNumber (linkGraph G v) := by
  -- Key: Vertex cover S in link graph gives edge cover {v, s} for s ∈ S
  -- Each triangle {v, a, b} has edge {v, a} or {v, b} in the cover
  sorry

/-- MAIN THEOREM: Local Tuza bound via link graph reduction -/
theorem local_tuza_via_link_graph (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    triangleCoveringNumberOn G (trianglesContainingVertex G v) ≤
    2 * trianglePackingOn G (trianglesContainingVertex G v) := by
  calc triangleCoveringNumberOn G (trianglesContainingVertex G v)
      ≤ vertexCoverNumber (linkGraph G v) := cover_at_v_le_vertex_cover G v
    _ ≤ 2 * maxMatchingNumber (linkGraph G v) := vertex_cover_le_two_matching (linkGraph G v)
    _ = 2 * trianglePackingOn G (trianglesContainingVertex G v) := by
        rw [packing_at_v_eq_matching]

-- ══════════════════════════════════════════════════════════════════════════════
-- APPLICATION TO CYCLE_4 PARTITION
-- ══════════════════════════════════════════════════════════════════════════════

/-- For each partition piece T_i (triangles containing shared vertex v_i),
    we have τ(T_i) ≤ 2·ν(T_i) -/
theorem partition_piece_tuza_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (Ti : Finset (Finset V)) (v : V)
    (hTi : Ti ⊆ trianglesContainingVertex G v) :
    triangleCoveringNumberOn G Ti ≤ 2 * trianglePackingOn G Ti := by
  -- Since Ti ⊆ triangles at v, we can apply local_tuza_via_link_graph
  -- with appropriate subset handling
  sorry

end
