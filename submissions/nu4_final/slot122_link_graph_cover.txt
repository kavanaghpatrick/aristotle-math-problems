/-
Tuza ν=4 Cycle_4: LINK GRAPH COVERING BOUND
Slot 122

AI CONSENSUS KEY INSIGHT:
The gap to τ ≤ 8 requires proving: τ(triangles at v) ≤ 2 for each shared vertex

THIS SLOT'S APPROACH (from Codex):
- Define the LINK GRAPH at vertex v
- Triangles containing v ↔ edges in link graph G[N(v)]
- Covering triangles at v = vertex cover of link graph
- Use: Vertex Cover ≤ 2 × Matching (König-type bound)
- Prove: Matching in link graph is bounded by packing structure

KEY THEOREM CHAIN:
1. link_graph_definition: Edges in G[N(v)] = triangles at v
2. triangle_cover_equals_vertex_cover: τ(triangles at v) = vc(link graph)
3. vertex_cover_le_twice_matching: vc ≤ 2 × matching (true for ALL graphs)
4. link_matching_bounded: matching in link graph ≤ 2 (KEY CLAIM)
5. THEREFORE: τ(triangles at v) ≤ 4

NOTE: Getting ≤ 2 (not ≤ 4) requires stronger argument about packing interaction.
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

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesContainingVertex (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- LINK GRAPH DEFINITION
-- ══════════════════════════════════════════════════════════════════════════════

/-- The link graph at v: the induced subgraph on neighbors of v -/
def linkGraph (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj u w := u ≠ v ∧ w ≠ v ∧ u ≠ w ∧ G.Adj v u ∧ G.Adj v w ∧ G.Adj u w
  symm := by
    intro u w ⟨huv, hwv, huw, hvu, hvw, huw'⟩
    exact ⟨hwv, huv, huw.symm, hvw, hvu, huw'.symm⟩
  loopless := by
    intro u ⟨_, _, h, _, _, _⟩
    exact h rfl

/-- Key bijection: Triangles containing v ↔ edges in link graph -/
lemma triangles_at_v_correspond_to_link_edges (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ∀ t ∈ trianglesContainingVertex G v,
      ∃ u w : V, u ≠ w ∧ u ∈ t ∧ w ∈ t ∧ (linkGraph G v).Adj u w := by
  intro t ht
  simp only [trianglesContainingVertex, Finset.mem_filter] at ht
  obtain ⟨ht_tri, hv_t⟩ := ht
  -- t is a 3-clique containing v, so t = {v, u, w} for some u ≠ w with v ~ u ~ w ~ v
  have ht_card : t.card = 3 := Finset.mem_cliqueFinset_iff.mp ht_tri |>.2
  have ht_clique := Finset.mem_cliqueFinset_iff.mp ht_tri |>.1
  -- Extract the other two vertices
  have ⟨a, ha_mem, ha_ne⟩ : ∃ a ∈ t, a ≠ v := by
    by_contra h
    push_neg at h
    have : t ⊆ {v} := fun x hx => Finset.mem_singleton.mpr (h x hx)
    have : t.card ≤ 1 := Finset.card_le_card this |> fun h => le_trans h (by simp)
    omega
  have ⟨b, hb_mem, hb_ne_v, hb_ne_a⟩ : ∃ b ∈ t, b ≠ v ∧ b ≠ a := by
    have h_sub : ({v, a} : Finset V).card ≤ 2 := by
      by_cases hva : v = a
      · simp [hva]
      · rw [Finset.card_pair hva]
    have h_exists : ∃ b ∈ t, b ∉ ({v, a} : Finset V) := by
      by_contra h
      push_neg at h
      have : t ⊆ {v, a} := h
      have : t.card ≤ 2 := Finset.card_le_card this |> fun h => le_trans h h_sub
      omega
    obtain ⟨b, hb_mem, hb_notin⟩ := h_exists
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb_notin
    exact ⟨b, hb_mem, hb_notin.1, hb_notin.2⟩
  use a, b
  constructor
  · exact hb_ne_a.symm
  constructor
  · exact ha_mem
  constructor
  · exact hb_mem
  · -- Show (linkGraph G v).Adj a b
    simp only [linkGraph]
    constructor
    · exact ha_ne
    constructor
    · exact hb_ne_v
    constructor
    · exact hb_ne_a.symm
    -- Need: G.Adj v a, G.Adj v b, G.Adj a b
    -- All from t being a clique
    constructor
    · exact ht_clique ha_ne.symm hv_t ha_mem
    constructor
    · exact ht_clique hb_ne_v.symm hv_t hb_mem
    · exact ht_clique hb_ne_a.symm ha_mem hb_mem

-- ══════════════════════════════════════════════════════════════════════════════
-- VERTEX COVER OF LINK GRAPH
-- ══════════════════════════════════════════════════════════════════════════════

/-- A vertex cover of a graph -/
def isVertexCover (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ e ∈ G.edgeFinset, ∃ v ∈ S, v ∈ e

/-- Minimum vertex cover number -/
noncomputable def vertexCoverNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ : Finset V).powerset.filter (isVertexCover G) |>.image Finset.card |>.min |>.getD 0

/-- Key insight: Vertex cover of link graph → edge cover of triangles at v -/
lemma vertex_cover_gives_triangle_cover (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (S : Finset V) (hS : isVertexCover (linkGraph G v) S) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ S.card ∧
      ∀ t ∈ trianglesContainingVertex G v, ∃ e ∈ E, e ∈ t.sym2 := by
  -- For each w ∈ S, the edge s(v, w) covers triangles at v containing w
  let edge_set : Finset (Sym2 V) := S.image (fun w => s(v, w))
  use edge_set
  constructor
  · -- Card bound
    exact Finset.card_image_le
  · -- Coverage
    intro t ht
    -- t contains v and has an edge in the link graph
    obtain ⟨u, w, huw, hu_t, hw_t, h_link⟩ := triangles_at_v_correspond_to_link_edges G v t ht
    -- The edge s(u, w) is in link graph, so S covers it
    have h_edge_mem : s(u, w) ∈ (linkGraph G v).edgeFinset := by
      simp only [SimpleGraph.mem_edgeFinset]
      exact h_link
    obtain ⟨x, hx_S, hx_in_edge⟩ := hS (s(u, w)) h_edge_mem
    -- x ∈ {u, w} and x ∈ S
    simp only [Sym2.mem_iff] at hx_in_edge
    use s(v, x)
    constructor
    · -- s(v, x) ∈ edge_set
      simp only [edge_set, Finset.mem_image]
      exact ⟨x, hx_S, rfl⟩
    · -- s(v, x) ∈ t.sym2
      -- We need v ∈ t and x ∈ t
      -- v ∈ t: from ht
      simp only [trianglesContainingVertex, Finset.mem_filter] at ht
      have hv_t := ht.2
      -- x ∈ t: x ∈ {u, w} and both u, w ∈ t
      have hx_t : x ∈ t := by
        rcases hx_in_edge with rfl | rfl
        · exact hu_t
        · exact hw_t
      -- Need x ≠ v
      have hx_ne_v : x ≠ v := by
        rcases hx_in_edge with rfl | rfl
        · simp only [linkGraph] at h_link; exact h_link.1
        · simp only [linkGraph] at h_link; exact h_link.2.1
      sorry -- s(v, x) ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- VERTEX COVER ≤ 2 × MATCHING (König-type bound)
-- ══════════════════════════════════════════════════════════════════════════════

/-- A matching in a graph -/
def isMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  M ⊆ G.edgeFinset ∧
  M.toSet.Pairwise (fun e₁ e₂ => Disjoint e₁ e₂)

/-- Matching number -/
noncomputable def matchingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isMatching G) |>.image Finset.card |>.max |>.getD 0

/--
KEY THEOREM: Vertex cover ≤ 2 × matching for ANY graph.

This is NOT König's theorem (which gives equality for bipartite).
This is a weaker bound that holds for all graphs.

Proof idea: Given matching M with |M| = m, we need ≥ m vertices to cover M.
A greedy vertex cover uses at most 2m vertices (both endpoints of each matching edge).
-/
lemma vertex_cover_le_twice_matching (G : SimpleGraph V) [DecidableRel G.Adj] :
    vertexCoverNumber G ≤ 2 * matchingNumber G := by
  -- Standard result, but technical to prove formally
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MATCHING BOUND FOR LINK GRAPH (THE KEY CLAIM)
-- ══════════════════════════════════════════════════════════════════════════════

/--
KEY CLAIM: For a shared vertex v in a maximal packing with ν = 4,
the link graph at v has matching number ≤ 2.

WHY THIS SHOULD BE TRUE:
- Matching in link graph = edge-disjoint triangles containing v (in original graph)
- If matching ≥ 3, we have ≥ 3 edge-disjoint triangles at v
- Combined with ν = 4 packing structure, this should force ν ≥ 5

CAUTION: This needs careful proof. The triangles at v share vertex v,
so they're not part of the packing (packing requires edge-disjoint).
-/
lemma link_matching_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : ∃ A B ∈ M, A ≠ B ∧ v ∈ A ∧ v ∈ B) :
    matchingNumber (linkGraph G v) ≤ 2 := by
  -- This is the KEY claim that needs proof
  -- Approach: If matching ≥ 3, derive contradiction with ν = 4
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN RESULT
-- ══════════════════════════════════════════════════════════════════════════════

/--
MAIN THEOREM: For shared vertex v in ν = 4 packing,
τ(triangles at v) ≤ 4.

Proof chain:
1. τ(triangles at v) ≤ vc(link graph at v)  [vertex_cover_gives_triangle_cover]
2. vc(link graph) ≤ 2 × matching(link graph) [vertex_cover_le_twice_matching]
3. matching(link graph) ≤ 2 [link_matching_le_2]
4. Therefore τ ≤ 4
-/
theorem tau_triangles_at_shared_vertex_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : ∃ A B ∈ M, A ≠ B ∧ v ∈ A ∧ v ∈ B) :
    triangleCoveringNumberOn G (trianglesContainingVertex G v) ≤ 4 := by
  -- Get matching bound
  have h_match := link_matching_le_2 G M hM hM_card v hv
  -- Get vc ≤ 2 × matching
  have h_vc := vertex_cover_le_twice_matching (linkGraph G v)
  -- vc ≤ 2 × 2 = 4
  have h_vc_le_4 : vertexCoverNumber (linkGraph G v) ≤ 4 := by
    calc vertexCoverNumber (linkGraph G v)
        ≤ 2 * matchingNumber (linkGraph G v) := h_vc
      _ ≤ 2 * 2 := by omega
      _ = 4 := by ring
  -- Now convert vc to triangle cover
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 APPLICATION
-- ══════════════════════════════════════════════════════════════════════════════

def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

/--
For CYCLE_4 with all triangles containing some shared vertex (PROVEN: cycle4_all_triangles_contain_shared),
we get τ ≤ 4 × 4 = 16 from the link graph approach.

This is WEAKER than the target τ ≤ 8, but it's a valid bound.
To get τ ≤ 8, we need to exploit OVERLAP between partitions.
-/
theorem tau_cycle4_le_16_via_link_graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab v_bc v_cd v_da : V)
    (hAB : A ∩ B = {v_ab}) (hBC : B ∩ C = {v_bc})
    (hCD : C ∩ D = {v_cd}) (hDA : D ∩ A = {v_da})
    (h_all_contain : ∀ t ∈ G.cliqueFinset 3,
      v_ab ∈ t ∨ v_bc ∈ t ∨ v_cd ∈ t ∨ v_da ∈ t) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 16 := by
  -- Partition by first shared vertex
  -- Each partition has τ ≤ 4
  -- Total ≤ 16
  sorry

end
