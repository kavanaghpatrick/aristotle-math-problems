/-
slot129: Support Sunflower - Triangles at Shared Vertex Covered by ≤2 Edges

GITHUB ISSUE: #30
GOAL: Prove that triangles sharing an M-edge at vertex v can be covered by ≤2 edges

AI CONSENSUS (Dec 26-27, 2025):
- Grok: "support_sunflower is LIKELY TRUE. Degenerate sunflower insight."
- Gemini: "The Codex counterexample PROVES it works - all 4 triangles share {v_ab, x}!"

KEY INSIGHT (Codex counterexample analysis):
T1 = {v_ab, v_da, x}, T2 = {v_ab, a_priv, x}, T3 = {v_ab, v_bc, x}, T4 = {v_ab, b_priv, x}
All share edge {v_ab, x}! The "sunflower" is DEGENERATE with all petals sharing the same non-M edge.

PROOF STRATEGY:
1. Let T_v = triangles at v that share an M-edge (trianglesSharingMEdgeAt G M v)
2. Each t ∈ T_v has form {v, m, x} where m is M-neighbor of v, x is external
3. If two triangles t1 = {v, m1, x1}, t2 = {v, m2, x2} with m1 ≠ m2:
   - They can only share v (M-edge disjointness)
   - But both contain v, so if x1 = x2, they share edge {v, x1}
4. Claim: At most 2 distinct external vertices appear
   - Otherwise we'd get ν > 4 (can pack 5+ triangles)
5. Therefore E = {{v, x1}, {v, x2}} covers all of T_v, with |E| ≤ 2

CRITICAL DISTINCTION (avoiding FALSE lemma):
- FALSE: local_cover_le_2 (M-edges only) - 4 M-edges may be needed
- TRUE: support_sunflower (any graph edges) - 2 non-M edges suffice
The cover edges {v, x} need NOT be M-edges!

DEPENDENCIES:
- cycle4_element_contains_shared (slot128)
- triangle_shares_edge_with_packing (PROVEN)
- Cycle4 with distinctness (slot127)
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

/-- M-edges incident to vertex v -/
def M_edges_at (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion (fun X => X.sym2.filter (fun e => v ∈ e))

/-- Triangles that share an M-edge containing v -/
def trianglesSharingMEdgeAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ∃ e ∈ M_edges_at M v, e ∈ t.sym2)

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 STRUCTURE WITH DISTINCTNESS
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
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A
  h_diag_AC : (A ∩ C).card ≤ 1
  h_diag_BD : (B ∩ D).card ≤ 1
  h_vab_ne_vbc : v_ab ≠ v_bc
  h_vbc_ne_vcd : v_bc ≠ v_cd
  h_vcd_ne_vda : v_cd ≠ v_da
  h_vda_ne_vab : v_da ≠ v_ab

-- ══════════════════════════════════════════════════════════════════════════════
-- EXTERNAL VERTICES AT A SHARED VERTEX
-- ══════════════════════════════════════════════════════════════════════════════

/-- External vertices that appear in triangles at v (non-M-neighbor vertices) -/
def externalVerticesAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset V :=
  (trianglesSharingMEdgeAt G M v).biUnion (fun t => t.filter (fun x => x ≠ v ∧ ∀ X ∈ M, v ∈ X → x ∉ X))

/-- All third vertices (besides v and the M-neighbor) in triangles at v -/
def thirdVerticesAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset V :=
  (trianglesSharingMEdgeAt G M v).biUnion (fun t => t.filter (fun x => x ≠ v))

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: BOUNDED EXTERNAL VERTICES
-- ══════════════════════════════════════════════════════════════════════════════

/--
At a shared vertex v in cycle_4, triangles cluster around at most 2 external vertices.

PROOF IDEA:
Suppose there are 3+ external vertices x1, x2, x3 appearing in triangles at v.
Then we have triangles t1 = {v, m1, x1}, t2 = {v, m2, x2}, t3 = {v, m3, x3}.
These share only vertex v pairwise (since mi ≠ mj and xi ≠ xj).
So we could add any of these to M, violating maximality with ν = 4.

Actually, we already HAVE 4 triangles in M (A, B, C, D).
The triangles t1, t2, t3 share edges with M (by the M-edge condition).
The key constraint is that ν = 4 limits how many "external" directions we can have.

REFINED ARGUMENT:
At shared vertex v (say v = v_ab), v belongs to exactly 2 packing elements: A and B.
- M-neighbors of v in A: {other vertices of A except v}
- M-neighbors of v in B: {other vertices of B except v}

For a triangle t = {v, m, x} at v:
- m is an M-neighbor (either in A or B)
- x is the third vertex (may or may not be in M)

If x is ALSO a shared vertex, t might actually be one of A, B, C, D.
If x is NOT a shared vertex, it's truly "external".

The key observation: all triangles at v that use the SAME M-edge {v, m}
share that edge, hence pairwise share 2 vertices. So for maximality,
at most one such triangle can be outside M.

But triangles using DIFFERENT M-edges cluster by their external vertex.
The Codex example shows: all external triangles at v share the SAME external vertex x.
This is because any two triangles with different external vertices would be
almost disjoint (sharing only v), allowing us to add more to M.

The formal bound of 2 comes from: v touches 2 packing elements, each contributes
at most 1 "external direction" for non-M triangles.
-/
lemma external_vertices_bounded (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (cfg : Cycle4 G M)
    (v : V) (h_shared : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da) :
    (thirdVerticesAt G M v).card ≤ 4 := by
  -- v is in exactly 2 packing elements
  -- Each packing element has 2 other vertices (since |X| = 3 and v ∈ X)
  -- So there are at most 2 × 2 = 4 possible M-neighbors of v
  -- Each M-neighbor can pair with at most finitely many third vertices
  -- But by ν = 4 maximality, the structure is constrained

  -- Simple bound: third vertices are all in some triangle containing v
  -- Each triangle has 2 vertices besides v
  -- Number of triangles at v in a simple graph is bounded by degree considerations

  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- SUPPORT SUNFLOWER: MAIN LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/--
## The Sunflower Lemma (Support Version)

At a shared vertex v, all triangles that share an M-edge at v
can be covered by at most 2 edges (spokes from v to external vertices).

This is DIFFERENT from the false local_cover_le_2 because:
- We allow ANY graph edges for covering, not just M-edges
- The 2 edges are of form {v, x1} and {v, x2} for external vertices

PROOF:
1. Let T_v = trianglesSharingMEdgeAt G M v
2. Each t ∈ T_v has form {v, m, x} where:
   - v is the shared vertex
   - m is an M-neighbor (vertex in a packing element containing v, m ≠ v)
   - x is the third vertex
3. The edge {v, x} is in every triangle of T_v (when x is the same)
4. By the sunflower structure, at most 2 distinct values of x appear
5. So E = {{v, x1}, {v, x2}} covers all of T_v

FORMAL CLAIM: ∃ E with |E| ≤ 2, E ⊆ G.edgeFinset, ∀ t ∈ T_v, ∃ e ∈ E, e ∈ t.sym2
-/
lemma support_sunflower (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (v : V) (h_shared : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da) :
    ∃ E : Finset (Sym2 V),
      E.card ≤ 2 ∧
      E ⊆ G.edgeFinset ∧
      ∀ t ∈ trianglesSharingMEdgeAt G M v, ∃ e ∈ E, e ∈ t.sym2 := by
  -- Strategy: Use the M-edges containing v as the covering set
  -- Since v is in exactly 2 packing elements, there are at most 4 M-edges at v
  -- But we claim 2 edges suffice due to the sunflower structure

  -- Actually, simpler approach: use ANY 2 edges from v
  -- Every triangle in trianglesSharingMEdgeAt contains v by definition
  -- So any edge of the triangle contains v OR is opposite to v

  -- Let's think about what edges each triangle has:
  -- t = {v, m, x} has edges {v,m}, {v,x}, {m,x}
  -- At least one of {v,m} or {v,x} contains v and is NOT the opposite

  -- The M-edge {v,m} is the one that's in M_edges_at
  -- But we want to cover with potentially non-M edges

  -- Key insight: every triangle t at v contains the edge {v, x} where x ≠ m
  -- If all triangles share the same x, one edge suffices
  -- Otherwise, collect all x's and pick 2 that cover everything

  -- For now, let's use a simple existential construction
  -- and let Aristotle find the witnesses

  -- Degenerate case: if no triangles at v, empty set works
  by_cases h_empty : trianglesSharingMEdgeAt G M v = ∅
  · use ∅
    simp [h_empty]

  -- Non-empty case: extract structure
  push_neg at h_empty
  obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr h_empty

  -- t is a triangle containing v with an M-edge at v
  have ht_tri : t ∈ G.cliqueFinset 3 := by
    simp only [trianglesSharingMEdgeAt, Finset.mem_filter] at ht
    exact ht.1

  -- v ∈ t (since t shares an M-edge containing v)
  have hv_in_t : v ∈ t := by
    simp only [trianglesSharingMEdgeAt, Finset.mem_filter] at ht
    obtain ⟨e, he_M, he_t⟩ := ht.2
    simp only [M_edges_at, Finset.mem_biUnion, Finset.mem_filter] at he_M
    obtain ⟨X, hX, he_X, hv_e⟩ := he_M
    -- e ∈ t.sym2 means both endpoints of e are in t
    simp only [Finset.mem_sym2_iff] at he_t
    obtain ⟨a, b, hab, ha, hb, he_eq⟩ := he_t
    -- v ∈ e means v = a or v = b
    simp only [he_eq, Sym2.mem_iff] at hv_e
    cases hv_e with
    | inl h => exact h ▸ ha
    | inr h => exact h ▸ hb

  -- Pick any two edges from v in t
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht_tri).2

  -- t \ {v} has 2 elements (the other vertices)
  have h_other : (t \ {v}).card = 2 := by
    rw [Finset.card_sdiff (Finset.singleton_subset_iff.mpr hv_in_t)]
    rw [ht_card, Finset.card_singleton]

  -- Get the two other vertices
  obtain ⟨x, hx, y, hy, hxy, h_eq⟩ := Finset.card_eq_two.mp h_other

  -- Define the covering edges
  let e1 : Sym2 V := s(v, x)
  let e2 : Sym2 V := s(v, y)

  -- These are graph edges (since t is a clique)
  have h_clique := (SimpleGraph.mem_cliqueFinset_iff.mp ht_tri).1

  have hx_in_t : x ∈ t := by
    have := Finset.mem_sdiff.mp hx
    exact this.1

  have hy_in_t : y ∈ t := by
    have := Finset.mem_sdiff.mp hy
    exact this.1

  have hx_ne_v : x ≠ v := by
    have := Finset.mem_sdiff.mp hx
    simp at this
    exact this.2

  have hy_ne_v : y ≠ v := by
    have := Finset.mem_sdiff.mp hy
    simp at this
    exact this.2

  have he1_adj : G.Adj v x := h_clique hv_in_t hx_in_t hx_ne_v.symm
  have he2_adj : G.Adj v y := h_clique hv_in_t hy_in_t hy_ne_v.symm

  have he1_edge : e1 ∈ G.edgeFinset := by
    simp only [SimpleGraph.mem_edgeFinset]
    exact he1_adj

  have he2_edge : e2 ∈ G.edgeFinset := by
    simp only [SimpleGraph.mem_edgeFinset]
    exact he2_adj

  -- The covering set
  use {e1, e2}

  constructor
  · -- Card ≤ 2
    by_cases h : e1 = e2
    · simp [h]
    · rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
      simp [h]

  constructor
  · -- Subset of edgeFinset
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    cases he with
    | inl h => exact h ▸ he1_edge
    | inr h => exact h ▸ he2_edge

  · -- Covers all triangles
    intro t' ht'

    -- t' contains v (same argument as above)
    have hv_in_t' : v ∈ t' := by
      simp only [trianglesSharingMEdgeAt, Finset.mem_filter] at ht'
      obtain ⟨e, he_M, he_t'⟩ := ht'.2
      simp only [M_edges_at, Finset.mem_biUnion, Finset.mem_filter] at he_M
      obtain ⟨X, hX, he_X, hv_e⟩ := he_M
      simp only [Finset.mem_sym2_iff] at he_t'
      obtain ⟨a, b, hab, ha, hb, he_eq⟩ := he_t'
      simp only [he_eq, Sym2.mem_iff] at hv_e
      cases hv_e with
      | inl h => exact h ▸ ha
      | inr h => exact h ▸ hb

    -- t' is a triangle, so it has 3 vertices
    have ht'_tri : t' ∈ G.cliqueFinset 3 := by
      simp only [trianglesSharingMEdgeAt, Finset.mem_filter] at ht'
      exact ht'.1

    have ht'_card : t'.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht'_tri).2

    -- t' = {v, a, b} for some a, b
    have h_other' : (t' \ {v}).card = 2 := by
      rw [Finset.card_sdiff (Finset.singleton_subset_iff.mpr hv_in_t')]
      rw [ht'_card, Finset.card_singleton]

    obtain ⟨a, ha, b, hb, hab', h_eq'⟩ := Finset.card_eq_two.mp h_other'

    have ha_in_t' : a ∈ t' := (Finset.mem_sdiff.mp ha).1
    have hb_in_t' : b ∈ t' := (Finset.mem_sdiff.mp hb).1
    have ha_ne_v : a ≠ v := (Finset.mem_sdiff.mp ha).2 (Finset.mem_singleton.mpr rfl)
    have hb_ne_v : b ≠ v := (Finset.mem_sdiff.mp hb).2 (Finset.mem_singleton.mpr rfl)

    -- The edge {v, a} is in t'.sym2
    have hva_in_t' : s(v, a) ∈ t'.sym2 := by
      simp only [Finset.mem_sym2_iff]
      exact ⟨v, a, ha_ne_v.symm, hv_in_t', ha_in_t', rfl⟩

    -- Now we need to show one of e1, e2 is in t'.sym2
    -- This requires showing a = x or a = y or b = x or b = y

    -- IMPORTANT: This is where the "sunflower" structure matters.
    -- We constructed e1, e2 from ONE triangle t.
    -- For other triangles t', we need to show they share an edge with t.

    -- The key insight: ALL triangles in trianglesSharingMEdgeAt share an M-edge at v.
    -- Two triangles sharing an M-edge share at least 2 vertices (the M-edge endpoints).
    -- Since v is in both, they share v and the M-neighbor m.

    -- Wait, but different triangles might use DIFFERENT M-edges at v.
    -- Then they only share v.

    -- The sunflower argument says: external vertices cluster.
    -- For Aristotle to prove this, we need a more careful construction.

    -- Let's use a different approach: for EACH triangle t' at v,
    -- pick an edge {v, z} where z is the third vertex (not the M-neighbor).
    -- Then show at most 2 distinct z's appear.

    -- For now, use sorry and let Aristotle handle the combinatorics
    sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: τ AT SHARED VERTEX ≤ 2
-- ══════════════════════════════════════════════════════════════════════════════

/-- τ(trianglesSharingMEdgeAt v) ≤ 2 follows from support_sunflower -/
lemma tau_at_shared_vertex_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (v : V) (h_shared : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da) :
    triangleCoveringNumberOn G (trianglesSharingMEdgeAt G M v) ≤ 2 := by
  obtain ⟨E, hE_card, hE_sub, hE_covers⟩ := support_sunflower G M hM cfg v h_shared
  unfold triangleCoveringNumberOn
  have h_mem : E ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ trianglesSharingMEdgeAt G M v, ∃ e ∈ E', e ∈ t.sym2) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hE_sub, hE_covers⟩
  have h_min_le : (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ trianglesSharingMEdgeAt G M v, ∃ e ∈ E', e ∈ t.sym2)).image Finset.card |>.min ≤ E.card := by
    exact Finset.min_le (Finset.mem_image_of_mem Finset.card h_mem)
  calc
    triangleCoveringNumberOn G (trianglesSharingMEdgeAt G M v)
      = (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ trianglesSharingMEdgeAt G M v, ∃ e ∈ E', e ∈ t.sym2)).image Finset.card |>.min |>.getD 0 := rfl
    _ ≤ E.card := by
        cases h : (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ trianglesSharingMEdgeAt G M v, ∃ e ∈ E', e ∈ t.sym2)).image Finset.card |>.min with
        | none => simp
        | some m => simp only [Option.getD]; exact WithTop.coe_le_coe.mp (h ▸ h_min_le)
    _ ≤ 2 := hE_card

end
