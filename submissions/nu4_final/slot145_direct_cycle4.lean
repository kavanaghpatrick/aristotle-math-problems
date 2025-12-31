/-
Tuza ν=4 Cycle_4: τ ≤ 8 via Direct Cycle_4 Application

APPROACH 4: Direct Cycle_4 Application
=======================================
Skip abstract König machinery entirely. Use the specific structure of cycle_4
to construct an explicit 8-edge cover.

Key insight: At each shared vertex v, we have exactly 2 M-triangles.
Each M-triangle contributes 2 edges through v (excluding the shared edge).
We select 1 edge from each M-triangle at each vertex = 2 edges per vertex × 4 = 8.

From AI research (Dec 30, 2025):
- "Hardcode for cycle_4 structure" - fastest approach
- Uses specific geometry rather than general theory
- Estimated 100-150 lines, 65% success probability

WARNING: Previous "fixed 8-edge" attempts failed. This approach must be ADAPTIVE
to the actual external triangle structure, not fixed diagonal spokes.

GitHub Issue: #32
-/

import Mathlib

open scoped Classical

set_option maxHeartbeats 400000

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from proven slot139)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 CONFIGURATION (with additional structure)
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
  -- Additional: the "private" vertices of each triangle
  a_priv : V  -- the vertex of A not shared with B or D
  b_priv : V  -- the vertex of B not shared with A or C
  c_priv : V  -- the vertex of C not shared with B or D
  d_priv : V  -- the vertex of D not shared with C or A
  hA_eq : A = {v_ab, v_da, a_priv}
  hB_eq : B = {v_ab, v_bc, b_priv}
  hC_eq : C = {v_bc, v_cd, c_priv}
  hD_eq : D = {v_cd, v_da, d_priv}
  -- Distinctness
  h_distinct : v_ab ≠ v_bc ∧ v_bc ≠ v_cd ∧ v_cd ≠ v_da ∧ v_da ≠ v_ab ∧
               a_priv ≠ v_ab ∧ a_priv ≠ v_da ∧
               b_priv ≠ v_ab ∧ b_priv ≠ v_bc ∧
               c_priv ≠ v_bc ∧ c_priv ≠ v_cd ∧
               d_priv ≠ v_cd ∧ d_priv ≠ v_da

-- ══════════════════════════════════════════════════════════════════════════════
-- TRIANGLES CLASSIFICATION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles at vertex v -/
def trianglesAt (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

/-- M-triangles at vertex v -/
def MTrianglesAt (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  M.filter (fun X => v ∈ X)

/-- External triangles at v: triangles containing v but not in M -/
def externalTrianglesAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (trianglesAt G v).filter (fun t => t ∉ M)

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Every triangle shares edge with M
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
  sorry -- PROVEN in slot139

-- ══════════════════════════════════════════════════════════════════════════════
-- EXTERNAL TRIANGLE STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

/-- An external triangle at v must share an edge with one of the M-triangles at v -/
lemma external_shares_edge_with_M_at_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V)
    (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V))
    (t : Finset V) (ht : t ∈ externalTrianglesAt G M v) :
    ∃ X ∈ MTrianglesAt M v, (t ∩ X).card ≥ 2 := by
  -- t shares edge with some M-element (maximality)
  -- t contains v
  -- The M-element must also contain v (since they share edge and both contain v)
  simp only [externalTrianglesAt, Finset.mem_filter, trianglesAt] at ht
  obtain ⟨⟨ht_clique, hv_t⟩, ht_not_M⟩ := ht
  obtain ⟨X, hX_M, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht_clique
  -- X shares ≥2 vertices with t, and v ∈ t
  -- We need to show v ∈ X
  -- If v ∉ X, then t ∩ X ⊆ t \ {v}, which has 2 elements
  -- So (t ∩ X).card ≤ 2, and we need ≥ 2, so = 2
  -- This means t and X share exactly 2 vertices, neither is v
  -- But t contains v, so t = {v, a, b} where {a, b} ⊆ X
  -- Since X is a triangle (3 elements), X = {a, b, c} for some c ≠ v
  -- t and X both triangles, share edge {a,b}, so t could be added to M if v not in any M-element
  -- But t contains v, and v is in some M-element (cfg structure)
  sorry -- Aristotle: case analysis

/-- Edges of M-triangle X through vertex v (excluding edges not through v) -/
def MEdgesThroughV (X : Finset V) (v : V) : Finset (Sym2 V) :=
  (X.filter (· ≠ v)).image (fun u => s(v, u))

/-- An external triangle at v is covered by an edge through v from its shared M-triangle -/
lemma external_covered_by_M_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V)
    (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V))
    (t : Finset V) (ht : t ∈ externalTrianglesAt G M v) :
    ∃ e ∈ (MTrianglesAt M v).biUnion (MEdgesThroughV · v), e ∈ t.sym2 := by
  -- t shares edge with some X ∈ MTrianglesAt M v
  obtain ⟨X, hX_M_v, hX_share⟩ := external_shares_edge_with_M_at_v G M hM cfg v hv t ht
  -- The shared edge contains v (since both t and X contain v and share ≥2 vertices)
  -- So the shared edge is in MEdgesThroughV X v
  sorry -- Aristotle: extract the shared edge

-- ══════════════════════════════════════════════════════════════════════════════
-- COUNTING ARGUMENT: At most 2 edges needed per vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- At each shared vertex, exactly 2 M-triangles meet -/
lemma M_triangles_at_shared (cfg : Cycle4 G M) (v : V)
    (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V)) :
    (MTrianglesAt M v).card = 2 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · -- v = v_ab: M-triangles are A and B
    simp only [MTrianglesAt, cfg.hM_eq]
    have : (({cfg.A, cfg.B, cfg.C, cfg.D} : Finset (Finset V)).filter (fun X => cfg.v_ab ∈ X)) =
           {cfg.A, cfg.B} := by
      ext X
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro ⟨hX, hv_X⟩
        rcases hX with rfl | rfl | rfl | rfl
        · left; rfl
        · right; left; rfl
        · right; right
          -- v_ab ∈ C?
          rw [cfg.hC_eq] at hv_X
          simp at hv_X
          rcases hv_X with rfl | rfl | rfl
          · exact (cfg.h_distinct.1 rfl).elim
          · exact (cfg.h_distinct.2.1 (cfg.h_distinct.1.symm)).elim
          · sorry -- c_priv ≠ v_ab
        · right; right
          rw [cfg.hD_eq] at hv_X
          simp at hv_X
          sorry -- similar
      · intro hX
        rcases hX with rfl | rfl
        · exact ⟨Or.inl rfl, by rw [cfg.hA_eq]; simp⟩
        · exact ⟨Or.inr (Or.inl rfl), by rw [cfg.hB_eq]; simp⟩
    rw [this]
    sorry -- Aristotle: show {A, B}.card = 2
  · sorry -- v_bc case
  · sorry -- v_cd case
  · sorry -- v_da case

/-- Each M-triangle contributes 2 edges through v (the non-shared edges) -/
lemma M_edges_through_v_card (cfg : Cycle4 G M) (v : V) (X : Finset V) (hX : X ∈ M) (hv : v ∈ X) :
    (MEdgesThroughV X v).card = 2 := by
  -- X is a triangle containing v, so X = {v, u, w} for some u ≠ w
  -- MEdgesThroughV X v = {s(v,u), s(v,w)}
  sorry -- Aristotle: unfold and compute

-- ══════════════════════════════════════════════════════════════════════════════
-- ADAPTIVE COVER CONSTRUCTION
-- ══════════════════════════════════════════════════════════════════════════════

/-- At each shared vertex v, select 2 edges that cover all triangles at v.
    This is ADAPTIVE to the graph structure, not a fixed selection. -/
noncomputable def adaptiveCoverAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  -- For each M-triangle X at v, we need to select 1 edge from X through v
  -- The selection depends on which external triangles exist
  -- Key insight: the "link graph" at v has matching ≤ 2, so vertex cover ≤ 2
  -- Each vertex in link graph = edge through v
  -- Vertex cover = set of edges through v that hit all triangles
  let X_at_v := MTrianglesAt M v
  let all_edges := X_at_v.biUnion (MEdgesThroughV · v)
  -- Use Finset.filter to find a minimal cover
  -- For now, we claim such a 2-edge cover exists
  Classical.choose (adaptiveCoverAt_exists G M v)
where
  adaptiveCoverAt_exists (G : SimpleGraph V) [DecidableRel G.Adj]
      (M : Finset (Finset V)) (v : V) :
      ∃ E_v : Finset (Sym2 V), E_v.card ≤ 2 ∧
        ∀ t ∈ trianglesAt G v, ∃ e ∈ E_v, e ∈ t.sym2 := by
    -- This is the core König-lite claim
    sorry

/-- The adaptive cover has size ≤ 2 -/
lemma adaptiveCoverAt_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) :
    (adaptiveCoverAt G M v).card ≤ 2 := by
  unfold adaptiveCoverAt
  exact (Classical.choose_spec (adaptiveCoverAt.adaptiveCoverAt_exists G M v)).1

/-- The adaptive cover covers all triangles at v -/
lemma adaptiveCoverAt_covers (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) :
    ∀ t ∈ trianglesAt G v, ∃ e ∈ adaptiveCoverAt G M v, e ∈ t.sym2 := by
  unfold adaptiveCoverAt
  exact (Classical.choose_spec (adaptiveCoverAt.adaptiveCoverAt_exists G M v)).2

-- ══════════════════════════════════════════════════════════════════════════════
-- EVERY TRIANGLE CONTAINS A SHARED VERTEX
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V), v ∈ t := by
  -- t shares edge with some M-element X
  -- Every edge of every M-element contains a shared vertex (in cycle_4)
  obtain ⟨X, hX, hShare⟩ := triangle_shares_edge_with_packing G M hM t ht
  -- X ∈ {A, B, C, D}, each has structure with shared vertices
  rw [cfg.hM_eq] at hX
  simp only [Finset.mem_insert, Finset.mem_singleton] at hX
  rcases hX with rfl | rfl | rfl | rfl
  · -- X = A = {v_ab, v_da, a_priv}
    -- t shares ≥2 vertices with A
    -- Possible shared pairs: {v_ab, v_da}, {v_ab, a_priv}, {v_da, a_priv}
    -- First two contain shared vertices
    sorry -- Aristotle: case analysis
  · sorry -- X = B
  · sorry -- X = C
  · sorry -- X = D

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: τ ≤ 8 for cycle_4 via direct adaptive cover -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- Construct adaptive cover at each shared vertex
  let E_ab := adaptiveCoverAt G M cfg.v_ab
  let E_bc := adaptiveCoverAt G M cfg.v_bc
  let E_cd := adaptiveCoverAt G M cfg.v_cd
  let E_da := adaptiveCoverAt G M cfg.v_da

  -- Union of all covers
  let E := E_ab ∪ E_bc ∪ E_cd ∪ E_da

  -- Size bound
  have h_card : E.card ≤ 8 := by
    calc E.card
        ≤ E_ab.card + E_bc.card + E_cd.card + E_da.card := by
          unfold_let E
          apply le_trans (Finset.card_union_le _ _)
          apply le_trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
          apply le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _)
          omega
      _ ≤ 2 + 2 + 2 + 2 := by
          apply Nat.add_le_add
          apply Nat.add_le_add
          apply Nat.add_le_add
          · exact adaptiveCoverAt_card G M cfg.v_ab
          · exact adaptiveCoverAt_card G M cfg.v_bc
          · exact adaptiveCoverAt_card G M cfg.v_cd
          · exact adaptiveCoverAt_card G M cfg.v_da
      _ = 8 := by ring

  -- It covers all triangles
  have h_cover : isTriangleCover G E := by
    constructor
    · -- E ⊆ G.edgeFinset
      sorry -- Aristotle: adaptive covers are subsets of edge set
    · -- Covers all triangles
      intro t ht
      obtain ⟨v, hv_shared, hv_t⟩ := triangle_contains_shared G M hM cfg t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv_shared
      have ht_at_v : t ∈ trianglesAt G v := by simp [trianglesAt, ht, hv_t]
      rcases hv_shared with rfl | rfl | rfl | rfl
      · obtain ⟨e, he_mem, he_in⟩ := adaptiveCoverAt_covers G M cfg.v_ab t ht_at_v
        exact ⟨e, by simp [he_mem], he_in⟩
      · obtain ⟨e, he_mem, he_in⟩ := adaptiveCoverAt_covers G M cfg.v_bc t ht_at_v
        exact ⟨e, by simp [he_mem], he_in⟩
      · obtain ⟨e, he_mem, he_in⟩ := adaptiveCoverAt_covers G M cfg.v_cd t ht_at_v
        exact ⟨e, by simp [he_mem], he_in⟩
      · obtain ⟨e, he_mem, he_in⟩ := adaptiveCoverAt_covers G M cfg.v_da t ht_at_v
        exact ⟨e, by simp [he_mem], he_in⟩

  -- Conclude τ ≤ 8
  unfold triangleCoveringNumber
  have h_mem : E.card ∈ G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card := by
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨E, ⟨h_cover.1, h_cover⟩, rfl⟩
  sorry -- Aristotle: conclude from min ≤ E.card ≤ 8

end
