/-
  slot217_adaptive_8_cover.lean

  THEOREM: τ ≤ 8 for cycle_4 via adaptive 2-covers at shared vertices

  APPROACH:
  1. Every triangle contains a shared vertex v ∈ {v_ab, v_bc, v_cd, v_da}
  2. At each shared vertex, we can cover ALL triangles with 2 edges
  3. Total: 4 vertices × 2 edges = 8 edges

  KEY LEMMA (exists_two_cover_at_shared_vertex):
  At each shared vertex v, there exist 2 edges through v that cover all triangles at v.

  This is NOT the same as Pattern 1 (local_cover_le_2) which was FALSE!
  Pattern 1 used M_edges_at (only edges from M-elements).
  Here we use ALL edges at v, not just M-edges.

  FALSE PATTERNS AVOIDED:
  - Pattern 1: We don't restrict to M_edges_at
  - Pattern 9: We don't use fixed 8-edge M-subset
  - Pattern 17: We don't assume fan apex covers all sharing

  DIFFICULTY: 4/5
  SUCCESS PROBABILITY: 50%
-/

import Mathlib

open scoped Classical

set_option maxHeartbeats 400000

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- BASIC DEFINITIONS
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

-- ══════════════════════════════════════════════════════════════════════════════
-- SHARED VERTICES AND TRIANGLES
-- ══════════════════════════════════════════════════════════════════════════════

/-- The set of shared vertices -/
def sharedVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4 G M) : Finset V :=
  {cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da}

/-- Triangles containing vertex v -/
def trianglesAt (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

/-- Edges incident to vertex v -/
def edgesAt (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => v ∈ e)

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 1: Every triangle contains a shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle contains at least one shared vertex -/
lemma triangle_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ v ∈ sharedVertices G M cfg, v ∈ t := by
  -- By maximality of M, triangle t must share ≥2 vertices with some M-element X
  -- Each M-element X contains exactly 2 shared vertices (e.g., A contains v_ab, v_da)
  -- Therefore t shares at least one shared vertex with X
  simp only [sharedVertices]
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 2: 2-cover exists at each shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- At each shared vertex v, there exist 2 edges that cover ALL triangles at v.

This is the key structural lemma. Unlike Pattern 1 (which restricted to M-edges),
we allow ANY edges at v, giving more flexibility.

Proof sketch:
- Let v = v_ab (other cases symmetric)
- v_ab is in M-elements A and B
- Any triangle T at v_ab either:
  1. T = A: covered by any edge of A through v_ab
  2. T = B: covered by any edge of B through v_ab
  3. T is external: T shares edge with A or B through v_ab

For case 3, externals at v_ab form a "star" around v_ab.
Each external shares an edge {v_ab, x} with A or with B.
At most 2 such "arms" exist (one for A's neighbors, one for B's neighbors).
-/
lemma exists_two_cover_at_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (v : V) (hv : v ∈ sharedVertices G M cfg) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ edgesAt G v ∧
      ∀ t ∈ trianglesAt G v, ∃ e ∈ E', e ∈ t.sym2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- COVER CONSTRUCTION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Select a 2-cover at each shared vertex using Choice -/
noncomputable def twoCoverAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ sharedVertices G M cfg) :
    Finset (Sym2 V) :=
  (exists_two_cover_at_shared G M hM cfg v hv).choose

lemma twoCoverAt_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ sharedVertices G M cfg) :
    (twoCoverAt G M hM cfg v hv).card ≤ 2 :=
  (exists_two_cover_at_shared G M hM cfg v hv).choose_spec.1

lemma twoCoverAt_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ sharedVertices G M cfg) :
    twoCoverAt G M hM cfg v hv ⊆ edgesAt G v :=
  (exists_two_cover_at_shared G M hM cfg v hv).choose_spec.2.1

lemma twoCoverAt_covers (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ sharedVertices G M cfg) :
    ∀ t ∈ trianglesAt G v, ∃ e ∈ twoCoverAt G M hM cfg v hv, e ∈ t.sym2 :=
  (exists_two_cover_at_shared G M hM cfg v hv).choose_spec.2.2

-- ══════════════════════════════════════════════════════════════════════════════
-- 8-COVER CONSTRUCTION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Shared vertices have cardinality at most 4 -/
lemma shared_vertices_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4 G M) :
    (sharedVertices G M cfg).card ≤ 4 := by
  simp only [sharedVertices]
  -- {v_ab, v_bc, v_cd, v_da} has at most 4 elements (trivial set cardinality)
  sorry

/-- The 8-edge cover: union of 2-covers -/
noncomputable def eightEdgeCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) : Finset (Sym2 V) :=
  (sharedVertices G M cfg).attach.biUnion (fun ⟨v, hv⟩ => twoCoverAt G M hM cfg v hv)

/-- The 8-edge cover has at most 8 edges -/
lemma eight_edge_cover_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    (eightEdgeCover G M hM cfg).card ≤ 8 := by
  simp only [eightEdgeCover]
  calc ((sharedVertices G M cfg).attach.biUnion (fun ⟨v, hv⟩ => twoCoverAt G M hM cfg v hv)).card
      ≤ (sharedVertices G M cfg).attach.sum (fun ⟨v, hv⟩ => (twoCoverAt G M hM cfg v hv).card) :=
        Finset.card_biUnion_le
    _ ≤ (sharedVertices G M cfg).attach.sum (fun _ => 2) := by
        apply Finset.sum_le_sum
        intro ⟨v, hv⟩ _
        exact twoCoverAt_card G M hM cfg v hv
    _ = 2 * (sharedVertices G M cfg).attach.card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
    _ = 2 * (sharedVertices G M cfg).card := by simp [Finset.card_attach]
    _ ≤ 2 * 4 := Nat.mul_le_mul_left 2 (shared_vertices_card G M cfg)
    _ = 8 := by ring

/-- The 8-edge cover is a subset of graph edges -/
lemma eight_edge_cover_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    eightEdgeCover G M hM cfg ⊆ G.edgeFinset := by
  simp only [eightEdgeCover]
  intro e he
  simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists] at he
  obtain ⟨v, hv, he_cover⟩ := he
  have h_subset := twoCoverAt_subset G M hM cfg v hv
  have h_in_edges := h_subset he_cover
  simp only [edgesAt, Finset.mem_filter] at h_in_edges
  exact h_in_edges.1

/-- The 8-edge cover covers all triangles -/
lemma eight_edge_cover_covers (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ eightEdgeCover G M hM cfg, e ∈ t.sym2 := by
  intro t ht
  -- t contains a shared vertex
  obtain ⟨v, hv_shared, hv_in_t⟩ := triangle_contains_shared_vertex G M hM cfg t ht
  -- t is in trianglesAt G v
  have ht_at_v : t ∈ trianglesAt G v := by
    simp only [trianglesAt, Finset.mem_filter]
    exact ⟨ht, hv_in_t⟩
  -- twoCoverAt covers t
  obtain ⟨e, he_cover, he_t⟩ := twoCoverAt_covers G M hM cfg v hv_shared t ht_at_v
  use e
  constructor
  · simp only [eightEdgeCover, Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists]
    exact ⟨v, hv_shared, he_cover⟩
  · exact he_t

/-- The 8-edge cover is a valid triangle cover -/
lemma eight_edge_cover_is_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    isTriangleCover G (eightEdgeCover G M hM cfg) :=
  ⟨eight_edge_cover_subset G M hM cfg, eight_edge_cover_covers G M hM cfg⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- MAIN THEOREM: τ ≤ 8 for cycle_4 configuration -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- We have a cover with ≤ 8 edges
  have h_cover := eight_edge_cover_is_cover G M hM cfg
  have h_card := eight_edge_cover_card G M hM cfg
  -- τ is the minimum, so τ ≤ 8
  simp only [triangleCoveringNumber]
  sorry

end
