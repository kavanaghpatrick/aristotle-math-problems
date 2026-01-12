/-
Tuza ν=4 Strategy - Slot 373: PATH_4 τ ≤ 8 Main Theorem

DEPENDS ON:
  - slot370 (triangle_helly_vertex) - PROVEN
  - slot371 (fan_apex_exists)
  - slot372 (two_edges_cover_X)
  - slot182 (two_externals_share_edge) - PROVEN
  - slot347 (bridge_covered_by_adjacent) - PROVEN

THEOREM: For PATH_4 configuration with ν = 4, we have τ ≤ 8.

PATH_4 STRUCTURE:
  M = {A, B, C, D} where:
    A = {v1, a1, a2}     (endpoint)
    B = {v1, v2, b}      (middle)
    C = {v2, v3, c}      (middle)
    D = {v3, d1, d2}     (endpoint)

EXPLICIT 8-EDGE COVER (from multi-agent debate):
  For A: {v1, a1}, {a1, a2}
  For B: {v1, v2}, {v1, b}
  For C: {v2, v3}, {v2, c}
  For D: {v3, d1}, {d1, d2}

PROOF SKETCH:
1. By two_edges_cover_X_externals (slot372), for each X ∈ M,
   there exist 2 edges of X covering X and all X-externals
2. Bridges are covered by bridge_covered_by_adjacent (slot347)
3. Total edges needed: 4 × 2 = 8
4. Construct explicit cover and verify all triangles hit

COVERAGE VERIFICATION:
- M-elements: Each X contains at least one of its designated edges ✓
- X-externals: By slot372, covered by 2 edges of X ✓
- Bridges: By slot347, covered by adjacent edges ✓
- Every triangle shares edge with some X ∈ M (by maximality of M) ✓

TIER: 2 (Depends on slot371, slot372)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset Classical

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (T S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ T ∧ v ∈ T ∧ u ∈ S ∧ v ∈ S

/-- PATH_4 configuration: A-B-C-D with spine v1-v2-v3 -/
structure PATH4Config (V : Type*) where
  -- Spine vertices
  v1 v2 v3 : V
  -- Private vertices
  a1 a2 : V  -- A's private vertices
  b : V      -- B's private vertex
  c : V      -- C's private vertex
  d1 d2 : V  -- D's private vertices
  -- All distinct
  all_distinct : [v1, v2, v3, a1, a2, b, c, d1, d2].Nodup
  -- The four triangles
  A : Finset V := {v1, a1, a2}
  B : Finset V := {v1, v2, b}
  C : Finset V := {v2, v3, c}
  D : Finset V := {v3, d1, d2}

/-- The packing M = {A, B, C, D} -/
def PATH4Config.M [DecidableEq V] (cfg : PATH4Config V) : Finset (Finset V) :=
  {cfg.A, cfg.B, cfg.C, cfg.D}

/-- Edge cover: a set of edges (2-element subsets) -/
def isEdgeCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Finset V)) : Prop :=
  (∀ e ∈ E, e.card = 2) ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ⊆ T

/-- Triangle cover number τ(G) -/
def triangleCoverNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n | ∃ E : Finset (Finset V), E.card = n ∧ isEdgeCover G E}

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: PATH_4 Properties
-- ══════════════════════════════════════════════════════════════════════════════

/-- A, B, C, D are all triangles (card 3) -/
lemma path4_triangles_card [DecidableEq V] (cfg : PATH4Config V) :
    cfg.A.card = 3 ∧ cfg.B.card = 3 ∧ cfg.C.card = 3 ∧ cfg.D.card = 3 := by
  have hnd := cfg.all_distinct
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.nodup_nil,
             and_true, ne_eq] at hnd
  obtain ⟨⟨hv1_ne, _⟩, ⟨hv2_ne, _⟩, ⟨hv3_ne, _⟩, ⟨ha1_ne, _⟩, ⟨ha2_ne, _⟩,
          ⟨hb_ne, _⟩, ⟨hc_ne, _⟩, ⟨hd1_ne, _⟩, _⟩ := hnd
  constructor
  · -- A = {v1, a1, a2}
    simp only [PATH4Config.A, card_insert_of_not_mem, card_singleton]
    simp [mem_insert, mem_singleton]
    constructor
    · exact hv1_ne.2.2.1.symm
    · exact hv1_ne.2.2.2.1.symm
  constructor
  · -- B = {v1, v2, b}
    simp only [PATH4Config.B, card_insert_of_not_mem, card_singleton]
    simp [mem_insert, mem_singleton]
    constructor
    · exact hv1_ne.1.symm
    · exact hv1_ne.2.2.2.2.1.symm
  constructor
  · -- C = {v2, v3, c}
    simp only [PATH4Config.C, card_insert_of_not_mem, card_singleton]
    simp [mem_insert, mem_singleton]
    constructor
    · exact hv2_ne.1.symm
    · exact hv2_ne.2.2.2.2.1.symm
  · -- D = {v3, d1, d2}
    simp only [PATH4Config.D, card_insert_of_not_mem, card_singleton]
    simp [mem_insert, mem_singleton]
    constructor
    · exact hv3_ne.2.2.2.2.2.1.symm
    · exact hv3_ne.2.2.2.2.2.2.symm

/-- M has exactly 4 elements -/
lemma path4_M_card [DecidableEq V] (cfg : PATH4Config V) : cfg.M.card = 4 := by
  simp only [PATH4Config.M]
  -- Need to show A, B, C, D are all distinct
  sorry

/-- Adjacent triangles share exactly one vertex -/
lemma path4_adjacent_share_one [DecidableEq V] (cfg : PATH4Config V) :
    (cfg.A ∩ cfg.B).card = 1 ∧ (cfg.B ∩ cfg.C).card = 1 ∧ (cfg.C ∩ cfg.D).card = 1 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- THE EXPLICIT 8-EDGE COVER
-- ══════════════════════════════════════════════════════════════════════════════

/-- The explicit 8-edge cover for PATH_4 -/
def path4_cover [DecidableEq V] (cfg : PATH4Config V) : Finset (Finset V) :=
  { {cfg.v1, cfg.a1},   -- A edge 1
    {cfg.a1, cfg.a2},   -- A edge 2 (base)
    {cfg.v1, cfg.v2},   -- B edge 1 (spine)
    {cfg.v1, cfg.b},    -- B edge 2
    {cfg.v2, cfg.v3},   -- C edge 1 (spine)
    {cfg.v2, cfg.c},    -- C edge 2
    {cfg.v3, cfg.d1},   -- D edge 1
    {cfg.d1, cfg.d2} }  -- D edge 2 (base)

/-- The cover has exactly 8 edges -/
lemma path4_cover_card [DecidableEq V] (cfg : PATH4Config V) :
    (path4_cover cfg).card = 8 := by
  simp only [path4_cover]
  -- Need to show all 8 edges are distinct
  sorry

/-- Each edge in the cover has cardinality 2 -/
lemma path4_cover_edges [DecidableEq V] (cfg : PATH4Config V) :
    ∀ e ∈ path4_cover cfg, e.card = 2 := by
  intro e he
  simp only [path4_cover, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp [card_insert_of_not_mem]
    have hnd := cfg.all_distinct
    simp only [List.nodup_cons] at hnd
    sorry -- distinctness from all_distinct

-- ══════════════════════════════════════════════════════════════════════════════
-- COVERAGE LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A is covered by the cover -/
lemma path4_cover_hits_A [DecidableEq V] (cfg : PATH4Config V) :
    ∃ e ∈ path4_cover cfg, e ⊆ cfg.A := by
  use {cfg.v1, cfg.a1}
  constructor
  · simp [path4_cover]
  · simp [PATH4Config.A, subset_iff, mem_insert, mem_singleton]

/-- B is covered by the cover -/
lemma path4_cover_hits_B [DecidableEq V] (cfg : PATH4Config V) :
    ∃ e ∈ path4_cover cfg, e ⊆ cfg.B := by
  use {cfg.v1, cfg.v2}
  constructor
  · simp [path4_cover]
  · simp [PATH4Config.B, subset_iff, mem_insert, mem_singleton]

/-- C is covered by the cover -/
lemma path4_cover_hits_C [DecidableEq V] (cfg : PATH4Config V) :
    ∃ e ∈ path4_cover cfg, e ⊆ cfg.C := by
  use {cfg.v2, cfg.v3}
  constructor
  · simp [path4_cover]
  · simp [PATH4Config.C, subset_iff, mem_insert, mem_singleton]

/-- D is covered by the cover -/
lemma path4_cover_hits_D [DecidableEq V] (cfg : PATH4Config V) :
    ∃ e ∈ path4_cover cfg, e ⊆ cfg.D := by
  use {cfg.v3, cfg.d1}
  constructor
  · simp [path4_cover]
  · simp [PATH4Config.D, subset_iff, mem_insert, mem_singleton]

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: PATH_4 has τ ≤ 8

PROOF SKETCH:
1. Construct explicit 8-edge cover (path4_cover)
2. Show it covers all M-elements (A, B, C, D)
3. Show it covers all X-externals (by two_edges_cover_X)
4. Show it covers all bridges (by bridge_covered_by_adjacent)
5. Every triangle shares edge with some M-element (maximality)
6. Therefore cover hits all triangles
7. Cover has 8 edges, so τ ≤ 8
-/
theorem path4_tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : PATH4Config V)
    (hG : ∀ x y, x ∈ cfg.A ∪ cfg.B ∪ cfg.C ∪ cfg.D → y ∈ cfg.A ∪ cfg.B ∪ cfg.C ∪ cfg.D →
          x ≠ y → (∃ T ∈ ({cfg.A, cfg.B, cfg.C, cfg.D} : Finset (Finset V)), x ∈ T ∧ y ∈ T) → G.Adj x y)
    (hM : isMaxPacking G cfg.M)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4) :
    ∃ E : Finset (Finset V), E.card ≤ 8 ∧ isEdgeCover G E := by
  use path4_cover cfg
  constructor
  · -- Cover has ≤ 8 edges
    sorry -- From path4_cover_card
  · -- Cover is an edge cover
    constructor
    · exact path4_cover_edges cfg
    · -- Every triangle is hit
      intro T hT
      -- Case: T ∈ M
      -- Case: T is external of some X
      -- Case: T is a bridge
      sorry

/-- Corollary: τ(G) ≤ 8 for any PATH_4 configuration -/
theorem path4_triangle_cover_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : PATH4Config V)
    (hM : isMaxPacking G cfg.M)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4) :
    triangleCoverNumber G ≤ 8 := by
  sorry

end
