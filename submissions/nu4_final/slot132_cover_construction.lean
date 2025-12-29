/-
slot132: Cover Construction for Cycle4

GOAL: Construct an explicit edge cover of size ≤ 8 for cycle4 case.

STRATEGY (Corrected Dec 28, 2025):
1. Cover each M-element with 1 edge: {e_A, e_B, e_C, e_D} (4 edges)
2. Cover external triangles at each shared vertex with 1 edge: {f_ab, f_bc, f_cd, f_da} (4 edges)
3. Total: 8 edges

WHY THIS WORKS:
- Every triangle shares edge with some M-element (by maximality) or is in M
- M-elements are covered by their own edges
- External triangles at v share common external vertex x (slot131)
- So {v, x} covers all externals at v

KEY LEMMA USED: cycle4_all_triangles_contain_shared (from slot128)
- Every triangle in G contains at least one shared vertex {v_ab, v_bc, v_cd, v_da}
- This means all triangles are in some trianglesSharingMEdgeAt
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

/-- M-edges incident to vertex v -/
def M_edges_at (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion (fun X => X.sym2.filter (fun e => v ∈ e))

/-- Triangles that share an M-edge containing v -/
def trianglesSharingMEdgeAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ∃ e ∈ M_edges_at M v, e ∈ t.sym2)

def externalTrianglesAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  trianglesSharingMEdgeAt G M v \ M

/-- Triangle covering number -/
noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { n | ∃ E : Finset (Sym2 V), E.card = n ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 }

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 STRUCTURE
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
-- SLOT128 PROVEN: Every triangle contains a shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- From slot128: Every triangle in G shares an edge with some packing element.
    Consequence: Every triangle contains at least one shared vertex. -/
axiom cycle4_all_triangles_contain_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    cfg.v_ab ∈ t ∨ cfg.v_bc ∈ t ∨ cfg.v_cd ∈ t ∨ cfg.v_da ∈ t

-- ══════════════════════════════════════════════════════════════════════════════
-- SLOT131: External triangles share common vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- From slot131: External triangles at v share a common external vertex x -/
axiom external_share_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (v : V) (h_shared : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da) :
    ∃ x : V, x ≠ v ∧ ∀ t ∈ externalTrianglesAt G M v, x ∈ t

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_eq_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : t.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp ht).2

/-- Every packing element is a triangle -/
lemma packing_element_is_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (X : Finset V) (hX : X ∈ M) :
    X ∈ G.cliqueFinset 3 := hM.1 hX

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN CONSTRUCTION: 8-edge cover
-- ══════════════════════════════════════════════════════════════════════════════

/--
Construct the covering set of 8 edges.
Let a_priv be the third vertex of A (not v_ab or v_da).
Define:
- e_A := {v_ab, v_da} (one edge of A)
- e_B := {v_ab, v_bc}
- e_C := {v_bc, v_cd}
- e_D := {v_cd, v_da}
These 4 edges cover all M-elements.

For external triangles, use slot131 to get x_v for each shared vertex v:
- f_ab := {v_ab, x_ab}
- f_bc := {v_bc, x_bc}
- f_cd := {v_cd, x_cd}
- f_da := {v_da, x_da}
-/

/-- The 4 edges covering M-elements -/
def M_cover_edges (cfg : Cycle4 G M) : Finset (Sym2 V) :=
  {s(cfg.v_ab, cfg.v_da), s(cfg.v_ab, cfg.v_bc), s(cfg.v_bc, cfg.v_cd), s(cfg.v_cd, cfg.v_da)}

lemma M_cover_edges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4 G M) :
    (M_cover_edges cfg).card ≤ 4 := by
  unfold M_cover_edges
  apply Finset.card_insert_le_of_card_le _ _ _ (Finset.card_insert_le_of_card_le _ _ _ _)
  all_goals simp

/-- M_cover_edges covers every element of M -/
lemma M_cover_covers_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (X : Finset V) (hX : X ∈ M) :
    ∃ e ∈ M_cover_edges cfg, e ∈ X.sym2 := by
  rw [cfg.hM_eq] at hX
  simp only [Finset.mem_insert, Finset.mem_singleton] at hX
  rcases hX with rfl | rfl | rfl | rfl
  · -- X = A, covered by {v_ab, v_da}
    use s(cfg.v_ab, cfg.v_da)
    constructor
    · simp [M_cover_edges]
    · simp only [Finset.mem_sym2_iff]
      have hne : cfg.v_ab ≠ cfg.v_da := cfg.h_vda_ne_vab.symm
      exact ⟨cfg.v_ab, cfg.v_da, hne, cfg.h_vab_A, cfg.h_vda_A, rfl⟩
  · -- X = B, covered by {v_ab, v_bc}
    use s(cfg.v_ab, cfg.v_bc)
    constructor
    · simp [M_cover_edges]
    · simp only [Finset.mem_sym2_iff]
      exact ⟨cfg.v_ab, cfg.v_bc, cfg.h_vab_ne_vbc, cfg.h_vab_B, cfg.h_vbc_B, rfl⟩
  · -- X = C, covered by {v_bc, v_cd}
    use s(cfg.v_bc, cfg.v_cd)
    constructor
    · simp [M_cover_edges]
    · simp only [Finset.mem_sym2_iff]
      exact ⟨cfg.v_bc, cfg.v_cd, cfg.h_vbc_ne_vcd, cfg.h_vbc_C, cfg.h_vcd_C, rfl⟩
  · -- X = D, covered by {v_cd, v_da}
    use s(cfg.v_cd, cfg.v_da)
    constructor
    · simp [M_cover_edges]
    · simp only [Finset.mem_sym2_iff]
      exact ⟨cfg.v_cd, cfg.v_da, cfg.h_vcd_ne_vda, cfg.h_vcd_D, cfg.h_vda_D, rfl⟩

/-- Get external vertex for each shared vertex -/
noncomputable def get_x_ab (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) : V :=
  (external_share_common_vertex G M hM cfg cfg.v_ab (Or.inl rfl)).choose

noncomputable def get_x_bc (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) : V :=
  (external_share_common_vertex G M hM cfg cfg.v_bc (Or.inr (Or.inl rfl))).choose

noncomputable def get_x_cd (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) : V :=
  (external_share_common_vertex G M hM cfg cfg.v_cd (Or.inr (Or.inr (Or.inl rfl)))).choose

noncomputable def get_x_da (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) : V :=
  (external_share_common_vertex G M hM cfg cfg.v_da (Or.inr (Or.inr (Or.inr rfl)))).choose

/-- The 4 edges covering external triangles -/
noncomputable def external_cover_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) : Finset (Sym2 V) :=
  {s(cfg.v_ab, get_x_ab G M hM cfg),
   s(cfg.v_bc, get_x_bc G M hM cfg),
   s(cfg.v_cd, get_x_cd G M hM cfg),
   s(cfg.v_da, get_x_da G M hM cfg)}

lemma external_cover_edges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) :
    (external_cover_edges G M hM cfg).card ≤ 4 := by
  unfold external_cover_edges
  apply Finset.card_insert_le_of_card_le _ _ _ (Finset.card_insert_le_of_card_le _ _ _ _)
  all_goals simp

/-- External triangles contain v and x_v -/
lemma external_triangle_contains_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) (t : Finset V)
    (ht : t ∈ externalTrianglesAt G M v) : v ∈ t := by
  simp only [externalTrianglesAt, trianglesSharingMEdgeAt, Finset.mem_sdiff,
             Finset.mem_filter] at ht
  obtain ⟨⟨_, e, he_M, he_t⟩, _⟩ := ht
  simp only [M_edges_at, Finset.mem_biUnion, Finset.mem_filter] at he_M
  obtain ⟨_, _, _, hv_e⟩ := he_M
  simp only [Finset.mem_sym2_iff] at he_t
  obtain ⟨a, b, _, ha, hb, he_eq⟩ := he_t
  simp only [he_eq, Sym2.mem_iff] at hv_e
  cases hv_e with
  | inl h => exact h ▸ ha
  | inr h => exact h ▸ hb

/-- External cover covers external triangles at v_ab -/
lemma external_cover_covers_vab (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (t : Finset V) (ht : t ∈ externalTrianglesAt G M cfg.v_ab) :
    ∃ e ∈ external_cover_edges G M hM cfg, e ∈ t.sym2 := by
  have hspec := (external_share_common_vertex G M hM cfg cfg.v_ab (Or.inl rfl)).choose_spec
  have hx_ne := hspec.1
  have hx_in := hspec.2 t ht
  have hv_in := external_triangle_contains_v G M cfg.v_ab t ht
  use s(cfg.v_ab, get_x_ab G M hM cfg)
  constructor
  · simp [external_cover_edges]
  · simp only [Finset.mem_sym2_iff]
    exact ⟨cfg.v_ab, get_x_ab G M hM cfg, hx_ne.symm, hv_in, hx_in, rfl⟩

-- Similar lemmas for v_bc, v_cd, v_da (symmetric)
lemma external_cover_covers_vbc (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (t : Finset V) (ht : t ∈ externalTrianglesAt G M cfg.v_bc) :
    ∃ e ∈ external_cover_edges G M hM cfg, e ∈ t.sym2 := by
  have hspec := (external_share_common_vertex G M hM cfg cfg.v_bc
                  (Or.inr (Or.inl rfl))).choose_spec
  have hx_ne := hspec.1
  have hx_in := hspec.2 t ht
  have hv_in := external_triangle_contains_v G M cfg.v_bc t ht
  use s(cfg.v_bc, get_x_bc G M hM cfg)
  constructor
  · simp [external_cover_edges]
  · simp only [Finset.mem_sym2_iff]
    exact ⟨cfg.v_bc, get_x_bc G M hM cfg, hx_ne.symm, hv_in, hx_in, rfl⟩

lemma external_cover_covers_vcd (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (t : Finset V) (ht : t ∈ externalTrianglesAt G M cfg.v_cd) :
    ∃ e ∈ external_cover_edges G M hM cfg, e ∈ t.sym2 := by
  have hspec := (external_share_common_vertex G M hM cfg cfg.v_cd
                  (Or.inr (Or.inr (Or.inl rfl)))).choose_spec
  have hx_ne := hspec.1
  have hx_in := hspec.2 t ht
  have hv_in := external_triangle_contains_v G M cfg.v_cd t ht
  use s(cfg.v_cd, get_x_cd G M hM cfg)
  constructor
  · simp [external_cover_edges]
  · simp only [Finset.mem_sym2_iff]
    exact ⟨cfg.v_cd, get_x_cd G M hM cfg, hx_ne.symm, hv_in, hx_in, rfl⟩

lemma external_cover_covers_vda (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (t : Finset V) (ht : t ∈ externalTrianglesAt G M cfg.v_da) :
    ∃ e ∈ external_cover_edges G M hM cfg, e ∈ t.sym2 := by
  have hspec := (external_share_common_vertex G M hM cfg cfg.v_da
                  (Or.inr (Or.inr (Or.inr rfl)))).choose_spec
  have hx_ne := hspec.1
  have hx_in := hspec.2 t ht
  have hv_in := external_triangle_contains_v G M cfg.v_da t ht
  use s(cfg.v_da, get_x_da G M hM cfg)
  constructor
  · simp [external_cover_edges]
  · simp only [Finset.mem_sym2_iff]
    exact ⟨cfg.v_da, get_x_da G M hM cfg, hx_ne.symm, hv_in, hx_in, rfl⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Full cover
-- ══════════════════════════════════════════════════════════════════════════════

/-- The full cover: M edges + external edges -/
noncomputable def full_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) : Finset (Sym2 V) :=
  M_cover_edges cfg ∪ external_cover_edges G M hM cfg

/-- Full cover has at most 8 edges -/
theorem full_cover_card_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) :
    (full_cover G M hM cfg).card ≤ 8 := by
  unfold full_cover
  calc (M_cover_edges cfg ∪ external_cover_edges G M hM cfg).card
    ≤ (M_cover_edges cfg).card + (external_cover_edges G M hM cfg).card := Finset.card_union_le _ _
    _ ≤ 4 + 4 := Nat.add_le_add (M_cover_edges_card G M cfg) (external_cover_edges_card G M hM cfg)
    _ = 8 := rfl

/-- Full cover covers all triangles -/
theorem full_cover_covers_all (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ full_cover G M hM cfg, e ∈ t.sym2 := by
  -- Case 1: t ∈ M
  by_cases h_in_M : t ∈ M
  · obtain ⟨e, he, he_t⟩ := M_cover_covers_M G M hM cfg t h_in_M
    use e
    constructor
    · exact Finset.mem_union_left _ he
    · exact he_t

  -- Case 2: t ∉ M
  -- t contains some shared vertex (by cycle4_all_triangles_contain_shared)
  have h_contains := cycle4_all_triangles_contain_shared G M hM cfg t ht

  -- t shares an M-edge at that vertex, so t ∈ externalTrianglesAt
  -- (since t ∉ M but t shares M-edge)
  rcases h_contains with h_vab | h_vbc | h_vcd | h_vda
  · -- t contains v_ab
    -- Since t ∉ M and t shares an M-edge at v_ab (because t is a triangle
    -- containing v_ab which shares edge with A or B), t ∈ externalTrianglesAt v_ab
    -- Need to show t ∈ trianglesSharingMEdgeAt v_ab first
    have h_ext : t ∈ externalTrianglesAt G M cfg.v_ab ∨
                 ∃ e ∈ M_cover_edges cfg, e ∈ t.sym2 := by
      -- t is a triangle containing v_ab
      -- If t shares edge with A or B, then t shares M-edge at v_ab
      -- A = {v_ab, v_da, a_priv}, B = {v_ab, v_bc, b_priv}
      -- M-edges at v_ab: {v_ab, v_da}, {v_ab, a_priv}, {v_ab, v_bc}, {v_ab, b_priv}
      -- Any triangle containing v_ab either:
      -- 1. Shares one of these M-edges → t ∈ trianglesSharingMEdgeAt v_ab
      -- 2. Contains v_ab but no other vertex from A ∪ B at v_ab
      --    But by maximality, t shares edge with some M-element
      --    If t shares edge with C or D (at v_bc, v_cd, v_da), then it's external there
      sorry
    rcases h_ext with h_ext_at | ⟨e, he, he_t⟩
    · obtain ⟨e, he, he_t⟩ := external_cover_covers_vab G M hM cfg t h_ext_at
      exact ⟨e, Finset.mem_union_right _ he, he_t⟩
    · exact ⟨e, Finset.mem_union_left _ he, he_t⟩

  · -- Similar for v_bc
    have h_ext : t ∈ externalTrianglesAt G M cfg.v_bc ∨
                 ∃ e ∈ M_cover_edges cfg, e ∈ t.sym2 := sorry
    rcases h_ext with h_ext_at | ⟨e, he, he_t⟩
    · obtain ⟨e, he, he_t⟩ := external_cover_covers_vbc G M hM cfg t h_ext_at
      exact ⟨e, Finset.mem_union_right _ he, he_t⟩
    · exact ⟨e, Finset.mem_union_left _ he, he_t⟩

  · -- Similar for v_cd
    have h_ext : t ∈ externalTrianglesAt G M cfg.v_cd ∨
                 ∃ e ∈ M_cover_edges cfg, e ∈ t.sym2 := sorry
    rcases h_ext with h_ext_at | ⟨e, he, he_t⟩
    · obtain ⟨e, he, he_t⟩ := external_cover_covers_vcd G M hM cfg t h_ext_at
      exact ⟨e, Finset.mem_union_right _ he, he_t⟩
    · exact ⟨e, Finset.mem_union_left _ he, he_t⟩

  · -- Similar for v_da
    have h_ext : t ∈ externalTrianglesAt G M cfg.v_da ∨
                 ∃ e ∈ M_cover_edges cfg, e ∈ t.sym2 := sorry
    rcases h_ext with h_ext_at | ⟨e, he, he_t⟩
    · obtain ⟨e, he, he_t⟩ := external_cover_covers_vda G M hM cfg t h_ext_at
      exact ⟨e, Finset.mem_union_right _ he, he_t⟩
    · exact ⟨e, Finset.mem_union_left _ he, he_t⟩

end
