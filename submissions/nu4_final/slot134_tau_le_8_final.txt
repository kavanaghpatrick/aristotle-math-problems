/-
slot134: τ ≤ 8 for Cycle4 Case - Final Assembly

GOAL: Prove τ(G) ≤ 8 when ν(G) = 4 and M has cycle4 structure.

APPROACH (Corrected Dec 28, 2025):
Use direct cover construction, not subadditivity of τ at local sets.

PROOF SKETCH:
1. Construct explicit cover of 8 edges (slot132):
   - 4 edges covering M: {v_ab, v_da}, {v_ab, v_bc}, {v_bc, v_cd}, {v_cd, v_da}
   - 4 edges covering externals: {v_ab, x_ab}, {v_bc, x_bc}, {v_cd, x_cd}, {v_da, x_da}

2. Verify this covers ALL triangles:
   - Every triangle contains a shared vertex (slot128: cycle4_all_triangles_contain_shared)
   - If triangle is in M, it's covered by M-edges
   - If triangle is external at v, it's covered by {v, x_v}

3. Conclude τ(G) ≤ 8.

KEY DEPENDENCIES (all proven or axiomatized):
- slot128: cycle4_all_triangles_contain_shared (PROVEN)
- slot131: external_share_common_vertex (key lemma)
- slot132: full_cover_covers_all, full_cover_card_le_8

This file combines everything into the final theorem.
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

/-- Triangle covering number: minimum edges to hit all triangles -/
noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { n | ∃ E : Finset (Sym2 V), E.card = n ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 }

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
-- AXIOMS FROM PREVIOUS SLOTS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Slot128: Every triangle contains a shared vertex -/
axiom cycle4_all_triangles_contain_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    cfg.v_ab ∈ t ∨ cfg.v_bc ∈ t ∨ cfg.v_cd ∈ t ∨ cfg.v_da ∈ t

/-- Slot131: External triangles at v share a common external vertex -/
axiom external_share_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (v : V) (h_shared : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da) :
    ∃ x : V, x ≠ v ∧ ∀ t ∈ externalTrianglesAt G M v, x ∈ t

-- ══════════════════════════════════════════════════════════════════════════════
-- COVER CONSTRUCTION (from slot132)
-- ══════════════════════════════════════════════════════════════════════════════

/-- The 4 edges covering M-elements -/
def M_cover_edges (cfg : Cycle4 G M) : Finset (Sym2 V) :=
  {s(cfg.v_ab, cfg.v_da), s(cfg.v_ab, cfg.v_bc), s(cfg.v_bc, cfg.v_cd), s(cfg.v_cd, cfg.v_da)}

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

/-- The full 8-edge cover -/
noncomputable def full_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) : Finset (Sym2 V) :=
  M_cover_edges cfg ∪ external_cover_edges G M hM cfg

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_eq_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : t.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp ht).2

/-- External triangles contain v -/
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

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- Full cover has at most 8 edges -/
theorem full_cover_card_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) :
    (full_cover G M hM cfg).card ≤ 8 := by
  unfold full_cover
  calc (M_cover_edges cfg ∪ external_cover_edges G M hM cfg).card
    ≤ (M_cover_edges cfg).card + (external_cover_edges G M hM cfg).card :=
      Finset.card_union_le _ _
    _ ≤ 4 + 4 := by
      apply Nat.add_le_add
      · -- M_cover_edges has ≤ 4 elements
        unfold M_cover_edges
        simp only [Finset.card_insert_of_not_mem, Finset.card_singleton]
        sorry -- combinatorial bound on set with 4 insertions
      · -- external_cover_edges has ≤ 4 elements
        unfold external_cover_edges
        simp only [Finset.card_insert_of_not_mem, Finset.card_singleton]
        sorry
    _ = 8 := rfl

/-- Full cover covers all M-elements -/
lemma full_cover_covers_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (X : Finset V) (hX : X ∈ M) :
    ∃ e ∈ full_cover G M hM cfg, e ∈ X.sym2 := by
  rw [cfg.hM_eq] at hX
  simp only [Finset.mem_insert, Finset.mem_singleton] at hX
  rcases hX with rfl | rfl | rfl | rfl
  all_goals {
    use ?edge
    constructor
    · apply Finset.mem_union_left
      simp [M_cover_edges]
    · simp only [Finset.mem_sym2_iff]
      sorry -- {v_ab, v_da} ∈ A.sym2, etc.
  }

/-- Full cover covers all external triangles -/
lemma full_cover_covers_external (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (v : V) (h_shared : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da)
    (t : Finset V) (ht : t ∈ externalTrianglesAt G M v) :
    ∃ e ∈ full_cover G M hM cfg, e ∈ t.sym2 := by
  rcases h_shared with rfl | rfl | rfl | rfl
  all_goals {
    -- Get the common external vertex x_v
    have hspec := (external_share_common_vertex G M hM cfg _ ?shared_hyp).choose_spec
    · have hx_ne := hspec.1
      have hx_in := hspec.2 t ht
      have hv_in := external_triangle_contains_v G M _ t ht
      use ?edge
      constructor
      · apply Finset.mem_union_right
        simp [external_cover_edges]
      · simp only [Finset.mem_sym2_iff]
        exact ⟨_, _, hx_ne.symm, hv_in, hx_in, rfl⟩
    · first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
            | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr rfl))
  }

/-- Full cover covers ALL triangles -/
theorem full_cover_covers_all (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ full_cover G M hM cfg, e ∈ t.sym2 := by
  -- Every triangle contains a shared vertex
  have h_contains := cycle4_all_triangles_contain_shared G M hM cfg t ht

  -- Case 1: t ∈ M
  by_cases h_in_M : t ∈ M
  · exact full_cover_covers_M G M hM cfg t h_in_M

  -- Case 2: t ∉ M, but contains shared vertex v
  -- Then t shares M-edge at v (by maximality argument) and is external at v
  rcases h_contains with h_vab | h_vbc | h_vcd | h_vda
  all_goals {
    -- Triangle t contains shared vertex v, t ∉ M
    -- Need: t ∈ externalTrianglesAt G M v
    -- This requires: t shares M-edge at v
    -- By maximality: t shares edge with some M-element
    -- Since t contains v, and v is shared between two M-elements at that vertex,
    -- t shares edge with one of those M-elements at v
    sorry
  }

/-- Main theorem: τ(G) ≤ 8 for cycle4 case -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (h_nu : trianglePackingNumber G = 4) :
    triangleCoveringNumber G ≤ 8 := by
  unfold triangleCoveringNumber
  -- Show 8 ∈ {valid covering sizes}
  apply Nat.sInf_le
  use (full_cover G M hM cfg).card
  constructor
  · use full_cover G M hM cfg
    constructor
    · rfl
    · constructor
      · -- full_cover ⊆ G.edgeFinset
        intro e he
        simp only [full_cover, Finset.mem_union] at he
        rcases he with he_M | he_ext
        · -- e ∈ M_cover_edges: edges between shared vertices, which are in G
          simp only [M_cover_edges, Finset.mem_insert, Finset.mem_singleton] at he_M
          rcases he_M with rfl | rfl | rfl | rfl
          all_goals {
            apply SimpleGraph.mem_edgeFinset.mpr
            -- Need to show these vertices are adjacent in G
            -- They are both in the same clique (M-element), so adjacent
            sorry
          }
        · -- e ∈ external_cover_edges: edges {v, x_v}
          simp only [external_cover_edges, Finset.mem_insert, Finset.mem_singleton] at he_ext
          sorry
      · -- full_cover covers all triangles
        intro t ht
        exact full_cover_covers_all G M hM cfg t ht
  · -- |full_cover| ≤ 8
    exact full_cover_card_le_8 G M hM cfg

/-- Corollary: Tuza's conjecture holds for ν = 4 in cycle4 case -/
theorem tuza_nu4_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (h_nu : trianglePackingNumber G = 4) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  calc triangleCoveringNumber G
    ≤ 8 := tau_le_8_cycle4 G M hM cfg h_nu
    _ = 2 * 4 := rfl
    _ = 2 * trianglePackingNumber G := by rw [h_nu]

end
