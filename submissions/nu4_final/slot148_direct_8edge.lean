/-
slot148: Direct 8-Edge Construction for τ ≤ 8 in Cycle_4

THE 8 EDGES:
Ring edges (4): {v_ab,v_da}, {v_ab,v_bc}, {v_bc,v_cd}, {v_cd,v_da}
Private spokes (4): {v_ab,a_priv}, {v_bc,b_priv}, {v_cd,c_priv}, {v_da,d_priv}

AVOIDS FALSE LEMMAS:
- No König theorem (link_graph_bipartite is FALSE)
- No local_cover_le_2 (FALSE)  
- No external_share_common_vertex (FALSE)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- STANDARD DEFINITIONS  
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ M' : Finset (Finset V), isTrianglePacking G M' → M'.card ≤ M.card

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧
    (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card = n}

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 CONFIGURATION
-- ══════════════════════════════════════════════════════════════════════════════

structure Cycle4Config (V : Type*) where
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  a_priv : V
  b_priv : V
  c_priv : V
  d_priv : V

def Cycle4Config.A (cfg : Cycle4Config V) : Finset V := {cfg.v_ab, cfg.v_da, cfg.a_priv}
def Cycle4Config.B (cfg : Cycle4Config V) : Finset V := {cfg.v_ab, cfg.v_bc, cfg.b_priv}
def Cycle4Config.C (cfg : Cycle4Config V) : Finset V := {cfg.v_bc, cfg.v_cd, cfg.c_priv}
def Cycle4Config.D (cfg : Cycle4Config V) : Finset V := {cfg.v_cd, cfg.v_da, cfg.d_priv}

def Cycle4Config.M (cfg : Cycle4Config V) : Finset (Finset V) := {cfg.A, cfg.B, cfg.C, cfg.D}

def Cycle4Config.allDistinct (cfg : Cycle4Config V) : Prop :=
  cfg.v_ab ≠ cfg.v_bc ∧ cfg.v_ab ≠ cfg.v_cd ∧ cfg.v_ab ≠ cfg.v_da ∧
  cfg.v_ab ≠ cfg.a_priv ∧ cfg.v_ab ≠ cfg.b_priv ∧ cfg.v_ab ≠ cfg.c_priv ∧ cfg.v_ab ≠ cfg.d_priv ∧
  cfg.v_bc ≠ cfg.v_cd ∧ cfg.v_bc ≠ cfg.v_da ∧
  cfg.v_bc ≠ cfg.a_priv ∧ cfg.v_bc ≠ cfg.b_priv ∧ cfg.v_bc ≠ cfg.c_priv ∧ cfg.v_bc ≠ cfg.d_priv ∧
  cfg.v_cd ≠ cfg.v_da ∧
  cfg.v_cd ≠ cfg.a_priv ∧ cfg.v_cd ≠ cfg.b_priv ∧ cfg.v_cd ≠ cfg.c_priv ∧ cfg.v_cd ≠ cfg.d_priv ∧
  cfg.v_da ≠ cfg.a_priv ∧ cfg.v_da ≠ cfg.b_priv ∧ cfg.v_da ≠ cfg.c_priv ∧ cfg.v_da ≠ cfg.d_priv ∧
  cfg.a_priv ≠ cfg.b_priv ∧ cfg.a_priv ≠ cfg.c_priv ∧ cfg.a_priv ≠ cfg.d_priv ∧
  cfg.b_priv ≠ cfg.c_priv ∧ cfg.b_priv ≠ cfg.d_priv ∧
  cfg.c_priv ≠ cfg.d_priv

-- ══════════════════════════════════════════════════════════════════════════════
-- THE 8-EDGE COVER
-- ══════════════════════════════════════════════════════════════════════════════

def cover8 (cfg : Cycle4Config V) : Finset (Sym2 V) :=
  {s(cfg.v_ab, cfg.v_da), s(cfg.v_ab, cfg.v_bc),
   s(cfg.v_bc, cfg.v_cd), s(cfg.v_cd, cfg.v_da),
   s(cfg.v_ab, cfg.a_priv), s(cfg.v_bc, cfg.b_priv),
   s(cfg.v_cd, cfg.c_priv), s(cfg.v_da, cfg.d_priv)}

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle shares an edge with some packing element -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ m ∈ M, (t ∩ m).card ≥ 2 := by
  sorry

/-- Ring edges cover all M-triangles -/
lemma cover8_covers_M (cfg : Cycle4Config V) (h : cfg.allDistinct)
    (t : Finset V) (ht : t ∈ cfg.M) :
    ∃ e ∈ cover8 cfg, e ∈ t.sym2 := by
  sorry

/-- Every triangle contains a shared vertex -/
lemma triangle_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Cycle4Config V) (h : cfg.allDistinct)
    (hM : isMaxPacking G (cfg.M)) (hM_triangles : cfg.M ⊆ G.cliqueFinset 3)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    cfg.v_ab ∈ t ∨ cfg.v_bc ∈ t ∨ cfg.v_cd ∈ t ∨ cfg.v_da ∈ t := by
  sorry

/-- External triangles at any shared vertex are covered -/
lemma externals_covered (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Cycle4Config V) (h : cfg.allDistinct)
    (hM : isMaxPacking G (cfg.M)) (hM_triangles : cfg.M ⊆ G.cliqueFinset 3)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_M : t ∉ cfg.M)
    (hv : cfg.v_ab ∈ t ∨ cfg.v_bc ∈ t ∨ cfg.v_cd ∈ t ∨ cfg.v_da ∈ t) :
    ∃ e ∈ cover8 cfg, e ∈ t.sym2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- COVER8 COVERS ALL TRIANGLES
-- ══════════════════════════════════════════════════════════════════════════════

theorem cover8_covers_all (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Cycle4Config V) (h : cfg.allDistinct)
    (hM : isMaxPacking G (cfg.M)) (hM_triangles : cfg.M ⊆ G.cliqueFinset 3)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ cover8 cfg, e ∈ t.sym2 := by
  by_cases ht_M : t ∈ cfg.M
  · exact cover8_covers_M cfg h t ht_M
  · have hv := triangle_contains_shared G cfg h hM hM_triangles t ht
    exact externals_covered G cfg h hM hM_triangles t ht ht_M hv

-- ══════════════════════════════════════════════════════════════════════════════
-- COVER8 PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

lemma cover8_card_le_8 (cfg : Cycle4Config V) : (cover8 cfg).card ≤ 8 := by
  sorry

lemma cover8_subset_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Cycle4Config V) (hM_triangles : cfg.M ⊆ G.cliqueFinset 3) :
    cover8 cfg ⊆ G.edgeFinset := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Cycle4Config V) (h : cfg.allDistinct)
    (hM : isMaxPacking G (cfg.M)) (hM_triangles : cfg.M ⊆ G.cliqueFinset 3) :
    triangleCoveringNumber G ≤ 8 := by
  have h_subset : cover8 cfg ⊆ G.edgeFinset := cover8_subset_edges G cfg hM_triangles
  have h_covers : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ cover8 cfg, e ∈ t.sym2 :=
    fun t ht => cover8_covers_all G cfg h hM hM_triangles t ht
  have h_card : (cover8 cfg).card ≤ 8 := cover8_card_le_8 cfg
  -- τ ≤ |cover8| ≤ 8
  have h_in_set : (cover8 cfg).card ∈ {n : ℕ | ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧
      (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card = n} := by
    simp only [Set.mem_setOf_eq]
    exact ⟨cover8 cfg, h_subset, h_covers, rfl⟩
  unfold triangleCoveringNumber
  calc sInf {n : ℕ | ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧
        (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card = n}
      ≤ (cover8 cfg).card := Nat.sInf_le h_in_set
    _ ≤ 8 := h_card

end
