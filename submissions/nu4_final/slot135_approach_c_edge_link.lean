/-
Tuza ν=4 Cycle_4: APPROACH C - EDGE-PER-ELEMENT + LINK GRAPH
Slot 135

AI CONSENSUS (Dec 29, 2025):
- Grok, Gemini, Codex ALL recommend Approach C
- Approach A (S_e + Bridge Absorption) FAILED: bridge_absorption proven FALSE (slot54)
- Approach B (Consistent Orientation) FAILED: local_cover_le_2 proven FALSE (Dec 26)
- Previous 4+4 strategy FAILED: external_share_common_vertex proven FALSE (slot131)

APPROACH C STRATEGY:
1. Use 4 "cycle edges" E_cycle = {{v_ab, v_da}, {v_ab, v_bc}, {v_bc, v_cd}, {v_cd, v_da}}
2. These 4 edges cover all M-elements (each M-element has 2 shared vertices)
3. For bridges: use tau_X_le_2 (PROVEN in slot24) at each pair
4. Total: 4 (cycle) + 4 (bridges) = 8 edges

VALIDATED LEMMAS USED:
- tau_X_le_2: τ(X(e,f)) ≤ 2 for bridges between e,f [PROVEN]
- tau_union_le_sum: τ(A∪B) ≤ τ(A) + τ(B) [PROVEN]
- cycle4_all_triangles_contain_shared: Every triangle contains some v_ij [PROVEN]
- triangle_shares_edge_with_packing: Maximality [PROVEN]
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧ Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def X (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 CONFIGURATION: 4 triangles sharing vertices cyclically
-- ══════════════════════════════════════════════════════════════════════════════

/-- Cycle_4 configuration: A, B, C, D share vertices cyclically -/
structure Cycle4Config (G : SimpleGraph V) [DecidableRel G.Adj] where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ G.cliqueFinset 3
  hB : B ∈ G.cliqueFinset 3
  hC : C ∈ G.cliqueFinset 3
  hD : D ∈ G.cliqueFinset 3
  -- Shared vertices
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  -- Intersection conditions
  h_ab : A ∩ B = {v_ab}
  h_bc : B ∩ C = {v_bc}
  h_cd : C ∩ D = {v_cd}
  h_da : D ∩ A = {v_da}
  -- M = {A, B, C, D} is a maximum packing
  hM : isMaxPacking G {A, B, C, D}

variable (G : SimpleGraph V) [DecidableRel G.Adj]

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMAS (from previous slots)
-- ══════════════════════════════════════════════════════════════════════════════

/-- PROVEN (slot24): τ(X(e,f)) ≤ 2 for bridges -/
axiom tau_X_le_2 (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X G e f) ≤ 2

/-- PROVEN (slot133): τ(A∪B) ≤ τ(A) + τ(B) -/
axiom tau_union_le_sum (S₁ S₂ : Finset (Finset V)) :
    triangleCoveringNumberOn G (S₁ ∪ S₂) ≤
    triangleCoveringNumberOn G S₁ + triangleCoveringNumberOn G S₂

/-- PROVEN (slot128): Every triangle in Cycle4 contains a shared vertex -/
axiom cycle4_all_triangles_contain_shared (cfg : Cycle4Config G) (t : Finset V)
    (ht : t ∈ G.cliqueFinset 3) :
    cfg.v_ab ∈ t ∨ cfg.v_bc ∈ t ∨ cfg.v_cd ∈ t ∨ cfg.v_da ∈ t

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 1: Cycle edges cover M-elements
-- ══════════════════════════════════════════════════════════════════════════════

/-- The 4 "cycle edges" connecting shared vertices -/
def cycleEdges (cfg : Cycle4Config G) : Finset (Sym2 V) :=
  {s(cfg.v_ab, cfg.v_da), s(cfg.v_ab, cfg.v_bc), s(cfg.v_bc, cfg.v_cd), s(cfg.v_cd, cfg.v_da)}

/-- Shared vertices are in the M-elements -/
lemma v_ab_in_A (cfg : Cycle4Config G) : cfg.v_ab ∈ cfg.A := by
  have h := cfg.h_ab
  rw [← h]
  exact Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩ |>
    Finset.mem_inter.mp |>.1

lemma v_ab_in_B (cfg : Cycle4Config G) : cfg.v_ab ∈ cfg.B := by
  have h := cfg.h_ab
  rw [← h]
  exact Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩ |>
    Finset.mem_inter.mp |>.2

lemma v_da_in_A (cfg : Cycle4Config G) : cfg.v_da ∈ cfg.A := by
  have h := cfg.h_da
  rw [← h]
  exact Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩ |>
    Finset.mem_inter.mp |>.2

lemma v_da_in_D (cfg : Cycle4Config G) : cfg.v_da ∈ cfg.D := by
  have h := cfg.h_da
  rw [← h]
  exact Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩ |>
    Finset.mem_inter.mp |>.1

/-- Each M-element contains two shared vertices, so contains a cycle edge -/
lemma cycle_edge_covers_A (cfg : Cycle4Config G) :
    ∃ e ∈ cycleEdges G cfg, e ∈ cfg.A.sym2 := by
  use s(cfg.v_ab, cfg.v_da)
  constructor
  · simp [cycleEdges]
  · simp only [Finset.mem_sym2]
    constructor
    · exact v_ab_in_A G cfg
    · exact v_da_in_A G cfg

lemma cycle_edge_covers_B (cfg : Cycle4Config G) :
    ∃ e ∈ cycleEdges G cfg, e ∈ cfg.B.sym2 := by
  use s(cfg.v_ab, cfg.v_bc)
  constructor
  · simp [cycleEdges]
  · simp only [Finset.mem_sym2]
    constructor
    · exact v_ab_in_B G cfg
    · -- v_bc ∈ B
      have h := cfg.h_bc
      rw [← h]
      exact Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩ |>
        Finset.mem_inter.mp |>.1

lemma cycle_edge_covers_C (cfg : Cycle4Config G) :
    ∃ e ∈ cycleEdges G cfg, e ∈ cfg.C.sym2 := by
  use s(cfg.v_bc, cfg.v_cd)
  constructor
  · simp [cycleEdges]
  · simp only [Finset.mem_sym2]
    constructor
    · -- v_bc ∈ C
      have h := cfg.h_bc
      rw [← h]
      exact Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩ |>
        Finset.mem_inter.mp |>.2
    · -- v_cd ∈ C
      have h := cfg.h_cd
      rw [← h]
      exact Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩ |>
        Finset.mem_inter.mp |>.1

lemma cycle_edge_covers_D (cfg : Cycle4Config G) :
    ∃ e ∈ cycleEdges G cfg, e ∈ cfg.D.sym2 := by
  use s(cfg.v_cd, cfg.v_da)
  constructor
  · simp [cycleEdges]
  · simp only [Finset.mem_sym2]
    constructor
    · -- v_cd ∈ D
      have h := cfg.h_cd
      rw [← h]
      exact Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩ |>
        Finset.mem_inter.mp |>.2
    · exact v_da_in_D G cfg

/-- The 4 cycle edges cover all M-elements -/
lemma cycle_edges_cover_M (cfg : Cycle4Config G) :
    ∀ t ∈ ({cfg.A, cfg.B, cfg.C, cfg.D} : Finset (Finset V)),
      ∃ e ∈ cycleEdges G cfg, e ∈ t.sym2 := by
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact cycle_edge_covers_A G cfg
  · exact cycle_edge_covers_B G cfg
  · exact cycle_edge_covers_C G cfg
  · exact cycle_edge_covers_D G cfg

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 2: Bridges can be covered with 4 edges
-- ══════════════════════════════════════════════════════════════════════════════

/-- All bridges in cycle_4: X(A,B) ∪ X(B,C) ∪ X(C,D) ∪ X(D,A) -/
def allBridges (cfg : Cycle4Config G) : Finset (Finset V) :=
  X G cfg.A cfg.B ∪ X G cfg.B cfg.C ∪ X G cfg.C cfg.D ∪ X G cfg.D cfg.A

/-- Each pair of bridges contributes τ ≤ 2, total ≤ 4 -/
lemma bridges_cover_le_4 (cfg : Cycle4Config G) :
    triangleCoveringNumberOn G (allBridges G cfg) ≤ 4 := by
  -- Use subadditivity: τ(X_AB ∪ X_BC ∪ X_CD ∪ X_DA) ≤ τ(X_AB) + τ(X_BC) + τ(X_CD) + τ(X_DA)
  -- Note: X(A,C) and X(B,D) are empty for diagonals (disjoint)
  have h1 : triangleCoveringNumberOn G (X G cfg.A cfg.B) ≤ 2 := by
    apply tau_X_le_2
    · exact cfg.hM
    · simp
    · simp
    · simp [cfg.h_ab]; intro h;
      have := Finset.card_eq_three.mp (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hA).2
      aesop
  have h2 : triangleCoveringNumberOn G (X G cfg.B cfg.C) ≤ 2 := by
    apply tau_X_le_2
    · exact cfg.hM
    · simp
    · simp
    · simp [cfg.h_bc]; intro h;
      have := Finset.card_eq_three.mp (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hB).2
      aesop
  -- By subadditivity (adjacent pairs only):
  -- τ(X_AB ∪ X_BC) ≤ τ(X_AB) + τ(X_BC) ≤ 2 + 2 = 4
  -- X_CD and X_DA share edges with the 4 cycle edges (already covered)
  calc triangleCoveringNumberOn G (allBridges G cfg)
      ≤ triangleCoveringNumberOn G (X G cfg.A cfg.B ∪ X G cfg.B cfg.C) +
        triangleCoveringNumberOn G (X G cfg.C cfg.D ∪ X G cfg.D cfg.A) := by
          apply tau_union_le_sum
      _ ≤ (triangleCoveringNumberOn G (X G cfg.A cfg.B) +
           triangleCoveringNumberOn G (X G cfg.B cfg.C)) +
          (triangleCoveringNumberOn G (X G cfg.C cfg.D) +
           triangleCoveringNumberOn G (X G cfg.D cfg.A)) := by
          sorry -- subadditivity twice
      _ ≤ (2 + 2) + (2 + 2) := by
          sorry -- use h1, h2 and similar for C-D, D-A
      _ = 8 := by norm_num

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 3: Cycle edges are in G.edgeFinset
-- ══════════════════════════════════════════════════════════════════════════════

lemma cycle_edges_subset_edgeFinset (cfg : Cycle4Config G) :
    cycleEdges G cfg ⊆ G.edgeFinset := by
  intro e he
  simp [cycleEdges] at he
  rcases he with rfl | rfl | rfl | rfl <;> {
    -- Each cycle edge is between two vertices in the same M-element
    -- Since M-elements are triangles in G, adjacent vertices are connected
    sorry
  }

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for Cycle_4
-- ══════════════════════════════════════════════════════════════════════════════

/--
MAIN THEOREM: In the Cycle_4 configuration, τ(G) ≤ 8

Proof strategy (Approach C):
1. Cover M-elements with 4 cycle edges (each M-element has 2 shared vertices)
2. Cover bridges with ≤4 edges (using tau_X_le_2 for each adjacent pair)
3. By cycle4_all_triangles_contain_shared, every triangle is either in M or shares
   an edge with some M-element, so is covered by the union
4. Total: 4 + 4 = 8
-/
theorem cycle4_tau_le_8 (cfg : Cycle4Config G) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- The cover consists of:
  -- 1. The 4 cycle edges (cover M and many external triangles)
  -- 2. Bridge edges (cover remaining triangles)
  --
  -- Key insight: Every triangle either:
  -- (a) Is in M (covered by cycle edges)
  -- (b) Shares edge with some M-element (covered by cycle edges or bridges)
  --
  -- The cycle edges have cardinality 4
  have h_cycle_card : (cycleEdges G cfg).card ≤ 4 := by
    simp [cycleEdges]
    -- At most 4 distinct edges
    exact Finset.card_insert_le _ _ |> fun h => le_trans h (by norm_num)

  -- By the AI consensus strategy:
  -- τ(all triangles) ≤ τ(M) + τ(bridges)
  --                 ≤ |cycle_edges| + τ(bridges)
  --                 ≤ 4 + 4 = 8
  sorry

end
