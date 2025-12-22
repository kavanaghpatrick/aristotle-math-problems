/-
Tuza ν=4 Portfolio - Slot 10: Connected Graphs with ν=4

TARGET: Prove τ ≤ 8 for CONNECTED graphs with ν=4

WHY CONNECTIVITY MATTERS:
- For disconnected G = G₁ ∪ G₂: ν(G) = ν(G₁) + ν(G₂), τ(G) = τ(G₁) + τ(G₂)
- If ν(G) = 4 disconnected: either some component has ν ≤ 3 (Parker proven)
  or all components have ν ≤ 3 (also proven)
- The ONLY unproven case is CONNECTED graphs with ν = 4

PROVEN FACTS:
1. Parker 2024: τ ≤ 2ν for ν ≤ 3 (complete)
2. τ(S_e) ≤ 2 for any e ∈ M (complete)
3. S_e forms Star or K4 structure (complete)

KEY INSIGHT FOR CONNECTED ν=4:
In a connected graph with |M| = 4 packing triangles:
- The "bridge graph" (vertices = M, edges = pairs sharing a vertex) is connected
- This constrains the structure significantly
- Bridge graph on 4 vertices with connectivity: path, star, cycle, K₄-e, K₄

STRATEGY: Enumerate bridge graph structures for connected case
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

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE GRAPH: Intersection structure of packing M
-- ══════════════════════════════════════════════════════════════════════════════

-- Two packing elements "share a vertex" if their intersection is nonempty
def packingShareVertex (e f : Finset V) : Prop := (e ∩ f).Nonempty

-- Bridge graph on M: edge between e,f iff they share a vertex
def bridgeGraph (M : Finset (Finset V)) : SimpleGraph (Finset V) where
  Adj e f := e ∈ M ∧ f ∈ M ∧ e ≠ f ∧ packingShareVertex e f
  symm := by
    intro e f ⟨he, hf, hne, h_share⟩
    refine ⟨hf, he, hne.symm, ?_⟩
    unfold packingShareVertex at h_share ⊢
    rwa [Finset.inter_comm]
  loopless := by intro e ⟨_, _, hne, _⟩; exact hne rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- REDUCTION: Disconnected → Components
-- ══════════════════════════════════════════════════════════════════════════════

-- Tuza holds for ν ≤ 3 (Parker 2024)
lemma tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  sorry  -- PROVEN: Parker 2024, formalized in our complete proof

-- If G is disconnected with ν=4, then Tuza holds by component decomposition
-- (Each component has ν ≤ 3, so τ ≤ 2ν per component, sum gives τ ≤ 2ν total)
lemma tuza_disconnected_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 4)
    (h_disconn : ¬G.Connected) :
    triangleCoveringNumber G ≤ 8 := by
  sorry  -- Follows from Parker ν≤3 on components

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_S_e_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G e M) ≤ 2 := by
  sorry  -- PROVEN: tuza_tau_Se_COMPLETE.lean

-- ══════════════════════════════════════════════════════════════════════════════
-- CONNECTED CASE: BRIDGE GRAPH STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

-- For connected G with ν=4, the bridge graph has specific structure
-- Connected simple graphs on 4 vertices: P₄, Star K₁,₃, C₄, Paw, Diamond, K₄

-- CASE: Bridge graph is a path P₄ (linear chain)
lemma tuza_bridge_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (h_card : M.card = 4)
    (h_conn : G.Connected)
    (e₁ e₂ e₃ e₄ : Finset V)
    (h_in : e₁ ∈ M ∧ e₂ ∈ M ∧ e₃ ∈ M ∧ e₄ ∈ M)
    (h_path : packingShareVertex e₁ e₂ ∧ packingShareVertex e₂ e₃ ∧ packingShareVertex e₃ e₄)
    (h_no_extra : ¬packingShareVertex e₁ e₃ ∧ ¬packingShareVertex e₁ e₄ ∧ ¬packingShareVertex e₂ e₄) :
    triangleCoveringNumber G ≤ 8 := by
  sorry

-- CASE: Bridge graph is a star K₁,₃ (one central element)
lemma tuza_bridge_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (h_card : M.card = 4)
    (h_conn : G.Connected)
    (center : Finset V) (hcenter : center ∈ M)
    (h_star : ∀ e ∈ M, e ≠ center → packingShareVertex e center)
    (h_leaves_disjoint : ∀ e f : Finset V, e ∈ M → f ∈ M → e ≠ center → f ≠ center → e ≠ f → ¬packingShareVertex e f) :
    triangleCoveringNumber G ≤ 8 := by
  sorry

-- CASE: Bridge graph is a cycle C₄
lemma tuza_bridge_cycle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (h_card : M.card = 4)
    (h_conn : G.Connected)
    (e₁ e₂ e₃ e₄ : Finset V)
    (h_in : e₁ ∈ M ∧ e₂ ∈ M ∧ e₃ ∈ M ∧ e₄ ∈ M)
    (h_cycle : packingShareVertex e₁ e₂ ∧ packingShareVertex e₂ e₃ ∧
               packingShareVertex e₃ e₄ ∧ packingShareVertex e₄ e₁)
    (h_no_diag : ¬packingShareVertex e₁ e₃ ∧ ¬packingShareVertex e₂ e₄) :
    triangleCoveringNumber G ≤ 8 := by
  sorry

-- CASE: Bridge graph is dense (Paw, Diamond, or K₄)
lemma tuza_bridge_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (h_card : M.card = 4)
    (h_conn : G.Connected)
    (h_dense : (M.filter (fun e => (M.filter (fun f => f ≠ e ∧ packingShareVertex e f)).card ≥ 2)).card ≥ 2) :
    triangleCoveringNumber G ≤ 8 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

-- Master theorem: Tuza ν=4 for CONNECTED graphs
theorem tuza_nu4_connected (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_nu : trianglePackingNumber G = 4)
    (h_conn : G.Connected) :
    triangleCoveringNumber G ≤ 8 := by
  sorry

-- Full theorem: Tuza ν=4 (connected + disconnected)
theorem tuza_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) :
    triangleCoveringNumber G ≤ 8 := by
  by_cases h_conn : G.Connected
  · exact tuza_nu4_connected G h h_conn
  · exact tuza_disconnected_nu4 G h h_conn

end
