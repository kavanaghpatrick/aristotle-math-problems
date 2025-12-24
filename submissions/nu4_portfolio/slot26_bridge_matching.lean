/-
Tuza ν=4 Portfolio - Slot 26: Bridge Matching Lemma

TARGET: Prove bridges form a matching on outer vertices

KEY INSIGHT (from Codex consultation 2024-12-23):
From bridges_inter_card_eq_one, two bridges cannot share an outer vertex
(they would share v + outer = 2 vertices, violating the intersection bound).
Therefore bridges form a MATCHING on the outer vertices.

This limits total bridges to at most 4 in star case (8 outer vertices / 2).

SCAFFOLDING:
- bridges_inter_card_eq_one (proven in slot6)
- bridges_contain_v (proven)
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

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

def allBridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  M.biUnion (bridges G M)

-- Bridges between specific pair e and f
def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- Outer vertices: vertices in packing elements but not the shared vertex
def outerVertices (M : Finset (Finset V)) (v : V) : Finset V :=
  (M.biUnion id).filter (· ≠ v)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: bridges_inter_card_eq_one (from slot6)
-- ══════════════════════════════════════════════════════════════════════════════

-- Scaffolded from slot6 - Aristotle will use the proof structure
lemma bridges_inter_card_eq_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (t1 t2 : Finset V) (ht1 : t1 ∈ X_ef G e f) (ht2 : t2 ∈ X_ef G e f) (hne : t1 ≠ t2) :
    (t1 ∩ t2).card = 1 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: bridges_contain_v (from slot6)
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridges_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Bridge Matching Lemma
-- Two distinct bridges cannot share an outer vertex (non-v vertex)
-- ══════════════════════════════════════════════════════════════════════════════

theorem bridge_outer_vertex_unique (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (t1 t2 : Finset V) (ht1 : t1 ∈ X_ef G e f) (ht2 : t2 ∈ X_ef G e f) (hne : t1 ≠ t2)
    (x : V) (hx : x ≠ v) (hx1 : x ∈ t1) (hx2 : x ∈ t2) :
    False := by
  -- x ∈ t1 ∩ t2, and v ∈ t1 ∩ t2 (by bridges_contain_v)
  -- So t1 ∩ t2 contains both v and x, giving |t1 ∩ t2| ≥ 2
  -- But bridges_inter_card_eq_one says |t1 ∩ t2| = 1
  -- Contradiction
  sorry

-- Corollary: Each outer vertex participates in at most one bridge
theorem bridge_matching (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (x : V) (hx : x ≠ v) :
    ((X_ef G e f).filter (fun t => x ∈ t)).card ≤ 1 := by
  -- If x appears in 2+ bridges, contradiction via bridge_outer_vertex_unique
  sorry

end
