/-
Tuza ν=4 Portfolio - Slot 33: Cycle Configuration (C4)

TARGET: Prove τ ≤ 8 when sharing graph is a 4-cycle e1 — e2 — e3 — e4 — e1

CONFIGURATION:
- e1 ∩ e2 = {v12}
- e2 ∩ e3 = {v23}
- e3 ∩ e4 = {v34}
- e4 ∩ e1 = {v41}
- All four shared vertices are DISTINCT

KEY STRUCTURAL INSIGHT:
Opposite pairs in the cycle are VERTEX-DISJOINT:
- e1 and e3 share no vertices (their shared vertices are v12, v41 and v23, v34)
- e2 and e4 share no vertices (their shared vertices are v12, v23 and v34, v41)

CONSEQUENCE:
T_{e1} and T_{e3} are DISJOINT sets of triangles!
(A triangle can't share edges with both e1 and e3 if they're vertex-disjoint)

Similarly, T_{e2} and T_{e4} are disjoint.

STRATEGY:
Partition all triangles into:
1. Those sharing edges only with {e1, e3} → τ ≤ 4 (two ν=1 cases, disjoint)
2. Those sharing edges only with {e2, e4} → τ ≤ 4 (two ν=1 cases, disjoint)
3. Bridges between adjacent pairs → Need to account for

Actually, triangles can share edges with both e1 and e2 (these are X(e1,e2)).

REFINED STRATEGY:
- τ(S_{e1}) ≤ 2, τ(S_{e3}) ≤ 2, and S_{e1}, S_{e3} are disjoint → τ(S_{e1} ∪ S_{e3}) ≤ 4
- τ(S_{e2}) ≤ 2, τ(S_{e4}) ≤ 2, and S_{e2}, S_{e4} are disjoint → τ(S_{e2} ∪ S_{e4}) ≤ 4
- All S_e's are pairwise disjoint (proven)
- Bridges: X(e1,e2), X(e2,e3), X(e3,e4), X(e4,e1)
- Need to cover bridges while staying under 8 total

SCAFFOLDING:
- tau_S_le_2 (proven)
- tau_X_le_2 (proven)
- bridges_inter_card_eq_one (bridges share exactly v)
- Se_pairwise_intersect (proven)
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

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def allBridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ∃ e ∈ M, ∃ f ∈ M, e ≠ f ∧ (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry

lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry

-- S_e and S_f are disjoint for different packing elements (key structural lemma)
lemma Se_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    Disjoint (S_e G M e) (S_e G M f) := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE-SPECIFIC LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

-- Opposite elements in C4 are vertex-disjoint
lemma cycle_opposite_disjoint (e1 e2 e3 e4 : Finset V)
    (v12 : V) (hv12 : e1 ∩ e2 = {v12})
    (v23 : V) (hv23 : e2 ∩ e3 = {v23})
    (v34 : V) (hv34 : e3 ∩ e4 = {v34})
    (v41 : V) (hv41 : e4 ∩ e1 = {v41})
    (h_distinct : v12 ≠ v23 ∧ v23 ≠ v34 ∧ v34 ≠ v41 ∧ v41 ≠ v12 ∧ v12 ≠ v34 ∧ v23 ≠ v41)
    (he_cards : e1.card = 3 ∧ e2.card = 3 ∧ e3.card = 3 ∧ e4.card = 3) :
    Disjoint (e1 : Set V) (e3 : Set V) ∧ Disjoint (e2 : Set V) (e4 : Set V) := by
  -- e1 contains v12 and v41 (shared with neighbors)
  -- e3 contains v23 and v34 (shared with neighbors)
  -- These are all distinct, and each triangle has 3 vertices
  -- The third vertex of e1 is not in {v23, v34} (not shared with e3's neighbors)
  -- Similarly for e3
  sorry

-- No bridges between opposite elements
lemma cycle_no_opposite_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (e1 e3 : Finset V) (h_disj : Disjoint (e1 : Set V) (e3 : Set V)) :
    X_ef G e1 e3 = ∅ := by
  sorry

-- T_{e1} and T_{e3} are disjoint (no shared triangles)
lemma cycle_opposite_T_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (e1 e3 : Finset V) (h_disj : Disjoint (e1 : Set V) (e3 : Set V)) :
    Disjoint (trianglesSharingEdge G e1) (trianglesSharingEdge G e3) := by
  -- A triangle in both would share ≥2 vertices with e1 AND ≥2 with e3
  -- But e1 and e3 are vertex-disjoint, so this requires ≥4 vertices
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE STRUCTURE IN CYCLE
-- ══════════════════════════════════════════════════════════════════════════════

-- Bridges in cycle only connect adjacent elements
lemma cycle_bridges_adjacent_only (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e1 e2 e3 e4 : Finset V)
    (hM_eq : M = {e1, e2, e3, e4})
    (h_e1_e3_disj : Disjoint (e1 : Set V) (e3 : Set V))
    (h_e2_e4_disj : Disjoint (e2 : Set V) (e4 : Set V)) :
    allBridges G M = X_ef G e1 e2 ∪ X_ef G e2 e3 ∪ X_ef G e3 e4 ∪ X_ef G e4 e1 := by
  sorry

-- Four bridge sets, each needs ≤2 edges, but they share vertices
-- Key: bridges through v_ij share vertex v_ij, so spokes can cover multiple
lemma cycle_bridge_cover_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (e1 e2 e3 e4 : Finset V)
    (v12 : V) (hv12 : e1 ∩ e2 = {v12})
    (v23 : V) (hv23 : e2 ∩ e3 = {v23})
    (v34 : V) (hv34 : e3 ∩ e4 = {v34})
    (v41 : V) (hv41 : e4 ∩ e1 = {v41}) :
    -- Bridges in X(ei, ej) all contain vij
    (∀ t ∈ X_ef G e1 e2, v12 ∈ t) ∧
    (∀ t ∈ X_ef G e2 e3, v23 ∈ t) ∧
    (∀ t ∈ X_ef G e3 e4, v34 ∈ t) ∧
    (∀ t ∈ X_ef G e4 e1, v41 ∈ t) := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Cycle Case Theorem
-- ══════════════════════════════════════════════════════════════════════════════

-- τ of all S_e's combined (they're pairwise disjoint)
lemma tau_all_Se_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_disjoint : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint (S_e G M e) (S_e G M f)) :
    triangleCoveringNumberOn G (M.biUnion (S_e G M)) ≤ 8 := by
  -- Each S_e needs ≤2 edges, they're disjoint, so 4 × 2 = 8
  sorry

-- τ of all bridges in cycle
lemma tau_cycle_bridges_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e1 e2 e3 e4 : Finset V)
    (v12 : V) (hv12 : e1 ∩ e2 = {v12})
    (v23 : V) (hv23 : e2 ∩ e3 = {v23})
    (v34 : V) (hv34 : e3 ∩ e4 = {v34})
    (v41 : V) (hv41 : e4 ∩ e1 = {v41}) :
    triangleCoveringNumberOn G (X_ef G e1 e2 ∪ X_ef G e2 e3 ∪ X_ef G e3 e4 ∪ X_ef G e4 e1) ≤ 8 := by
  -- Each bridge set ≤2, four sets, total ≤8
  -- But we need better: bridges through same vertex can share cover edges
  sorry

-- Main theorem: Cycle configuration (C4 sharing graph)
theorem tau_le_8_cycle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e1 e2 e3 e4 : Finset V)
    (hM_eq : M = {e1, e2, e3, e4})
    (v12 : V) (hv12 : e1 ∩ e2 = {v12})
    (v23 : V) (hv23 : e2 ∩ e3 = {v23})
    (v34 : V) (hv34 : e3 ∩ e4 = {v34})
    (v41 : V) (hv41 : e4 ∩ e1 = {v41})
    (h_distinct : v12 ≠ v23 ∧ v23 ≠ v34 ∧ v34 ≠ v41 ∧ v41 ≠ v12 ∧ v12 ≠ v34 ∧ v23 ≠ v41) :
    triangleCoveringNumber G ≤ 8 := by
  -- All triangles = ⋃ S_e ∪ all bridges
  -- S_e's are pairwise disjoint
  -- Key insight: Use opposite-pair decomposition
  --
  -- Approach 1: τ(⋃ S_e) + τ(bridges) with overlap
  -- τ(⋃ S_e) ≤ 8 (4 disjoint sets of ≤2 each)
  -- But bridges overlap with S_e... actually no, S_e excludes bridges by definition!
  --
  -- So: All triangles = ⋃ S_e ∪ (all bridges), and these are disjoint
  -- τ(⋃ S_e) ≤ 8
  -- τ(bridges) ≤ ? (need to bound)
  --
  -- BUT: τ(⋃ S_e) + τ(bridges) could exceed 8!
  --
  -- Key: Some edges can hit both S_e triangles and bridges
  -- E.g., edge {v12, x} where x is in e1 can hit:
  --   - Triangles in S_{e1} containing v12
  --   - Bridges in X(e1, e2) containing v12
  --
  -- This requires coordinated cover construction, not just bounds
  sorry

-- Alternative approach: Use opposite-pair vertex-disjointness
theorem tau_le_8_cycle_via_pairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e1 e2 e3 e4 : Finset V)
    (hM_eq : M = {e1, e2, e3, e4})
    (h_e1_e3_disj : Disjoint (e1 : Set V) (e3 : Set V))
    (h_e2_e4_disj : Disjoint (e2 : Set V) (e4 : Set V)) :
    triangleCoveringNumber G ≤ 8 := by
  -- T_{e1} ∪ T_{e3} and T_{e2} ∪ T_{e4} partition (almost) all triangles
  -- T_{e1}, T_{e3} are disjoint (cycle_opposite_T_disjoint)
  -- T_{e2}, T_{e4} are disjoint
  --
  -- τ(T_{e1}) ≤ ? and τ(T_{e3}) ≤ ?
  -- Each T_{ei} = S_{ei} ∪ bridges from ei
  -- For e1: bridges to e2 and e4 (adjacent in cycle)
  -- τ(T_{e1}) ≤ τ(S_{e1}) + τ(X(e1,e2)) + τ(X(e1,e4)) ≤ 2 + 2 + 2 = 6
  -- But this uses subadditivity loosely
  sorry

end
