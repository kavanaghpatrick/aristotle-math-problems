/-
Tuza ν=4: τ(T_e ∪ T_f) ≤ 4

GOAL: When e, f ∈ M (max packing) share a vertex v, prove τ(T_e ∪ T_f) ≤ 4.

PROVEN SCAFFOLDING AVAILABLE:
1. tau_S_le_2: τ(S_e) ≤ 2 for any e ∈ M (proven in tuza_tau_Se_COMPLETE.lean)
2. triangle_bridge: If h shares edges with edge-disjoint e,f, then e ∩ f = {v} and v ∈ h
3. bridge_triangles_contain_v: All triangles in X(e,f) contain the shared vertex v

Pattern: Boris Minimal - let Aristotle find the proof path
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e) ∩ (trianglesSharingEdge G f)

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- PROVEN: τ(S_e) ≤ 2 (from tuza_tau_Se_COMPLETE.lean, uuid f9473ebd)
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G e M) ≤ 2 := by
  sorry

-- PROVEN: Triangles in X(e,f) contain shared vertex (from triangle_bridge_COMPLETE.lean)
lemma X_triangles_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V)
    (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (h_disjoint : (e ∩ f).card ≤ 1)
    (h_inter : e ∩ f = {v}) :
    ∀ t ∈ X_ef G e f, v ∈ t := by
  sorry

-- PROVEN: τ(X(e,f)) ≤ 2 when all triangles contain v (star cover)
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V)
    (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (h_inter : e ∩ f = {v})
    (h_all_contain_v : ∀ t ∈ X_ef G e f, v ∈ t) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry

-- TARGET: τ(T_e ∪ T_f) ≤ 4 when e, f share a vertex
theorem tau_union_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  sorry

end
