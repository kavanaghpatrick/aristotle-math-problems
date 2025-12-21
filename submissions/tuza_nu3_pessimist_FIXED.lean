/-
Tuza ν ≤ 3: PESSIMIST with FIXED definition

Hunt for counterexamples using CORRECT coveringNumberOn (restricted to G.edgeFinset)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def shareEdge (t1 t2 : Finset V) : Prop := (t1 ∩ t2).card ≥ 2

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  Set.Pairwise (T : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (IsTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

-- FIXED: restricted to G.edgeFinset
noncomputable def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E =>
    ∀ t ∈ S, ∃ e ∈ E, e ∈ t.sym2
  ) |>.image Finset.card |>.min |>.getD 0

-- COUNTEREXAMPLE HUNT: Find a graph where τ(T_e) ≥ 3 for some e ∈ M with |M| ≤ 3
theorem tau_Te_counterexample :
    ∃ (V : Type*) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj)
      (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
      (e : Finset V) (he : e ∈ M),
    coveringNumberOn G (T_e G e) ≥ 3 := by
  sorry

end
