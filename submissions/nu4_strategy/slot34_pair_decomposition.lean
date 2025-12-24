/-
Tuza ν=4 Strategy - Slot 34: Pair Decomposition (Boris Minimal)

TARGET: Prove there exists a pair {e,f} in the packing such that τ(T_e ∪ T_f) ≤ 4

STRATEGIC VALUE:
If any pair has τ(T_e ∪ T_f) ≤ 4, then residual has ν ≤ 2 (already proven τ ≤ 4).
Total: τ ≤ 4 + 4 = 8 ✓

This is a Boris-minimal submission - let Aristotle explore freely.
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

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Pair Decomposition Bound
-- ══════════════════════════════════════════════════════════════════════════════

/--
In any ν=4 packing, there exists a pair {e,f} such that τ(T_e ∪ T_f) ≤ 4.

If this is true: Combined with residual ν≤2 (τ≤4), we get τ(G) ≤ 8.
If this is false: Finding a counterexample would be valuable.
-/
theorem packing_pair_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4) :
    ∃ e f, e ∈ M ∧ f ∈ M ∧ e ≠ f ∧ triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  sorry

end
