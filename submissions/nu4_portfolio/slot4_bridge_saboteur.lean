/-
Tuza ν=4 Portfolio - Slot 4: Bridge Saboteur

TARGET: bridges_limited_by_nu - bridges must be limited or ν increases
STRATEGY: Scaffolded
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

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

def bridges_to_f (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e f : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => (t ∩ f).card ≥ 2)

lemma edge_disjoint_share_le_1 (e f : Finset V)
    (he : e.card = 3) (hf : f.card = 3)
    (h_disjoint : ∀ x y, x ∈ e → y ∈ e → x ≠ y → ∀ a b, a ∈ f → b ∈ f → a ≠ b → ({x, y} : Finset V) ≠ {a, b}) :
    (e ∩ f).card ≤ 1 := by
  sorry

lemma bridges_to_f_share_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (t1 t2 : Finset V) (ht1 : t1 ∈ bridges_to_f G M e f) (ht2 : t2 ∈ bridges_to_f G M e f) :
    (t1 ∩ t2).card ≥ 1 := by
  sorry

lemma bridges_to_f_in_k4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : v ∈ e ∧ v ∈ f) :
    ∃ U : Finset V, U.card ≤ 4 ∧ ∀ t ∈ bridges_to_f G M e f, t ⊆ U := by
  sorry

lemma bridge_count_limit (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (bridges G M e).card ≤ 2 * (M.card - 1) := by
  sorry

end
