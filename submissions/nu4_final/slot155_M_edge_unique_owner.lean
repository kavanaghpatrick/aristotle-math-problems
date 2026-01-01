/-
Tuza ν=4: M_edge_unique_owner - Each M-edge appears in exactly one M-element

GOAL: Prove that in a triangle packing, if edge e appears in m1 and m2, then m1 = m2.

APPROACH:
If m1 ≠ m2 both contain edge e = s(u,v), then {u,v} ⊆ m1 ∩ m2, so |m1 ∩ m2| ≥ 2.
But triangle packing requires |m1 ∩ m2| ≤ 1 for distinct elements. Contradiction.

1 SORRY: Extract the two endpoints from e ∈ m.sym2 and show |m1 ∩ m2| ≥ 2.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

/-- Each edge in a triangle packing appears in at most one packing element. -/
theorem M_edge_unique_owner (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m1 m2 : Finset V) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (he1 : e ∈ m1.sym2) (he2 : e ∈ m2.sym2) :
    m1 = m2 := by
  by_contra hne
  have h_card : (m1 ∩ m2).card ≥ 2 := by
    -- e = s(u,v) with u,v ∈ m1 (from he1) and u,v ∈ m2 (from he2)
    -- Therefore {u,v} ⊆ m1 ∩ m2, so card ≥ 2
    -- Key API: Sym2.mem_iff or Finset.mem_sym2_iff
    sorry
  have h_pairwise := hM.2 hm1 hm2 hne
  omega
