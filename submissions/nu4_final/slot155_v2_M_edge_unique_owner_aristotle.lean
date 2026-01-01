/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a355f17f-8977-4730-95e5-1a93aecb5710
-/

/-
Tuza ν=4: M_edge_unique_owner - Each M-edge appears in exactly one M-element

GOAL: Prove that in a triangle packing, if ACTUAL EDGE e appears in m1 and m2, then m1 = m2.

CRITICAL FIX: Require e ∈ G.edgeFinset to exclude diagonal elements s(v,v).
Finset.sym2 includes diagonals, but actual graph edges are non-diagonal.

APPROACH:
If m1 ≠ m2 both contain edge e = s(u,v) with u ≠ v, then {u,v} ⊆ m1 ∩ m2, so |m1 ∩ m2| ≥ 2.
But triangle packing requires |m1 ∩ m2| ≤ 1 for distinct elements. Contradiction.

1 SORRY: Extract the two distinct endpoints from e and show |m1 ∩ m2| ≥ 2.
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

/-- Each actual edge in a triangle packing appears in at most one packing element.
    Note: We require e ∈ G.edgeFinset to exclude diagonal elements s(v,v). -/
theorem M_edge_unique_owner (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he_edge : e ∈ G.edgeFinset)  -- KEY: e is an actual edge
    (m1 m2 : Finset V) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (he1 : e ∈ m1.sym2) (he2 : e ∈ m2.sym2) :
    m1 = m2 := by
  by_contra hne
  -- Since e ∈ G.edgeFinset, e = s(u,v) with u ≠ v (no self-loops in SimpleGraph)
  -- From he1: u,v ∈ m1. From he2: u,v ∈ m2.
  -- Therefore {u,v} ⊆ m1 ∩ m2, so |m1 ∩ m2| ≥ 2
  have h_card : (m1 ∩ m2).card ≥ 2 := by
    -- e ∈ G.edgeFinset means e = s(u,v) with G.Adj u v, hence u ≠ v
    rw [SimpleGraph.mem_edgeFinset] at he_edge
    -- Extract endpoints from Sym2
    obtain ⟨u, v⟩ := e
    have hne_uv : u ≠ v := G.ne_of_adj he_edge
    -- u,v ∈ m1 (from he1) and u,v ∈ m2 (from he2)
    simp only [Finset.mem_sym2_iff, Sym2.mem_iff] at he1 he2
    have hu1 : u ∈ m1 := he1 u (Or.inl rfl)
    have hv1 : v ∈ m1 := he1 v (Or.inr rfl)
    have hu2 : u ∈ m2 := he2 u (Or.inl rfl)
    have hv2 : v ∈ m2 := he2 v (Or.inr rfl)
    -- {u,v} ⊆ m1 ∩ m2
    have hu_inter : u ∈ m1 ∩ m2 := Finset.mem_inter.mpr ⟨hu1, hu2⟩
    have hv_inter : v ∈ m1 ∩ m2 := Finset.mem_inter.mpr ⟨hv1, hv2⟩
    -- card ≥ 2
    exact Finset.one_lt_card.mpr ⟨u, hu_inter, v, hv_inter, hne_uv⟩
  have h_pairwise := hM.2 hm1 hm2 hne
  omega