/-
Tuza ν=4: external_shares_M_edge - Every external triangle shares an M-edge

GOAL: Prove ∃ e ∈ M_edges G M, e ∈ t.sym2 for external triangle t.

APPROACH:
- Maximality: if t ∉ M, then ∃ m ∈ M with |t ∩ m| ≥ 2
- Two 3-sets sharing 2 elements share an edge (the pair)
- That edge is in m.sym2 (hence M_edges) and t.sym2
- Need to show the shared pair is in G.edgeFinset (clique property)

1 SORRY: Show the shared pair {u,v} is in G.edgeFinset using clique property.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

def externals (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => t ∉ M)

/-- Every external triangle shares at least one edge with some M-element. -/
theorem external_shares_M_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ externals G M) :
    ∃ e ∈ M_edges G M, e ∈ t.sym2 := by
  simp only [externals, mem_filter] at ht
  obtain ⟨ht_clique, ht_not_M⟩ := ht
  obtain ⟨m, hm, h_inter⟩ := hM.2 t ht_clique ht_not_M
  -- Get two distinct vertices from t ∩ m
  have h_one : 1 < (t ∩ m).card := by omega
  rw [Finset.one_lt_card] at h_one
  obtain ⟨u, hu, v, hv, huv⟩ := h_one
  use s(u, v)
  constructor
  · simp only [M_edges, mem_biUnion, mem_filter]
    refine ⟨m, hm, ?_, ?_⟩
    · -- s(u,v) ∈ m.sym2
      simp only [Finset.mem_sym2_iff, Sym2.mem_iff]
      intro x hx
      cases hx with
      | inl h => rw [h]; exact Finset.mem_of_mem_inter_right hu
      | inr h => rw [h]; exact Finset.mem_of_mem_inter_right hv
    · -- s(u,v) ∈ G.edgeFinset because m is a clique and u,v ∈ m
      -- Key API: SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.mem_edgeFinset
      sorry
  · -- s(u,v) ∈ t.sym2
    simp only [Finset.mem_sym2_iff, Sym2.mem_iff]
    intro x hx
    cases hx with
    | inl h => rw [h]; exact Finset.mem_of_mem_inter_left hu
    | inr h => rw [h]; exact Finset.mem_of_mem_inter_left hv
