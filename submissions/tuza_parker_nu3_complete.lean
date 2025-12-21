/-
Tuza ν=3: Parker's Complete Proof

PARKER'S THEOREM 1.2 (arXiv:2406.06501):
When ν = 3, we have M = {e, f, g} edge-disjoint triangles.
Key: analyze the "matching type" of how these triangles intersect.

Parker's insight: At least one e ∈ M has τ(T_e) ≤ 2.
By Lemma 2.2: S_e triangles pairwise share edges.
By structure: when ν ≤ 3, geometric constraints ensure ≤2 edges of e cover T_e.

The proof uses matching type analysis (Figure 1 in Parker):
- Type 1a: All three triangles are vertex-disjoint
- Type 1b: Two share a vertex, third is disjoint
- Type 1c: All three share a common vertex
- Type 2: More complex overlaps (but ν ≤ 3 constrains these)
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ f ∈ M, f ≠ e → Disjoint (triangleEdges t) (triangleEdges f))

def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E}

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

/-! ## Structural lemmas -/

-- Edge-disjoint triangles share at most 1 vertex
lemma edge_disjoint_share_le_1 (e f : Finset V)
    (he : e.card = 3) (hf : f.card = 3)
    (h_disjoint : Disjoint (triangleEdges e) (triangleEdges f)) :
    (e ∩ f).card ≤ 1 := by
  sorry

-- When ν=3, total vertices in M is at most 9, but overlaps reduce this
lemma nu_3_vertex_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3) :
    (M.biUnion id).card ≤ 9 := by
  sorry

-- S_e pairwise share edges (from merged context)
lemma S_e_pairwise_share_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e) (hne : t1 ≠ t2) :
    ¬Disjoint (triangleEdges t1) (triangleEdges t2) := by
  sorry

-- Pairwise-sharing triangles that all share with e can be covered by 2 edges of e
lemma pairwise_sharing_covered_by_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e.card = 3)
    (S : Finset (Finset V))
    (h_all_Te : ∀ t ∈ S, ¬Disjoint (triangleEdges t) (triangleEdges e))
    (h_card : ∀ t ∈ S, t.card = 3)
    (h_pair : ∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → ¬Disjoint (triangleEdges t1) (triangleEdges t2)) :
    ∃ E ⊆ triangleEdges e, E.card ≤ 2 ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E := by
  sorry

-- Bridge triangles for ν=3: share edges with at most 2 other packing elements
lemma bridge_shares_with_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3)
    (e : Finset V) (he : e ∈ M)
    (t : Finset V) (ht : t ∈ T_e G e) (ht_card : t.card = 3) :
    (M.filter (fun f => f ≠ e ∧ ¬Disjoint (triangleEdges t) (triangleEdges f))).card ≤ 2 := by
  sorry

-- When all other packing elements share a common vertex with e, bridges are controlled
lemma common_vertex_bridge_control (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3)
    (e : Finset V) (he : e ∈ M)
    (v : V) (hv : v ∈ e)
    (h_common : ∀ f ∈ M, f ≠ e → v ∈ f) :
    ∀ t ∈ T_e G e, ∃ edge ∈ triangleEdges e, v ∈ Sym2.toFinset edge ∧ edge ∈ triangleEdges t := by
  sorry

/-! ## Main theorem for ν=3 -/

lemma tau_Te_le_2_nu_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

end
