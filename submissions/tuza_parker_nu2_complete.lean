/-
Tuza ν=2: Parker's Complete Proof

PARKER'S THEOREM 1.1 (arXiv:2406.06501):
When ν = 2, we have M = {e, f} where e, f are edge-disjoint triangles.
Since e, f are triangles (3 vertices each) that are edge-disjoint:
  |e ∩ f| ≤ 1 (if ≥2 they'd share an edge)

Case 1: |e ∩ f| = 0 (vertex-disjoint)
  - No triangle can share edges with both e and f
  - So T_e \ S_e = ∅, and T_e = S_e
  - τ(T_e) = τ(S_e) ≤ 2

Case 2: |e ∩ f| = 1 (share exactly one vertex v)
  - Bridge triangles (T_e \ S_e) must contain v
  - All triangles in T_e share edge with e AND either:
    - Only with e (S_e), or
    - Also with f (bridges containing v)
  - Cover S_e with ≤2 edges of e containing v
  - These edges also hit bridges (which contain v)
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

/-! ## Structural lemmas for ν=2 -/

-- Edge-disjoint triangles share at most 1 vertex
lemma edge_disjoint_triangles_share_le_1_vertex (e f : Finset V)
    (he : e.card = 3) (hf : f.card = 3)
    (h_disjoint : Disjoint (triangleEdges e) (triangleEdges f)) :
    (e ∩ f).card ≤ 1 := by
  sorry

-- When e, f share 0 vertices, no triangle can share edges with both
lemma no_bridge_when_vertex_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e.card = 3) (hf : f.card = 3)
    (h_inter : e ∩ f = ∅)
    (t : Finset V) (ht : t.card = 3) :
    ¬Disjoint (triangleEdges t) (triangleEdges e) →
    Disjoint (triangleEdges t) (triangleEdges f) := by
  sorry

-- When e, f share exactly vertex v, bridge triangles contain v
lemma bridge_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e.card = 3) (hf : f.card = 3)
    (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t.card = 3)
    (ht_e : ¬Disjoint (triangleEdges t) (triangleEdges e))
    (ht_f : ¬Disjoint (triangleEdges t) (triangleEdges f)) :
    v ∈ t := by
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

-- When ν=2, get the other packing element
lemma nu_2_other_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e : Finset V) (he : e ∈ M) :
    ∃ f ∈ M, f ≠ e ∧ Disjoint (triangleEdges e) (triangleEdges f) := by
  sorry

/-! ## Main theorem for ν=2 -/

lemma tau_Te_le_2_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

end
