/-
Tuza ν=2 Case: Focused Submission

STRATEGY (from multi-agent analysis):
When ν=2, M = {e, f} where e,f are edge-disjoint triangles.
- S_e = triangles sharing edge with e but NOT with f
- T_e \ S_e = triangles sharing edge with BOTH e and f (bridges)

KEY INSIGHT: A bridge triangle t sharing edges with both e and f has:
- 2 vertices from e (shared edge)
- 2 vertices from f (shared edge)
- e and f are edge-disjoint (packing)
- So t shares exactly 1 vertex with both e and f beyond the shared edges

This means bridges are highly constrained. The 2 edges covering S_e
also cover bridges because all triangles in T_e share an edge with e.
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

-- When ν=2, M has exactly 2 elements: e and some f ≠ e
lemma nu_2_other_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e : Finset V) (he : e ∈ M) :
    ∃ f ∈ M, f ≠ e := by
  have h : (M.erase e).card = 1 := by simp [Finset.card_erase_of_mem he, hnu]
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp h
  use f
  have : f ∈ M.erase e := by rw [hf]; exact Finset.mem_singleton_self f
  simp only [Finset.mem_erase] at this
  exact ⟨this.2, this.1⟩

-- Key: when ν=2, τ(T_e) ≤ 2
lemma tau_Te_le_2_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

end
