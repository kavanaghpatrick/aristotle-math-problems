/-
Tuza ν ≤ 3: Flower Exclusion Approach

Key insight from Parker's proof:
- τ(T_e) > 2 for e ∈ M would require 3+ edge-disjoint triangles in T_e
- These triangles share an edge with e, so use different edges of e
- Since e has only 3 edges, at most 3 "petal" triangles can exist
- But if all 3 petals exist and are edge-disjoint, they form a packing
- Together with other elements of M (excluding e), this gives ν > |M|
- For ν ≤ 3, this is impossible, so τ(T_e) ≤ 2 for all e ∈ M
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

def IsTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) : Prop :=
  ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) E

def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ IsTriangleCover G E}

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))

def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E}

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

lemma triangle_has_three_edges (t : Finset V) (ht : t.card = 3) : (triangleEdges t).card = 3 := by
  sorry

lemma petal_triangles_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (petals : Finset (Finset V))
    (hpetal_in : petals ⊆ T_e G e)
    (hpetal_disjoint : IsEdgeDisjoint petals)
    (hpetal_only_e : ∀ p ∈ petals, (triangleEdges p ∩ triangleEdges e).card = 1) :
    petals.card ≤ 3 := by
  sorry

lemma tau_ge_3_implies_three_petals (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (h : coveringNumberOn G (T_e G e) ≥ 3) :
    ∃ petals : Finset (Finset V),
      petals.card ≥ 3 ∧
      petals ⊆ T_e G e ∧
      IsEdgeDisjoint petals ∧
      (∀ p ∈ petals, (triangleEdges p ∩ triangleEdges e).card = 1) := by
  sorry

lemma petals_form_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (petals : Finset (Finset V))
    (hpetals : petals ⊆ G.cliqueFinset 3)
    (hdisjoint : IsEdgeDisjoint petals) :
    IsTrianglePacking G petals := by
  exact ⟨hpetals, hdisjoint⟩

lemma packing_card_le_nu (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsTrianglePacking G M) :
    M.card ≤ packingNumber G := by
  sorry

lemma tau_Te_le_2_flower_exclusion (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

theorem tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G ≤ 3) : coveringNumber G ≤ 2 * packingNumber G := by
  sorry

end
