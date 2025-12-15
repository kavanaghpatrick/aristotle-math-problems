/-
TUZA'S CONJECTURE - FULL PROBLEM WITH PROVEN BUILDING BLOCKS
τ(G) ≤ 2ν(G) for ALL graphs G

Includes all lemmas proven for ν=1 case as building blocks.
Goal: Prove the FULL conjecture.
-/

import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 4000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

-- PROVEN: Base case ν=0
lemma tuza_base_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  have h_no_triangles : (G.cliqueFinset 3).card = 0 := by
    contrapose! h
    refine' ne_of_gt (lt_of_lt_of_le _ (Finset.le_sup (f := Finset.card) 
      (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr 
        (Classical.choose_spec (Finset.card_pos.mp (Nat.pos_of_ne_zero h)))), _⟩))) <;> norm_num
    intro x hx y hy; aesop
  unfold triangleCoveringNumber IsTriangleCovering; aesop
  rw [show (Finset.image Finset.card (Finset.filter (fun S => (G.deleteEdges S).CliqueFree 3) 
    G.edgeFinset.powerset)).min = some 0 from ?_]
  · rfl
  · refine' le_antisymm _ _
    · refine' Finset.min_le _; aesop
    · simp +decide [Finset.min]
      exact fun _ _ _ => WithTop.coe_le_coe.mpr (Nat.zero_le _)

-- PROVEN: Deletion lemma (key for induction)
lemma triangleCoveringNumber_le_card_add_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) :
    triangleCoveringNumber G ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (Sym2 V), T ⊆ (G.deleteEdges S).edgeFinset ∧ 
    IsTriangleCovering (G.deleteEdges S) T ∧ T.card = triangleCoveringNumber (G.deleteEdges S) := by
    unfold triangleCoveringNumber; aesop
    have := Finset.min_of_nonempty (show Finset.Nonempty (Finset.image Finset.card 
      (Finset.filter (IsTriangleCovering (G.deleteEdges S)) 
        (G.deleteEdges S).edgeFinset.powerset)) from ?_); aesop
    · have := Finset.mem_of_min h; aesop
    · simp +zetaDelta at *; use (G.deleteEdges S).edgeFinset; simp [IsTriangleCovering]
  have h_union : IsTriangleCovering G (S ∪ T) := by unfold IsTriangleCovering at *; aesop
  have h_union_card : triangleCoveringNumber G ≤ (S ∪ T).card := by
    unfold triangleCoveringNumber
    have h_card : (S ∪ T).card ∈ Finset.image Finset.card 
      (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
      simp_all +decide [Finset.subset_iff, SimpleGraph.deleteEdges]
      exact ⟨S ∪ T, ⟨fun x hx => by aesop, h_union⟩, rfl⟩
    have := Finset.min_le h_card; aesop
    cases h : Finset.min (Finset.image Finset.card 
      (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) <;> aesop
  exact h_union_card.trans (Finset.card_union_le _ _) |> le_trans <| by rw [hT.2.2]

-- PROVEN: ν=1 implies τ≤2
lemma tuza_case_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  sorry -- Full proof in tuza_SUCCESS_nu1_case.lean (400+ lines)

-- Monotonicity: removing edges doesn't increase packing
lemma packing_mono_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) :
    trianglePackingNumber (G.deleteEdges S) ≤ trianglePackingNumber G := by
  unfold trianglePackingNumber
  apply Finset.sup_mono
  intro P hP
  simp only [Finset.mem_filter, Finset.mem_powerset] at hP ⊢
  constructor
  · intro t ht
    have := hP.1 ht
    simp only [SimpleGraph.mem_cliqueFinset_iff] at this ⊢
    exact ⟨this.1.mono (SimpleGraph.deleteEdges_le _ _), this.2⟩
  · exact hP.2

/-
TUZA'S CONJECTURE - THE MAIN THEOREM
τ(G) ≤ 2ν(G) for all graphs G
-/
theorem tuza_conjecture (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  sorry

end
