/-
TUZA'S CONJECTURE - CONDITIONAL THEOREM (SUCCESS)
Proven by Aristotle (b4549d16-372d-4cbf-8c29-e4aca74ee1be)

WHAT WAS PROVEN:
If TuzaReductionProperty holds (removing ≤2 edges can always decrease ν),
then Tuza's Conjecture holds (τ(G) ≤ 2ν(G)).

This formally verifies the strong induction proof strategy is correct.
The ONLY remaining gap is proving TuzaReductionProperty itself.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical


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

lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
  have h_finite : (G.cliqueFinset 3).powerset.Nonempty :=
    ⟨∅, Finset.mem_powerset.mpr <| Finset.empty_subset _⟩
  have h_exists : ∃ P : Finset (Finset V), P ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint ∧
      ∀ Q ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint, P.card ≥ Q.card :=
    Finset.exists_max_image _ _ ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),
      by simp +decide [IsEdgeDisjoint]⟩⟩
  obtain ⟨P, hP₁, hP₂⟩ := h_exists; use P; aesop
  exact le_antisymm (Finset.le_sup (f := Finset.card) (by aesop)) (Finset.sup_le fun Q hQ => by aesop)

lemma triangle_shares_edge_with_max_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) (hP_card : P.card = trianglePackingNumber G)
    (hP_sub : P ⊆ G.cliqueFinset 3) (hP_disj : IsEdgeDisjoint P)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ p ∈ P, ¬ Disjoint (triangleEdges t) (triangleEdges p) := by
      contrapose! hP_card;
      refine' ne_of_lt ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ _, _ ⟩ ) ) _ );
      exact P ∪ { t };
      · exact Finset.subset_union_left;
      · norm_num +zetaDelta at *;
        rw [ Finset.ext_iff ] ; specialize hP_card t ; aesop;
        unfold triangleEdges at hP_card; simp_all +decide [ Finset.ext_iff ] ;
        obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := Finset.card_eq_three.mp ht.2; specialize hP_card ( Sym2.mk ( x, y ) ) x y; aesop;
      · refine' Finset.le_sup ( f := Finset.card ) _ |> le_trans ( _ : _ ≤ _ ) ; aesop;
        simp_all +decide [ Finset.subset_iff, IsEdgeDisjoint ];
        intro x hx y hy hxy; aesop;
        · exact Disjoint.symm ( hP_card x h_1 );
        · exact hP_disj h_1 h_2 hxy

/--
The Tuza Reduction Property: For any graph with ν > 0, there exist ≤2 edges
whose removal strictly decreases the packing number.

This is the ONLY remaining gap to prove the full Tuza's Conjecture.
-/
def TuzaReductionProperty : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
    trianglePackingNumber G > 0 →
    ∃ (S : Finset (Sym2 V)), S.card ≤ 2 ∧ S ⊆ G.edgeFinset ∧
      trianglePackingNumber (G.deleteEdges S) < trianglePackingNumber G

/--
CONDITIONAL TUZA'S CONJECTURE (PROVEN BY ARISTOTLE)

If TuzaReductionProperty holds, then Tuza's Conjecture holds.

This theorem formally verifies that the strong induction proof strategy is correct.
The only remaining work is to prove TuzaReductionProperty itself.
-/
theorem tuza_conjecture_conditional (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_red : ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      trianglePackingNumber G > 0 →
      ∃ (S : Finset (Sym2 V)), S.card ≤ 2 ∧ S ⊆ G.edgeFinset ∧
        trianglePackingNumber (G.deleteEdges S) < trianglePackingNumber G) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  induction h : trianglePackingNumber G using Nat.strong_induction_on generalizing G with
  | _ k ih =>
    by_cases hk : k = 0
    · subst hk
      have := tuza_base_case G h
      simp [this]
    · have hpos : trianglePackingNumber G > 0 := by omega
      obtain ⟨S, hS_card, hS_sub, hS_reduce⟩ := h_red G hpos
      have h_del := triangleCoveringNumber_le_card_add_deleteEdges G S hS_sub
      have h_smaller : trianglePackingNumber (G.deleteEdges S) < k := by
        rw [← h]; exact hS_reduce
      have h_ih := ih (trianglePackingNumber (G.deleteEdges S)) h_smaller (G.deleteEdges S) rfl
      calc triangleCoveringNumber G
          ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := h_del
        _ ≤ 2 + 2 * trianglePackingNumber (G.deleteEdges S) := by
            have : S.card ≤ 2 := hS_card
            omega
        _ ≤ 2 + 2 * (k - 1) := by
            have : trianglePackingNumber (G.deleteEdges S) ≤ k - 1 := by omega
            omega
        _ = 2 * k := by omega

end
