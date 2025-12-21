/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a2f49fd5-79c5-4192-ac7e-199b5c6c8ed0

The following was proved by Aristotle:

- lemma parker_lemma_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM_sub : M ⊆ G.cliqueFinset 3)
    (hM_disj : IsEdgeDisjoint M)
    (hM_max : M.card = trianglePackingNumber G)
    (e : Finset V) (he : e ∈ M)
    (h1 h2 : Finset V) (hh1 : h1 ∈ S_e G M e) (hh2 : h2 ∈ S_e G M e) (hne : h1 ≠ h2) :
    sharesEdge h1 h2

- lemma parker_lemma_2_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM_sub : M ⊆ G.cliqueFinset 3)
    (hM_disj : IsEdgeDisjoint M)
    (hM_max : M.card = trianglePackingNumber G)
    (e : Finset V) (he : e ∈ M)
    (hM_pos : M.card ≥ 1)
    (H' : Finset (Finset V)) (hH' : H' = G.cliqueFinset 3 \ T_e G e) :
    ∀ N ⊆ H', IsEdgeDisjoint N → N.card ≤ M.card - 1

The following was negated by Aristotle:

- lemma T_e_cover_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) :
    ∃ C : Finset (Sym2 V), C.card ≤ 2 ∧
    ∀ t ∈ T_e G e, ¬ Disjoint (triangleEdges t) C

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```


-/

/-
Parker's Proof of Tuza for ν ≤ 3 (arXiv:2406.06501)
Scaffolded version with key lemmas.

PROOF STRUCTURE:
1. Lemma 2.2: For maximum matching M and e ∈ M, any two triangles in S_e share an edge
   - S_e = {t : t shares edge with e, t doesn't share edge with any other f ∈ M}
   - Proof: If t1, t2 ∈ S_e don't share edge, then (M\{e}) ∪ {t1,t2} is larger matching

2. Lemma 2.3: Removing T_e (all triangles sharing edge with e) leaves graph with ν' = ν - 1
   - T_e = {t : t shares edge with e}
   - Proof: If N is matching in G\T_e with |N| ≥ ν, then N ∪ {e} is larger matching in G

3. Induction: τ(G) ≤ τ(T_e) + τ(G\T_e) ≤ τ(T_e) + 2(ν-1)
   - Need τ(T_e) ≤ 2 for Tuza bound
   - Paper proves this via case analysis for ν ≤ 3
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

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

def sharesEdge (t1 t2 : Finset V) : Prop :=
  ¬ Disjoint (triangleEdges t1) (triangleEdges t2)

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun h => sharesEdge h e)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun h =>
    sharesEdge h e ∧ ∀ f ∈ M, f ≠ e → ¬ sharesEdge h f)

lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M, M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M ∧ M.card = trianglePackingNumber G := by
  have h : (G.cliqueFinset 3).powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
  have h_max := Finset.exists_max_image _ _ ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [IsEdgeDisjoint]⟩⟩
  obtain ⟨M, hM₁, hM₂⟩ := h_max
  simp [Finset.mem_filter, Finset.mem_powerset] at hM₁
  exact ⟨M, hM₁.1, hM₁.2, le_antisymm (Finset.le_sup (by simp_all)) (Finset.sup_le fun Q hQ => by simp_all)⟩

lemma parker_lemma_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM_sub : M ⊆ G.cliqueFinset 3)
    (hM_disj : IsEdgeDisjoint M)
    (hM_max : M.card = trianglePackingNumber G)
    (e : Finset V) (he : e ∈ M)
    (h1 h2 : Finset V) (hh1 : h1 ∈ S_e G M e) (hh2 : h2 ∈ S_e G M e) (hne : h1 ≠ h2) :
    sharesEdge h1 h2 := by
  -- If $h1$ and $h2$ were edge-disjoint, then their union would form a larger edge-disjoint set, contradicting the maximality of $M$.
  by_contra h_disjoint;
  -- If $h1$ and $h2$ were edge-disjoint, then their union with $M$ would form a larger edge-disjoint set, contradicting the maximality of $M$.
  have h_union : (M \ {e}) ∪ {h1, h2} ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint ((M \ {e}) ∪ {h1, h2}) := by
    unfold S_e at hh1 hh2; aesop;
    · simp_all +decide [ Finset.subset_iff ];
    · intro f hf g hg hfg; simp_all +decide [ IsEdgeDisjoint ] ;
      rcases hf with ( rfl | rfl | ⟨ hf, hf' ⟩ ) <;> rcases hg with ( rfl | rfl | ⟨ hg, hg' ⟩ ) <;> simp_all +decide [ sharesEdge ];
      · exact h_disjoint.symm;
      · exact right _ hf hf' |> Disjoint.symm;
      · -- Since $f \in M$ and $f \neq e$, we can apply the hypothesis $right_1$ to conclude that $triangleEdges g$ is disjoint from $triangleEdges f$.
        have := right_1 f hf hf'; exact this.symm;
      · exact hM_disj hf hg hfg;
  have h_card : ((M \ {e}) ∪ {h1, h2}).card > M.card := by
    have h_card : ((M \ {e}) ∪ {h1, h2}).card = (M \ {e}).card + 2 := by
      rw [ Finset.card_union_of_disjoint ] <;> simp_all +decide [ Finset.disjoint_left ];
      intro a ha ha_ne; simp_all +decide [ S_e ] ;
      exact ⟨ by rintro rfl; exact hh1.2.2 _ ha ha_ne ( by tauto ), by rintro rfl; exact hh2.2.2 _ ha ha_ne ( by tauto ) ⟩;
    grind;
  have h_contradiction : ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card ≥ ((M \ {e}) ∪ {h1, h2}).card := by
    exact Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h_union.1, h_union.2 ⟩ );
  exact h_card.not_le ( hM_max ▸ h_contradiction )

lemma parker_lemma_2_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM_sub : M ⊆ G.cliqueFinset 3)
    (hM_disj : IsEdgeDisjoint M)
    (hM_max : M.card = trianglePackingNumber G)
    (e : Finset V) (he : e ∈ M)
    (hM_pos : M.card ≥ 1)
    (H' : Finset (Finset V)) (hH' : H' = G.cliqueFinset 3 \ T_e G e) :
    ∀ N ⊆ H', IsEdgeDisjoint N → N.card ≤ M.card - 1 := by
  intros N hN_sub hN_disj
  have hN_card : (N ∪ {e}).card ≤ M.card := by
    refine' hM_max ▸ _;
    -- Since $N \cup \{e\}$ is an edge-disjoint set of triangles in $G$, we have $|N \cup \{e\}| \leq \nu(G)$ by definition of $\nu(G)$.
    have h_union : IsEdgeDisjoint (N ∪ {e}) := by
      intro x hx y hy hxy; by_cases hx' : x = e <;> by_cases hy' : y = e <;> simp_all +decide [ IsEdgeDisjoint ] ;
      · have := hN_sub hy; simp_all +decide [ T_e ] ;
        -- Since $y \neq e$, their triangleEdges are disjoint.
        have h_disjoint : Disjoint (triangleEdges y) (triangleEdges e) := by
          exact Classical.not_not.1 ( this.2 this.1 );
        exact h_disjoint.symm;
      · have := hN_sub hx; aesop;
        contrapose! right; unfold T_e at *; aesop;
      · exact hN_disj hx hy hxy;
    refine' Finset.le_sup ( f := Finset.card ) _;
    simp_all +decide [ Finset.subset_iff ];
  by_cases h : e ∈ N <;> aesop;
  · have := hN_sub h; simp_all +decide [ T_e ] ;
    unfold sharesEdge at this; aesop;
    unfold triangleEdges at right; simp_all +decide [ Finset.ext_iff ] ;
    rcases left with ⟨ he₁, he₂ ⟩ ; rcases Finset.card_eq_three.mp he₂ with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; specialize right ( Sym2.mk ( x, y ) ) x y ; aesop;
  · exact Nat.le_sub_one_of_lt hN_card

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Defines a 'flower' graph with a central triangle and 3 petals, and asserts it is a counterexample to the covering bound.
-/
def flowerEdges : Finset (Sym2 (Fin 6)) :=
  {Sym2.mk (0, 1), Sym2.mk (1, 2), Sym2.mk (0, 2),
   Sym2.mk (0, 3), Sym2.mk (1, 3),
   Sym2.mk (1, 4), Sym2.mk (2, 4),
   Sym2.mk (0, 5), Sym2.mk (2, 5)}

def flowerGraph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet (flowerEdges : Set (Sym2 (Fin 6)))

instance : DecidableRel flowerGraph.Adj := fun a b =>
  decidable_of_iff (Sym2.mk (a, b) ∈ flowerEdges ∧ a ≠ b) (by
    simp [flowerGraph, SimpleGraph.fromEdgeSet]
  )

lemma flower_counterexample :
    let G := flowerGraph
    let e : Finset (Fin 6) := {0, 1, 2}
    e ∈ G.cliqueFinset 3 ∧
    ∀ C : Finset (Sym2 (Fin 6)), C.card ≤ 2 →
    ∃ t ∈ T_e G e, Disjoint (triangleEdges t) C := by
      bound;
      · native_decide +revert;
      · -- Let's unfold the definition of `T_e`.
        unfold T_e;
        unfold sharesEdge; simp +decide ;
        native_decide +revert

/-
Disproves the T_e_cover_bound conjecture using the flower graph counterexample.
-/
lemma T_e_cover_bound_false : ¬ (∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) (he : e ∈ G.cliqueFinset 3), ∃ C : Finset (Sym2 V), C.card ≤ 2 ∧ ∀ t ∈ T_e G e, ¬ Disjoint (triangleEdges t) C) := by
  intro h_contra;
  contrapose! h_contra;
  refine' ⟨ _, _, _, _, _, _ ⟩;
  exact ULift ( Fin 6 );
  all_goals try infer_instance;
  exact SimpleGraph.comap ( fun x => ULift.down x ) flowerGraph;
  infer_instance;
  unfold T_e triangleEdges; simp +decide ;
  refine' ⟨ { ⟨ 0 ⟩, ⟨ 1 ⟩, ⟨ 2 ⟩ }, _, _ ⟩ <;> simp +decide [ SimpleGraph.isNClique_iff ];
  intro x hx; unfold sharesEdge; simp +decide [ SimpleGraph.comap, SimpleGraph.isClique_iff ] ;
  revert x; native_decide;

/-
The number of edges in a triangle (clique of size 3) is 3.
-/
lemma triangleEdges_card_eq_three {V : Type*} [DecidableEq V] (t : Finset V) (h : t.card = 3) :
  (triangleEdges t).card = 3 := by
    refine' le_antisymm _ _;
    · have := Finset.card_eq_three.mp h;
      rcases this with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩;
      exact le_trans ( Finset.card_le_card ( show ( { x, y, z } |> Finset.offDiag |> Finset.image fun x => Sym2.mk ( x.1, x.2 ) ) ⊆ { Sym2.mk ( x, y ), Sym2.mk ( x, z ), Sym2.mk ( y, z ) } by aesop_cat ) ) ( Finset.card_insert_le _ _ |> le_trans <| add_le_add_right ( Finset.card_insert_le _ _ ) _ );
    · unfold triangleEdges; aesop;
      rw [ Finset.card_eq_three ] at h ; aesop;
      refine' Finset.two_lt_card.2 _ ; simp_all +decide [ Finset.mem_offDiag ];
      refine' ⟨ _, ⟨ w, w_1, ⟨ by tauto, by tauto, by tauto ⟩, rfl ⟩, _, ⟨ w, w_2, ⟨ by tauto, by tauto, by tauto ⟩, rfl ⟩, _, ⟨ w_1, w_2, ⟨ by tauto, by tauto, by tauto ⟩, rfl ⟩, _, _, _ ⟩ <;> simp +decide [ *, Sym2.eq_iff ]

/-
Corrected version of the conjecture with bound 3.
-/
lemma T_e_cover_bound_corrected (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) :
    ∃ C : Finset (Sym2 V), C.card ≤ 3 ∧
    ∀ t ∈ T_e G e, ¬ Disjoint (triangleEdges t) C := by
  have h_card : e.card = 3 := by
    rw [G.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at he
    exact he.2
  use triangleEdges e
  constructor
  · rw [triangleEdges_card_eq_three e h_card]
  · intro t ht
    unfold T_e at ht
    rw [Finset.mem_filter] at ht
    exact ht.2

/-
Shows that the existence of a cover of size 2 for the flower graph leads to a contradiction.
-/
lemma flower_contradiction (h : ∃ C : Finset (Sym2 (Fin 6)), C.card ≤ 2 ∧ ∀ t ∈ T_e flowerGraph {0, 1, 2}, ¬ Disjoint (triangleEdges t) C) : False := by
  obtain ⟨C, hC_card, hC_cover⟩ := h
  have := flower_counterexample.2 C hC_card
  obtain ⟨t, ht_Te, ht_disj⟩ := this
  specialize hC_cover t ht_Te
  contradiction

end AristotleLemmas

lemma T_e_cover_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) :
    ∃ C : Finset (Sym2 V), C.card ≤ 2 ∧
    ∀ t ∈ T_e G e, ¬ Disjoint (triangleEdges t) C := by
  by_cases h : ∃ C : Finset ( Sym2 V ), C.card ≤ 2 ∧ ∀ t ∈ T_e G e, ¬Disjoint ( triangleEdges t ) C;
  sorry;
  · -- Wait, there's a mistake. We can actually prove the opposite.
    negate_state;
    -- Proof starts here:
    -- Let's choose the flower graph as our counterexample.
    use ULift (Fin 6);
    refine' ⟨ inferInstance, inferInstance, _, _, _ ⟩;
    refine' SimpleGraph.fromEdgeSet ( flowerEdges.image ( fun x : Sym2 ( Fin 6 ) => Sym2.map ( fun y : Fin 6 => ULift.up y ) x ) );
    infer_instance;
    refine' ⟨ { ⟨ 0 ⟩, ⟨ 1 ⟩, ⟨ 2 ⟩ }, _, _ ⟩ <;> simp +decide [ SimpleGraph.IsNClique ];
    intro x hx;
    -- Since $x$ has at most 2 edges, and there are three possible triangles in $T_e$, at least one of these triangles must not share any edges with $x$.
    have h_triangle : ∃ t ∈ ({ {⟨0⟩, ⟨1⟩, ⟨2⟩}, {⟨0⟩, ⟨1⟩, ⟨3⟩}, {⟨1⟩, ⟨2⟩, ⟨4⟩}, {⟨0⟩, ⟨2⟩, ⟨5⟩} } : Finset (Finset (ULift (Fin 6)))), Disjoint (triangleEdges t) x := by
      native_decide +revert;
    obtain ⟨ t, ht₁, ht₂ ⟩ := h_triangle; use t; simp_all +decide [ T_e ] ;
    rcases ht₁ with ( rfl | rfl | rfl | rfl ) <;> simp +decide [ SimpleGraph.IsNClique, sharesEdge ];
    · simp +decide [ SimpleGraph.isNClique_iff ];
    · simp +decide [ SimpleGraph.isNClique_iff ];
    · simp +decide [ SimpleGraph.isNClique_iff ];
    · simp +decide [ SimpleGraph.isNClique_iff ]

-/
lemma T_e_cover_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) :
    ∃ C : Finset (Sym2 V), C.card ≤ 2 ∧
    ∀ t ∈ T_e G e, ¬ Disjoint (triangleEdges t) C := by
  sorry

/- Aristotle failed to find a proof. -/
theorem tuza_case_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) : triangleCoveringNumber G ≤ 6 := by
  sorry

/- Aristotle failed to find a proof. -/
theorem tuza_case_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  sorry

end