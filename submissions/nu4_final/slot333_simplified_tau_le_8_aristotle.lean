/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a0636b6a-f0ab-4c52-ae7f-e09e66c8f475

The following was proved by Aristotle:

- lemma path4_spine_card (A B C D : Finset V) (h : isPath4 ({A, B, C, D} : Finset (Finset V)) A B C D) :
    (spineVertices A B C D).card = 3

The following was negated by Aristotle:

- lemma triangle_contains_spine_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    (T ∩ spineVertices A B C D).Nonempty

- lemma triangles_at_vertex_cover_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (triangles : Finset (Finset V))
    (h_contain : ∀ T ∈ triangles, T ∈ G.cliqueFinset 3 ∧ v ∈ T) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ G.edgeFinset ∧
    ∀ T ∈ triangles, ∃ e ∈ E, e ∈ T.sym2

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
  slot333: SIMPLIFIED tau_le_8 for PATH_4

  Key insight: Use proven decomposition with better accounting.

  PATH_4: A — B — C — D (consecutive share 1 vertex, non-consecutive disjoint)

  Decomposition: All triangles = ⋃ (T_e for e ∈ M)
  where T_e = triangles sharing edge with e

  Key proven facts:
  1. τ(S_e) ≤ 2 for all e (externals to e)
  2. τ(X_ef) ≤ 2 for adjacent e,f (bridges between e,f)
  3. X_ef = ∅ for disjoint e,f (no bridges between disjoint)

  For PATH_4, the bridges are: X_AB, X_BC, X_CD (3 sets)
  And X_AC = X_AD = X_BD = ∅.

  EXPLICIT 8-EDGE COVER:
  - 2 edges covering S_A ∪ A (from vertex a = A \ (A ∩ B))
  - 2 edges covering S_D ∪ D (from vertex d = D \ (C ∩ D))
  - 2 edges covering X_AB ∪ X_BC (from shared vertex v_BC = B ∩ C)
  - 2 edges covering X_CD (from shared vertex v_CD = C ∩ D) -- wait, overlaps with D

  Actually simpler: Cover from the 4 spine vertices
  - v1 = A ∩ B: 2 edges incident to v1 cover X_AB and parts of A,B
  - v2 = B ∩ C: 2 edges incident to v2 cover X_BC and parts of B,C
  - v3 = C ∩ D: 2 edges incident to v3 cover X_CD and parts of C,D
  - ??? This gives only 6 edges for middle, need to cover S_A and S_D too

  CORRECT: Use endpoint structure
  - τ(T_A) ≤ 4 (proven: tau_Te_le_4_for_endpoint)
  - τ(T_D) ≤ 4 (proven: tau_Te_le_4_for_endpoint_D)
  - T_A ∪ T_D covers EVERYTHING because:
    - S_B ⊆ T_B, but triangles in S_B share vertex with X_AB ⊆ T_A, so they're hit
    - Wait, no that's not right either...

  NEW APPROACH: Use explicit vertex counting
  In PATH_4, the spine has 4 vertices: v_da, v_ab, v_bc, v_cd
  Every triangle in G shares at least one edge, hence at least one vertex.

  Partition triangles by which spine vertex they contain:
  - Triangles containing v_ab: covered by 2 edges incident to v_ab
  - Triangles containing v_bc (but not v_ab): covered by 2 edges incident to v_bc
  - etc.

  Since there are 4 spine vertices and each needs ≤2 edges, we get τ ≤ 8!

  The key lemma: Every triangle shares edge with SOME M-element,
  hence contains at least 2 vertices of some M-element,
  hence contains at least 1 spine vertex.
-/

import Mathlib


set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

-- PATH_4 configuration: A — B — C — D (a path, not a cycle!)
-- Adjacent pairs share exactly 1 vertex, non-adjacent are disjoint
def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧ A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  -- Adjacent pairs share exactly 1 vertex
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  -- Non-adjacent pairs are disjoint (including A and D - endpoints of path)
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩,
                                   v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

lemma nonpacking_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3) (hT_notin : T ∉ M) :
    ∃ X ∈ M, sharesEdgeWith T X := by
  obtain ⟨m, hm_in, hm_inter⟩ := hM.2 T hT_tri hT_notin
  exact ⟨m, hm_in, sharesEdgeWith_iff_card_inter_ge_two T m |>.mpr hm_inter⟩

lemma edge_in_sym2_iff (T : Finset V) (u v : V) :
    s(u, v) ∈ T.sym2 ↔ u ∈ T ∧ v ∈ T := by
  rw [Finset.mem_sym2_iff]
  constructor
  · intro h
    exact ⟨h u (Sym2.mem_iff.mpr (Or.inl rfl)), h v (Sym2.mem_iff.mpr (Or.inr rfl))⟩
  · intro ⟨hu, hv⟩ x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> assumption

-- Every triangle shares edge with some M-element → contains 2 vertices of some M-element
lemma triangle_contains_two_from_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨ ∃ X ∈ M, ∃ u v : V, u ≠ v ∧ u ∈ T ∧ v ∈ T ∧ u ∈ X ∧ v ∈ X := by
  by_cases hT_in : T ∈ M
  · left; exact hT_in
  · right
    obtain ⟨X, hX_in, u, v, huv, hu_T, hv_T, hu_X, hv_X⟩ := by
      obtain ⟨X, hX, hshare⟩ := nonpacking_shares_edge G M hM T hT hT_in
      obtain ⟨u, v, huv, hu_T, hv_T, hu_X, hv_X⟩ := hshare
      exact ⟨X, hX, u, v, huv, hu_T, hv_T, hu_X, hv_X⟩
    exact ⟨X, hX_in, u, v, huv, hu_T, hv_T, hu_X, hv_X⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SPINE VERTEX STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

-- In PATH_4, spine vertices are the 3 shared vertices: A∩B, B∩C, C∩D
-- (A and D don't share a vertex since they're non-adjacent endpoints)
def spineVertices (A B C D : Finset V) : Finset V :=
  (A ∩ B) ∪ (B ∩ C) ∪ (C ∩ D)

lemma path4_spine_card (A B C D : Finset V) (h : isPath4 ({A, B, C, D} : Finset (Finset V)) A B C D) :
    (spineVertices A B C D).card = 3 := by
  -- Each intersection has card 1, and they're pairwise disjoint
  -- Since the intersections are pairwise disjoint and each has 1 element, their union has 3 elements.
  have h_disjoint : Disjoint (A ∩ B) (B ∩ C) ∧ Disjoint (A ∩ B) (C ∩ D) ∧ Disjoint (B ∩ C) (C ∩ D) := by
    unfold isPath4 at h;
    simp_all +decide [ Finset.disjoint_left, Finset.ext_iff ];
  have h_card : (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 := by
    rw [ isPath4 ] at h ; aesop;
  unfold spineVertices; aesop;

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
There exists a graph and a Path4 packing M such that some triangle T is disjoint from the spine of M.
-/
lemma path4_counterexample_exists : ∃ (G : SimpleGraph (Fin 10)) (M : Finset (Finset (Fin 10))) (A B C D : Finset (Fin 10)),
  isPath4 M A B C D ∧
  isMaxPacking G M ∧
  ∃ T ∈ G.cliqueFinset 3, T ∩ spineVertices A B C D = ∅ := by
    -- Define the vertices and sets as given in the provided solution.
    set A : Finset (Fin 10) := {0, 1, 2}
    set B : Finset (Fin 10) := {0, 3, 4}
    set C : Finset (Fin 10) := {3, 5, 6}
    set D : Finset (Fin 10) := {5, 7, 8}
    set T : Finset (Fin 10) := {1, 2, 4};
    -- Define the graph G.
    set G : SimpleGraph (Fin 10) := SimpleGraph.fromRel (fun u v => u ≠ v ∧ (u ∈ A ∧ v ∈ A ∨ u ∈ B ∧ v ∈ B ∨ u ∈ C ∧ v ∈ C ∨ u ∈ D ∧ v ∈ D ∨ u ∈ T ∧ v ∈ T));
    refine' ⟨ G, { A, B, C, D }, A, B, C, D, _, _, _ ⟩;
    · unfold isPath4; simp +decide ;
      native_decide +revert;
    · constructor;
      · constructor;
        · intro t ht;
          simp +zetaDelta at *;
          rcases ht with ( rfl | rfl | rfl | rfl ) <;> simp +decide [ SimpleGraph.isNClique_iff ];
        · native_decide +revert;
      · simp +decide [ SimpleGraph.cliqueFinset ];
        intro t ht htA htB htC htD;
        have h_cases : ∀ t : Finset (Fin 10), t.card = 3 → (∀ u ∈ t, ∀ v ∈ t, u ≠ v → (u ∈ A ∧ v ∈ A ∨ u ∈ B ∧ v ∈ B ∨ u ∈ C ∧ v ∈ C ∨ u ∈ D ∧ v ∈ D ∨ u ∈ T ∧ v ∈ T)) → 2 ≤ #(t ∩ A) ∨ 2 ≤ #(t ∩ B) ∨ 2 ≤ #(t ∩ C) ∨ 2 ≤ #(t ∩ D) := by
          native_decide;
        simp +zetaDelta at *;
        apply h_cases t;
        · exact ht.card_eq;
        · intro u hu v hv huv; have := ht.1 hu hv; simp +decide [ huv ] at this;
          grind;
    · simp +zetaDelta at *;
      exact ⟨ { 1, 2, 4 }, by simp +decide [ SimpleGraph.isNClique_iff ], by simp +decide [ spineVertices ] ⟩

/-
Auxiliary lemma for path4_counterexample_exists.
-/
lemma path4_counterexample_exists_aux : ∃ (G : SimpleGraph (Fin 10)) (M : Finset (Finset (Fin 10))) (A B C D : Finset (Fin 10)),
  isPath4 M A B C D ∧
  isMaxPacking G M ∧
  ∃ T ∈ G.cliqueFinset 3, T ∩ spineVertices A B C D = ∅ := by
    -- Define the vertices and sets as given in the provided solution.
    set A : Finset (Fin 10) := {0, 1, 2}
    set B : Finset (Fin 10) := {0, 3, 4}
    set C : Finset (Fin 10) := {3, 5, 6}
    set D : Finset (Fin 10) := {5, 7, 8}
    set T : Finset (Fin 10) := {1, 2, 4};
    -- Define the graph G.
    set G : SimpleGraph (Fin 10) := SimpleGraph.fromRel (fun u v => u ≠ v ∧ (u ∈ A ∧ v ∈ A ∨ u ∈ B ∧ v ∈ B ∨ u ∈ C ∧ v ∈ C ∨ u ∈ D ∧ v ∈ D ∨ u ∈ T ∧ v ∈ T));
    refine' ⟨ G, { A, B, C, D }, A, B, C, D, _, _, _ ⟩;
    · unfold isPath4; simp +decide ;
      native_decide +revert;
    · constructor;
      · constructor;
        · intro t ht;
          simp +zetaDelta at *;
          rcases ht with ( rfl | rfl | rfl | rfl ) <;> simp +decide [ SimpleGraph.isNClique_iff ];
        · native_decide +revert;
      · simp +decide [ SimpleGraph.cliqueFinset ];
        intro t ht htA htB htC htD;
        have h_cases : ∀ t : Finset (Fin 10), t.card = 3 → (∀ u ∈ t, ∀ v ∈ t, u ≠ v → (u ∈ A ∧ v ∈ A ∨ u ∈ B ∧ v ∈ B ∨ u ∈ C ∧ v ∈ C ∨ u ∈ D ∧ v ∈ D ∨ u ∈ T ∧ v ∈ T)) → 2 ≤ #(t ∩ A) ∨ 2 ≤ #(t ∩ B) ∨ 2 ≤ #(t ∩ C) ∨ 2 ≤ #(t ∩ D) := by
          native_decide;
        simp +zetaDelta at *;
        apply h_cases t;
        · exact ht.card_eq;
        · intro u hu v hv huv; have := ht.1 hu hv; simp +decide [ huv ] at this;
          grind;
    · simp +zetaDelta at *;
      exact ⟨ { 1, 2, 4 }, by simp +decide [ SimpleGraph.isNClique_iff ], by simp +decide [ spineVertices ] ⟩

/-
Explicit definition of the counterexample components and verification of their properties.
-/
def ce_A : Finset (Fin 10) := {0, 1, 2}
def ce_B : Finset (Fin 10) := {0, 3, 4}
def ce_C : Finset (Fin 10) := {3, 5, 6}
def ce_D : Finset (Fin 10) := {5, 7, 8}
def ce_T : Finset (Fin 10) := {1, 2, 4}

def ce_M : Finset (Finset (Fin 10)) := {ce_A, ce_B, ce_C, ce_D}

def ce_G : SimpleGraph (Fin 10) := SimpleGraph.fromRel (fun u v => u ≠ v ∧ (u ∈ ce_A ∧ v ∈ ce_A ∨ u ∈ ce_B ∧ v ∈ ce_B ∨ u ∈ ce_C ∧ v ∈ ce_C ∨ u ∈ ce_D ∧ v ∈ ce_D ∨ u ∈ ce_T ∧ v ∈ ce_T))

lemma ce_is_valid :
  isPath4 ce_M ce_A ce_B ce_C ce_D ∧
  isMaxPacking ce_G ce_M ∧
  ce_T ∈ ce_G.cliqueFinset 3 ∧
  ce_T ∩ spineVertices ce_A ce_B ce_C ce_D = ∅ := by
    apply And.intro;
    · constructor <;> norm_cast;
    · refine' ⟨ _, _, _ ⟩;
      · refine' ⟨ _, _ ⟩;
        · constructor <;> norm_cast;
          unfold ce_M ce_G; simp +decide [ SimpleGraph.cliqueFinset ] ;
          simp +decide [ Set.subset_def, SimpleGraph.isNClique_iff ];
          simp +decide [ Set.Pairwise ];
        · unfold ce_G;
          simp +decide [ SimpleGraph.isNClique_iff ];
          intro t ht ht' ht''; simp_all +decide [ Set.Pairwise ] ;
          native_decide +revert;
      · unfold ce_G ce_T; simp +decide ;
        simp +decide [ SimpleGraph.isNClique_iff ];
      · native_decide

/-
The statement `triangle_contains_spine_vertex` is false for the specific case of `Fin 10`.
-/
lemma specific_counterexample_negation : ¬ (∀ (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj] (M : Finset (Finset (Fin 10))) (hM : isMaxPacking G M) (A B C D : Finset (Fin 10)) (hpath : isPath4 M A B C D) (T : Finset (Fin 10)) (hT : T ∈ G.cliqueFinset 3), (T ∩ spineVertices A B C D).Nonempty) := by
  by_contra h;
  -- Apply the lemma `ce_is_valid` to obtain the specific components and their properties.
  obtain ⟨hM, hT, hT_inter⟩ := ce_is_valid;
  specialize h ce_G ce_M hT ce_A ce_B ce_C ce_D hM ce_T hT_inter.1;
  aesop

/-
The statement `triangle_contains_spine_vertex` is false.
-/
lemma triangle_contains_spine_vertex_false : ¬ (∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (hM : isMaxPacking G M) (A B C D : Finset V) (hpath : isPath4 M A B C D) (T : Finset V) (hT : T ∈ G.cliqueFinset 3), (T ∩ spineVertices A B C D).Nonempty) := by
  push_neg;
  refine' ⟨ _, _, _, _, _, _ ⟩;
  exact ULift ( Fin 10 );
  all_goals try infer_instance;
  refine' SimpleGraph.map _ ( ce_G );
  exact ⟨ fun x => ⟨ x ⟩, fun x y h => by simpa using h ⟩;
  infer_instance;
  refine' ⟨ Finset.image ( fun x : Finset ( Fin 10 ) => Finset.image ( fun y : Fin 10 => ⟨ y ⟩ ) x ) ce_M, _, _ ⟩;
  · constructor;
    · constructor;
      · intro x hx;
        simp +zetaDelta at *;
        rcases hx with ⟨ a, ha, rfl ⟩ ; fin_cases ha <;> simp +decide [ SimpleGraph.isNClique_iff ] ;
        · simp +decide [ SimpleGraph.IsClique, Set.Pairwise ];
          simp +decide [ ce_A, ce_G ];
        · simp +decide [ SimpleGraph.IsClique, Set.Pairwise ];
          simp +decide [ ce_B, ce_G ];
        · simp +decide [ SimpleGraph.IsClique, Set.Pairwise ];
          simp +decide [ ce_C, ce_G ];
        · simp +decide [ SimpleGraph.IsClique, Set.Pairwise ];
          simp +decide [ ce_D, ce_G ];
      · simp +decide [ Set.Pairwise ];
    · intro t ht ht';
      -- Let's choose any triangle $T$ in $G$ that is not in $M$.
      obtain ⟨T, hT⟩ : ∃ T : Finset (Fin 10), T ∈ ce_G.cliqueFinset 3 ∧ Finset.image (fun y : Fin 10 => ⟨y⟩) T = t := by
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        obtain ⟨ T, hT ⟩ := ht;
        refine' ⟨ Finset.univ.filter fun x => ⟨ x ⟩ ∈ t, _, _ ⟩;
        · constructor;
          · intro x hx y hy hxy; specialize T ( show { down := x } ∈ t from by simpa using hx ) ( show { down := y } ∈ t from by simpa using hy ) ; aesop;
          · convert hT using 1;
            refine' Finset.card_bij ( fun x hx => ⟨ x ⟩ ) _ _ _ <;> simp +decide;
        · ext ⟨ x ⟩ ; aesop;
      obtain ⟨m, hm⟩ : ∃ m ∈ ce_M, sharesEdgeWith T m := by
        have := ce_is_valid.2.1.2 T hT.1;
        by_cases h : T ∈ ce_M <;> simp_all +decide [ sharesEdgeWith_iff_card_inter_ge_two ];
      use Finset.image ( fun y : Fin 10 => ⟨ y ⟩ ) m;
      obtain ⟨ u, v, huv, hu, hv, hu', hv' ⟩ := hm.2;
      refine' ⟨ Finset.mem_image_of_mem _ hm.1, _ ⟩;
      refine' Finset.one_lt_card.mpr ⟨ _, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
      exact ⟨ u ⟩;
      · exact ⟨ hT.2 ▸ Finset.mem_image_of_mem _ hu, u, hu', rfl ⟩;
      · grind;
  · refine' ⟨ Finset.image ( fun y : Fin 10 => ⟨ y ⟩ ) ce_A, Finset.image ( fun y : Fin 10 => ⟨ y ⟩ ) ce_B, Finset.image ( fun y : Fin 10 => ⟨ y ⟩ ) ce_C, Finset.image ( fun y : Fin 10 => ⟨ y ⟩ ) ce_D, _, _ ⟩ <;> simp +decide [ isPath4 ];
    refine' ⟨ Finset.image ( fun x : Fin 10 => ⟨ x ⟩ ) ce_T, _, _ ⟩ <;> simp +decide [ SimpleGraph.isNClique_iff ];
    simp +decide [ SimpleGraph.IsClique, Set.Pairwise ];
    simp +decide [ ce_G ]

end AristotleLemmas

/-
KEY LEMMA: Every triangle contains a spine vertex
-/
lemma triangle_contains_spine_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    (T ∩ spineVertices A B C D).Nonempty := by
  -- By triangle_contains_two_from_M, T contains 2 vertices from some X ∈ M
  -- In PATH_4, every X ∈ M = {A, B, C, D} contains 2 spine vertices
  -- If T ∩ X has 2 vertices, at least one must be a spine vertex
  -- (because X has only 1 private vertex)
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  by_contra! h_contra';
  -- Apply the specific counterexample to the assumption.
  apply triangle_contains_spine_vertex_false;
  intro V _ _ G _ M hM A B C D hpath T hT;
  exact?

-/
-- KEY LEMMA: Every triangle contains a spine vertex
lemma triangle_contains_spine_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    (T ∩ spineVertices A B C D).Nonempty := by
  -- By triangle_contains_two_from_M, T contains 2 vertices from some X ∈ M
  -- In PATH_4, every X ∈ M = {A, B, C, D} contains 2 spine vertices
  -- If T ∩ X has 2 vertices, at least one must be a spine vertex
  -- (because X has only 1 private vertex)
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Definitions for a counterexample graph (3 triangles sharing vertex 0) and a lemma stating they are valid triangles containing 0.
-/
abbrev CE_V := Fin 7

def CE_edges : Finset (Sym2 CE_V) :=
  {Sym2.mk (0,1), Sym2.mk (0,2), Sym2.mk (1,2),
   Sym2.mk (0,3), Sym2.mk (0,4), Sym2.mk (3,4),
   Sym2.mk (0,5), Sym2.mk (0,6), Sym2.mk (5,6)}

def CE_G : SimpleGraph CE_V := SimpleGraph.fromEdgeSet (CE_edges : Set (Sym2 CE_V))

instance : DecidableRel CE_G.Adj := fun a b =>
  decidable_of_iff (Sym2.mk (a, b) ∈ CE_edges ∧ a ≠ b) (by simp [CE_G, SimpleGraph.fromEdgeSet_adj])

def CE_triangles : Finset (Finset CE_V) :=
  { {0, 1, 2}, {0, 3, 4}, {0, 5, 6} }

lemma CE_h_contain (T : Finset CE_V) (hT : T ∈ CE_triangles) :
    T ∈ CE_G.cliqueFinset 3 ∧ (0 : CE_V) ∈ T := by
      revert T; native_decide;

/-
Disproof of the cover claim for the specific counterexample graph CE_G.
-/
lemma CE_disproof :
    ¬ ∃ E : Finset (Sym2 CE_V), E.card ≤ 2 ∧ E ⊆ CE_edges ∧
    ∀ T ∈ CE_triangles, ∃ e ∈ E, e ∈ T.sym2 := by
      have h_semiformal : ∀ (E : Finset (Sym2 CE_V)), E ⊆ CE_edges → E.card ≤ 2 → ¬(∀ T ∈ CE_triangles, ∃ e ∈ E, e ∈ T.sym2) := by
        native_decide +revert;
      exact fun ⟨ E, hE₁, hE₂, hE₃ ⟩ => h_semiformal E hE₂ hE₁ hE₃

/-
Helper lemma stating that the edge set of the counterexample graph is exactly the set of edges used to define it.
-/
lemma CE_edges_eq_edgeFinset : CE_G.edgeFinset = CE_edges := by
  native_decide +revert

/-
Formal disproof of the conjecture `triangles_at_vertex_cover_le_2` using the counterexample `CE_G`.
-/
theorem triangles_at_vertex_cover_le_2_false :
  ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (triangles : Finset (Finset V))
    (h_contain : ∀ T ∈ triangles, T ∈ G.cliqueFinset 3 ∧ v ∈ T),
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ G.edgeFinset ∧
    ∀ T ∈ triangles, ∃ e ∈ E, e ∈ T.sym2 := by
  intro h
  specialize h CE_V CE_G 0 CE_triangles CE_h_contain
  rw [CE_edges_eq_edgeFinset] at h
  exact CE_disproof h

end AristotleLemmas

/-
══════════════════════════════════════════════════════════════════════════════
VERTEX-BASED COVER BOUND
══════════════════════════════════════════════════════════════════════════════

Triangles containing a fixed vertex v can be covered by 2 edges from v
-/
lemma triangles_at_vertex_cover_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (triangles : Finset (Finset V))
    (h_contain : ∀ T ∈ triangles, T ∈ G.cliqueFinset 3 ∧ v ∈ T) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ G.edgeFinset ∧
    ∀ T ∈ triangles, ∃ e ∈ E, e ∈ T.sym2 := by
  -- Every triangle containing v has v and 2 other vertices
  -- Pick any 2 edges from v; they hit all triangles at v
  -- Actually, we need 2 edges incident to v that together hit all triangles
  by_contra h;
  apply_assumption;
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  simp +zetaDelta at *;
  use ULift ( Fin 7 );
  refine' ⟨ ⟨ inferInstance ⟩, _ ⟩;
  refine' ⟨ _, _, _, _, _ ⟩;
  refine' SimpleGraph.fromEdgeSet _;
  exact { Sym2.mk ( ⟨ 0, by decide ⟩, ⟨ 1, by decide ⟩ ), Sym2.mk ( ⟨ 0, by decide ⟩, ⟨ 2, by decide ⟩ ), Sym2.mk ( ⟨ 1, by decide ⟩, ⟨ 2, by decide ⟩ ), Sym2.mk ( ⟨ 0, by decide ⟩, ⟨ 3, by decide ⟩ ), Sym2.mk ( ⟨ 0, by decide ⟩, ⟨ 4, by decide ⟩ ), Sym2.mk ( ⟨ 3, by decide ⟩, ⟨ 4, by decide ⟩ ), Sym2.mk ( ⟨ 0, by decide ⟩, ⟨ 5, by decide ⟩ ), Sym2.mk ( ⟨ 0, by decide ⟩, ⟨ 6, by decide ⟩ ), Sym2.mk ( ⟨ 5, by decide ⟩, ⟨ 6, by decide ⟩ ) };
  exact ⟨ 0, by decide ⟩;
  exact { { ⟨ 0, by decide ⟩, ⟨ 1, by decide ⟩, ⟨ 2, by decide ⟩ }, { ⟨ 0, by decide ⟩, ⟨ 3, by decide ⟩, ⟨ 4, by decide ⟩ }, { ⟨ 0, by decide ⟩, ⟨ 5, by decide ⟩, ⟨ 6, by decide ⟩ } };
  · simp +decide [ SimpleGraph.IsNClique ];
  · simp +decide [ Set.subset_def ];
    intro x hx hx'; interval_cases _ : #x <;> simp_all +decide ;
    · rw [ Finset.card_eq_one ] at * ; aesop;
    · rw [ Finset.card_eq_two ] at * ; aesop ( simp_config := { decide := true } ) ;

-/
-- ══════════════════════════════════════════════════════════════════════════════
-- VERTEX-BASED COVER BOUND
-- ══════════════════════════════════════════════════════════════════════════════

-- Triangles containing a fixed vertex v can be covered by 2 edges from v
lemma triangles_at_vertex_cover_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (triangles : Finset (Finset V))
    (h_contain : ∀ T ∈ triangles, T ∈ G.cliqueFinset 3 ∧ v ∈ T) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ G.edgeFinset ∧
    ∀ T ∈ triangles, ∃ e ∈ E, e ∈ T.sym2 := by
  -- Every triangle containing v has v and 2 other vertices
  -- Pick any 2 edges from v; they hit all triangles at v
  -- Actually, we need 2 edges incident to v that together hit all triangles
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8_path4:

PATH_4 vertices:
- A = {a1, a2, v_ab} where a1, a2 are private, v_ab = A ∩ B
- B = {v_ab, b, v_bc} where b is private, v_bc = B ∩ C
- C = {v_bc, c, v_cd} where c is private, v_cd = C ∩ D
- D = {v_cd, d1, d2} where d1, d2 are private

EXPLICIT 8-EDGE COVER:
1. {a1, a2} - private edge of A, covers S_A (externals to A)
2. {a1, v_ab} - edge in A
3. {v_ab, b} - edge in B
4. {v_ab, v_bc} - spine edge, in B, covers bridges X_AB
5. {v_bc, c} - edge in C
6. {v_bc, v_cd} - spine edge, in C, covers bridges X_BC and X_CD
7. {d1, d2} - private edge of D, covers S_D (externals to D)
8. {d1, v_cd} - edge in D

COVERAGE VERIFICATION:
- M-elements: Each hit by 2 of its edges
  - A: edges 1, 2
  - B: edges 3, 4
  - C: edges 5, 6
  - D: edges 7, 8

- Externals S_A: triangles {a1, a2, x} hit by edge 1 = {a1, a2}
- Externals S_D: triangles {d1, d2, x} hit by edge 7 = {d1, d2}
- Externals S_B: share edge with B = {v_ab, b, v_bc}, contain v_ab or v_bc, hit by 3,4,5
- Externals S_C: share edge with C = {v_bc, c, v_cd}, contain v_bc or v_cd, hit by 5,6,8

- Bridges X_AB: contain v_ab (the shared vertex), hit by edges 2,3,4
- Bridges X_BC: contain v_bc (the shared vertex), hit by edges 4,5,6
- Bridges X_CD: contain v_cd (the shared vertex), hit by edges 6,8
-/

-- Define the explicit 8-edge cover for PATH_4
def path4_cover (a1 a2 v_ab b v_bc c v_cd d1 d2 : V) : Finset (Sym2 V) :=
  {s(a1, a2), s(a1, v_ab), s(v_ab, b), s(v_ab, v_bc),
   s(v_bc, c), s(v_bc, v_cd), s(d1, d2), s(d1, v_cd)}

lemma path4_cover_card (a1 a2 v_ab b v_bc c v_cd d1 d2 : V)
    (h_distinct : a1 ≠ a2 ∧ a1 ≠ v_ab ∧ a2 ≠ v_ab ∧ v_ab ≠ b ∧ v_ab ≠ v_bc ∧
                  b ≠ v_bc ∧ v_bc ≠ c ∧ v_bc ≠ v_cd ∧ c ≠ v_cd ∧
                  v_cd ≠ d1 ∧ v_cd ≠ d2 ∧ d1 ≠ d2) :
    (path4_cover a1 a2 v_ab b v_bc c v_cd d1 d2).card ≤ 8 := by
  simp only [path4_cover]
  exact Finset.card_insert_le.trans (by norm_num)

-- Helper: edge in triangle.sym2 means both endpoints are in triangle
lemma edge_covers_triangle (T : Finset V) (u v : V) (hu : u ∈ T) (hv : v ∈ T) :
    s(u, v) ∈ T.sym2 := by
  rw [Finset.mem_sym2_iff]
  intro x hx
  simp only [Sym2.mem_iff] at hx
  rcases hx with rfl | rfl <;> assumption

/- Aristotle failed to find a proof. -/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hcard : M.card = 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ isTriangleCover G E := by
  -- Extract the specific vertices
  -- The explicit construction follows from the proof sketch above
  sorry

end