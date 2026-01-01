/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f7bd8a26-61dc-4a7a-b67b-3e67c5629499

The following was negated by Aristotle:

- theorem M_edge_unique_owner (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m1 m2 : Finset V) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (he1 : e ∈ m1.sym2) (he2 : e ∈ m2.sym2) :
    m1 = m2

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
Tuza ν=4: M_edge_unique_owner - Each M-edge appears in exactly one M-element

GOAL: Prove that in a triangle packing, if edge e appears in m1 and m2, then m1 = m2.

APPROACH:
If m1 ≠ m2 both contain edge e = s(u,v), then {u,v} ⊆ m1 ∩ m2, so |m1 ∩ m2| ≥ 2.
But triangle packing requires |m1 ∩ m2| ≤ 1 for distinct elements. Contradiction.

1 SORRY: Extract the two endpoints from e ∈ m.sym2 and show |m1 ∩ m2| ≥ 2.
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Helper lemmas: `diag_in_sym2` confirms that diagonals are in `sym2`. `M_edge_unique_owner_of_not_isDiag` proves the theorem under the assumption that the edge is not a diagonal.
-/
theorem diag_in_sym2 {V : Type*} [DecidableEq V] (s : Finset V) (v : V) (h : v ∈ s) :
    Sym2.mk (v, v) ∈ s.sym2 := by
      -- By definition of Sym2, the pair (v, v) is in the sym2 of s.
      simp [Sym2.mk];
      assumption

theorem M_edge_unique_owner_of_not_isDiag {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : ¬e.IsDiag) (m1 m2 : Finset V) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (he1 : e ∈ m1.sym2) (he2 : e ∈ m2.sym2) :
    m1 = m2 := by
      have := hM.2 hm1 hm2;
      contrapose! this;
      rcases e with ⟨ x, y ⟩ ; simp_all +decide [ Finset.ext_iff, Sym2.forall ];
      exact Finset.one_lt_card.2 ⟨ x, by aesop, y, by aesop ⟩

/-
Counterexample showing the theorem is false for diagonal edges. `badG` is K5. `badm1` and `badm2` share vertex 0. `bade` is the diagonal at 0.
-/
def badG : SimpleGraph (Fin 5) := ⊤
def badm1 : Finset (Fin 5) := {0, 1, 2}
def badm2 : Finset (Fin 5) := {0, 3, 4}
def badM : Finset (Finset (Fin 5)) := {badm1, badm2}
def bade : Sym2 (Fin 5) := Sym2.mk (0, 0)

lemma bad_counterexample : ∃ (G : SimpleGraph (Fin 5)) (M : Finset (Finset (Fin 5))) (e : Sym2 (Fin 5)) (m1 m2 : Finset (Fin 5)),
    isTrianglePacking G M ∧ m1 ∈ M ∧ m2 ∈ M ∧ e ∈ m1.sym2 ∧ e ∈ m2.sym2 ∧ m1 ≠ m2 := by
  use badG, badM, bade, badm1, badm2
  simp only [isTrianglePacking, badM, badm1, badm2, bade, SimpleGraph.cliqueFinset, badG]
  -- Show that the set of triangles is indeed a valid triangle packing.
  simp +decide [Finset.subset_iff]

/-
Explicit negation of the theorem `M_edge_unique_owner`, proved using `bad_counterexample`.
-/
theorem M_edge_unique_owner_is_false : ¬ (∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m1 m2 : Finset V) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (he1 : e ∈ m1.sym2) (he2 : e ∈ m2.sym2),
    m1 = m2) := by
      push_neg;
      use ULift ( Fin 5 );
      refine' ⟨ inferInstance, inferInstance, _, _, _, _, _ ⟩;
      refine' ⊤;
      infer_instance;
      exact { { ⟨ 0 ⟩, ⟨ 1 ⟩, ⟨ 2 ⟩ }, { ⟨ 0 ⟩, ⟨ 3 ⟩, ⟨ 4 ⟩ } };
      · constructor <;> simp +decide [ isTrianglePacking ];
      · exists Sym2.mk ( ⟨ 0 ⟩, ⟨ 0 ⟩ ), { ⟨ 0 ⟩, ⟨ 1 ⟩, ⟨ 2 ⟩ }, { ⟨ 0 ⟩, ⟨ 3 ⟩, ⟨ 4 ⟩ }

/-
Lemma: If a non-diagonal edge is in the sym2 of two finsets, their intersection has cardinality at least 2.
-/
theorem overlap_of_edge {V : Type*} [DecidableEq V] (e : Sym2 V) (m1 m2 : Finset V)
    (he1 : e ∈ m1.sym2) (he2 : e ∈ m2.sym2) (h : ¬e.IsDiag) :
    2 ≤ (m1 ∩ m2).card := by
      rcases e with ⟨ x, y ⟩;
      exact Finset.one_lt_card.2 ⟨ x, by aesop, y, by aesop ⟩

end AristotleLemmas

/-
Each edge in a triangle packing appears in at most one packing element.
-/
theorem M_edge_unique_owner (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m1 m2 : Finset V) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (he1 : e ∈ m1.sym2) (he2 : e ∈ m2.sym2) :
    m1 = m2 := by
  by_contra hne
  have h_card : (m1 ∩ m2).card ≥ 2 := by
    -- e = s(u,v) with u,v ∈ m1 (from he1) and u,v ∈ m2 (from he2)
    -- Therefore {u,v} ⊆ m1 ∩ m2, so card ≥ 2
    -- Key API: Sym2.mem_iff or Finset.mem_sym2_iff
    -- Wait, there's a mistake. We can actually prove the opposite.
    negate_state;
    -- Proof starts here:
    -- Let's choose the specific counterexample from the provided solution.
    use ULift (Fin 5);
    refine' ⟨ inferInstance, inferInstance, ⊤, _, _ ⟩ <;> norm_num;
    infer_instance;
    -- Let's choose the set of triangles $M = \{ \{0, 1, 2\}, \{0, 3, 4\} \}$.
    use { {⟨0⟩, ⟨1⟩, ⟨2⟩}, {⟨0⟩, ⟨3⟩, ⟨4⟩} };
    simp +decide [ isTrianglePacking ]
  have h_pairwise := hM.2 hm1 hm2 hne
  omega

-/
/-- Each edge in a triangle packing appears in at most one packing element. -/
theorem M_edge_unique_owner (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m1 m2 : Finset V) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (he1 : e ∈ m1.sym2) (he2 : e ∈ m2.sym2) :
    m1 = m2 := by
  by_contra hne
  have h_card : (m1 ∩ m2).card ≥ 2 := by
    -- e = s(u,v) with u,v ∈ m1 (from he1) and u,v ∈ m2 (from he2)
    -- Therefore {u,v} ⊆ m1 ∩ m2, so card ≥ 2
    -- Key API: Sym2.mem_iff or Finset.mem_sym2_iff
    sorry
  have h_pairwise := hM.2 hm1 hm2 hne
  omega