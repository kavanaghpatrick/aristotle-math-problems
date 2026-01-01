/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6dddd795-58d2-4707-ba0c-07d23f261086

The following was proved by Aristotle:

- lemma M_char_edge_sum_M_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ G.edgeFinset)
    (m : Finset V) (hm : m ∈ M) (he_m : e ∈ m.sym2) :
    ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum (M_char M) = 1

- lemma M_char_weight_eq_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    packingWeight G (M_char M) = M.card

The following was negated by Aristotle:

- lemma M_edge_in_exactly_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2

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
Tuza nu=4 Cycle_4: Fractional Packing Lower Bound (nu* >= 4)

GOAL: Prove that the fractional packing number is at least 4.
      This is the EASY direction - we construct a feasible packing.

APPROACH:
1. Define fractional packing predicate
2. Construct M_char: assign weight 1 to each M-element, 0 to externals
3. Prove M_char is a valid fractional packing
4. Show it achieves weight 4

SCAFFOLDING:
- M_edge_in_exactly_one (slot64c - PROVEN)

SORRIES FOR ARISTOTLE TO COMPLETE
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- DEFINITIONS

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

/-- A fractional triangle packing assigns weights to triangles
    such that each edge has total weight <= 1 -/
def IsFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
  (∀ t, t ∉ G.cliqueFinset 3 → w t = 0) ∧
  (∀ e ∈ G.edgeFinset,
    ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w ≤ 1)

/-- Total weight of a fractional packing -/
def packingWeight (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : ℝ :=
  (G.cliqueFinset 3).sum w

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

#check Finset.sym2
#print Finset.sym2
example : s(1, 1) ∈ ({1, 2} : Finset ℕ).sym2 := by
  -- Since $(1, 1)$ is a pair in the symmetric square of $\{1, 2\}$, we have $s(1, 1) \in \{1, 2\}.sym2$.
  simp [Sym2.mk]

/-
Corrected version of M_edge_in_exactly_one: If e is an edge of G, it appears in at most one triangle of the packing.
-/
lemma M_edge_in_exactly_one_corrected (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he_edge : e ∈ G.edgeFinset)
    (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
      intro m' hm' hne hmem
      have h_inter : (m ∩ m').card < 2 := by
        exact lt_of_le_of_lt ( hM.2 hm hm' ( by aesop ) ) ( by decide );
      rcases e with ⟨ u, v ⟩ ; simp_all +decide [ Sym2.eq_iff ] ;
      exact h_inter.not_le ( Finset.one_lt_card.2 ⟨ u, by aesop, v, by aesop ⟩ )

example : s(1, 1) ∈ ({1, 2} : Finset ℕ).sym2 := by simp
example : s(1, 2) ∈ ({1, 2} : Finset ℕ).sym2 := by simp

/-
If an element of Sym2 V is in two distinct triangles of a packing, it must be a diagonal element (loop).
-/
lemma shared_element_implies_diag (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m m' : Finset V) (hm : m ∈ M) (hm' : m' ∈ M) (hne : m ≠ m')
    (he_m : e ∈ m.sym2) (he_m' : e ∈ m'.sym2) :
    e.IsDiag := by
      -- Since m and m' are distinct triangles in the packing, their intersection can have at most one element.
      have h_inter : (m ∩ m').card ≤ 1 := by
        exact hM.2 hm hm' hne;
      rcases e with ⟨ u, v ⟩;
      exact Classical.not_not.1 fun h => h_inter.not_lt <| Finset.one_lt_card.2 ⟨ u, by aesop, v, by aesop ⟩

def counterexampleGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {s(0, 1), s(1, 2), s(2, 0), s(0, 3), s(3, 4), s(4, 0)}

def counterexamplePacking : Finset (Finset (Fin 5)) :=
  { {0, 1, 2}, {0, 3, 4} }

/-
Proof that the counterexample construction is indeed a valid triangle packing.
-/
lemma counterexample_is_packing : isTrianglePacking counterexampleGraph counterexamplePacking := by
  constructor <;> simp +decide [ *, Finset.subset_iff ];
  simp +decide [ counterexamplePacking, counterexampleGraph, SimpleGraph.IsNClique ]

/-
Proof that the original lemma is false by exhibiting a counterexample where the shared element is a diagonal (loop) corresponding to a shared vertex.
-/
lemma counterexample_fails_lemma :
  ∃ (e : Sym2 (Fin 5)) (m : Finset (Fin 5)),
    m ∈ counterexamplePacking ∧
    e ∈ m.sym2 ∧
    ∃ m' ∈ counterexamplePacking, m' ≠ m ∧ e ∈ m'.sym2 := by
      simp +decide [ counterexamplePacking ]

/-
Proof that the statement of M_edge_in_exactly_one is false by exhibiting a counterexample (Fin 5, specific graph and packing).
-/
lemma M_edge_in_exactly_one_false :
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (_ : DecidableRel G.Adj)
    (M : Finset (Finset V)) (_ : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (_ : e ∈ m.sym2),
    ∃ m' ∈ M, m' ≠ m ∧ e ∈ m'.sym2 := by
      -- Let's choose the vertices, graph, and packing from the provided counterexample.
      use Fin 5, inferInstance, inferInstance, counterexampleGraph, inferInstance, counterexamplePacking, counterexample_is_packing;
      native_decide

/-
Existence of a counterexample to the subgoal `(m ∩ m').card ≥ 2` under the hypotheses of the failed lemma.
-/
lemma subgoal_counterexample_fixed :
  ∃ (G : SimpleGraph (Fin 5)) (_ : DecidableRel G.Adj) (M : Finset (Finset (Fin 5)))
    (m : Finset (Fin 5)) (m' : Finset (Fin 5)) (e : Sym2 (Fin 5)),
    isTrianglePacking G M ∧ m ∈ M ∧ m' ∈ M ∧ m ≠ m' ∧ e ∈ m.sym2 ∧ e ∈ m'.sym2 ∧
    ¬ ((m ∩ m').card ≥ 2) := by
      use counterexampleGraph, by infer_instance, counterexamplePacking, {0, 1, 2}, {0, 3, 4}, s(0, 0), by
        exact?, by decide, by decide, by decide, by decide, by decide, by decide;

end AristotleLemmas

/-
SCAFFOLDING (from slot64c - PROVEN)

Each edge in a triangle packing appears in exactly one triangle.
-/
lemma M_edge_in_exactly_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
  -- If two packing elements share an edge, they share 2 vertices
  -- This contradicts the pairwise intersection <= 1 property
  intro m' hm' hne he'
  have h_card : (m ∩ m').card ≥ 2 := by
    -- Wait, there's a mistake. We can actually prove the opposite.
    negate_state;
    -- Proof starts here:
    -- Let's choose the counterexample graph and packing.
    use ULift (Fin 5), inferInstance, inferInstance, (counterexampleGraph.comap (fun x => x.down)), inferInstance, (counterexamplePacking.image (fun s => s.image (fun x => ULift.up x)));
    constructor;
    · constructor <;> simp +decide [ *, Finset.subset_iff ];
      unfold counterexamplePacking; simp +decide [ SimpleGraph.IsNClique ] ;
      simp +decide [ SimpleGraph.isNClique_iff ];
      simp +decide [ counterexampleGraph ];
    · simp +decide [ counterexamplePacking ] -- Aristotle: extract vertices from e in m and m', show intersection >= 2
  have := hM.2 hm hm' hne.symm
  omega

-/
-- SCAFFOLDING (from slot64c - PROVEN)

/-- Each edge in a triangle packing appears in exactly one triangle. -/
lemma M_edge_in_exactly_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
  -- If two packing elements share an edge, they share 2 vertices
  -- This contradicts the pairwise intersection <= 1 property
  intro m' hm' hne he'
  have h_card : (m ∩ m').card ≥ 2 := by
    sorry -- Aristotle: extract vertices from e in m and m', show intersection >= 2
  have := hM.2 hm hm' hne.symm
  omega

-- M_CHAR: CHARACTERISTIC FUNCTION OF PACKING

/-- Characteristic function: 1 on M-elements, 0 elsewhere -/
def M_char (M : Finset (Finset V)) (t : Finset V) : ℝ :=
  if t ∈ M then 1 else 0

/-- M_char is nonnegative -/
lemma M_char_nonneg (M : Finset (Finset V)) (t : Finset V) :
    0 ≤ M_char M t := by
  unfold M_char
  split_ifs <;> linarith

/-- M_char is zero outside triangles (if M is subset of cliqueFinset 3) -/
lemma M_char_zero_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (t : Finset V) (ht : t ∉ G.cliqueFinset 3) :
    M_char M t = 0 := by
  unfold M_char
  split_ifs with h
  · exfalso; exact ht (hM.1 h)
  · rfl

/-- For M-edge e in M-element m, the sum over triangles containing e is exactly 1 -/
lemma M_char_edge_sum_M_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ G.edgeFinset)
    (m : Finset V) (hm : m ∈ M) (he_m : e ∈ m.sym2) :
    ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum (M_char M) = 1 := by
  -- The sum is over all triangles containing e
  -- By M_edge_in_exactly_one, only m among M-elements contains e
  -- So the sum counts only m with weight 1, plus externals with weight 0
  rw [ Finset.sum_eq_single m ] <;> simp_all +decide [ M_char ];
  · intro b hb hb' hne hbM;
    have := hM.2 hbM hm hne; simp_all +decide [ Finset.card_le_one ] ;
    rcases e with ⟨ u, v ⟩ ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    exact absurd ( this u hb'.1 he_m.1 v hb'.2 he_m.2 ) ( by aesop );
  · have := hM.1 hm; aesop;

-- Aristotle: use add_sum_erase and M_edge_in_exactly_one

/-- For non-M-edge e, the sum over triangles containing e is 0 (no M-element contains e) -/
lemma M_char_edge_sum_non_M_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ G.edgeFinset)
    (h_not_M : ∀ m ∈ M, e ∉ m.sym2) :
    ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum (M_char M) = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  simp only [Finset.mem_filter] at ht
  unfold M_char
  split_ifs with ht_M
  · exfalso; exact h_not_M t ht_M ht.2
  · rfl

/-- Edge constraint: sum over triangles containing e is at most 1 -/
lemma M_char_edge_sum_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum (M_char M) ≤ 1 := by
  by_cases h : ∃ m ∈ M, e ∈ m.sym2
  · obtain ⟨m, hm, he_m⟩ := h
    rw [M_char_edge_sum_M_edge G M hM e he m hm he_m]
  · push_neg at h
    rw [M_char_edge_sum_non_M_edge G M hM e he h]
    linarith

/-- M_char is a valid fractional packing -/
theorem M_char_is_fractional_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    IsFractionalPacking G (M_char M) := by
  refine ⟨M_char_nonneg M, M_char_zero_outside G M hM, ?_⟩
  intro e he
  exact M_char_edge_sum_le_1 G M hM e he

-- WEIGHT CALCULATION

/-- The weight of M_char equals |M| -/
lemma M_char_weight_eq_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    packingWeight G (M_char M) = M.card := by
  -- Split sum: M-elements contribute 1 each, non-M-elements contribute 0
  -- Sum over cliqueFinset = sum over M + sum over complement
  simp +decide [ packingWeight, M_char ];
  rw [ Finset.inter_eq_right.mpr hM.1 ]

-- Aristotle: use sum_union and M_char definition

-- MAIN THEOREM: nu* >= 4 for nu = 4

/-- For a packing of size 4, there exists a fractional packing of weight 4 -/
theorem nu_star_ge_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM4 : M.card = 4) :
    ∃ w : Finset V → ℝ, IsFractionalPacking G w ∧ packingWeight G w = 4 := by
  use M_char M
  constructor
  · exact M_char_is_fractional_packing G M hM
  · rw [M_char_weight_eq_card G M hM]
    norm_cast

end