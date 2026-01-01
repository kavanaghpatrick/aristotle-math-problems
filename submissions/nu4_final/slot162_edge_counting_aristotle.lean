/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 25d4fddf-3c95-424c-9556-b1c5b06725aa

The following was proved by Aristotle:

- lemma M_element_has_3_M_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (m : Finset V) (hm : m ∈ M) :
    (m.sym2.filter (fun e => e ∈ G.edgeFinset)).card = 3

- lemma M_edges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    (M_edges G M).card = 3 * M.card

The following was negated by Aristotle:

- lemma M_edge_in_exactly_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2

- theorem packingWeight_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    packingWeight G w ≤ M.card

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
Tuza nu=4 Cycle_4: Fractional Packing Upper Bound (nu* <= 4)

GOAL: Prove that ANY fractional packing has weight at most 4.
      This is the HARD direction - requires edge-counting argument.

APPROACH (from AI Debate - Grok's Edge-Counting):
1. Sum edge constraints over all 12 M-edges
2. Each M-element contributes 3x its weight (3 edges each)
3. Therefore: 3(w(A)+w(B)+w(C)+w(D)) <= 12
4. So: w(A)+w(B)+w(C)+w(D) <= 4

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

def IsFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
  (∀ t, t ∉ G.cliqueFinset 3 → w t = 0) ∧
  (∀ e ∈ G.edgeFinset,
    ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w ≤ 1)

def packingWeight (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : ℝ :=
  (G.cliqueFinset 3).sum w

/-- M-edges: edges appearing in some M-element -/
def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
If two distinct vertices are in both t1 and t2, then the intersection of t1 and t2 has size at least 2.
-/
lemma shared_edge_card_inter {V : Type*} [DecidableEq V] (t1 t2 : Finset V) (u v : V) (huv : u ≠ v)
    (hu1 : u ∈ t1) (hv1 : v ∈ t1) (hu2 : u ∈ t2) (hv2 : v ∈ t2) :
    2 ≤ (t1 ∩ t2).card := by
      exact Finset.one_lt_card.2 ⟨ u, by aesop, v, by aesop ⟩

/-
If e is an edge of G and appears in m, it cannot appear in any other m' in the packing.
-/
lemma M_edge_in_exactly_one_of_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) (he_edge : e ∈ G.edgeFinset) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
      intro m' hm' hne hm''; have := hM.2; simp_all +decide [ isTrianglePacking ] ;
      specialize this hm' hm ; simp_all +decide [ Set.Pairwise ];
      rcases e with ⟨ u, v ⟩ ; simp_all +decide [ Sym2.eq ] ;
      exact this.not_lt ( Finset.one_lt_card.2 ⟨ u, by aesop, v, by aesop ⟩ )

/-
Construction of a counterexample where a diagonal Sym2 element is shared between two triangles in a packing.
-/
abbrev V_ex := Fin 5
def t1 : Finset V_ex := {0, 1, 2}
def t2 : Finset V_ex := {0, 3, 4}
def M_ex : Finset (Finset V_ex) := {t1, t2}
def edges_ex : Set (Sym2 V_ex) := ↑t1.sym2 ∪ ↑t2.sym2
def G_ex : SimpleGraph V_ex := SimpleGraph.fromEdgeSet edges_ex

lemma t1_clique : G_ex.IsClique t1 := by
  simp +decide [ G_ex, t1 ];
  simp +decide [ edges_ex ]

lemma t2_clique : G_ex.IsClique t2 := by
  intros v hv w hw hvw ; fin_cases v <;> fin_cases w <;> simp_all +decide only ;
  all_goals simp +decide [ G_ex ] ;
  all_goals simp +decide [ edges_ex ] ;

lemma M_ex_packing : isTrianglePacking G_ex M_ex := by
  constructor <;> simp +decide [ G_ex, M_ex ];
  simp +decide [ Finset.insert_subset_iff ];
  simp +decide [ SimpleGraph.isNClique_iff, edges_ex, t1, t2 ]

lemma counterexample_exists : ∃ (V : Type) (instF : Fintype V) (instD : DecidableEq V) (G : SimpleGraph V) (instR : DecidableRel G.Adj) (M : Finset (Finset V)),
    isTrianglePacking G M ∧
    ∃ e m, m ∈ M ∧ e ∈ m.sym2 ∧ ∃ m' ∈ M, m' ≠ m ∧ e ∈ m'.sym2 := by
      -- Let's choose a specific example. Consider $V = \{0, 1, 2, 3, 4\}$.
      use Fin 5;
      use inferInstance, inferInstance, ⊤, inferInstance;
      exists { { 0, 1, 2 }, { 0, 3, 4 } }

/-
The statement `M_edge_in_exactly_one` is false, as shown by the counterexample.
-/
lemma M_edge_in_exactly_one_FALSE : ¬ (∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2),
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2) := by
      push_neg;
      use ULift ( Fin 5 );
      -- Let's choose the vertices and edges as described.
      use inferInstance, inferInstance, SimpleGraph.fromEdgeSet {Sym2.mk (⟨0, by decide⟩, ⟨1, by decide⟩), Sym2.mk (⟨0, by decide⟩, ⟨2, by decide⟩), Sym2.mk (⟨1, by decide⟩, ⟨2, by decide⟩), Sym2.mk (⟨0, by decide⟩, ⟨3, by decide⟩), Sym2.mk (⟨0, by decide⟩, ⟨4, by decide⟩), Sym2.mk (⟨3, by decide⟩, ⟨4, by decide⟩)}, inferInstance, { {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩}, {⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩} };
      constructor;
      · constructor <;> simp +decide [ Finset.subset_iff ];
      · simp +decide

end AristotleLemmas

/-
SCAFFOLDING

Each edge in a triangle packing appears in exactly one packing element.
-/
lemma M_edge_in_exactly_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any $V$ with 5 elements.
  use ULift (Fin 5);
  -- Let's choose the graph $G$ to be the complete graph on 5 vertices.
  use inferInstance, inferInstance, ⊤, inferInstance, { {⟨0⟩, ⟨1⟩, ⟨2⟩}, {⟨0⟩, ⟨3⟩, ⟨4⟩} };
  simp +decide [ isTrianglePacking ]

-/
-- SCAFFOLDING

/-- Each edge in a triangle packing appears in exactly one packing element. -/
lemma M_edge_in_exactly_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
  sorry

-- Aristotle: If two M-elements share an edge, they share 2 vertices, contradiction

/-- M-edges in an M-element are exactly 3 (edges of a triangle) -/
lemma M_element_has_3_M_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (m : Finset V) (hm : m ∈ M) :
    (m.sym2.filter (fun e => e ∈ G.edgeFinset)).card = 3 := by
  -- Since m is a triangle in G, it must have exactly 3 edges.
  have h_triangle_edges : ∀ t ∈ G.cliqueFinset 3, Finset.card (t.sym2.filter (fun e => e ∈ G.edgeFinset)) = 3 := by
    simp +decide [ SimpleGraph.cliqueFinset ];
    intro t ht
    have h_triangle_edges : Finset.card (t.sym2.filter (fun e => e ∈ G.edgeSet)) = Finset.card (Finset.powersetCard 2 t) := by
      refine' Finset.card_bij _ _ _ _;
      use fun e he => e.toFinset;
      · simp +decide [ Finset.mem_powersetCard, Finset.subset_iff ];
        rintro ⟨ a, b ⟩ hab h; cases eq_or_ne a b <;> simp_all +decide [ SimpleGraph.adj_comm ] ;
        simp +decide [ *, Sym2.toFinset ];
        simp +decide [ *, Sym2.toMultiset ];
      · simp +contextual [ Finset.ext_iff, Sym2.ext_iff ];
      · simp +decide [ Finset.mem_powersetCard, SimpleGraph.isNClique_iff ] at ht ⊢;
        intro b hb hb'; obtain ⟨ x, y, hxy ⟩ := Finset.card_eq_two.mp hb'; use Sym2.mk ( x, y ) ; aesop;
    simp_all +decide [ SimpleGraph.isNClique_iff ];
  exact h_triangle_edges m ( hM.1 hm )

-- Aristotle: A 3-clique has exactly 3 edges

/-- Total M-edges = 3 x |M| -/
lemma M_edges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    (M_edges G M).card = 3 * M.card := by
  -- Since these edges are disjoint for different $m \in M$, we can apply the cardinality addition formula.
  have h_card_add : ∀ m1 m2 : Finset V, m1 ∈ M → m2 ∈ M → m1 ≠ m2 → Disjoint (m1.sym2.filter (fun e => e ∈ G.edgeFinset)) (m2.sym2.filter (fun e => e ∈ G.edgeFinset)) := by
    have := hM.2;
    intro m1 m2 hm1 hm2 hne; specialize this hm1 hm2 hne; rw [ Finset.disjoint_left ] ; simp_all +decide [ Finset.ext_iff ] ;
    contrapose! this;
    obtain ⟨ a, ha1, ha2, ha3 ⟩ := this; rcases a with ⟨ x, y ⟩ ; simp_all +decide [ Finset.ext_iff ] ;
    exact Finset.one_lt_card.2 ⟨ x, by aesop, y, by aesop ⟩;
  rw [ M_edges, Finset.card_biUnion ];
  · rw [ Finset.sum_congr rfl fun x hx => M_element_has_3_M_edges G M hM x hx ] ; simp +decide [ mul_comm ];
  · exact fun x hx y hy hxy => h_card_add x y hx hy hxy

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Aristotle: biUnion of disjoint 3-element sets

KEY THEOREM: Any fractional packing has total weight <= |M|
-/
theorem packingWeight_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    packingWeight G w ≤ M.card := by
  -- Strategy: Edge-counting over M-edges
  -- Each M-edge e has constraint: sum over triangles containing e <= 1
  -- Sum over all 3|M| M-edges: each M-element appears 3 times
  -- So: 3 * (sum of M-element weights) <= 3|M|
  -- Therefore: sum of M-element weights <= |M|
  -- External triangles contribute >= 0 but are bounded by residual capacity
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  use ULift ( Fin 4 );
  refine' ⟨ inferInstance, inferInstance, ⊤, _, _ ⟩ <;> norm_num [ isTrianglePacking ];
  infer_instance;
  refine' ⟨ ∅, _, _ ⟩ <;> norm_num [ IsFractionalPacking ];
  refine' ⟨ fun t => if t.card = 3 then 1 / 3 else 0, _, _ ⟩ <;> norm_num [ packingWeight ];
  · refine' ⟨ _, _, _ ⟩ <;> norm_num [ SimpleGraph.isNClique_iff ];
    · exact fun t => by split_ifs <;> norm_num;
    · native_decide +revert;
    · intro e he; rw [ Finset.sum_ite ] ; norm_num;
      rw [ mul_one_div, div_le_iff₀ ] <;> norm_cast ; fin_cases e <;> simp +decide at he ⊢;
  · rw [ Finset.sum_ite ] ; norm_num [ SimpleGraph.cliqueFinset ];
    simp +decide [ SimpleGraph.isNClique_iff ]

-/
-- Aristotle: biUnion of disjoint 3-element sets

/-- KEY THEOREM: Any fractional packing has total weight <= |M| -/
theorem packingWeight_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    packingWeight G w ≤ M.card := by
  -- Strategy: Edge-counting over M-edges
  -- Each M-edge e has constraint: sum over triangles containing e <= 1
  -- Sum over all 3|M| M-edges: each M-element appears 3 times
  -- So: 3 * (sum of M-element weights) <= 3|M|
  -- Therefore: sum of M-element weights <= |M|
  -- External triangles contribute >= 0 but are bounded by residual capacity
  sorry

-- Aristotle: Complete edge-counting argument

-- MAIN THEOREM: nu* <= 4 for nu = 4

/-- Any fractional packing has weight at most 4 when |M| = 4 -/
theorem nu_star_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    packingWeight G w ≤ 4 := by
  calc packingWeight G w ≤ M.card := packingWeight_le_card G M hM.1 w hw
    _ = 4 := by rw [hM4]; norm_num

end