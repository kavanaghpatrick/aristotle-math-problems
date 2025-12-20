/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4dc5bdd3-b001-4851-9237-ea4c5d954b58

The following was negated by Aristotle:

- theorem erdos_128 (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDenseInducedSubgraphs G → ∃ (a b c : V), G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

- theorem erdos_128' (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDenseInducedSubgraphs G → ¬ G.CliqueFree 3

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
Erdős Problem #128 - Triangle in Dense Induced Subgraph
$250 Prize

PROBLEM: Let G be a graph with n vertices such that every induced subgraph
on ≥ n/2 vertices has more than n²/50 edges. Must G contain a triangle?

BORIS PATTERN ANALYSIS:
- Pre-formalized in FC: ✅
- Concrete bounds: ✅ (n/2, n²/50)
- Graph theory: ✅
- No asymptotics: ✅
- Finite: ✅
-/

import Mathlib


set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Erdos128

open SimpleGraph Set

/-- Every induced subgraph on at least half the vertices has more than n²/50 edges -/
def HasDenseInducedSubgraphs (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, 2 * S.ncard ≥ Fintype.card V →
    50 * (G.induce S).edgeFinset.card > (Fintype.card V)^2

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
The 5-cycle graph on ZMod 5. Vertices are 0, 1, 2, 3, 4. Edges are (i, i+1).
-/
def C5 : SimpleGraph (ZMod 5) := SimpleGraph.fromRel (fun a b => b = a + 1)

/-
The graph C5 contains no triangles (cliques of size 3).
-/
lemma C5_triangle_free : ¬ ∃ (a b c : ZMod 5), C5.Adj a b ∧ C5.Adj b c ∧ C5.Adj a c := by
  simp +decide [ Erdos128.C5 ]

/-
The graph C5 satisfies the dense induced subgraphs condition: every induced subgraph on at least half the vertices (size >= 3) has > n^2/50 edges.
-/
lemma C5_dense : Erdos128.HasDenseInducedSubgraphs Erdos128.C5 := by
  -- We need to show that for any set S of vertices in C5 with 2 * |S| ≥ 5 (i.e., |S| ≥ 3), the induced subgraph has more than 25/50 = 0.5 edges.
  intros S hS
  by_cases hS_card : S.ncard ≥ 3;
  · simp +zetaDelta at *;
    -- Since S has at least 3 elements, the induced subgraph must contain at least one edge.
    have h_edge_exists : ∃ u v : ZMod 5, u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ (Erdos128.C5).Adj u v := by
      have h_edge_exists : ∀ (S : Finset (ZMod 5)), S.card ≥ 3 → ∃ u v : ZMod 5, u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ (Erdos128.C5).Adj u v := by
        simp +decide [ Erdos128.C5 ];
      contrapose! h_edge_exists;
      exact ⟨ S.toFinset, by simpa [ ← Set.ncard_coe_Finset ] using hS_card, by simpa [ Set.toFinset_card ] using h_edge_exists ⟩;
    aesop;
    exact lt_of_lt_of_le ( by decide ) ( Nat.mul_le_mul_left _ ( Finset.card_pos.mpr ⟨ Sym2.mk ( ⟨ w, left ⟩, ⟨ w_1, left_1 ⟩ ), by aesop ⟩ ) );
  · interval_cases _ : S.ncard <;> simp_all +decide

/-
The conjecture Erdos128 is false, as shown by the counterexample C5.
-/
lemma erdos_128_false : ¬ ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], Erdos128.HasDenseInducedSubgraphs G → ∃ (a b c : V), G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
  aesop;
  refine' ⟨ ULift ( Fin 5 ), inferInstance, _, _, _ ⟩;
  exact SimpleGraph.comap ( fun x => x.down ) ( SimpleGraph.fromRel fun a b : Fin 5 => b = a + 1 );
  · unfold Erdos128.HasDenseInducedSubgraphs;
    simp +decide [ Set.ncard_eq_toFinset_card' ];
    refine' fun S hS => lt_of_lt_of_le _ ( Nat.mul_le_mul_left _ <| Finset.card_pos.mpr _ );
    · norm_num;
    · simp +decide [ Finset.Nonempty ];
      by_contra! h;
      simp_all +decide [ SimpleGraph.fromRel, Sym2.forall ];
      have h_card : (Finset.filter (Membership.mem S) Finset.univ).card ≤ 2 := by
        have h_card : ∀ T : Finset (Fin 5), (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬(x = y + 1 ∨ y = x + 1)) → T.card ≤ 2 := by
          native_decide;
        convert h_card ( Finset.image ( fun x : ULift ( Fin 5 ) => x.down ) ( Finset.filter ( Membership.mem S ) Finset.univ ) ) _ using 1;
        · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
        · simp +zetaDelta at *;
          exact fun x hx y hy hxy => ⟨ by have := h x hx y hy hxy; tauto, by have := h x hx y hy hxy; tauto ⟩;
      linarith;
  · simp +decide [ SimpleGraph.comap ]

end AristotleLemmas

/-
Erdős Problem #128: If every large induced subgraph is dense (>n²/50 edges),
then G must contain a triangle.
-/
theorem erdos_128 (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDenseInducedSubgraphs G → ∃ (a b c : V), G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose the vertices of the C5 graph.
  use ULift (ZMod 5);
  simp +zetaDelta at *;
  refine' ⟨ inferInstance, _, _, _ ⟩;
  exact SimpleGraph.fromRel fun a b => b = a + 1;
  · intro S hS;
    simp_all +decide [ Set.ncard_eq_toFinset_card' ];
    -- Since $S$ has at least 3 elements, the induced subgraph on $S$ must have at least one edge.
    have h_edge : ∃ a b : ULift (ZMod 5), a ∈ S ∧ b ∈ S ∧ b = a + 1 := by
      have h_card : (Finset.filter (Membership.mem S) Finset.univ).card ≥ 3 := by
        linarith;
      have h_cases : ∀ (T : Finset (ZMod 5)), T.card ≥ 3 → ∃ x ∈ T, x + 1 ∈ T := by
        native_decide;
      specialize h_cases ( Finset.image ( fun x : ULift ( ZMod 5 ) => x.down ) ( Finset.filter ( Membership.mem S ) Finset.univ ) ) ; aesop;
      convert h_cases _;
      rwa [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
    obtain ⟨ a, b, ha, hb, rfl ⟩ := h_edge;
    refine' lt_of_lt_of_le _ ( Nat.mul_le_mul_left _ ( Finset.card_pos.mpr ⟨ Sym2.mk ( ⟨ a, ha ⟩, ⟨ a + 1, hb ⟩ ), _ ⟩ ) ) <;> simp +decide [ SimpleGraph.fromRel ];
  · simp +decide [ SimpleGraph.fromRel ]

-/
/--
Erdős Problem #128: If every large induced subgraph is dense (>n²/50 edges),
then G must contain a triangle.
-/
theorem erdos_128 (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDenseInducedSubgraphs G → ∃ (a b c : V), G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Define C5 as the cycle graph on 5 vertices.
-/
def C5 : SimpleGraph (Fin 5) := SimpleGraph.cycleGraph 5

lemma C5_dense : Erdos128.HasDenseInducedSubgraphs C5 := by
  -- Let's choose any subset $S$ of $C_5$ with $|S| ≥ 3$.
  intro S hS
  by_contra h_contra;
  -- Since $S$ has at least 3 elements, we can check all possible subsets of $\{0, 1, 2, 3, 4\}$ with at least 3 elements to see if any of them form an independent set in $C5$.
  have h_check : ∀ (S : Finset (Fin 5)), S.card ≥ 3 → ¬(∀ (i j : Fin 5), i ∈ S → j ∈ S → i ≠ j → ¬(Erdos128.C5.Adj i j)) := by
    simp +decide [ Erdos128.C5 ];
  norm_num +zetaDelta at *;
  obtain ⟨ x, hx, y, hy, hxy, h ⟩ := h_check ( Finset.filter ( fun v => v ∈ S ) Finset.univ ) ( by rw [ ← Set.ncard_coe_finset ] ; simpa [ Finset.filter_mem_eq_inter ] using by linarith ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;
  exact h_contra.not_lt ( by exact lt_of_lt_of_le ( by decide ) ( mul_le_mul_of_nonneg_left ( Finset.card_pos.mpr ⟨ Sym2.mk ( ⟨ x, hx ⟩, ⟨ y, hy ⟩ ), by aesop ⟩ ) ( by decide ) ) )

lemma C5_triangle_free : Erdos128.C5.CliqueFree 3 := by
  unfold Erdos128.C5;
  simp +decide [ SimpleGraph.CliqueFree ]

/-
There exists a graph (namely C5) that has dense induced subgraphs but is triangle-free, disproving the conjecture.
-/
theorem erdos_128_counterexample : ∃ (V : Type*) (hV : Fintype V) (hD : DecidableEq V) (G : SimpleGraph V) (hR : DecidableRel G.Adj), Erdos128.HasDenseInducedSubgraphs G ∧ G.CliqueFree 3 := by
  use ULift ( Fin 5 );
  refine' ⟨ inferInstance, inferInstance, _, _, _, _ ⟩;
  exact SimpleGraph.comap ULift.down ( SimpleGraph.cycleGraph 5 );
  · infer_instance;
  · intro S hS;
    rw [ Set.ncard_eq_toFinset_card' ] at hS ; aesop;
    refine' lt_of_lt_of_le _ ( Nat.mul_le_mul_left _ ( Finset.card_pos.mpr _ ) ) <;> norm_cast;
    simp +decide [ Finset.Nonempty ];
    -- Since $S$ has at least 3 elements, we can choose any two adjacent vertices in $S$.
    obtain ⟨a, b, hab⟩ : ∃ a b : ULift (Fin 5), a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ (SimpleGraph.cycleGraph 5).Adj a.down b.down := by
      have h_card : (Finset.filter (Membership.mem S) Finset.univ).card ≥ 3 := by
        linarith;
      have h_adj : ∀ (S : Finset (Fin 5)), S.card ≥ 3 → ∃ a b : Fin 5, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ (SimpleGraph.cycleGraph 5).Adj a b := by
        native_decide +revert;
      obtain ⟨ a, b, ha, hb, hab, h ⟩ := h_adj ( Finset.image ( fun x : ULift ( Fin 5 ) => x.down ) ( Finset.filter ( Membership.mem S ) Finset.univ ) ) ( by simpa [ Finset.card_image_of_injective, Function.Injective ] using h_card ) ; use ⟨ a ⟩, ⟨ b ⟩ ; aesop;
    exact ⟨ Sym2.mk ⟨ ⟨ a, hab.1 ⟩, ⟨ b, hab.2.1 ⟩ ⟩, by aesop ⟩;
  · intro s hs;
    fin_cases s <;> simp_all +decide

end AristotleLemmas

/-
Alternative formulation: dense induced subgraphs imply not triangle-free
-/
theorem erdos_128' (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDenseInducedSubgraphs G → ¬ G.CliqueFree 3 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Apply the theorem that states such a graph exists.
  apply erdos_128_counterexample

-/
/-- Alternative formulation: dense induced subgraphs imply not triangle-free -/
theorem erdos_128' (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDenseInducedSubgraphs G → ¬ G.CliqueFree 3 := by
  sorry

end Erdos128