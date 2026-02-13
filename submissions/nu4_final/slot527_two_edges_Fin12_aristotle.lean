/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f104f919-7e50-4977-b081-42085806befc

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- lemma not_all_three_types12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (hNu4 : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M) (he3 : e.card = 3)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬((S_e_type12 G M e a b c).Nonempty ∧
      (S_e_type12 G M e b c a).Nonempty ∧
      (S_e_type12 G M e a c b).Nonempty)

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
  slot527_two_edges_Fin12.lean

  SIMPLIFIED VERSION: Concrete Fin 12 instead of generic V

  KEY FIX: Aristotle does better with decidable Fin n types
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS on Fin 12
-- ══════════════════════════════════════════════════════════════════════════════

abbrev V12 := Fin 12

def isTrianglePacking12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V12)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def S_e12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12) : Finset (Finset V12) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧ ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

/-- Externals using specific edges of e = {a,b,c} -/
def S_e_type12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12) (x y z : V12) : Finset (Finset V12) :=
  (S_e12 G M e).filter (fun T => x ∈ T ∧ y ∈ T ∧ z ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Clique edges are graph edges
-- ══════════════════════════════════════════════════════════════════════════════

lemma clique_adj12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (e : Finset V12) (he : e ∈ G.cliqueFinset 3)
    (a b : V12) (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) :
    G.Adj a b := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at he
  exact he.2 ha hb hab

lemma clique_edge_mem12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (e : Finset V12) (he : e ∈ G.cliqueFinset 3)
    (a b : V12) (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) :
    s(a, b) ∈ G.edgeFinset :=
  SimpleGraph.mem_edgeFinset.mpr (clique_adj12 G e he a b ha hb hab)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Edge covers triangle
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_sym2_12 (T : Finset V12) (a b : V12) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 :=
  Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: S_e external shares exactly 2 vertices
-- ══════════════════════════════════════════════════════════════════════════════

lemma Se_inter_eq_2_12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12) (he3 : e.card = 3)
    (T : Finset V12) (hT : T ∈ S_e12 G M e) :
    (T ∩ e).card = 2 := by
  simp only [S_e12, mem_filter] at hT
  obtain ⟨hT_tri, hT_ne, hT_inter, _⟩ := hT
  have hT3 : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT_tri
    exact hT_tri.1.card_eq
  have hle3 : (T ∩ e).card ≤ 3 := (card_le_card inter_subset_right).trans he3.le
  interval_cases (T ∩ e).card <;> [omega; omega; rfl; skip]
  have heq : T ∩ e = e := eq_of_subset_of_card_le inter_subset_right (by omega)
  have he_sub_T : e ⊆ T := fun x hx => mem_of_mem_inter_left (heq ▸ mem_inter.mpr ⟨?_, hx⟩)
  · have hTeq : T = e := eq_of_subset_of_card_le he_sub_T (by omega)
    exact absurd hTeq hT_ne
  · rw [heq]; exact mem_inter.mpr ⟨mem_of_mem_inter_left (heq.symm ▸ mem_inter_self hx), hx⟩

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Characterization of S_e_type elements as triangles {a,b,x} with x outside e.
-/
lemma S_e_type_mem_iff12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12) (he3 : e.card = 3)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (T : Finset V12) :
    T ∈ S_e_type12 G M e a b c ↔
    ∃ x, x ∉ e ∧ T = {a, b, x} ∧ T ∈ S_e12 G M e := by
      constructor <;> intro hT;
      · -- By definition of $S_e_type12$, if $T \in S_e_type12 G M e a b c$, then $T$ is a triangle in $S_e12 G M e$ with $a, b \in T$ and $c \notin T$.
        obtain ⟨hx_not_in_e, hT_triangle⟩ : ∃ x, x ∉ e ∧ T = {a, b, x} ∧ T ∈ S_e12 G M e := by
          have h_triangle : T ∈ S_e12 G M e := by
            exact Finset.mem_filter.mp hT |>.1
          -- By definition of $S_e_type12$, if $T \in S_e_type12 G M e a b c$, then $T$ is a triangle in $S_e12 G M e$ with $a, b \in T$ and $c \notin T$. Therefore, $T$ must be of the form $\{a, b, x\}$ for some $x \notin e$.
          obtain ⟨x, hx⟩ : ∃ x, x ∉ e ∧ T = {a, b, x} := by
            have h_card : T.card = 3 := by
              have h_card_T : T ∈ G.cliqueFinset 3 := by
                exact Finset.mem_filter.mp h_triangle |>.1;
              exact Finset.mem_filter.mp h_card_T |>.2.2
            have h_inter : (T ∩ e).card = 2 := by
              exact?
            -- Since $T$ is a triangle and $T \cap e$ has exactly two elements, the third element of $T$ must be outside $e$.
            obtain ⟨x, hx⟩ : ∃ x, x ∈ T ∧ x ∉ e := by
              contrapose! h_inter;
              rw [ Finset.inter_eq_left.mpr h_inter ] ; aesop;
            have h_third : T = {a, b, x} := by
              have h_subset : {a, b, x} ⊆ T := by
                simp_all +decide [ Finset.subset_iff ];
                unfold S_e_type12 at hT; aesop;
              have h_card_eq : ({a, b, x} : Finset V12).card = T.card := by
                rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> aesop
              rw [ Finset.eq_of_subset_of_card_le h_subset ( by linarith ) ];
            exact ⟨ x, hx.2, h_third ⟩;
          exact ⟨ x, hx.1, hx.2, h_triangle ⟩;
        use hx_not_in_e;
      · unfold S_e_type12; aesop;

/-
Definitions for the counterexample graph G_ex and packing M_ex.
G_ex has edges for K4 on {0,1,2,3}, and triangles {3,4,5}, {6,7,8}, {9,10,11}.
M_ex is the set of 4 disjoint triangles.
The graph is symmetric and loopless by construction (proofs omitted).
-/
def is_edge_ex (n m : Nat) : Bool :=
  let s := if n < m then (n, m) else (m, n)
  s == (0, 1) || s == (1, 2) || s == (0, 2) ||
  s == (0, 3) || s == (1, 3) || s == (2, 3) ||
  s == (3, 4) || s == (4, 5) || s == (3, 5) ||
  s == (6, 7) || s == (7, 8) || s == (6, 8) ||
  s == (9, 10) || s == (10, 11) || s == (9, 11)

def Adj_ex (x y : V12) : Prop := x ≠ y ∧ is_edge_ex x.val y.val

instance : DecidableRel Adj_ex := fun x y =>
  if h : x ≠ y ∧ is_edge_ex x.val y.val then isTrue h else isFalse h

def G_ex : SimpleGraph V12 := {
  Adj := Adj_ex
  symm := by
    -- By definition of `is_edge_ex`, we know that it is symmetric.
    simp [Symmetric];
    native_decide +revert
  loopless := by
    -- By definition of $adj_ex$, we know that $adj_ex u u$ is false for all $u$.
    intro u
    simp [Adj_ex]
}

def M_ex : Finset (Finset V12) :=
  { {0, 1, 2}, {3, 4, 5}, {6, 7, 8}, {9, 10, 11} }

/-
Instance for DecidableRel G_ex.Adj and proof that M_ex is a packing.
-/
instance : DecidableRel G_ex.Adj := by
  dsimp [G_ex]
  infer_instance

lemma M_ex_is_packing : isTrianglePacking12 G_ex M_ex := by
  constructor;
  · native_decide +revert;
  · decide +kernel

/-
Proof that G_ex has max packing size 4.
First, we list all cliques (triangles) in G_ex.
Then we check all subsets of these cliques to see if they form a packing, and verify their size is <= 4.
Finally, we lift this to the general statement.
-/
lemma G_ex_cliques_eq : G_ex.cliqueFinset 3 =
    { {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {3, 4, 5}, {6, 7, 8}, {9, 10, 11} } := by
      native_decide +revert

lemma G_ex_max_packing_aux :
    ∀ S ∈ (G_ex.cliqueFinset 3).powerset,
    (Set.Pairwise (S : Set (Finset V12)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)) →
    S.card ≤ 4 := by
      simp +contextual [ Set.Pairwise ];
      native_decide +revert

lemma G_ex_max_packing : ∀ S, isTrianglePacking12 G_ex S → S.card ≤ 4 := by
  intro S hS;
  -- By definition of $G_ex$, we know that any triangle packing in $G_ex$ can have at most 4 triangles.
  have h_max_packing : ∀ M : Finset (Finset V12), M ⊆ (G_ex.cliqueFinset 3) → Set.Pairwise (M : Set (Finset V12)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) → M.card ≤ 4 := by
    native_decide +revert;
  exact h_max_packing S hS.1 hS.2

/-
Proof that for e={0,1,2} in G_ex, all three external types are nonempty.
We witness {0,1,3}, {1,2,3}, {0,2,3} respectively.
We use native_decide to verify the conditions.
-/
lemma G_ex_externals_nonempty :
    let e := ({0, 1, 2} : Finset V12)
    (S_e_type12 G_ex M_ex e 0 1 2).Nonempty ∧
    (S_e_type12 G_ex M_ex e 1 2 0).Nonempty ∧
    (S_e_type12 G_ex M_ex e 0 2 1).Nonempty := by
      decide +kernel

end AristotleLemmas

/-
══════════════════════════════════════════════════════════════════════════════
6-PACKING: At most 2 edge-types have externals
══════════════════════════════════════════════════════════════════════════════

PROOF SKETCH (6-packing argument):
If all 3 edge-types {ab}, {bc}, {ac} have externals T_ab, T_bc, T_ac:
1. T_ab, T_bc, T_ac are pairwise edge-disjoint (they share different pairs of {a,b,c})
2. With B, C, D ∈ M (other 3 elements of M), we get 6 edge-disjoint triangles:
   {A, T_ab, T_bc, T_ac, B, C, D} minus A gives 6 triangles
3. But M.card = 4, so M = {A, B, C, D}
4. The 3 externals T_ab, T_bc, T_ac plus B, C, D gives 6 edge-disjoint triangles
5. This contradicts ν = 4
-/
lemma not_all_three_types12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (hNu4 : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M) (he3 : e.card = 3)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬((S_e_type12 G M e a b c).Nonempty ∧
      (S_e_type12 G M e b c a).Nonempty ∧
      (S_e_type12 G M e a c b).Nonempty) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose the graph G_ex and the packing M_ex.
  use G_ex, inferInstance, M_ex;
  -- Let's choose the edge e = {0, 1, 2} from M_ex.
  use M_ex_is_packing, G_ex_max_packing, {0, 1, 2};
  -- Let's choose the vertices a = 0, b = 1, and c = 2.
  simp [G_ex_externals_nonempty];
  -- Let's choose the edge $e = \{0, 1, 2\}$ and show that it satisfies the conditions.
  simp [M_ex]

-/
-- ══════════════════════════════════════════════════════════════════════════════
-- 6-PACKING: At most 2 edge-types have externals
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH (6-packing argument):
If all 3 edge-types {ab}, {bc}, {ac} have externals T_ab, T_bc, T_ac:
1. T_ab, T_bc, T_ac are pairwise edge-disjoint (they share different pairs of {a,b,c})
2. With B, C, D ∈ M (other 3 elements of M), we get 6 edge-disjoint triangles:
   {A, T_ab, T_bc, T_ac, B, C, D} minus A gives 6 triangles
3. But M.card = 4, so M = {A, B, C, D}
4. The 3 externals T_ab, T_bc, T_ac plus B, C, D gives 6 edge-disjoint triangles
5. This contradicts ν = 4
-/

lemma not_all_three_types12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (hNu4 : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M) (he3 : e.card = 3)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬((S_e_type12 G M e a b c).Nonempty ∧
      (S_e_type12 G M e b c a).Nonempty ∧
      (S_e_type12 G M e a c b).Nonempty) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

`simp` made no progress-/
-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: External uses one edge-type
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_uses_one_type12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (he3 : e.card = 3)
    (T : Finset V12) (hT : T ∈ S_e12 G M e) :
    T ∈ S_e_type12 G M e a b c ∨ T ∈ S_e_type12 G M e b c a ∨ T ∈ S_e_type12 G M e a c b := by
  have hinter := Se_inter_eq_2_12 G M e he3 T hT
  simp only [S_e_type12, mem_filter]
  -- T ∩ e has exactly 2 elements, so exactly one of {a,b,c} is not in T
  by_cases haT : a ∈ T <;> by_cases hbT : b ∈ T <;> by_cases hcT : c ∈ T
  · -- all 3 in T: impossible since |T ∩ e| = 2
    have h3 : ({a, b, c} : Finset V12) ⊆ T ∩ e := by
      intro x hx; simp at hx
      rcases hx with rfl | rfl | rfl
      · exact mem_inter.mpr ⟨haT, ha⟩
      · exact mem_inter.mpr ⟨hbT, hb⟩
      · exact mem_inter.mpr ⟨hcT, hc⟩
    have hcard : 3 ≤ (T ∩ e).card := by
      calc 3 = ({a, b, c} : Finset V12).card := by
              simp only [card_insert_of_not_mem, card_singleton, not_mem_singleton]
              simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
           _ ≤ (T ∩ e).card := card_le_card h3
    omega
  · -- a, b in T, c not in T: type ab
    left; exact ⟨hT, haT, hbT, hcT⟩
  · -- a, c in T, b not in T: type ac
    right; right; exact ⟨hT, haT, hcT, hbT⟩
  · -- a in T, b, c not: impossible since |T ∩ e| = 2
    have h1 : (T ∩ e).card ≤ 1 := by
      have hsub : T ∩ e ⊆ {a} := by
        intro x hx
        simp at hx ⊢
        have hxe := hx.2
        -- x ∈ e means x is a, b, or c
        -- x ∈ T and x ∈ e
        -- But b ∉ T and c ∉ T
        -- So x must be a
        -- Need to show e = {a,b,c} first
        sorry
      calc (T ∩ e).card ≤ ({a} : Finset V12).card := card_le_card hsub
           _ = 1 := card_singleton a
    omega
  · -- b, c in T, a not in T: type bc
    right; left; exact ⟨hT, hbT, hcT, haT⟩
  · -- b in T, a, c not: impossible since |T ∩ e| = 2
    sorry
  · -- c in T, a, b not: impossible since |T ∩ e| = 2
    sorry
  · -- none in T: impossible since |T ∩ e| = 2
    have h0 : (T ∩ e).card = 0 := by
      rw [card_eq_zero]
      ext x
      simp only [mem_inter, not_mem_empty, iff_false, not_and]
      intro hxT hxe
      sorry
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 2 edges cover S_e (with valid edges)
-- ══════════════════════════════════════════════════════════════════════════════

theorem two_edges_cover_Se12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (hNu4 : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M) (he3 : e.card = 3)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ E : Finset (Sym2 V12),
      E ⊆ G.edgeFinset ∧
      E.card ≤ 2 ∧
      ∀ T ∈ S_e12 G M e, ∃ edge ∈ E, edge ∈ T.sym2 := by
  -- Get that e is a clique, so its edges are in G.edgeFinset
  have he_clq : e ∈ G.cliqueFinset 3 := hM.1 he
  have hab_edge := clique_edge_mem12 G e he_clq a b ha hb hab
  have hbc_edge := clique_edge_mem12 G e he_clq b c hb hc hbc
  have hac_edge := clique_edge_mem12 G e he_clq a c ha hc hac
  -- At most 2 of {ab, bc, ac} have externals
  have h_not_all := not_all_three_types12 G M hM hNu4 e he he3 a b c ha hb hc hab hbc hac
  push_neg at h_not_all
  -- Case split on which types are empty
  by_cases h_ab : (S_e_type12 G M e a b c).Nonempty
  · by_cases h_bc : (S_e_type12 G M e b c a).Nonempty
    · -- ab, bc nonempty → ac empty. Use {ab, bc}
      have h_ac : ¬(S_e_type12 G M e a c b).Nonempty := h_not_all h_ab h_bc
      use {s(a, b), s(b, c)}
      refine ⟨?_, ?_, ?_⟩
      · intro e' he'; simp at he'; rcases he' with rfl | rfl <;> assumption
      · simp only [card_insert_of_not_mem, card_singleton, Nat.reduceAdd]
        intro h
        have := Sym2.eq_iff.mp h
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hbc rfl; exact hab rfl]
      · intro T hT
        rcases external_uses_one_type12 G M e a b c ha hb hc hab hbc hac he3 T hT with h | h | h
        · simp only [S_e_type12, mem_filter] at h
          exact ⟨s(a, b), by simp, edge_in_sym2_12 T a b h.2.1 h.2.2.1⟩
        · simp only [S_e_type12, mem_filter] at h
          exact ⟨s(b, c), by simp, edge_in_sym2_12 T b c h.2.1 h.2.2.1⟩
        · exfalso; exact h_ac ⟨T, h⟩
    · -- ab nonempty, bc empty. Use {ab, ac}
      use {s(a, b), s(a, c)}
      refine ⟨?_, ?_, ?_⟩
      · intro e' he'; simp at he'; rcases he' with rfl | rfl <;> assumption
      · simp only [card_insert_of_not_mem, card_singleton, Nat.reduceAdd]
        intro h
        have := Sym2.eq_iff.mp h
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hac rfl; exact hac rfl]
      · intro T hT
        rcases external_uses_one_type12 G M e a b c ha hb hc hab hbc hac he3 T hT with h | h | h
        · simp only [S_e_type12, mem_filter] at h
          exact ⟨s(a, b), by simp, edge_in_sym2_12 T a b h.2.1 h.2.2.1⟩
        · exfalso; exact h_bc ⟨T, h⟩
        · simp only [S_e_type12, mem_filter] at h
          exact ⟨s(a, c), by simp, edge_in_sym2_12 T a c h.2.1 h.2.2.1⟩
  · -- ab empty
    by_cases h_bc : (S_e_type12 G M e b c a).Nonempty
    · -- bc nonempty, ab empty. Use {bc, ac}
      use {s(b, c), s(a, c)}
      refine ⟨?_, ?_, ?_⟩
      · intro e' he'; simp at he'; rcases he' with rfl | rfl <;> assumption
      · simp only [card_insert_of_not_mem, card_singleton, Nat.reduceAdd]
        intro h
        have := Sym2.eq_iff.mp h
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hab rfl; exact (hbc rfl).elim]
      · intro T hT
        rcases external_uses_one_type12 G M e a b c ha hb hc hab hbc hac he3 T hT with h | h | h
        · exfalso; exact h_ab ⟨T, h⟩
        · simp only [S_e_type12, mem_filter] at h
          exact ⟨s(b, c), by simp, edge_in_sym2_12 T b c h.2.1 h.2.2.1⟩
        · simp only [S_e_type12, mem_filter] at h
          exact ⟨s(a, c), by simp, edge_in_sym2_12 T a c h.2.1 h.2.2.1⟩
    · -- ab empty, bc empty. Use {ac, ab} (covers only ac type if any)
      use {s(a, c), s(a, b)}
      refine ⟨?_, ?_, ?_⟩
      · intro e' he'; simp at he'; rcases he' with rfl | rfl <;> assumption
      · simp only [card_insert_of_not_mem, card_singleton, Nat.reduceAdd]
        intro h
        have := Sym2.eq_iff.mp h
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hac rfl; exact hac.symm rfl]
      · intro T hT
        rcases external_uses_one_type12 G M e a b c ha hb hc hab hbc hac he3 T hT with h | h | h
        · exfalso; exact h_ab ⟨T, h⟩
        · exfalso; exact h_bc ⟨T, h⟩
        · simp only [S_e_type12, mem_filter] at h
          exact ⟨s(a, c), by simp, edge_in_sym2_12 T a c h.2.1 h.2.2.1⟩