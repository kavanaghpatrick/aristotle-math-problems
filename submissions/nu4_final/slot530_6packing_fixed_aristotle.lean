/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7fe32aae-c6a8-4f0d-8ebc-ea8de4e4def9

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem not_all_three_types12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (hM4 : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M)
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
  slot529_6packing_K4_case.lean

  FOCUSED: The 6-packing argument with K4 case analysis

  KEY INSIGHT: When all 3 edge-types have externals T_ab, T_bc, T_ac:
  Case 1: Third vertices are distinct → 6-packing with {T_ab, T_bc, T_ac, f, g, h}
  Case 2: Two share third vertex → 5-packing with {T_ab, T_ac, f, g, h} (if T_ab, T_bc share)
  Case 3: All share same vertex x (K4) → Still get 5-packing

  TIER: 2 (case analysis + construction)
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset

abbrev V12 := Fin 12

def isTrianglePacking12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V12)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def S_e12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12) : Finset (Finset V12) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧ ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

def S_e_type12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12) (x y z : V12) : Finset (Finset V12) :=
  (S_e12 G M e).filter (fun T => x ∈ T ∧ y ∈ T ∧ z ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: External not in M
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
If T ∈ S_e and T ∈ M, then since T ≠ e (from S_e definition), we have T ∈ M \ {e}.
But T shares edge with e (2 ≤ |T ∩ e|), which contradicts M being a packing
(packing elements share at most 1 vertex).
-/

lemma external_not_in_M (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (e : Finset V12) (he : e ∈ M)
    (T : Finset V12) (hT : T ∈ S_e12 G M e) :
    T ∉ M := by
  simp only [S_e12, mem_filter] at hT
  intro hTM
  -- T ∈ M and T ≠ e, so T is another packing element
  have hTe : T ≠ e := hT.2.1
  -- T shares ≥2 vertices with e
  have hinter : 2 ≤ (T ∩ e).card := hT.2.2.1
  -- But M is a packing, so T and e share ≤1 vertex
  have hpair := hM.2 hTM he hTe
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Externals share ≤1 vertex with other M-elements
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_exclusive (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e f : Finset V12) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (T : Finset V12) (hT : T ∈ S_e12 G M e) :
    (T ∩ f).card ≤ 1 := by
  simp only [S_e12, mem_filter] at hT
  exact hT.2.2.2 f hf (Ne.symm hef)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Two externals with different third vertices share ≤1 vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
T_ab = {a, b, x}, T_bc = {b, c, y} where x ≠ y and x, y ∉ {a,b,c}
T_ab ∩ T_bc = {b} ∪ ({x} ∩ {y}) = {b}
So |T_ab ∩ T_bc| = 1
-/

lemma externals_diff_third_share_one (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12)
    (a b c x y : V12)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hya : y ≠ a) (hyb : y ≠ b) (hyc : y ≠ c)
    (hxy : x ≠ y)
    (T_ab T_bc : Finset V12)
    (hTab_eq : T_ab = {a, b, x})
    (hTbc_eq : T_bc = {b, c, y}) :
    (T_ab ∩ T_bc).card ≤ 1 := by
  rw [hTab_eq, hTbc_eq]
  -- {a, b, x} ∩ {b, c, y} = {b}
  have h : ({a, b, x} : Finset V12) ∩ {b, c, y} = {b} := by
    ext v
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · intro ⟨h1, h2⟩
      rcases h1 with rfl | rfl | rfl
      · -- v = a: need a ∈ {b, c, y}
        rcases h2 with rfl | rfl | rfl <;> [exact (hab rfl).elim; exact (hac rfl).elim; exact (hya.symm rfl).elim]
      · -- v = b
        rfl
      · -- v = x: need x ∈ {b, c, y}
        rcases h2 with rfl | rfl | rfl <;> [exact (hxb rfl).elim; exact (hxc rfl).elim; exact (hxy rfl).elim]
    · intro hv
      rw [hv]
      exact ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩
  rw [h, card_singleton]

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN: 5-packing construction when 2 externals have different third vertices
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
If T_ab, T_ac have different third vertices x ≠ z:
- T_ab ∩ T_ac = {a} (they share only vertex a)
- T_ab shares ≤1 vertex with f, g, h (exclusivity)
- T_ac shares ≤1 vertex with f, g, h (exclusivity)
- f, g, h pairwise share ≤1 vertex (from M being packing)
So {T_ab, T_ac, f, g, h} is a 5-packing
-/

lemma five_packing_from_two_externals (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (hM4 : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M)
    (T_ab T_ac : Finset V12)
    (hTab : T_ab ∈ S_e12 G M e)
    (hTac : T_ac ∈ S_e12 G M e)
    (hTabTac : T_ab ≠ T_ac)
    (hInter : (T_ab ∩ T_ac).card ≤ 1) :
    False := by
  -- Get the other 3 elements of M
  have hMother : (M.erase e).card = 3 := by
    rw [card_erase_of_mem he, hM4]
    norm_num
  -- T_ab, T_ac are not in M
  have hTab_not_M := external_not_in_M G M hM e he T_ab hTab
  have hTac_not_M := external_not_in_M G M hM e he T_ac hTac
  -- T_ab, T_ac are triangles
  simp only [S_e12, mem_filter] at hTab hTac
  have hTab_tri := hTab.1
  have hTac_tri := hTac.1
  -- Build the 5-packing: {T_ab, T_ac} ∪ (M.erase e)
  let S := ({T_ab, T_ac} : Finset (Finset V12)) ∪ (M.erase e)
  -- Show S is a triangle packing
  have hS_pack : isTrianglePacking12 G S := by
    constructor
    · -- All elements are triangles
      intro T hTS
      simp only [S, mem_union, mem_insert, mem_singleton, mem_erase] at hTS
      rcases hTS with rfl | rfl | ⟨_, hTM⟩
      · exact hTab_tri
      · exact hTac_tri
      · exact hM.1 hTM
    · -- Pairwise share ≤1 vertex
      intro T1 hT1 T2 hT2 hT12
      simp only [S, coe_union, coe_insert, coe_singleton, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, coe_erase, Set.mem_diff] at hT1 hT2
      rcases hT1 with rfl | rfl | ⟨hT1M, hT1e⟩ <;>
      rcases hT2 with rfl | rfl | ⟨hT2M, hT2e⟩
      · -- T1 = T_ab, T2 = T_ab
        exact (hT12 rfl).elim
      · -- T1 = T_ab, T2 = T_ac
        exact hInter
      · -- T1 = T_ab, T2 ∈ M \ {e}
        exact external_exclusive G M e T2 he hT2M hT2e T_ab hTab
      · -- T1 = T_ac, T2 = T_ab
        rw [inter_comm]; exact hInter
      · -- T1 = T_ac, T2 = T_ac
        exact (hT12 rfl).elim
      · -- T1 = T_ac, T2 ∈ M \ {e}
        exact external_exclusive G M e T2 he hT2M hT2e T_ac hTac
      · -- T1 ∈ M \ {e}, T2 = T_ab
        rw [inter_comm]; exact external_exclusive G M e T1 he hT1M hT1e T_ab hTab
      · -- T1 ∈ M \ {e}, T2 = T_ac
        rw [inter_comm]; exact external_exclusive G M e T1 he hT1M hT1e T_ac hTac
      · -- T1, T2 ∈ M \ {e}
        exact hM.2 hT1M hT2M hT12
  -- S has 5 elements
  have hS_card : S.card = 5 := by
    simp only [S]
    -- {T_ab, T_ac} ∪ (M.erase e)
    -- |{T_ab, T_ac}| = 2 (since T_ab ≠ T_ac)
    -- |M.erase e| = 3
    -- Disjoint because T_ab, T_ac ∉ M
    have h_pair : ({T_ab, T_ac} : Finset (Finset V12)).card = 2 := by
      rw [card_insert_of_not_mem, card_singleton]
      simp [hTabTac]
    have h_disj : Disjoint ({T_ab, T_ac} : Finset (Finset V12)) (M.erase e) := by
      rw [disjoint_iff_ne]
      intro x hx y hy
      simp at hx
      rcases hx with rfl | rfl
      · intro heq; rw [heq] at hTab_not_M
        exact hTab_not_M (mem_of_mem_erase hy)
      · intro heq; rw [heq] at hTac_not_M
        exact hTac_not_M (mem_of_mem_erase hy)
    rw [card_union_of_disjoint h_disj, h_pair, hMother]
  -- But ν = 4, so S.card ≤ 4
  have := hNu4 S hS_pack
  omega

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
A counterexample graph and packing exists where all 3 external types are present.
-/
open Sym2

def counter_edges_finset : Finset (Sym2 V12) :=
  {s(0,1), s(0,2), s(0,3), s(1,2), s(1,3), s(2,3),
   s(4,5), s(5,6), s(4,6),
   s(6,7), s(7,8), s(6,8),
   s(8,9), s(9,10), s(8,10)}

def counter_G : SimpleGraph V12 := SimpleGraph.fromEdgeSet (counter_edges_finset : Set (Sym2 V12))

instance : DecidableRel counter_G.Adj := fun a b =>
  decidable_of_iff (s(a, b) ∈ counter_edges_finset ∧ a ≠ b) (by
    simp [counter_G, SimpleGraph.fromEdgeSet_adj]
  )

def counter_M : Finset (Finset V12) :=
  {{0,1,2}, {4,5,6}, {6,7,8}, {8,9,10}}

lemma counterexample_valid :
    isTrianglePacking12 counter_G counter_M ∧
    counter_M.card = 4 ∧
    (∀ S, isTrianglePacking12 counter_G S → S.card ≤ 4) ∧
    {0,1,2} ∈ counter_M ∧
    (S_e_type12 counter_G counter_M {0,1,2} 0 1 2).Nonempty ∧
    (S_e_type12 counter_G counter_M {0,1,2} 1 2 0).Nonempty ∧
    (S_e_type12 counter_G counter_M {0,1,2} 0 2 1).Nonempty := by
      all_goals norm_num [ isTrianglePacking12, S_e_type12 ];
      all_goals native_decide

/-
The theorem `not_all_three_types12` is false, as shown by the counterexample.
-/
theorem not_all_three_types12_false : ¬ (∀ (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (hM4 : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c),
    ¬((S_e_type12 G M e a b c).Nonempty ∧
      (S_e_type12 G M e b c a).Nonempty ∧
      (S_e_type12 G M e a c b).Nonempty)) := by
  intro h
  let G := counter_G
  let M := counter_M
  let e : Finset V12 := {0, 1, 2}
  let a : V12 := 0
  let b : V12 := 1
  let c : V12 := 2
  have h_valid := counterexample_valid
  have hM : isTrianglePacking12 G M := h_valid.1
  have hM4 : M.card = 4 := h_valid.2.1
  have hNu4 : ∀ S, isTrianglePacking12 G S → S.card ≤ 4 := h_valid.2.2.1
  have he : e ∈ M := h_valid.2.2.2.1
  have ha : a ∈ e := by simp [e, a]
  have hb : b ∈ e := by simp [e, b]
  have hc : c ∈ e := by simp [e, c]
  have hab : a ≠ b := by decide
  have hbc : b ≠ c := by decide
  have hac : a ≠ c := by decide
  have h_types : (S_e_type12 G M e a b c).Nonempty ∧
                 (S_e_type12 G M e b c a).Nonempty ∧
                 (S_e_type12 G M e a c b).Nonempty := by
    exact ⟨h_valid.2.2.2.2.1, h_valid.2.2.2.2.2.1, h_valid.2.2.2.2.2.2⟩
  specialize h G M hM hM4 hNu4 e he a b c ha hb hc hab hbc hac
  contradiction

end AristotleLemmas

/-
══════════════════════════════════════════════════════════════════════════════
MAIN THEOREM: Not all 3 types can have externals
══════════════════════════════════════════════════════════════════════════════

PROOF SKETCH:
Given T_ab, T_bc, T_ac (externals for all 3 edge-types):
- T_ab = {a, b, x}, T_bc = {b, c, y}, T_ac = {a, c, z} for some x, y, z
Case 1: x ≠ z (T_ab, T_ac have different third vertices)
  → T_ab ∩ T_ac = {a}, so |T_ab ∩ T_ac| = 1
  → 5-packing contradiction via five_packing_from_two_externals
Case 2: x = z but y ≠ z (T_ab, T_bc have different, T_ac same as T_ab)
  → T_bc ∩ T_ac = {c}, so |T_bc ∩ T_ac| = 1
  → 5-packing contradiction
Case 3: x = y = z (all share same third vertex, K4 structure)
  → T_ab ∩ T_ac = {a, x}, card = 2
  → Need different argument...
  → In K4, {T_ab, f, g, h} is a 4-packing alternative to M
  → But can we get 5-packing? Need external from another element...
-/
theorem not_all_three_types12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (hM4 : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬((S_e_type12 G M e a b c).Nonempty ∧
      (S_e_type12 G M e b c a).Nonempty ∧
      (S_e_type12 G M e a c b).Nonempty) := by
  intro ⟨⟨T_ab, hTab⟩, ⟨T_bc, hTbc⟩, ⟨T_ac, hTac⟩⟩
  -- Extract from S_e_type12
  simp only [S_e_type12, mem_filter] at hTab hTbc hTac
  -- T_ab contains a, b, not c
  -- T_bc contains b, c, not a
  -- T_ac contains a, c, not b
  have hTab_Se := hTab.1
  have hTbc_Se := hTbc.1
  have hTac_Se := hTac.1
  -- T_ab ∈ S_e12 means it's exclusive to e
  -- Check if T_ab and T_ac have different third vertices
  -- If |T_ab ∩ T_ac| ≤ 1, use five_packing_from_two_externals
  by_cases hInter : (T_ab ∩ T_ac).card ≤ 1
  · -- T_ab, T_ac share ≤1 vertex → 5-packing
    have hne : T_ab ≠ T_ac := by
      intro heq
      rw [heq] at hTab
      -- T_ab = T_ac means T_ac contains a, b, not c (from hTab)
      -- But T_ac should contain a, c, not b (from hTac)
      exact hTac.2.2.2 hTab.2.2.1  -- c ∉ T_ac but b ∈ T_ac
    exact five_packing_from_two_externals G M hM hM4 hNu4 e he T_ab T_ac hTab_Se hTac_Se hne hInter
  · -- T_ab ∩ T_ac has ≥2 vertices (K4 case)
    push_neg at hInter
    -- T_ab = {a, b, x}, T_ac = {a, c, x} share {a, x}
    -- Try T_bc and T_ab or T_bc and T_ac
    by_cases hInter2 : (T_bc ∩ T_ac).card ≤ 1
    · -- T_bc, T_ac share ≤1 vertex → 5-packing
      have hne : T_bc ≠ T_ac := by
        intro heq
        rw [heq] at hTbc
        -- hTbc.2.1 = b ∈ T_bc (= T_ac after rw), hTac.2.2.2 = b ∉ T_ac
        exact hTac.2.2.2 hTbc.2.1
      exact five_packing_from_two_externals G M hM hM4 hNu4 e he T_bc T_ac hTbc_Se hTac_Se hne hInter2
    · -- All pairs share ≥2 vertices (full K4)
      push_neg at hInter2
      by_cases hInter3 : (T_ab ∩ T_bc).card ≤ 1
      · have hne : T_ab ≠ T_bc := by
          intro heq
          rw [heq] at hTab
          exact hTab.2.2.2 hTbc.2.2.1
        exact five_packing_from_two_externals G M hM hM4 hNu4 e he T_ab T_bc hTab_Se hTbc_Se hne hInter3
      · -- All 3 pairs share ≥2 vertices
        -- This means they all share a common third vertex x
        -- T_ab ∩ T_ac ≥ 2, T_bc ∩ T_ac ≥ 2, T_ab ∩ T_bc ≥ 2
        -- Each pair shares both their common edge vertex AND the third vertex x
        -- This forms a K4 on {a, b, c, x}
        -- In this case, we can still form a 5-packing using external from f, g, or h
        -- Wait, there's a mistake. We can actually prove the opposite.
        negate_state;
        -- Proof starts here:
        -- Let's choose the graph G and the packing M from the counterexample.
        use counter_G, by infer_instance, counter_M;
        refine' ⟨ _, _, _, _ ⟩;
        · exact counterexample_valid.1;
        · native_decide +revert;
        · intro S hS; exact (counterexample_valid.2.2.1 S hS) ;
        · refine' ⟨ { 0, 1, 2 }, _, 0, 1, 2, _, _, _, _ ⟩ <;> simp +decide [ counter_M ];
          unfold S_e12; simp +decide ;
          refine' ⟨ { 0, 1, 3 }, _, { 1, 2, 3 }, _, { 0, 2, 3 }, _ ⟩ <;> simp +decide [ counter_edges_finset ] at *;

-/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Not all 3 types can have externals
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
Given T_ab, T_bc, T_ac (externals for all 3 edge-types):
- T_ab = {a, b, x}, T_bc = {b, c, y}, T_ac = {a, c, z} for some x, y, z
Case 1: x ≠ z (T_ab, T_ac have different third vertices)
  → T_ab ∩ T_ac = {a}, so |T_ab ∩ T_ac| = 1
  → 5-packing contradiction via five_packing_from_two_externals
Case 2: x = z but y ≠ z (T_ab, T_bc have different, T_ac same as T_ab)
  → T_bc ∩ T_ac = {c}, so |T_bc ∩ T_ac| = 1
  → 5-packing contradiction
Case 3: x = y = z (all share same third vertex, K4 structure)
  → T_ab ∩ T_ac = {a, x}, card = 2
  → Need different argument...
  → In K4, {T_ab, f, g, h} is a 4-packing alternative to M
  → But can we get 5-packing? Need external from another element...
-/

theorem not_all_three_types12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (hM4 : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬((S_e_type12 G M e a b c).Nonempty ∧
      (S_e_type12 G M e b c a).Nonempty ∧
      (S_e_type12 G M e a c b).Nonempty) := by
  intro ⟨⟨T_ab, hTab⟩, ⟨T_bc, hTbc⟩, ⟨T_ac, hTac⟩⟩
  -- Extract from S_e_type12
  simp only [S_e_type12, mem_filter] at hTab hTbc hTac
  -- T_ab contains a, b, not c
  -- T_bc contains b, c, not a
  -- T_ac contains a, c, not b
  have hTab_Se := hTab.1
  have hTbc_Se := hTbc.1
  have hTac_Se := hTac.1
  -- T_ab ∈ S_e12 means it's exclusive to e
  -- Check if T_ab and T_ac have different third vertices
  -- If |T_ab ∩ T_ac| ≤ 1, use five_packing_from_two_externals
  by_cases hInter : (T_ab ∩ T_ac).card ≤ 1
  · -- T_ab, T_ac share ≤1 vertex → 5-packing
    have hne : T_ab ≠ T_ac := by
      intro heq
      rw [heq] at hTab
      -- T_ab = T_ac means T_ac contains a, b, not c (from hTab)
      -- But T_ac should contain a, c, not b (from hTac)
      exact hTac.2.2.2 hTab.2.2.1  -- c ∉ T_ac but b ∈ T_ac
    exact five_packing_from_two_externals G M hM hM4 hNu4 e he T_ab T_ac hTab_Se hTac_Se hne hInter
  · -- T_ab ∩ T_ac has ≥2 vertices (K4 case)
    push_neg at hInter
    -- T_ab = {a, b, x}, T_ac = {a, c, x} share {a, x}
    -- Try T_bc and T_ab or T_bc and T_ac
    by_cases hInter2 : (T_bc ∩ T_ac).card ≤ 1
    · -- T_bc, T_ac share ≤1 vertex → 5-packing
      have hne : T_bc ≠ T_ac := by
        intro heq
        rw [heq] at hTbc
        -- hTbc.2.1 = b ∈ T_bc (= T_ac after rw), hTac.2.2.2 = b ∉ T_ac
        exact hTac.2.2.2 hTbc.2.1
      exact five_packing_from_two_externals G M hM hM4 hNu4 e he T_bc T_ac hTbc_Se hTac_Se hne hInter2
    · -- All pairs share ≥2 vertices (full K4)
      push_neg at hInter2
      by_cases hInter3 : (T_ab ∩ T_bc).card ≤ 1
      · have hne : T_ab ≠ T_bc := by
          intro heq
          rw [heq] at hTab
          exact hTab.2.2.2 hTbc.2.2.1
        exact five_packing_from_two_externals G M hM hM4 hNu4 e he T_ab T_bc hTab_Se hTbc_Se hne hInter3
      · -- All 3 pairs share ≥2 vertices
        -- This means they all share a common third vertex x
        -- T_ab ∩ T_ac ≥ 2, T_bc ∩ T_ac ≥ 2, T_ab ∩ T_bc ≥ 2
        -- Each pair shares both their common edge vertex AND the third vertex x
        -- This forms a K4 on {a, b, c, x}
        -- In this case, we can still form a 5-packing using external from f, g, or h
        sorry