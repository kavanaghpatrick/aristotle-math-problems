/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7857bb62-83c5-41d6-8f1a-0e4a3de97767

The following was negated by Aristotle:

- theorem bridge_externals_share_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M B T₂)
    (hT₁_v : v ∈ T₁) (hT₂_v : v ∈ T₂) :
    ∃ x : V, x ∉ A ∧ x ∉ B ∧ x ∈ T₁ ∧ x ∈ T₂

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
  slot227_bridge_externals_minimal.lean

  THE MAKE-OR-BREAK LEMMA FOR τ ≤ 8

  Clean minimal version with exactly 1 sorry.
  All scaffolding from proven slot224f.

  Key question: Do externals of DIFFERENT M-elements at shared vertex v
  share a common external apex?

  If TRUE → τ ≤ 8 achievable
  If FALSE (counterexample) → τ ≤ 12 is best via this approach
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot224f PROVEN)
-- ═══════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

-- ═══════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slot224f)
-- ═══════════════════════════════════════════════════════════════════════

lemma shares_edge_implies_two_vertices (t m : Finset V)
    (h_share : sharesEdgeWith t m) :
    (t ∩ m).card ≥ 2 := by
  obtain ⟨u, v, huv, hu_t, hv_t, hu_m, hv_m⟩ := h_share
  have hu_inter : u ∈ t ∩ m := Finset.mem_inter.mpr ⟨hu_t, hu_m⟩
  have hv_inter : v ∈ t ∩ m := Finset.mem_inter.mpr ⟨hv_t, hv_m⟩
  exact Finset.one_lt_card.mpr ⟨u, hu_inter, v, hv_inter, huv⟩

lemma not_share_implies_one_vertex (t m : Finset V)
    (h_not_share : ¬sharesEdgeWith t m) :
    (t ∩ m).card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
  exact h_not_share ⟨u, v, huv, (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1,
                     (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩

lemma external_intersects_other_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B : Finset V) (hB : B ∈ M) (hAB : A ≠ B)
    (t : Finset V) (ht_ext : isExternalOf G M A t) :
    (t ∩ B).card ≤ 1 := by
  exact not_share_implies_one_vertex t B (ht_ext.2.2.2 B hB hAB.symm)

-- ═══════════════════════════════════════════════════════════════════════
-- 5-PACKING (from slot182 PROVEN)
-- ═══════════════════════════════════════════════════════════════════════

theorem five_packing_from_disjoint_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_ne_T₂ : T₁ ≠ T₂)
    (h_no_shared_edge : ¬sharesEdgeWith T₁ T₂) :
    ∃ M' : Finset (Finset V), M'.card = 5 ∧ isTrianglePacking G M' := by
  let M' := {T₁, T₂} ∪ M.erase A
  use M'
  have hT₁_not_M : T₁ ∉ M := hT₁.2.1
  have hT₂_not_M : T₂ ∉ M := hT₂.2.1
  constructor
  · have h1 : (M.erase A).card = 3 := by rw [Finset.card_erase_of_mem hA]; omega
    have h2 : ({T₁, T₂} : Finset (Finset V)).card = 2 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
      simp only [Finset.mem_singleton]; exact hT₁_ne_T₂
    have h3 : Disjoint {T₁, T₂} (M.erase A) := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · intro h; exact hT₁_not_M (Finset.mem_erase.mp (h ▸ hy)).2
      · intro h; exact hT₂_not_M (Finset.mem_erase.mp (h ▸ hy)).2
    rw [Finset.card_union_of_disjoint h3, h2, h1]
  · constructor
    · intro t ht
      rcases Finset.mem_union.mp ht with hp | hm
      · rcases Finset.mem_insert.mp hp with rfl | hs
        · exact hT₁.1
        · rw [Finset.mem_singleton] at hs; rw [hs]; exact hT₂.1
      · exact hM.1.1 (Finset.mem_erase.mp hm).2
    · intro t₁ ht₁ t₂ ht₂ hne
      rcases Finset.mem_union.mp ht₁ with hp₁ | hm₁ <;>
      rcases Finset.mem_union.mp ht₂ with hp₂ | hm₂
      · rcases Finset.mem_insert.mp hp₁ with heq₁ | hs₁ <;>
        rcases Finset.mem_insert.mp hp₂ with heq₂ | hs₂
        · exact absurd (heq₁.trans heq₂.symm) hne
        · rw [Finset.mem_singleton] at hs₂; rw [heq₁, hs₂]
          exact not_share_implies_one_vertex T₁ T₂ h_no_shared_edge
        · rw [Finset.mem_singleton] at hs₁; rw [hs₁, heq₂, Finset.inter_comm]
          exact not_share_implies_one_vertex T₁ T₂ h_no_shared_edge
        · rw [Finset.mem_singleton] at hs₁ hs₂
          exact absurd (hs₁.trans hs₂.symm) hne
      · have hB := (Finset.mem_erase.mp hm₂).2
        have hB_ne := (Finset.mem_erase.mp hm₂).1
        rcases Finset.mem_insert.mp hp₁ with heq₁ | hs₁
        · rw [heq₁]; exact external_intersects_other_le_1 G M A t₂ hB hB_ne.symm T₁ hT₁
        · rw [Finset.mem_singleton] at hs₁; rw [hs₁]
          exact external_intersects_other_le_1 G M A t₂ hB hB_ne.symm T₂ hT₂
      · have hB := (Finset.mem_erase.mp hm₁).2
        have hB_ne := (Finset.mem_erase.mp hm₁).1
        rcases Finset.mem_insert.mp hp₂ with heq₂ | hs₂
        · rw [heq₂, Finset.inter_comm]
          exact external_intersects_other_le_1 G M A t₁ hB hB_ne.symm T₁ hT₁
        · rw [Finset.mem_singleton] at hs₂; rw [hs₂, Finset.inter_comm]
          exact external_intersects_other_le_1 G M A t₁ hB hB_ne.symm T₂ hT₂
      · exact hM.1.2 (Finset.mem_erase.mp hm₁).2 (Finset.mem_erase.mp hm₂).2 hne

-- ═══════════════════════════════════════════════════════════════════════
-- TWO EXTERNALS SHARE EDGE (from slot182 PROVEN)
-- ═══════════════════════════════════════════════════════════════════════

theorem two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  by_contra h_no_edge
  obtain ⟨M', hM'_card, hM'_packing⟩ := five_packing_from_disjoint_externals
    G M hM hM_card A hA T₁ T₂ hT₁ hT₂ h_ne h_no_edge
  have := hν M' hM'_packing
  omega

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Definitions for the counterexample graph using Fin 13 directly.
-/
def CE_edges : List (Fin 13 × Fin 13) := [
  (0, 1), (1, 2), (2, 0), -- A
  (0, 3), (3, 4), (4, 0), -- B
  (1, 5), (5, 0),         -- T1
  (3, 6), (6, 0),         -- T2
  (7, 8), (8, 9), (9, 7), -- C
  (10, 11), (11, 12), (12, 10) -- D
]

def CE_G : SimpleGraph (Fin 13) := SimpleGraph.fromRel (fun x y => (x, y) ∈ CE_edges ∨ (y, x) ∈ CE_edges)

def CE_A : Finset (Fin 13) := {0, 1, 2}
def CE_B : Finset (Fin 13) := {0, 3, 4}
def CE_C : Finset (Fin 13) := {7, 8, 9}
def CE_D : Finset (Fin 13) := {10, 11, 12}
def CE_M : Finset (Finset (Fin 13)) := {CE_A, CE_B, CE_C, CE_D}

def CE_T1 : Finset (Fin 13) := {0, 1, 5}
def CE_T2 : Finset (Fin 13) := {0, 3, 6}

/-
Proves that CE_M is a triangle packing in CE_G.
-/
lemma CE_isTrianglePacking : isTrianglePacking CE_G CE_M := by
  -- First, we need to verify that CE_A, CE_B, CE_C, and CE_D are indeed triangles in CE_G.
  have h_triangles : ∀ t ∈ CE_M, t ∈ CE_G.cliqueFinset 3 := by
    simp +decide [ SimpleGraph.isNClique_iff ];
    simp +decide [ SimpleGraph.IsClique, CE_G ];
    simp +decide [ Set.Pairwise ];
  -- Next, we need to verify that the elements of CE_M are pairwise intersecting in at most one vertex.
  have h_pairwise : ∀ t1 t2 : Finset (Fin 13), t1 ∈ CE_M → t2 ∈ CE_M → t1 ≠ t2 → (t1 ∩ t2).card ≤ 1 := by
    rintro t1 t2 ht1 ht2 hne; fin_cases ht1 <;> fin_cases ht2 <;> trivial;
  exact ⟨ Finset.subset_iff.mpr h_triangles, fun t1 ht1 t2 ht2 hne => h_pairwise t1 t2 ht1 ht2 hne ⟩

/-
Proves that the set of triangles in CE_G is exactly {A, B, C, D, T1, T2}.
-/
lemma CE_cliqueFinset_eq : CE_G.cliqueFinset 3 = {CE_A, CE_B, CE_C, CE_D, CE_T1, CE_T2} := by
  unfold CE_G SimpleGraph.cliqueFinset;
  simp +decide [ SimpleGraph.isNClique_iff ];
  simp +decide [ SimpleGraph.IsClique, CE_A, CE_B, CE_C, CE_D, CE_T1, CE_T2 ];
  ext s;
  -- We can prove this by checking each possible triangle in the graph.
  apply Iff.intro;
  · simp +decide [ Set.Pairwise ];
    intro hs hs'; have := Finset.card_eq_three.mp hs'; obtain ⟨ x, y, z, hxyz ⟩ := this; simp_all +decide ;
    -- By examining all possible combinations of x, y, and z, we can see that the only triangles in CE_G are {0,1,2}, {0,3,4}, {7,8,9}, {10,11,12}, {0,1,5}, and {0,3,6}.
    have h_triangles : ∀ x y z : Fin 13, x ≠ y → x ≠ z → y ≠ z → (CE_edges.contains (x, y) ∨ CE_edges.contains (y, x)) → (CE_edges.contains (x, z) ∨ CE_edges.contains (z, x)) → (CE_edges.contains (y, z) ∨ CE_edges.contains (z, y)) → ({x, y, z} : Finset (Fin 13)) = {0, 1, 2} ∨ ({x, y, z} : Finset (Fin 13)) = {0, 3, 4} ∨ ({x, y, z} : Finset (Fin 13)) = {7, 8, 9} ∨ ({x, y, z} : Finset (Fin 13)) = {10, 11, 12} ∨ ({x, y, z} : Finset (Fin 13)) = {0, 1, 5} ∨ ({x, y, z} : Finset (Fin 13)) = {0, 3, 6} := by
      native_decide;
    grind;
  · simp +decide [ Set.Pairwise ];
    rintro ( rfl | rfl | rfl | rfl | rfl | rfl ) <;> native_decide

/-
Proves that CE_M is a maximum packing in CE_G.
-/
lemma CE_isMaxPacking : isMaxPacking CE_G CE_M := by
  refine' ⟨ CE_isTrianglePacking, _ ⟩;
  rw [ CE_cliqueFinset_eq ];
  native_decide

/-
Proves that A and T1 share 2 vertices, and B and T2 share 2 vertices.
-/
lemma CE_conflicts : (CE_A ∩ CE_T1).card = 2 ∧ (CE_B ∩ CE_T2).card = 2 := by
  native_decide

/-
Proves that the maximum packing size in CE_G is 4 by partitioning the triangles into conflicting pairs.
-/
lemma CE_nu_le_4 : ∀ P : Finset (Finset (Fin 13)), isTrianglePacking CE_G P → P.card ≤ 4 := by
  intro P hP;
  -- Since P is a subset of the cliqueFinset 3 of CE_G, and the cliqueFinset 3 has 6 elements, P can't have more than 6 elements. But we need to show it's at most 4.
  have h_subset : P ⊆ CE_G.cliqueFinset 3 := by
    exact hP.1;
  -- Since P is a subset of the cliqueFinset 3 of CE_G, and the cliqueFinset 3 has 6 elements, P can't have more than 6 elements. But we need to show it's at most 4. Let's consider the possible combinations of triangles in P.
  have h_combinations : ∀ S ⊆ CE_G.cliqueFinset 3, S.card > 4 → ¬isTrianglePacking CE_G S := by
    intros S hS hS_card
    by_contra h_contra
    have h_combinations : ∀ S ⊆ {CE_A, CE_B, CE_C, CE_D, CE_T1, CE_T2}, S.card > 4 → ¬isTrianglePacking CE_G S := by
      simp +decide [ isTrianglePacking ];
      intros S hS hS_card hS_subset hS_pairwise;
      have h_combinations : ∀ S ⊆ ({CE_A, CE_B, CE_C, CE_D, CE_T1, CE_T2} : Finset (Finset (Fin 13))), S.card > 4 → ¬∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → (t1 ∩ t2).card ≤ 1 := by
        native_decide;
      exact h_combinations S hS hS_card fun t1 ht1 t2 ht2 hne => hS_pairwise ht1 ht2 hne;
    exact h_combinations S ( hS.trans ( by rw [ CE_cliqueFinset_eq ] ) ) hS_card h_contra;
  exact le_of_not_gt fun h => h_combinations P h_subset h hP

/-
Proves that CE_M is a maximum packing in CE_G (safe version).
-/
lemma CE_isMaxPacking_safe : isMaxPacking CE_G CE_M := by
  exact?

/-
Proves that T1 is external to A and T2 is external to B in the counterexample.
-/
lemma CE_externals : isExternalOf CE_G CE_M CE_A CE_T1 ∧ isExternalOf CE_G CE_M CE_B CE_T2 := by
  constructor;
  · apply And.intro;
    · unfold CE_T1; simp +decide [ CE_cliqueFinset_eq ] ;
    · unfold sharesEdgeWith;
      native_decide +revert;
  · constructor;
    · simp +decide [ CE_cliqueFinset_eq ];
    · unfold sharesEdgeWith;
      native_decide +revert

/-
Proves that the counterexample satisfies all hypotheses but falsifies the conclusion.
-/
theorem CE_disproves_conjecture :
    isMaxPacking CE_G CE_M ∧
    CE_M.card = 4 ∧
    (∀ P : Finset (Finset (Fin 13)), isTrianglePacking CE_G P → P.card ≤ 4) ∧
    CE_A ∈ CE_M ∧ CE_B ∈ CE_M ∧ CE_A ≠ CE_B ∧
    (0 : Fin 13) ∈ CE_A ∧ (0 : Fin 13) ∈ CE_B ∧
    isExternalOf CE_G CE_M CE_A CE_T1 ∧
    isExternalOf CE_G CE_M CE_B CE_T2 ∧
    (0 : Fin 13) ∈ CE_T1 ∧ (0 : Fin 13) ∈ CE_T2 ∧
    ∀ x : Fin 13, ¬(x ∉ CE_A ∧ x ∉ CE_B ∧ x ∈ CE_T1 ∧ x ∈ CE_T2) := by
      refine' ⟨ _, _, _, _, _, _ ⟩;
      exact?;
      · native_decide;
      · exact?;
      · exact Finset.mem_insert_self _ _;
      · native_decide +revert;
      · exact ⟨ by decide, by decide, by decide, by exact CE_externals.1, by exact CE_externals.2, by decide, by decide, by decide ⟩

/-
Proves the negation of the bridge_externals_share_apex conjecture using the counterexample.
-/
theorem bridge_externals_share_apex_false : ¬ (∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M B T₂)
    (hT₁_v : v ∈ T₁) (hT₂_v : v ∈ T₂),
    ∃ x : V, x ∉ A ∧ x ∉ B ∧ x ∈ T₁ ∧ x ∈ T₂) := by
      push_neg;
      refine' ⟨ _, _, _, _, _, _, _, _, _ ⟩;
      exact ULift ( Fin 13 );
      all_goals try infer_instance;
      exact SimpleGraph.comap ULift.down CE_G;
      infer_instance;
      exact Finset.image ( fun x : Finset ( Fin 13 ) => Finset.image ULift.up x ) CE_M;
      · constructor;
        · constructor;
          · simp +decide [ Finset.subset_iff ];
            simp +decide [ SimpleGraph.isNClique_iff, Finset.card_image_of_injective, Function.Injective ];
            simp +decide [ SimpleGraph.IsClique, Set.Pairwise ];
            unfold CE_G; simp +decide [ SimpleGraph.fromRel_adj ] ;
          · simp +decide [ Set.Pairwise ];
        · intro t ht ht';
          -- Since $t$ is a triangle in the comap graph, it must correspond to a triangle in the original CE_G.
          obtain ⟨t', ht', ht''⟩ : ∃ t' : Finset (Fin 13), t = Finset.image ULift.up t' ∧ t' ∈ CE_G.cliqueFinset 3 := by
            use Finset.image ULift.down t;
            simp_all +decide [ Finset.ext_iff, SimpleGraph.cliqueFinset ];
            simp_all +decide [ SimpleGraph.isNClique_iff, Finset.card_image_of_injective, Function.Injective ];
            intro x hx y hy hxy; aesop;
          -- Since $t'$ is a triangle in the original CE_G, it must be one of the triangles in the set {CE_A, CE_B, CE_C, CE_D, CE_T1, CE_T2}.
          have ht'_cases : t' = CE_A ∨ t' = CE_B ∨ t' = CE_C ∨ t' = CE_D ∨ t' = CE_T1 ∨ t' = CE_T2 := by
            have ht'_cases : t' ∈ CE_G.cliqueFinset 3 := by
              exact ht'';
            rw [ CE_cliqueFinset_eq ] at ht'_cases; aesop;
          rcases ht'_cases with ( rfl | rfl | rfl | rfl | rfl | rfl ) <;> simp_all +decide;
      · native_decide +revert;
      · refine' ⟨ _, _ ⟩;
        · intro P hP;
          convert CE_nu_le_4 ( Finset.image ( fun x : Finset ( ULift ( Fin 13 ) ) => Finset.image ULift.down x ) P ) _;
          · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using Finset.image_injective ( show Function.Injective ( fun x : ULift ( Fin 13 ) => x.down ) from fun x y hxy => by simpa using hxy ) hxy ];
          · unfold isTrianglePacking at *;
            simp_all +decide [ Finset.subset_iff, Set.Pairwise ];
            simp_all +decide [ Finset.ext_iff, SimpleGraph.isNClique_iff ];
            simp_all +decide [ Set.Pairwise, Finset.card_image_of_injective, Function.Injective ];
            refine' ⟨ fun a ha x hx y hy hxy => hP.1 ha |>.1 x hx y hy hxy, fun a ha b hb x hx => _ ⟩;
            convert hP.2 ha hb x hx using 1;
            rw [ ← Finset.card_image_of_injective _ ULift.up_injective ] ; congr ; ext ; aesop;
        · refine' ⟨ _, _, Finset.mem_image_of_mem _ ( Finset.mem_insert_self _ _ ), Finset.mem_image_of_mem _ ( Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ) ), _, _ ⟩ <;> simp +decide [ isExternalOf ];
          refine' ⟨ 0, _, _, _ ⟩ <;> simp +decide [ CE_A, CE_B, CE_M ];
          refine' ⟨ Finset.image ULift.up CE_T1, _, Finset.image ULift.up CE_T2, _, _ ⟩ <;> simp +decide [ CE_T1, CE_T2, sharesEdgeWith ];
          · simp +decide [ SimpleGraph.isNClique_iff ];
            simp +decide [ CE_G ];
          · simp +decide [ SimpleGraph.isNClique_iff ];
            simp +decide [ CE_G ]

end AristotleLemmas

/-
═══════════════════════════════════════════════════════════════════════
THE MAKE-OR-BREAK LEMMA (1 SORRY)
═══════════════════════════════════════════════════════════════════════

Bridge Externals Share Apex

  If T₁ is external of A at shared vertex v, and T₂ is external of B at v,
  do they share a common external vertex x (where x ∉ A ∧ x ∉ B)?

  Key insight from debate:
  - The naive 5-packing argument does NOT work here
  - T₁ external of A, T₂ external of B (different M-elements)
  - Replacing A,B with T₁,T₂ gives {T₁, T₂, C, D} = 4 elements (not 5!)

  Proof strategies for Aristotle:
  1. Show T₁ and T₂ must share an edge (extending slot182)
  2. Use cycle_4 structure constraints
  3. Find a 5th triangle to contradict ν = 4
  4. OR find counterexample graph where x₁ ≠ x₂ with ν = 4
-/
theorem bridge_externals_share_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M B T₂)
    (hT₁_v : v ∈ T₁) (hT₂_v : v ∈ T₂) :
    ∃ x : V, x ∉ A ∧ x ∉ B ∧ x ∈ T₁ ∧ x ∈ T₂ := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  have := @bridge_externals_share_apex_false;
  push_neg at this;
  convert this

-/
-- ═══════════════════════════════════════════════════════════════════════
-- THE MAKE-OR-BREAK LEMMA (1 SORRY)
-- ═══════════════════════════════════════════════════════════════════════

/--
  Bridge Externals Share Apex

  If T₁ is external of A at shared vertex v, and T₂ is external of B at v,
  do they share a common external vertex x (where x ∉ A ∧ x ∉ B)?

  Key insight from debate:
  - The naive 5-packing argument does NOT work here
  - T₁ external of A, T₂ external of B (different M-elements)
  - Replacing A,B with T₁,T₂ gives {T₁, T₂, C, D} = 4 elements (not 5!)

  Proof strategies for Aristotle:
  1. Show T₁ and T₂ must share an edge (extending slot182)
  2. Use cycle_4 structure constraints
  3. Find a 5th triangle to contradict ν = 4
  4. OR find counterexample graph where x₁ ≠ x₂ with ν = 4
-/
theorem bridge_externals_share_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (hv_A : v ∈ A) (hv_B : v ∈ B)
    (T₁ T₂ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M B T₂)
    (hT₁_v : v ∈ T₁) (hT₂_v : v ∈ T₂) :
    ∃ x : V, x ∉ A ∧ x ∉ B ∧ x ∈ T₁ ∧ x ∈ T₂ := by
  sorry

end