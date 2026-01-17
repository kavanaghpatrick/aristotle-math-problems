/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1296fb5e-98ca-4d4d-875a-8335c13e7f94

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem path4_bridge_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V)
    (hAB : (A ∩ B).card = 1)
    (hBC : (B ∩ C).card = 1)
    (hCD : (C ∩ D).card = 1)
    (hAC : Disjoint A C)
    (hAD : Disjoint A D)
    (hBD : Disjoint B D) :
    -- At most 3 adjacent pairs can have bridges
    ∀ T ∈ G.cliqueFinset 3,
      (2 ≤ (T ∩ A).card ∧ 2 ≤ (T ∩ B).card) ∨
      (2 ≤ (T ∩ B).card ∧ 2 ≤ (T ∩ C).card) ∨
      (2 ≤ (T ∩ C).card ∧ 2 ≤ (T ∩ D).card) ∨
      -- Or T is not a bridge (only shares edge with one element)
      (∀ E ∈ ({A, B, C, D} : Finset (Finset V)), (T ∩ E).card ≤ 1) ∨
      (∃! E, E ∈ ({A, B, C, D} : Finset (Finset V)) ∧ 2 ≤ (T ∩ E).card)
-/

/-
  slot448_bridge_classification.lean

  CRITICAL INSIGHT: Bridges are NOT S_e externals!

  A bridge between E and F shares edge with BOTH elements,
  so it fails the S_e definition (which requires sharing with only one).

  This resolves the "spine domination" paradox from the multi-agent debate.

  TIER: 2 (uses proven scaffolding, logical reasoning)
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (E : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ E ∧
    2 ≤ (T ∩ E).card ∧
    ∀ F ∈ M, F ≠ E → (T ∩ F).card ≤ 1)

def isBridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (T E F : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ 2 ≤ (T ∩ E).card ∧ 2 ≤ (T ∩ F).card

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Bridges are not in S_e
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. S_e(E) requires: ∀ F ∈ M, F ≠ E → (T ∩ F).card ≤ 1
2. Bridge requires: 2 ≤ (T ∩ E).card AND 2 ≤ (T ∩ F).card
3. Since F ∈ M and F ≠ E, the S_e condition fails for bridges
4. Therefore bridges are not in S_e(E) or S_e(F)
-/

theorem bridge_not_in_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (E F T : Finset V)
    (hE_in : E ∈ M) (hF_in : F ∈ M) (hEF_ne : E ≠ F)
    (hT_clique : T ∈ G.cliqueFinset 3)
    (hTE : 2 ≤ (T ∩ E).card) (hTF : 2 ≤ (T ∩ F).card) :
    T ∉ S_e G M E ∧ T ∉ S_e G M F := by
  constructor
  -- T ∉ S_e G M E
  · intro hT_Se
    simp only [S_e, mem_filter] at hT_Se
    obtain ⟨_, _, _, hT_disj⟩ := hT_Se
    -- hT_disj says: ∀ F' ∈ M, F' ≠ E → (T ∩ F').card ≤ 1
    -- But F ∈ M, F ≠ E, and (T ∩ F).card ≥ 2
    have h_contra := hT_disj F hF_in hEF_ne
    omega
  -- T ∉ S_e G M F
  · intro hT_Se
    simp only [S_e, mem_filter] at hT_Se
    obtain ⟨_, _, _, hT_disj⟩ := hT_Se
    -- hT_disj says: ∀ E' ∈ M, E' ≠ F → (T ∩ E').card ≤ 1
    -- But E ∈ M, E ≠ F, and (T ∩ E).card ≥ 2
    have h_contra := hT_disj E hE_in hEF_ne.symm
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: Bridge external edge
-- ══════════════════════════════════════════════════════════════════════════════

/-
For a bridge T = {v, x, y} between E (containing v, x) and F (containing v, y):
- The edge {x, y} is NOT in E or F (since E ∩ F = {v})
- But {x, y} covers the bridge T
-/

theorem bridge_has_external_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v x y : V)
    (hE_card : E.card = 3) (hF_card : F.card = 3)
    (hEF : E ∩ F = {v})
    (hx_E : x ∈ E) (hx_ne : x ≠ v)
    (hy_F : y ∈ F) (hy_ne : y ≠ v)
    (hxy_ne : x ≠ y) :
    -- x is not in F (except possibly through v, but x ≠ v)
    x ∉ F ∧
    -- y is not in E (except possibly through v, but y ≠ v)
    y ∉ E ∧
    -- The edge {x, y} is in the bridge {v, x, y}
    s(x, y) ∈ ({v, x, y} : Finset V).sym2 := by
  refine ⟨?_, ?_, ?_⟩
  -- x ∉ F
  · intro hx_F
    have hx_both : x ∈ E ∩ F := mem_inter.mpr ⟨hx_E, hx_F⟩
    rw [hEF] at hx_both
    exact hx_ne (mem_singleton.mp hx_both)
  -- y ∉ E
  · intro hy_E
    have hy_both : y ∈ E ∩ F := mem_inter.mpr ⟨hy_E, hy_F⟩
    rw [hEF] at hy_both
    exact hy_ne (mem_singleton.mp hy_both)
  -- s(x, y) ∈ {v, x, y}.sym2
  · simp only [Finset.mk_mem_sym2_iff, mem_insert, mem_singleton]
    exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- EXTERNAL EDGE NOT IN PACKING ELEMENT EDGES
-- ══════════════════════════════════════════════════════════════════════════════

theorem external_edge_not_in_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset V) (x y : V)
    (hE_card : E.card = 3)
    (hx_E : x ∈ E) (hy_not_E : y ∉ E) :
    s(x, y) ∉ E.sym2 := by
  simp only [Finset.mk_mem_sym2_iff, not_and_or]
  right
  exact hy_not_E

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE COVERAGE OPTIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-
A bridge T = {v, x, y} can be covered by:
1. E's edge {v, x} (the "internal" leg)
2. F's edge {v, y} (the "internal" leg)
3. The external edge {x, y}

If both E and F are committed to other edges (for S_e coverage),
option 3 provides the fallback.
-/

theorem bridge_three_cover_options (G : SimpleGraph V) [DecidableRel G.Adj]
    (v x y : V) (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y)
    (hT_clique : {v, x, y} ∈ G.cliqueFinset 3) :
    -- The three edges of the bridge
    s(v, x) ∈ ({v, x, y} : Finset V).sym2 ∧
    s(v, y) ∈ ({v, x, y} : Finset V).sym2 ∧
    s(x, y) ∈ ({v, x, y} : Finset V).sym2 := by
  simp only [Finset.mk_mem_sym2_iff, mem_insert, mem_singleton]
  refine ⟨⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩,
          ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩,
          ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 BRIDGE BOUND
-- ══════════════════════════════════════════════════════════════════════════════

/-
In PATH_4 (A-v1-B-v2-C-v3-D), there are at most 3 pairs of adjacent elements:
- (A, B), (B, C), (C, D)

Each pair can have bridges. The external edges for these bridges are:
- A-B bridge: edge between some a ∈ A\{v1} and some b' ∈ B\{v1}
- B-C bridge: edge between b ∈ B\{v2} and c ∈ C\{v2}
- C-D bridge: edge between c' ∈ C\{v3} and d ∈ D\{v3}

These are at most 3 extra edges if all bridges exist and none are covered
by the adaptive S_e cover.
-/

theorem path4_bridge_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V)
    (hAB : (A ∩ B).card = 1)
    (hBC : (B ∩ C).card = 1)
    (hCD : (C ∩ D).card = 1)
    (hAC : Disjoint A C)
    (hAD : Disjoint A D)
    (hBD : Disjoint B D) :
    -- At most 3 adjacent pairs can have bridges
    ∀ T ∈ G.cliqueFinset 3,
      (2 ≤ (T ∩ A).card ∧ 2 ≤ (T ∩ B).card) ∨
      (2 ≤ (T ∩ B).card ∧ 2 ≤ (T ∩ C).card) ∨
      (2 ≤ (T ∩ C).card ∧ 2 ≤ (T ∩ D).card) ∨
      -- Or T is not a bridge (only shares edge with one element)
      (∀ E ∈ ({A, B, C, D} : Finset (Finset V)), (T ∩ E).card ≤ 1) ∨
      (∃! E, E ∈ ({A, B, C, D} : Finset (Finset V)) ∧ 2 ≤ (T ∩ E).card) := by
  intro T _
  -- Non-adjacent pairs are disjoint, so T can share edge with at most
  -- one element from {A, C} and at most one from {B, D}
  -- This means at most 2 elements total, and if 2, they must be adjacent
  by_cases hT_A : 2 ≤ #(T ∩ A) <;> by_cases hT_B : 2 ≤ #(T ∩ B) <;> by_cases hT_C : 2 ≤ #(T ∩ C) <;> by_cases hT_D : 2 ≤ #(T ∩ D) <;> simp_all +decide [ ExistsUnique ];
  · have h_inter_A_C : #(T ∩ A ∩ C) ≤ 0 := by
      simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ];
    have h_inter_A_C : #(T ∩ A ∩ C) = #(T ∩ A) + #(T ∩ C) - #(T ∩ (A ∪ C)) := by
      rw [ ← Finset.card_union_add_card_inter, Finset.inter_union_distrib_left ];
      simp +decide [ Finset.inter_left_comm, Finset.inter_comm ];
    have h_inter_A_C : #(T ∩ (A ∪ C)) ≤ 3 := by
      exact le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ( by linarith [ ‹G.IsNClique 3 T›.card_eq ] );
    omega;
  · simp_all +decide [ SimpleGraph.isNClique_iff ];
    exact absurd ( Finset.card_le_card ( show T ∩ A ∪ T ∩ D ⊆ T from Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ) ( by rw [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx_A hx_D => by simp_all +decide [ Finset.disjoint_left ] ) ] ; linarith );
  · have h_inter_BD : Finset.card (T ∩ B ∪ T ∩ D) = Finset.card (T ∩ B) + Finset.card (T ∩ D) := by
      exact Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx_B hx_D => by have := Finset.disjoint_left.mp hBD ( Finset.mem_of_mem_inter_right hx_B ) ( Finset.mem_of_mem_inter_right hx_D ) ; contradiction );
    linarith [ show Finset.card ( T ∩ B ∪ T ∩ D ) ≤ 3 by exact le_trans ( Finset.card_le_card ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ) ( by linarith [ ‹G.IsNClique 3 T›.2 ] ) ];
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨ Nat.le_of_lt_succ hT_A, Nat.le_of_lt_succ hT_B, Nat.le_of_lt_succ hT_C, Nat.le_of_lt_succ hT_D ⟩

end