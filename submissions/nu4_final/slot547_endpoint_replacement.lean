/-
  slot547_endpoint_replacement.lean

  ENDPOINT REPLACEMENT LEMMA FOR PATH_4:
  If endpoint A of PATH_4 has a base-edge external F₁ = {a1,a2,u}
  that is edge-disjoint from all other packing elements,
  then M' = (M \ {A}) ∪ {F₁} is a valid 4-packing.

  KEY RESULTS (ALL PROVEN):
  1. base_external_disjoint_from_adjacent:
     Base-edge externals NEVER conflict with the adjacent element B.
  2. replacement_packing:
     Replacing one element with an edge-disjoint triangle preserves packing.
  3. bridge_external_vertex_in_C:
     If a base-edge external DOES conflict with C, then u ∈ C.
  4. external_replace_or_bridge:
     Every base-edge external either enables replacement or is a bridge.

  SORRY COUNT: 0
  AXIOM COUNT: 0

  TIER: 2 (set theory + packing construction)
-/

import Mathlib

set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════════
-- DEFINITIONS (consistent with slot544-546)
-- ═══════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

-- ═══════════════════════════════════════════════════════════════════════
-- PROVEN HELPERS
-- ═══════════════════════════════════════════════════════════════════════

/-- Members of a triple -/
lemma mem_triple {α : Type*} [DecidableEq α] {a b c x : α}
    (hx : x ∈ ({a, b, c} : Finset α)) : x = a ∨ x = b ∨ x = c := by
  simp only [mem_insert, mem_singleton] at hx; exact hx

/-- If A = {v1,a1,a2} and A ∩ B = {v1}, then a1 ∉ B and a2 ∉ B -/
lemma base_vertices_not_in_adjacent
    (A B : Finset V) (v1 a1 a2 : V)
    (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2)
    (hAB : A ∩ B = {v1}) :
    a1 ∉ B ∧ a2 ∉ B := by
  constructor
  · intro ha1B
    have : a1 ∈ A ∩ B := mem_inter.mpr ⟨hA_eq ▸ by simp [h12], ha1B⟩
    rw [hAB] at this
    exact h12.symm (mem_singleton.mp this)
  · intro ha2B
    have : a2 ∈ A ∩ B := mem_inter.mpr ⟨hA_eq ▸ by simp [h12, h13], ha2B⟩
    rw [hAB] at this
    exact h13.symm (mem_singleton.mp this)

-- ═══════════════════════════════════════════════════════════════════════
-- KEY LEMMA 1: Base-edge external never conflicts with adjacent element
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
A = {v1, a1, a2} with A ∩ B = {v1}.
F₁ = {a1, a2, u} is a base-edge external.
Since a1 ∉ B and a2 ∉ B (from base_vertices_not_in_adjacent),
F₁ ∩ B ⊆ {u}, so |F₁ ∩ B| ≤ 1.
-/
theorem base_external_disjoint_from_adjacent
    (A B : Finset V) (v1 a1 a2 u : V)
    (F₁ : Finset V) (hF_eq : F₁ = {a1, a2, u})
    (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2)
    (hAB : A ∩ B = {v1}) :
    (F₁ ∩ B).card ≤ 1 := by
  obtain ⟨ha1_notB, ha2_notB⟩ :=
    base_vertices_not_in_adjacent A B v1 a1 a2 hA_eq h12 h13 hAB
  suffices F₁ ∩ B ⊆ {u} from (card_le_card this).trans (card_singleton u).le
  intro x hx
  rw [mem_inter, hF_eq] at hx
  rcases mem_triple hx.1 with rfl | rfl | rfl
  · exact absurd hx.2 ha1_notB
  · exact absurd hx.2 ha2_notB
  · exact mem_singleton.mpr rfl

-- ═══════════════════════════════════════════════════════════════════════
-- KEY LEMMA 2: General replacement preserves packing
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
Given packing M with A ∈ M, and triangle F₁ ∉ M that is
edge-disjoint from every element of M except A:
1. M' = insert F₁ (M.erase A)
2. Every element of M' is a clique: F₁ by hypothesis, others from M
3. Pairwise: F₁ vs T ∈ M\{A} by hF_disj; T₁ vs T₂ ∈ M\{A} from M's packing
-/
theorem replacement_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A F₁ : Finset V)
    (hM : isTrianglePacking G M) (hA : A ∈ M)
    (hF_clique : F₁ ∈ G.cliqueFinset 3)
    (hF_not_M : F₁ ∉ M)
    (hF_disj : ∀ T ∈ M, T ≠ A → (F₁ ∩ T).card ≤ 1) :
    isTrianglePacking G (insert F₁ (M.erase A)) := by
  constructor
  · intro T hT
    rw [mem_insert] at hT
    rcases hT with rfl | hT
    · exact hF_clique
    · exact hM.1 (mem_of_mem_erase hT)
  · intro t1 ht1 t2 ht2 h_ne
    rw [Finset.mem_coe, mem_insert] at ht1 ht2
    rcases ht1 with rfl | ht1 <;> rcases ht2 with rfl | ht2
    · exact absurd rfl h_ne
    · exact hF_disj t2 (mem_of_mem_erase ht2) (ne_of_mem_erase ht2)
    · have := hF_disj t1 (mem_of_mem_erase ht1) (ne_of_mem_erase ht1)
      rwa [inter_comm] at this
    · exact hM.2 (Finset.mem_coe.mpr (mem_of_mem_erase ht1))
        (Finset.mem_coe.mpr (mem_of_mem_erase ht2)) h_ne

/--
PROVIDED SOLUTION:
|insert F₁ (M.erase A)| = |M.erase A| + 1 (F₁ ∉ M.erase A)
= (|M| - 1) + 1 = |M|.
-/
lemma card_replacement (M : Finset (Finset V)) (A F₁ : Finset V)
    (hA : A ∈ M) (hF_not_M : F₁ ∉ M) :
    (insert F₁ (M.erase A)).card = M.card := by
  have : F₁ ∉ M.erase A := fun h => hF_not_M (mem_of_mem_erase h)
  rw [card_insert_of_not_mem this, card_erase_of_mem hA]; omega

/-- A is not in the replacement packing -/
lemma not_mem_replacement (M : Finset (Finset V)) (A F₁ : Finset V)
    (hF_ne_A : F₁ ≠ A) :
    A ∉ insert F₁ (M.erase A) := by
  rw [mem_insert, not_or]
  exact ⟨hF_ne_A.symm, not_mem_erase A M⟩

-- ═══════════════════════════════════════════════════════════════════════
-- KEY LEMMA 3: If external conflicts with C, then u ∈ C
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
F₁ = {a1,a2,u}. If |F₁ ∩ C| ≥ 2 and |A ∩ C| ≤ 1:
Since a1,a2 ∈ A, at most 1 of {a1,a2} is in C.
If u ∉ C: F₁ ∩ C ⊆ {a1,a2} ∩ C ⊆ A ∩ C, so |F₁ ∩ C| ≤ 1. Contradiction.
Therefore u ∈ C.
-/
theorem bridge_external_vertex_in_target
    (A C F₁ : Finset V) (v1 a1 a2 u : V)
    (hA_eq : A = {v1, a1, a2})
    (hF_eq : F₁ = {a1, a2, u})
    (hAC : (A ∩ C).card ≤ 1)
    (hFC : 2 ≤ (F₁ ∩ C).card) :
    u ∈ C := by
  by_contra hu
  -- If u ∉ C: every element of F₁ ∩ C is in A
  have hsub : F₁ ∩ C ⊆ A ∩ C := by
    intro x hx
    rw [mem_inter] at hx ⊢
    constructor
    · rw [hF_eq] at hx
      rw [hA_eq]
      rcases mem_triple hx.1 with rfl | rfl | rfl
      · exact mem_insert_of_mem _ (mem_insert_self a1 {a2})
      · exact mem_insert_of_mem _ (mem_insert_of_mem a1 (mem_singleton.mpr rfl))
      · exact absurd hx.2 hu
    · exact hx.2
  linarith [card_le_card hsub]

-- ═══════════════════════════════════════════════════════════════════════
-- KEY LEMMA 4: Complete dichotomy — replace or it's a bridge
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
For any base-edge external F₁ = {a1,a2,u} with A ∩ B = {v1}:
- |F₁ ∩ B| ≤ 1 always (base_external_disjoint_from_adjacent)
- Either |F₁ ∩ C| ≤ 1 ∧ |F₁ ∩ D| ≤ 1 (replacement works)
  or |F₁ ∩ C| ≥ 2 ∨ |F₁ ∩ D| ≥ 2 (it's a bridge, and u ∈ C or u ∈ D)
-/
theorem external_replace_or_bridge
    (A B : Finset V) (v1 a1 a2 u : V)
    (F₁ : Finset V) (hF_eq : F₁ = {a1, a2, u})
    (C D : Finset V)
    (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2)
    (hAB : A ∩ B = {v1}) :
    -- Either F₁ is edge-disjoint from all of B, C, D
    ((F₁ ∩ B).card ≤ 1 ∧ (F₁ ∩ C).card ≤ 1 ∧ (F₁ ∩ D).card ≤ 1)
    -- Or F₁ shares an edge with C or D (is a bridge)
    ∨ (2 ≤ (F₁ ∩ C).card ∨ 2 ≤ (F₁ ∩ D).card) := by
  have hFB := base_external_disjoint_from_adjacent A B v1 a1 a2 u
    F₁ hF_eq hA_eq h12 h13 hAB
  by_cases hC : (F₁ ∩ C).card ≤ 1
  · by_cases hD : (F₁ ∩ D).card ≤ 1
    · left; exact ⟨hFB, hC, hD⟩
    · right; right; omega
  · right; left; omega

-- ═══════════════════════════════════════════════════════════════════════
-- MAIN APPLICATION: Endpoint replacement in PATH_4
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
Combines the above: if endpoint A has a base-edge external F₁
that doesn't conflict with any other packing element (the "replace" case
of external_replace_or_bridge), then:
1. replacement_packing gives M' is a valid packing
2. card_replacement gives |M'| = |M| = 4
3. F₁ ∈ M' and A ∉ M'

This is the clean version taking edge-disjointness as a direct hypothesis,
which is discharged by external_replace_or_bridge at the call site.
-/
theorem endpoint_replacement_clean (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A F₁ : Finset V)
    (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hA : A ∈ M)
    (hF_clique : F₁ ∈ G.cliqueFinset 3)
    (hF_not_M : F₁ ∉ M)
    (hF_ne_A : F₁ ≠ A)
    -- F₁ is edge-disjoint from every element of M except A
    (hF_disj : ∀ T ∈ M, T ≠ A → (F₁ ∩ T).card ≤ 1) :
    let M' := insert F₁ (M.erase A)
    isTrianglePacking G M' ∧ M'.card = 4 ∧ F₁ ∈ M' ∧ A ∉ M' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact replacement_packing G M A F₁ hM hA hF_clique hF_not_M hF_disj
  · exact (card_replacement M A F₁ hA hF_not_M).trans hM_card
  · exact mem_insert_self F₁ (M.erase A)
  · exact not_mem_replacement M A F₁ hF_ne_A

-- ═══════════════════════════════════════════════════════════════════════
-- F₁ SHARES BASE EDGE WITH A (confirming it's a real base-edge external)
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
{a1, a2} ⊆ F₁ ∩ A since a1,a2 are in both F₁ and A.
So |F₁ ∩ A| ≥ 2.
-/
lemma base_external_shares_edge
    (A F₁ : Finset V) (v1 a1 a2 u : V) (h23 : a1 ≠ a2)
    (hA_eq : A = {v1, a1, a2})
    (hF_eq : F₁ = {a1, a2, u}) :
    2 ≤ (F₁ ∩ A).card := by
  have hsub : ({a1, a2} : Finset V) ⊆ F₁ ∩ A := by
    intro x hx
    rw [mem_inter, hF_eq, hA_eq]
    simp only [mem_insert, mem_singleton] at hx ⊢
    rcases hx with rfl | rfl
    · exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (mem_singleton.mpr rfl))⟩
  have hcard : ({a1, a2} : Finset V).card = 2 := by
    rw [card_insert_of_not_mem (by simpa using h23), card_singleton]
  linarith [card_le_card hsub]

-- ═══════════════════════════════════════════════════════════════════════
-- BRIDGE CASE: u ∈ target ∧ exactly one base vertex in target
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
When F₁ = {a1,a2,u} conflicts with C (|F₁∩C| ≥ 2):
1. u ∈ C (by bridge_external_vertex_in_target)
2. Since |A∩C| ≤ 1, at most one of a1,a2 is in C
3. Since |F₁∩C| ≥ 2 and u ∈ C, exactly one of a1,a2 is in C
Result: u ∈ C ∧ (a1 ∈ C ∨ a2 ∈ C)
-/
theorem bridge_structure
    (A C F₁ : Finset V) (v1 a1 a2 u : V)
    (hA_eq : A = {v1, a1, a2})
    (hF_eq : F₁ = {a1, a2, u})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (hAC : (A ∩ C).card ≤ 1)
    (hFC : 2 ≤ (F₁ ∩ C).card) :
    u ∈ C ∧ (a1 ∈ C ∨ a2 ∈ C) := by
  have hu := bridge_external_vertex_in_target A C F₁ v1 a1 a2 u hA_eq hF_eq hAC hFC
  refine ⟨hu, ?_⟩
  -- Need at least one of a1, a2 in C (since |F₁∩C| ≥ 2 and only {a1,a2,u} available)
  by_contra h; push_neg at h
  -- If neither a1 nor a2 is in C: F₁ ∩ C ⊆ {u}
  have hsub : F₁ ∩ C ⊆ {u} := by
    intro x hx
    rw [mem_inter, hF_eq] at hx
    rcases mem_triple hx.1 with rfl | rfl | rfl
    · exact absurd hx.2 h.1
    · exact absurd hx.2 h.2
    · exact mem_singleton.mpr rfl
  linarith [card_le_card hsub, card_singleton u]

end
