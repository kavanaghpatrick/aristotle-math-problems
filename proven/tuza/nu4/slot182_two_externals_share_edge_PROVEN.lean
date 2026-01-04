/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8edeae11-cabe-4e10-bd0f-2cfd87c88f7f
-/

/-
Tuza ν=4 Strategy - Slot 182: Two Externals Share Edge (COMPLETE PROOF)

ANTI-TYPE-ESCAPE VERSION (Jan 2, 2026):
  This version adds explicit ν=4 hypothesis and completes the proof locally.
  NO SORRY for Aristotle to fill = NO opportunity for type-escape tricks.

KEY CHANGE from slot181:
  Added: hν : ∀ P, isTrianglePacking G P → P.card ≤ 4
  This explicitly states the packing number is 4, making the contradiction
  structural (5 ≤ 4 is false by omega) rather than semantic.

MULTI-AGENT VERIFIED (Jan 2, 2026):
  Grok: Scaffolding lemmas SOUND, definition correct
  Gemini: 5-packing construction VALID, no false patterns
  Codex: Theorem TRUE, gap was local→global maximality (now fixed)

KEY THEOREM: two_externals_share_edge
  If T₁, T₂ are distinct externals of M-element A, they share an edge.

PROOF STRATEGY (5-packing contradiction):
  1. Assume T₁, T₂ share no edge (edge-disjoint)
  2. Construct M' = {T₁, T₂} ∪ (M \ {A}) = {T₁, T₂, B, C, D}
  3. Verify M' is a valid 5-element packing
  4. |M'| = 5 but hν says all packings have ≤ 4 elements
  5. Contradiction: 5 ≤ 4 is false (omega)
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (standard)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

/-- Two vertex sets share an edge: ∃ distinct u,v in both sets -/
def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

/-- External triangle: in G's cliques, not in M, shares edge with A only -/
def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: Edge-sharing implies intersection ≥ 2
-- ══════════════════════════════════════════════════════════════════════════════

/-- If two triangles share an edge (u,v with u≠v), their intersection has ≥2 elements -/
lemma shares_edge_implies_two_vertices (t m : Finset V)
    (ht : t.card = 3) (hm : m.card = 3) (h_share : sharesEdgeWith t m) :
    (t ∩ m).card ≥ 2 := by
  obtain ⟨u, v, huv, hu_t, hv_t, hu_m, hv_m⟩ := h_share
  have hu_inter : u ∈ t ∩ m := Finset.mem_inter.mpr ⟨hu_t, hu_m⟩
  have hv_inter : v ∈ t ∩ m := Finset.mem_inter.mpr ⟨hv_t, hv_m⟩
  exact Finset.one_lt_card.mpr ⟨u, hu_inter, v, hv_inter, huv⟩

/-- If triangles don't share edge, intersection ≤ 1 (contrapositive) -/
lemma not_share_implies_one_vertex (t m : Finset V)
    (ht : t.card = 3) (hm : m.card = 3) (h_not_share : ¬sharesEdgeWith t m) :
    (t ∩ m).card ≤ 1 := by
  by_contra h
  push_neg at h
  have h2 : (t ∩ m).card ≥ 2 := h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
  have hu_t : u ∈ t := (Finset.mem_inter.mp hu).1
  have hu_m : u ∈ m := (Finset.mem_inter.mp hu).2
  have hv_t : v ∈ t := (Finset.mem_inter.mp hv).1
  have hv_m : v ∈ m := (Finset.mem_inter.mp hv).2
  exact h_not_share ⟨u, v, huv, hu_t, hv_t, hu_m, hv_m⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: External intersects other M-elements in ≤1 vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- External of A doesn't share edge with other M-elements → intersection ≤ 1 -/
lemma external_intersects_other_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (t : Finset V) (ht_ext : isExternalOf G M A t) :
    (t ∩ B).card ≤ 1 := by
  have ht_3 : t.card = 3 := by
    have : t ∈ G.cliqueFinset 3 := ht_ext.1
    exact SimpleGraph.mem_cliqueFinset_iff.mp this |>.2
  have hB_3 : B.card = 3 := by
    have : B ∈ G.cliqueFinset 3 := hM.1.1 hB
    exact SimpleGraph.mem_cliqueFinset_iff.mp this |>.2
  have h_not_share : ¬sharesEdgeWith t B := ht_ext.2.2.2 B hB hAB.symm
  exact not_share_implies_one_vertex t B ht_3 hB_3 h_not_share

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: Edge-disjoint triangles intersect in ≤1 vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- Key: If no shared edge, triangles intersect in at most 1 vertex -/
lemma edge_disjoint_implies_one_vertex (T₁ T₂ : Finset V)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False) :
    (T₁ ∩ T₂).card ≤ 1 := by
  have h_not_share : ¬sharesEdgeWith T₁ T₂ := by
    intro ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩
    exact h_edge_disj u v huv hu₁ hv₁ hu₂ hv₂
  exact not_share_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_not_share

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 5-packing from edge-disjoint externals
-- ══════════════════════════════════════════════════════════════════════════════

/-- If T₁, T₂ are edge-disjoint externals of A, then {T₁, T₂, B, C, D} is a 5-packing -/
theorem five_packing_from_disjoint_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_ne_T₂ : T₁ ≠ T₂)
    (h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False) :
    ∃ M' : Finset (Finset V), M'.card = 5 ∧ isTrianglePacking G M' := by
  -- Construct M' = {T₁, T₂} ∪ (M \ {A})
  let M_minus_A := M.erase A
  let M' := {T₁, T₂} ∪ M_minus_A
  use M'

  -- Get card facts
  have hT₁_not_M : T₁ ∉ M := hT₁.2.1
  have hT₂_not_M : T₂ ∉ M := hT₂.2.1
  have hM_minus_A_card : M_minus_A.card = 3 := by
    rw [Finset.card_erase_of_mem hA]
    omega

  constructor
  -- Part 1: |M'| = 5
  · have hT₁_not_MA : T₁ ∉ M_minus_A := fun h => hT₁_not_M (Finset.mem_erase.mp h).2
    have hT₂_not_MA : T₂ ∉ M_minus_A := fun h => hT₂_not_M (Finset.mem_erase.mp h).2
    have h_pair_card : ({T₁, T₂} : Finset (Finset V)).card = 2 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
      simp [hT₁_ne_T₂]
    have h_disj : Disjoint {T₁, T₂} M_minus_A := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · intro heq; exact hT₁_not_MA (heq ▸ hy)
      · intro heq; exact hT₂_not_MA (heq ▸ hy)
    rw [Finset.card_union_of_disjoint h_disj, h_pair_card, hM_minus_A_card]

  -- Part 2: M' is a triangle packing
  · constructor
    -- Part 2a: All elements are triangles (in G.cliqueFinset 3)
    · intro t ht
      have ht' := Finset.mem_union.mp ht
      rcases ht' with ht_pair | ht_MA
      · rcases Finset.mem_insert.mp ht_pair with rfl | ht_sing
        · exact hT₁.1
        · rw [Finset.mem_singleton] at ht_sing
          rw [ht_sing]; exact hT₂.1
      · exact hM.1.1 (Finset.mem_erase.mp ht_MA).2

    -- Part 2b: Pairwise intersection ≤ 1
    · intro t₁ ht₁ t₂ ht₂ h_ne
      have hT₁_3 : T₁.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₁.1 |>.2
      have hT₂_3 : T₂.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp hT₂.1 |>.2
      have ht₁' := Finset.mem_union.mp ht₁
      have ht₂' := Finset.mem_union.mp ht₂
      rcases ht₁' with ht₁_pair | ht₁_MA <;> rcases ht₂' with ht₂_pair | ht₂_MA
      -- Case 1: both in {T₁, T₂}
      · rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · exact absurd (heq₁.trans heq₂.symm) h_ne
          · rw [Finset.mem_singleton] at ht₂_sing
            rw [heq₁, ht₂_sing]
            exact edge_disjoint_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_edge_disj
        · rw [Finset.mem_singleton] at ht₁_sing
          rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
          · rw [ht₁_sing, heq₂]
            have h := edge_disjoint_implies_one_vertex T₁ T₂ hT₁_3 hT₂_3 h_edge_disj
            rw [Finset.inter_comm] at h; exact h
          · rw [Finset.mem_singleton] at ht₂_sing
            exact absurd (ht₁_sing.trans ht₂_sing.symm) h_ne
      -- Case 2: t₁ in {T₁, T₂}, t₂ in M\{A}
      · have hB_M : t₂ ∈ M := (Finset.mem_erase.mp ht₂_MA).2
        have hB_ne_A : t₂ ≠ A := (Finset.mem_erase.mp ht₂_MA).1
        rcases Finset.mem_insert.mp ht₁_pair with heq₁ | ht₁_sing
        · rw [heq₁]
          exact external_intersects_other_le_1 G M hM A t₂ hA hB_M hB_ne_A.symm T₁ hT₁
        · rw [Finset.mem_singleton] at ht₁_sing; rw [ht₁_sing]
          exact external_intersects_other_le_1 G M hM A t₂ hA hB_M hB_ne_A.symm T₂ hT₂
      -- Case 3: t₁ in M\{A}, t₂ in {T₁, T₂}
      · have hB_M : t₁ ∈ M := (Finset.mem_erase.mp ht₁_MA).2
        have hB_ne_A : t₁ ≠ A := (Finset.mem_erase.mp ht₁_MA).1
        rcases Finset.mem_insert.mp ht₂_pair with heq₂ | ht₂_sing
        · rw [heq₂]
          have h := external_intersects_other_le_1 G M hM A t₁ hA hB_M hB_ne_A.symm T₁ hT₁
          rw [Finset.inter_comm] at h; exact h
        · rw [Finset.mem_singleton] at ht₂_sing; rw [ht₂_sing]
          have h := external_intersects_other_le_1 G M hM A t₁ hA hB_M hB_ne_A.symm T₂ hT₂
          rw [Finset.inter_comm] at h; exact h
      -- Case 4: both in M\{A} - M is packing
      · have ht₁_M : t₁ ∈ M := (Finset.mem_erase.mp ht₁_MA).2
        have ht₂_M : t₂ ∈ M := (Finset.mem_erase.mp ht₂_MA).2
        exact hM.1.2 ht₁_M ht₂_M h_ne

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Two externals share an edge (COMPLETE - no sorry)
-- ══════════════════════════════════════════════════════════════════════════════

/-- KEY: Two distinct externals of same M-element must share an edge.
    Otherwise {T₁, T₂} ∪ (M \ {A}) would be a 5-packing, contradicting ν = 4.

    NOTE: This version has explicit ν=4 hypothesis to ensure structural proof.
    The contradiction is purely arithmetic: 5 ≤ 4 is false.
    NO type-escape possible because omega doesn't use decidability on V. -/
theorem two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    -- EXPLICIT ν=4 HYPOTHESIS: Prevents need for local→global maximality lemma
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  by_contra h_no_edge
  -- If they don't share an edge, they're edge-disjoint
  have h_edge_disj : ∀ u v, u ≠ v → u ∈ T₁ → v ∈ T₁ → u ∈ T₂ → v ∈ T₂ → False := by
    intro u v huv hu₁ hv₁ hu₂ hv₂
    exact h_no_edge ⟨u, v, huv, hu₁, hv₁, hu₂, hv₂⟩
  -- Construct the 5-packing
  obtain ⟨M', hM'_card, hM'_packing⟩ := five_packing_from_disjoint_externals
    G M hM hM_card A hA T₁ T₂ hT₁ hT₂ h_ne h_edge_disj
  -- M' is a 5-packing, but hν says all packings have ≤ 4 elements
  -- Structural contradiction: 5 ≤ 4 is false
  have h_bound : M'.card ≤ 4 := hν M' hM'_packing
  -- hM'_card : M'.card = 5
  -- h_bound : M'.card ≤ 4
  -- Contradiction: 5 ≤ 4
  omega

end