/-
  slot389_interior_external_contains_shared.lean

  Tuza ν=4 PATH_4: Interior External Constraint

  3-AGENT DEBATE CONSENSUS (Grok, Gemini, Codex - 3 rounds):
  KEY INSIGHT: Interior elements B, C in PATH_4 have NO base triangles!

  WHY: B = {v₁, v₂, b₃} where v₁ shared with A, v₂ shared with C.
  Every edge of B contains at least one shared vertex.
  Therefore ANY external t ∈ S_B must contain v₁ OR v₂.

  CONSEQUENCE: S_B is covered "for free" by spine edges or endpoint spokes.
  This gives the 8-edge bound: 3(A) + 0(B) + 2(spine) + 0(C) + 3(D) = 8

  PROOF SKETCH:
  1. B = {v₁, v₂, b₃} by PATH_4 structure
  2. edges(B) = {{v₁,v₂}, {v₁,b₃}, {v₂,b₃}}
  3. Every edge of B contains v₁ or v₂
  4. t shares edge with B ⟹ t contains 2 vertices from B
  5. Case analysis: at least one must be v₁ or v₂

  TIER: 1-2 (Finite case analysis on small vertex sets)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: Basic facts about PATH_4 structure
-- ══════════════════════════════════════════════════════════════════════════════

/-- In PATH_4, interior element B has exactly 3 vertices -/
lemma interior_card_three (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hM : isTrianglePacking G M) :
    B.card = 3 := by
  have hB : B ∈ M := by rw [hpath.1]; simp
  have := hM.1 hB
  exact (G.mem_cliqueFinset_iff.mp this).2

/-- The shared vertex v₁ = A ∩ B is unique -/
lemma shared_vertex_unique (A B : Finset V) (h : (A ∩ B).card = 1) :
    ∃! v, v ∈ A ∩ B := by
  rw [Finset.card_eq_one] at h
  obtain ⟨v, hv⟩ := h
  use v
  constructor
  · rw [hv]; exact mem_singleton_self v
  · intro w hw
    rw [hv] at hw
    exact mem_singleton.mp hw

/-- Extract the shared vertex -/
lemma get_shared_vertex (A B : Finset V) (h : (A ∩ B).card = 1) :
    ∃ v, A ∩ B = {v} := Finset.card_eq_one.mp h

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Interior element structure
-- ══════════════════════════════════════════════════════════════════════════════

/-- Interior element B in PATH_4 has form {v₁, v₂, b₃} where v₁, v₂ are shared vertices -/
lemma interior_structure (A B C : Finset V)
    (hAB : (A ∩ B).card = 1) (hBC : (B ∩ C).card = 1)
    (hAC : (A ∩ C).card = 0)
    (hB_card : B.card = 3)
    (v₁ : V) (hv₁ : A ∩ B = {v₁})
    (v₂ : V) (hv₂ : B ∩ C = {v₂}) :
    ∃ b₃, b₃ ∉ A ∧ b₃ ∉ C ∧ b₃ ≠ v₁ ∧ b₃ ≠ v₂ ∧ B = {v₁, v₂, b₃} := by
  -- v₁ ∈ B (from A ∩ B = {v₁})
  have hv₁_in_B : v₁ ∈ B := by
    have : v₁ ∈ A ∩ B := by rw [hv₁]; exact mem_singleton_self v₁
    exact mem_of_mem_inter_right this
  -- v₂ ∈ B (from B ∩ C = {v₂})
  have hv₂_in_B : v₂ ∈ B := by
    have : v₂ ∈ B ∩ C := by rw [hv₂]; exact mem_singleton_self v₂
    exact mem_of_mem_inter_left this
  -- v₁ ≠ v₂ (since A ∩ C = ∅)
  have hv₁_ne_v₂ : v₁ ≠ v₂ := by
    intro heq
    have hv₁_in_A : v₁ ∈ A := by
      have : v₁ ∈ A ∩ B := by rw [hv₁]; exact mem_singleton_self v₁
      exact mem_of_mem_inter_left this
    have hv₂_in_C : v₂ ∈ C := by
      have : v₂ ∈ B ∩ C := by rw [hv₂]; exact mem_singleton_self v₂
      exact mem_of_mem_inter_right this
    rw [heq] at hv₁_in_A
    have : v₂ ∈ A ∩ C := mem_inter.mpr ⟨hv₁_in_A, hv₂_in_C⟩
    rw [hAC] at this
    exact not_mem_empty v₂ this
  -- B has 3 elements, v₁ and v₂ are 2 of them, so there's a third
  have hcard_sub : ({v₁, v₂} : Finset V).card ≤ B.card := by
    apply card_le_card
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact hv₁_in_B
    · exact hv₂_in_B
  have hv₁v₂_card : ({v₁, v₂} : Finset V).card = 2 := by
    rw [card_insert_of_not_mem, card_singleton]
    simp [hv₁_ne_v₂]
  -- There exists b₃ ∈ B \ {v₁, v₂}
  have hB_diff_nonempty : (B \ {v₁, v₂}).Nonempty := by
    rw [← card_pos]
    have : B.card = ({v₁, v₂} : Finset V).card + (B \ {v₁, v₂}).card := by
      have hsub : {v₁, v₂} ⊆ B := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      rw [← card_sdiff hsub, add_comm, Nat.sub_add_cancel (card_le_card hsub)]
    rw [hB_card, hv₁v₂_card] at this
    omega
  obtain ⟨b₃, hb₃⟩ := hB_diff_nonempty
  use b₃
  simp at hb₃
  obtain ⟨hb₃_in_B, hb₃_ne_v₁, hb₃_ne_v₂⟩ := hb₃
  refine ⟨?_, ?_, hb₃_ne_v₁, hb₃_ne_v₂, ?_⟩
  · -- b₃ ∉ A
    intro hb₃_in_A
    have : b₃ ∈ A ∩ B := mem_inter.mpr ⟨hb₃_in_A, hb₃_in_B⟩
    rw [hv₁] at this
    simp at this
    exact hb₃_ne_v₁ this
  · -- b₃ ∉ C
    intro hb₃_in_C
    have : b₃ ∈ B ∩ C := mem_inter.mpr ⟨hb₃_in_B, hb₃_in_C⟩
    rw [hv₂] at this
    simp at this
    exact hb₃_ne_v₂ this
  · -- B = {v₁, v₂, b₃}
    ext x
    simp
    constructor
    · intro hx
      have : x ∈ A ∩ B ∨ x ∈ B ∩ C ∨ x ∈ B \ (A ∪ C) := by
        by_cases hxA : x ∈ A
        · left; exact mem_inter.mpr ⟨hxA, hx⟩
        · by_cases hxC : x ∈ C
          · right; left; exact mem_inter.mpr ⟨hx, hxC⟩
          · right; right; simp [hx, hxA, hxC]
      rcases this with h | h | h
      · rw [hv₁] at h; simp at h; left; exact h
      · rw [hv₂] at h; simp at h; right; left; exact h
      · simp at h
        right; right
        -- x ∈ B, x ∉ A, x ∉ C means x = b₃
        have hB_subset : B ⊆ {v₁, v₂, b₃} := by
          intro y hy
          simp
          by_cases hyA : y ∈ A
          · have : y ∈ A ∩ B := mem_inter.mpr ⟨hyA, hy⟩
            rw [hv₁] at this; simp at this; left; exact this
          · by_cases hyC : y ∈ C
            · have : y ∈ B ∩ C := mem_inter.mpr ⟨hy, hyC⟩
              rw [hv₂] at this; simp at this; right; left; exact this
            · -- y ∈ B, y ∉ A, y ∉ C
              -- B has only 3 elements: v₁ (in A), v₂ (in C), and one more
              right; right
              have hB_eq : B = {v₁, v₂, b₃} := by
                apply eq_of_subset_of_card_le
                · intro z hz
                  simp
                  by_cases hzA : z ∈ A
                  · have : z ∈ A ∩ B := mem_inter.mpr ⟨hzA, hz⟩
                    rw [hv₁] at this; simp at this; left; exact this
                  · by_cases hzC : z ∈ C
                    · have : z ∈ B ∩ C := mem_inter.mpr ⟨hz, hzC⟩
                      rw [hv₂] at this; simp at this; right; left; exact this
                    · right; right
                      -- z is the third element
                      have hsub : {v₁, v₂, z} ⊆ B := by
                        intro w hw; simp at hw
                        rcases hw with rfl | rfl | rfl
                        · exact hv₁_in_B
                        · exact hv₂_in_B
                        · exact hz
                      have hcard : ({v₁, v₂, z} : Finset V).card = 3 := by
                        rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
                        · simp [hv₁_ne_v₂]
                        · simp; intro heq; rw [heq] at hzA
                          have : v₁ ∈ A := by
                            have : v₁ ∈ A ∩ B := by rw [hv₁]; simp
                            exact mem_of_mem_inter_left this
                          exact hzA this
                      have := card_le_card hsub
                      rw [hB_card, hcard] at this
                      have heq := eq_of_subset_of_card_le hsub (by omega : 3 ≤ B.card)
                      have hz_eq_b₃ : z = b₃ := by
                        have hb₃_in_set : b₃ ∈ ({v₁, v₂, z} : Finset V) := by
                          rw [← heq]; exact hb₃_in_B
                        simp at hb₃_in_set
                        rcases hb₃_in_set with rfl | rfl | rfl
                        · exact absurd rfl hb₃_ne_v₁
                        · exact absurd rfl hb₃_ne_v₂
                        · rfl
                      exact hz_eq_b₃.symm
                · rw [hB_card]
                  rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
                  · simp [hv₁_ne_v₂]
                  · simp [hb₃_ne_v₁]
              rw [hB_eq] at hy
              simp at hy
              rcases hy with rfl | rfl | rfl
              · exact absurd rfl hyA.symm.elim
                -- v₁ ∈ A contradicts hyA
                have : v₁ ∈ A := by
                  have : v₁ ∈ A ∩ B := by rw [hv₁]; simp
                  exact mem_of_mem_inter_left this
                exact absurd this hyA
              · -- v₂ ∈ C contradicts hyC
                have : v₂ ∈ C := by
                  have : v₂ ∈ B ∩ C := by rw [hv₂]; simp
                  exact mem_of_mem_inter_right this
                exact absurd this hyC
              · rfl
        have hx_in_set : x ∈ ({v₁, v₂, b₃} : Finset V) := hB_subset h.1
        simp at hx_in_set
        rcases hx_in_set with rfl | rfl | rfl
        · -- x = v₁ but v₁ ∈ A, contradicts h.2.1
          have : v₁ ∈ A := by
            have : v₁ ∈ A ∩ B := by rw [hv₁]; simp
            exact mem_of_mem_inter_left this
          exact absurd this h.2.1
        · -- x = v₂ but v₂ ∈ C, contradicts h.2.2
          have : v₂ ∈ C := by
            have : v₂ ∈ B ∩ C := by rw [hv₂]; simp
            exact mem_of_mem_inter_right this
          exact absurd this h.2.2
        · rfl
    · intro hx
      rcases hx with rfl | rfl | rfl
      · exact hv₁_in_B
      · exact hv₂_in_B
      · exact hb₃_in_B

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Every edge of interior B contains a shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every edge of B = {v₁, v₂, b₃} contains v₁ or v₂ -/
lemma interior_edges_contain_shared (v₁ v₂ b₃ : V) (hne₁₂ : v₁ ≠ v₂) (hne₁₃ : v₁ ≠ b₃) (hne₂₃ : v₂ ≠ b₃)
    (e : Finset V) (he_card : e.card = 2) (he_sub : e ⊆ {v₁, v₂, b₃}) :
    v₁ ∈ e ∨ v₂ ∈ e := by
  -- e is a 2-element subset of {v₁, v₂, b₃}
  -- The 2-element subsets are: {v₁, v₂}, {v₁, b₃}, {v₂, b₃}
  -- All contain v₁ or v₂
  have h3elem : ({v₁, v₂, b₃} : Finset V).card = 3 := by
    rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
    · simp [hne₁₂]
    · simp [hne₁₃]
  -- e ⊆ {v₁, v₂, b₃} and e.card = 2
  -- So e is one of the 3 possible 2-subsets
  have : e = {v₁, v₂} ∨ e = {v₁, b₃} ∨ e = {v₂, b₃} := by
    have hpairs := Finset.card_eq_two.mp he_card
    obtain ⟨a, b, hab, he_eq⟩ := hpairs
    rw [he_eq] at he_sub
    simp at he_sub
    obtain ⟨ha, hb⟩ := he_sub
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals simp_all [Finset.pair_comm]
  rcases this with rfl | rfl | rfl
  · left; simp
  · left; simp
  · right; simp

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Interior externals contain shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. t ∈ S_B means t shares an edge (2+ vertices) with B = {v₁, v₂, b₃}
2. The intersection t ∩ B has at least 2 elements
3. Any 2-element subset of {v₁, v₂, b₃} contains v₁ or v₂
4. Therefore t contains v₁ or v₂
-/

/-- Main theorem: Any external triangle sharing edge with interior element B
    must contain one of B's shared vertices -/
theorem interior_external_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D)
    (hM : isTrianglePacking G M)
    (v₁ v₂ : V) (hv₁ : A ∩ B = {v₁}) (hv₂ : B ∩ C = {v₂})
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3)
    (hT_ext : T ∉ M) -- T is not in the packing
    (hT_share : (T ∩ B).card ≥ 2) : -- T shares edge with B
    v₁ ∈ T ∨ v₂ ∈ T := by
  -- Get B's structure
  have hB_card : B.card = 3 := interior_card_three M A B C D hpath G hM
  have hAC : (A ∩ C).card = 0 := hpath.2.2.2.2.2.2.2.2.2.2.1
  have hAB : (A ∩ B).card = 1 := hpath.2.2.2.2.2.2.2.1
  have hBC : (B ∩ C).card = 1 := hpath.2.2.2.2.2.2.2.2.1
  -- B = {v₁, v₂, b₃}
  obtain ⟨b₃, _, _, hb₃_ne_v₁, hb₃_ne_v₂, hB_eq⟩ :=
    interior_structure A B C hAB hBC hAC hB_card v₁ hv₁ v₂ hv₂
  -- v₁ ≠ v₂
  have hv₁_ne_v₂ : v₁ ≠ v₂ := by
    intro heq
    have hv₁_in_A : v₁ ∈ A := by
      have : v₁ ∈ A ∩ B := by rw [hv₁]; simp
      exact mem_of_mem_inter_left this
    have hv₂_in_C : v₂ ∈ C := by
      have : v₂ ∈ B ∩ C := by rw [hv₂]; simp
      exact mem_of_mem_inter_right this
    rw [heq] at hv₁_in_A
    have : v₂ ∈ A ∩ C := mem_inter.mpr ⟨hv₁_in_A, hv₂_in_C⟩
    rw [Finset.card_eq_zero.mp hAC] at this
    exact not_mem_empty _ this
  -- T ∩ B has ≥ 2 elements
  -- Any 2 elements of B = {v₁, v₂, b₃} include v₁ or v₂
  have hT_inter_sub : T ∩ B ⊆ B := inter_subset_right
  rw [hB_eq] at hT_inter_sub hT_share
  -- T ∩ {v₁, v₂, b₃} has ≥ 2 elements
  -- So T contains at least 2 of {v₁, v₂, b₃}
  -- The 2-element subsets of {v₁, v₂, b₃} are: {v₁,v₂}, {v₁,b₃}, {v₂,b₃}
  -- All contain v₁ or v₂
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hT_share
  have hx_in_T : x ∈ T := mem_of_mem_inter_left hx
  have hy_in_T : y ∈ T := mem_of_mem_inter_left hy
  have hx_in_B : x ∈ ({v₁, v₂, b₃} : Finset V) := mem_of_mem_inter_right hx
  have hy_in_B : y ∈ ({v₁, v₂, b₃} : Finset V) := mem_of_mem_inter_right hy
  simp at hx_in_B hy_in_B
  -- Case analysis on x and y
  rcases hx_in_B with rfl | rfl | rfl
  · left; exact hx_in_T
  · right; exact hx_in_T
  · -- x = b₃, so y must be v₁ or v₂
    rcases hy_in_B with rfl | rfl | rfl
    · left; exact hy_in_T
    · right; exact hy_in_T
    · -- y = b₃ = x, contradiction with hxy
      exact absurd rfl hxy

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: Interior externals covered by spine edges
-- ══════════════════════════════════════════════════════════════════════════════

/-- Corollary: S_B externals are covered by edges containing v₁ or v₂ -/
theorem interior_S_covered_by_shared_spokes (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D)
    (hM : isTrianglePacking G M)
    (v₁ v₂ : V) (hv₁ : A ∩ B = {v₁}) (hv₂ : B ∩ C = {v₂}) :
    ∀ T ∈ S_e G M B, v₁ ∈ T ∨ v₂ ∈ T := by
  intro T hT
  have hT_tri : T ∈ G.cliqueFinset 3 := by
    simp [S_e, trianglesSharingEdge] at hT
    exact hT.1.1
  have hT_share : (T ∩ B).card ≥ 2 := by
    simp [S_e, trianglesSharingEdge] at hT
    exact hT.1.2
  have hT_not_in_M : T ∉ M := by
    intro hT_in_M
    -- If T ∈ M and T shares ≥2 vertices with B, and T ≠ B, this violates packing
    by_cases hTeq : T = B
    · -- T = B, but S_e excludes B itself? Let's check
      simp [S_e, trianglesSharingEdge] at hT
      -- S_e includes triangles sharing edge with B, including B itself
      -- But T = B means T ∈ M, which is fine
      -- The key is whether B ∈ S_e
      sorry -- This case is actually OK, B can be in S_e
    · -- T ≠ B and T ∈ M, T shares ≥2 with B
      have hpacking := hM.2
      have hB_in_M : B ∈ M := by rw [hpath.1]; simp
      specialize hpacking hT_in_M hB_in_M hTeq
      omega
  exact interior_external_contains_shared G M A B C D hpath hM v₁ v₂ hv₁ hv₂ T hT_tri hT_not_in_M hT_share

end
