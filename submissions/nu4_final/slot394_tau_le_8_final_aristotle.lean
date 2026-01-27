/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b3e3a220-760b-4220-83df-7c9c28ab9092
-/

/-
  slot394_tau_le_8_final.lean

  Tuza ν=4 PATH_4: Final τ ≤ 8 Theorem

  PROVEN BUILDING BLOCKS:
  - slot390: ∀ T ∈ S_B, v₁ ∈ T ∨ v₂ ∈ T (B interior externals contain shared vertex)
  - slot392: ∀ T ∈ S_C, v₂ ∈ T ∨ v₃ ∈ T (C interior externals contain shared vertex)
  - slot393: ∀ T ∈ S_A, T contains an edge of A (endpoint externals contain edge)

  8-EDGE COVER CONSTRUCTION:
  ┌─────────────────────────────────────────────────────────────────────────┐
  │  E = edges(A) ∪ {v₁v₂, v₂v₃} ∪ edges(D)                                 │
  │      = 3 + 2 + 3 = 8 edges                                              │
  │                                                                         │
  │  Covers:                                                                │
  │  • A, D: by their own edges                                             │
  │  • B, C: by spine edges {v₁v₂} ⊂ B, {v₂v₃} ⊂ C                          │
  │  • S_A, S_D: by edges of A, D (from slot393)                            │
  │  • S_B: externals contain v₁ or v₂ → covered by edges incident to v₁,v₂ │
  │  • S_C: externals contain v₂ or v₃ → covered by edges incident to v₂,v₃ │
  └─────────────────────────────────────────────────────────────────────────┘

  KEY INSIGHT (from 3-agent debate):
  Interior elements B, C contribute 0 EXTRA edges because:
  - Their externals (S_B, S_C) are covered by edges already in the cover
  - spine edges hit all triangles containing both shared vertices
  - A-spokes hit S_B triangles containing v₁
  - D-spokes hit S_C triangles containing v₃

  TIER: 2 (Assembly of Tier 1 results)
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

-- Edge cover definition: set of edges that hits every triangle
def isEdgeCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) : Prop :=
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, ∃ u v : V, e = s(u, v) ∧ u ∈ T ∧ v ∈ T

-- Triangle cover number
def tau (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { n | ∃ E : Finset (Sym2 V), E.card = n ∧ isEdgeCover G E }

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: Extract vertices from PATH_4 structure
-- ══════════════════════════════════════════════════════════════════════════════

/-- Extract the shared vertex v₁ between A and B -/
lemma path4_shared_v1 (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D) :
    ∃ v₁ : V, A ∩ B = {v₁} := by
  have h : (A ∩ B).card = 1 := hpath.2.2.2.2.2.2.2.1
  exact card_eq_one.mp h

/-- Extract the shared vertex v₂ between B and C -/
lemma path4_shared_v2 (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D) :
    ∃ v₂ : V, B ∩ C = {v₂} := by
  have h : (B ∩ C).card = 1 := hpath.2.2.2.2.2.2.2.2.1
  exact card_eq_one.mp h

/-- Extract the shared vertex v₃ between C and D -/
lemma path4_shared_v3 (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D) :
    ∃ v₃ : V, C ∩ D = {v₃} := by
  have h : (C ∩ D).card = 1 := hpath.2.2.2.2.2.2.2.2.2.1
  exact card_eq_one.mp h

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN RESULTS (from slot390, slot392, slot393)
-- ══════════════════════════════════════════════════════════════════════════════

/-- slot390: Interior B externals contain v₁ or v₂ -/
theorem interior_B_external_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D)
    (hM : isTrianglePacking G M)
    (v₁ v₂ : V) (hv₁ : A ∩ B = {v₁}) (hv₂ : B ∩ C = {v₂}) :
    ∀ T ∈ S_e G M B, v₁ ∈ T ∨ v₂ ∈ T := by
  intro T hT
  by_cases hTeq : T = B
  · left
    rw [hTeq]
    have : v₁ ∈ A ∩ B := by rw [hv₁]; exact mem_singleton_self v₁
    exact mem_of_mem_inter_right this
  · have hT_tri : T ∈ G.cliqueFinset 3 := by
      simp only [S_e, trianglesSharingEdge, mem_filter] at hT
      exact hT.1.1
    have hT_share : (T ∩ B).card ≥ 2 := by
      simp only [S_e, trianglesSharingEdge, mem_filter] at hT
      exact hT.1.2
    have hT_not_in_M : T ∉ M := by
      intro hT_in_M
      have hpacking := hM.2
      have hB_in_M : B ∈ M := by rw [hpath.1]; simp
      specialize hpacking hT_in_M hB_in_M hTeq
      omega
    have hB_card : B.card = 3 := by
      have hB : B ∈ M := by rw [hpath.1]; simp
      exact (G.mem_cliqueFinset_iff.mp (hM.1 hB)).2
    have hBC : (B ∩ C).card = 1 := hpath.2.2.2.2.2.2.2.2.1
    have hAB : (A ∩ B).card = 1 := hpath.2.2.2.2.2.2.2.1
    have hBD : (B ∩ D).card = 0 := hpath.2.2.2.2.2.2.2.2.2.2.2
    -- B = {v₁, v₂, b₃} for some private vertex b₃
    have hv₁_in_B : v₁ ∈ B := by
      have : v₁ ∈ A ∩ B := by rw [hv₁]; exact mem_singleton_self v₁
      exact mem_of_mem_inter_right this
    have hv₂_in_B : v₂ ∈ B := by
      have : v₂ ∈ B ∩ C := by rw [hv₂]; exact mem_singleton_self v₂
      exact mem_of_mem_inter_left this
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
      have hAC : (A ∩ C).card = 0 := hpath.2.2.2.2.2.2.2.2.2.2.1
      rw [Finset.card_eq_zero.mp hAC] at this
      exact not_mem_empty _ this
    -- T shares edge with B, so T ∩ B has ≥ 2 elements from {v₁, v₂, b₃}
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hT_share
    have hx_in_T : x ∈ T := mem_of_mem_inter_left hx
    have hy_in_T : y ∈ T := mem_of_mem_inter_left hy
    have hx_in_B : x ∈ B := mem_of_mem_inter_right hx
    have hy_in_B : y ∈ B := mem_of_mem_inter_right hy
    -- x and y are distinct elements of B = {v₁, v₂, b₃}
    -- At least one of them must be v₁ or v₂
    by_cases hx_v1 : x = v₁
    · left; rw [← hx_v1]; exact hx_in_T
    · by_cases hx_v2 : x = v₂
      · right; rw [← hx_v2]; exact hx_in_T
      · -- x is the private vertex b₃
        by_cases hy_v1 : y = v₁
        · left; rw [← hy_v1]; exact hy_in_T
        · by_cases hy_v2 : y = v₂
          · right; rw [← hy_v2]; exact hy_in_T
          · -- Both x and y are b₃, contradiction since x ≠ y
            -- x ∈ B, x ≠ v₁, x ≠ v₂, y ∈ B, y ≠ v₁, y ≠ v₂
            -- B has only 3 elements, so x = y = b₃
            have hB_struct : ∃ b₃, b₃ ∉ A ∧ b₃ ∉ C ∧ b₃ ≠ v₁ ∧ b₃ ≠ v₂ ∧ B = {v₁, v₂, b₃} := by
              have hv₁v₂_card : ({v₁, v₂} : Finset V).card = 2 := by
                rw [card_insert_of_not_mem, card_singleton]
                simp [hv₁_ne_v₂]
              have hB_diff_nonempty : (B \ {v₁, v₂}).Nonempty := by
                rw [← card_pos]
                have : B.card = ({v₁, v₂} : Finset V).card + (B \ {v₁, v₂}).card := by
                  have hsub : {v₁, v₂} ⊆ B := by
                    intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
                  rw [← card_sdiff hsub, add_comm, Nat.sub_add_cancel (card_le_card hsub)]
                rw [hB_card, hv₁v₂_card] at this
                omega
              obtain ⟨b₃, hb₃⟩ := hB_diff_nonempty
              simp at hb₃
              obtain ⟨hb₃_in_B, hb₃_ne_v₁, hb₃_ne_v₂⟩ := hb₃
              use b₃
              refine ⟨?_, ?_, hb₃_ne_v₁, hb₃_ne_v₂, ?_⟩
              · intro hb₃_in_A
                have : b₃ ∈ A ∩ B := mem_inter.mpr ⟨hb₃_in_A, hb₃_in_B⟩
                rw [hv₁] at this; simp at this; exact hb₃_ne_v₁ this
              · intro hb₃_in_C
                have : b₃ ∈ B ∩ C := mem_inter.mpr ⟨hb₃_in_B, hb₃_in_C⟩
                rw [hv₂] at this; simp at this; exact hb₃_ne_v₂ this
              · ext z; simp
                constructor
                · intro hz
                  by_cases hzA : z ∈ A
                  · have : z ∈ A ∩ B := mem_inter.mpr ⟨hzA, hz⟩
                    rw [hv₁] at this; simp at this; left; exact this
                  · by_cases hzC : z ∈ C
                    · have : z ∈ B ∩ C := mem_inter.mpr ⟨hz, hzC⟩
                      rw [hv₂] at this; simp at this; right; left; exact this
                    · right; right
                      have hsub : {v₁, v₂, z} ⊆ B := by
                        intro w hw; simp at hw
                        rcases hw with rfl | rfl | rfl <;> [exact hv₁_in_B; exact hv₂_in_B; exact hz]
                      have hcard : ({v₁, v₂, z} : Finset V).card = 3 := by
                        rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
                        · simp [hv₁_ne_v₂]
                        · simp; intro heq; rw [heq] at hzA
                          have : v₁ ∈ A := by
                            have : v₁ ∈ A ∩ B := by rw [hv₁]; simp
                            exact mem_of_mem_inter_left this
                          exact hzA this
                      have heq := eq_of_subset_of_card_le hsub (by rw [hB_card, hcard])
                      have hb₃_in_set : b₃ ∈ ({v₁, v₂, z} : Finset V) := by rw [← heq]; exact hb₃_in_B
                      simp at hb₃_in_set
                      rcases hb₃_in_set with rfl | rfl | rfl
                      · exact absurd rfl hb₃_ne_v₁
                      · exact absurd rfl hb₃_ne_v₂
                      · rfl
                · intro hz
                  rcases hz with rfl | rfl | rfl <;> [exact hv₁_in_B; exact hv₂_in_B; exact hb₃_in_B]
            obtain ⟨b₃, _, _, hb₃_ne_v₁, hb₃_ne_v₂, hB_eq⟩ := hB_struct
            rw [hB_eq] at hx_in_B hy_in_B
            simp at hx_in_B hy_in_B
            rcases hx_in_B with rfl | rfl | rfl
            · exact absurd rfl hx_v1
            · exact absurd rfl hx_v2
            · rcases hy_in_B with rfl | rfl | rfl
              · exact absurd rfl hy_v1
              · exact absurd rfl hy_v2
              · exact absurd rfl hxy

/-- slot392: Interior C externals contain v₂ or v₃ -/
theorem interior_C_external_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D)
    (hM : isTrianglePacking G M)
    (v₂ v₃ : V) (hv₂ : B ∩ C = {v₂}) (hv₃ : C ∩ D = {v₃}) :
    ∀ T ∈ S_e G M C, v₂ ∈ T ∨ v₃ ∈ T := by
  intro T hT
  by_cases hTeq : T = C
  · left
    rw [hTeq]
    have : v₂ ∈ B ∩ C := by rw [hv₂]; exact mem_singleton_self v₂
    exact mem_of_mem_inter_right this
  · have hT_share : (T ∩ C).card ≥ 2 := by
      simp only [S_e, trianglesSharingEdge, mem_filter] at hT
      exact hT.1.2
    have hC_card : C.card = 3 := by
      have hC : C ∈ M := by rw [hpath.1]; simp
      exact (G.mem_cliqueFinset_iff.mp (hM.1 hC)).2
    have hv₂_in_C : v₂ ∈ C := by
      have : v₂ ∈ B ∩ C := by rw [hv₂]; exact mem_singleton_self v₂
      exact mem_of_mem_inter_right this
    have hv₃_in_C : v₃ ∈ C := by
      have : v₃ ∈ C ∩ D := by rw [hv₃]; exact mem_singleton_self v₃
      exact mem_of_mem_inter_left this
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hT_share
    have hx_in_T : x ∈ T := mem_of_mem_inter_left hx
    have hy_in_T : y ∈ T := mem_of_mem_inter_left hy
    have hx_in_C : x ∈ C := mem_of_mem_inter_right hx
    have hy_in_C : y ∈ C := mem_of_mem_inter_right hy
    -- C = {v₂, v₃, c₃}, at least one of x, y must be v₂ or v₃
    have hv₂_ne_v₃ : v₂ ≠ v₃ := by
      intro heq
      have hv₂_in_B : v₂ ∈ B := by
        have : v₂ ∈ B ∩ C := by rw [hv₂]; simp
        exact mem_of_mem_inter_left this
      have hv₃_in_D : v₃ ∈ D := by
        have : v₃ ∈ C ∩ D := by rw [hv₃]; simp
        exact mem_of_mem_inter_right this
      rw [heq] at hv₂_in_B
      have : v₃ ∈ B ∩ D := mem_inter.mpr ⟨hv₂_in_B, hv₃_in_D⟩
      have hBD : (B ∩ D).card = 0 := hpath.2.2.2.2.2.2.2.2.2.2.2
      rw [Finset.card_eq_zero.mp hBD] at this
      exact not_mem_empty _ this
    have hC_struct : ∃ c₃, c₃ ≠ v₂ ∧ c₃ ≠ v₃ ∧ C = {v₂, v₃, c₃} := by
      have hv₂v₃_card : ({v₂, v₃} : Finset V).card = 2 := by
        rw [card_insert_of_not_mem, card_singleton]
        simp [hv₂_ne_v₃]
      have hC_diff_nonempty : (C \ {v₂, v₃}).Nonempty := by
        rw [← card_pos]
        have : C.card = ({v₂, v₃} : Finset V).card + (C \ {v₂, v₃}).card := by
          have hsub : {v₂, v₃} ⊆ C := by
            intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
          rw [← card_sdiff hsub, add_comm, Nat.sub_add_cancel (card_le_card hsub)]
        rw [hC_card, hv₂v₃_card] at this
        omega
      obtain ⟨c₃, hc₃⟩ := hC_diff_nonempty
      simp at hc₃
      use c₃, hc₃.2.1, hc₃.2.2
      ext z; simp
      constructor
      · intro hz
        have hsub : {v₂, v₃, z} ⊆ C := by
          intro w hw; simp at hw
          rcases hw with rfl | rfl | rfl <;> [exact hv₂_in_C; exact hv₃_in_C; exact hz]
        have hcard_le : ({v₂, v₃, z} : Finset V).card ≤ C.card := card_le_card hsub
        by_cases hz_v2 : z = v₂
        · left; exact hz_v2
        · by_cases hz_v3 : z = v₃
          · right; left; exact hz_v3
          · right; right
            have hcard : ({v₂, v₃, z} : Finset V).card = 3 := by
              rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
              · simp [hv₂_ne_v₃]
              · simp [hz_v2]
            have heq := eq_of_subset_of_card_le hsub (by rw [hC_card, hcard])
            have hc₃_in_set : c₃ ∈ ({v₂, v₃, z} : Finset V) := by rw [← heq]; exact hc₃.1
            simp at hc₃_in_set
            rcases hc₃_in_set with rfl | rfl | rfl
            · exact absurd rfl hc₃.2.1
            · exact absurd rfl hc₃.2.2
            · rfl
      · intro hz
        rcases hz with rfl | rfl | rfl <;> [exact hv₂_in_C; exact hv₃_in_C; exact hc₃.1]
    obtain ⟨c₃, hc₃_ne_v₂, hc₃_ne_v₃, hC_eq⟩ := hC_struct
    rw [hC_eq] at hx_in_C hy_in_C
    simp at hx_in_C hy_in_C
    rcases hx_in_C with rfl | rfl | rfl
    · left; exact hx_in_T
    · right; exact hx_in_T
    · rcases hy_in_C with rfl | rfl | rfl
      · left; exact hy_in_T
      · right; exact hy_in_T
      · exact absurd rfl hxy

/-- slot393: Endpoint externals contain an edge -/
theorem endpoint_external_contains_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V)
    (hA_tri : A ∈ G.cliqueFinset 3)
    (T : Finset V)
    (hT_in_SA : T ∈ S_e G M A) :
    ∃ u v : V, u ∈ A ∧ v ∈ A ∧ u ≠ v ∧ u ∈ T ∧ v ∈ T := by
  have hT_share : (T ∩ A).card ≥ 2 := by
    simp only [S_e, trianglesSharingEdge, mem_filter] at hT_in_SA
    exact hT_in_SA.1.2
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hT_share
  use u, v
  exact ⟨mem_of_mem_inter_right hu, mem_of_mem_inter_right hv, huv,
         mem_of_mem_inter_left hu, mem_of_mem_inter_left hv⟩

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `mem_of_eq_singleton`
unsolved goals
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
A B C D : Finset V
hpath : isPath4 M A B C D
hM : isTrianglePacking G M
hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, #(T ∩ E) ≥ 2
v₁ : V
hv₁ : A ∩ B = {v₁}
v₂ : V
hv₂ : B ∩ C = {v₂}
v₃ : V
hv₃ : C ∩ D = {v₃}
hA_tri : A ∈ G.cliqueFinset 3
hB_tri : B ∈ G.cliqueFinset 3
hC_tri : C ∈ G.cliqueFinset 3
hD_tri : D ∈ G.cliqueFinset 3
hA_card : #A = 3
hD_card : #D = 3
hv₁_in_A : v₁ ∈ A
hA_minus_v1 : #(A \ {v₁}) = 2
a₂ : V
ha₂ : a₂ ∈ A \ {v₁}
ha₂' : a₂ ∈ A ∧ a₂ ∉ {v₁}
hrest : #((A \ {v₁}) \ {a₂}) = 1
a₃ : V
ha₃_eq : (A \ {v₁}) \ {a₂} = {a₃}
⊢ ∃ (a₂ : V) (a₃ : V), a₂ ∈ A ∧ a₃ ∈ A ∧ v₁ ≠ a₂ ∧ v₁ ≠ a₃ ∧ a₂ ≠ a₃ ∧ A = {v₁, a₂, a₃}
Unknown identifier `mem_of_eq_singleton`
unsolved goals
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
A B C D : Finset V
hpath : isPath4 M A B C D
hM : isTrianglePacking G M
hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, #(T ∩ E) ≥ 2
v₁ : V
hv₁ : A ∩ B = {v₁}
v₂ : V
hv₂ : B ∩ C = {v₂}
v₃ : V
hv₃ : C ∩ D = {v₃}
hA_tri : A ∈ G.cliqueFinset 3
hB_tri : B ∈ G.cliqueFinset 3
hC_tri : C ∈ G.cliqueFinset 3
hD_tri : D ∈ G.cliqueFinset 3
hA_card : #A = 3
hD_card : #D = 3
hv₁_in_A : v₁ ∈ A
a₂ a₃ : V
ha₂_in_A : a₂ ∈ A
ha₃_in_A : a₃ ∈ A
hv₁_ne_a₂ : v₁ ≠ a₂
hv₁_ne_a₃ : v₁ ≠ a₃
ha₂_ne_a₃ : a₂ ≠ a₃
hA_eq : A = {v₁, a₂, a₃}
hv₃_in_D : v₃ ∈ D
hD_minus_v3 : #(D \ {v₃}) = 2
d₂ : V
hd₂ : d₂ ∈ D \ {v₃}
hd₂' : d₂ ∈ D ∧ d₂ ∉ {v₃}
hrest : #((D \ {v₃}) \ {d₂}) = 1
d₃ : V
hd₃_eq : (D \ {v₃}) \ {d₂} = {d₃}
⊢ ∃ (d₂ : V) (d₃ : V), d₂ ∈ D ∧ d₃ ∈ D ∧ v₃ ≠ d₂ ∧ v₃ ≠ d₃ ∧ d₂ ≠ d₃ ∧ D = {v₃, d₂, d₃}
Type mismatch
  hpath.right.right.right.right.right.right.right.right.right.right.right
has type
  #(A ∩ D) = 0 ∧ #(B ∩ D) = 0
but is expected to have type
  #(B ∩ D) = 0-/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: For PATH_4 packing with ν = 4, there exists an 8-edge cover -/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D)
    (hM : isTrianglePacking G M)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2) :
    ∃ (cover : Finset (Sym2 V)), cover.card ≤ 8 ∧ isEdgeCover G cover := by
  -- Extract shared vertices
  obtain ⟨v₁, hv₁⟩ := path4_shared_v1 M A B C D hpath
  obtain ⟨v₂, hv₂⟩ := path4_shared_v2 M A B C D hpath
  obtain ⟨v₃, hv₃⟩ := path4_shared_v3 M A B C D hpath
  -- Get triangle structures
  have hA_tri : A ∈ G.cliqueFinset 3 := hM.1 (by rw [hpath.1]; simp)
  have hB_tri : B ∈ G.cliqueFinset 3 := hM.1 (by rw [hpath.1]; simp)
  have hC_tri : C ∈ G.cliqueFinset 3 := hM.1 (by rw [hpath.1]; simp)
  have hD_tri : D ∈ G.cliqueFinset 3 := hM.1 (by rw [hpath.1]; simp)
  have hA_card : A.card = 3 := (G.mem_cliqueFinset_iff.mp hA_tri).2
  have hD_card : D.card = 3 := (G.mem_cliqueFinset_iff.mp hD_tri).2
  -- Extract vertices of A = {v₁, a₂, a₃}
  have hv₁_in_A : v₁ ∈ A := by
    have : v₁ ∈ A ∩ B := by rw [hv₁]; simp
    exact mem_of_mem_inter_left this
  obtain ⟨a₂, a₃, ha₂_in_A, ha₃_in_A, hv₁_ne_a₂, hv₁_ne_a₃, ha₂_ne_a₃, hA_eq⟩ :
      ∃ a₂ a₃, a₂ ∈ A ∧ a₃ ∈ A ∧ v₁ ≠ a₂ ∧ v₁ ≠ a₃ ∧ a₂ ≠ a₃ ∧ A = {v₁, a₂, a₃} := by
    have hA_minus_v1 : (A \ {v₁}).card = 2 := by simp [card_sdiff, hv₁_in_A, hA_card]
    obtain ⟨a₂, ha₂⟩ := card_pos.mp (by omega : 0 < (A \ {v₁}).card)
    have ha₂' := mem_sdiff.mp ha₂
    have hrest : ((A \ {v₁}) \ {a₂}).card = 1 := by simp [card_sdiff, ha₂, hA_minus_v1]
    obtain ⟨a₃, ha₃_eq⟩ := card_eq_one.mp hrest
    have ha₃ := mem_of_eq_singleton ha₃_eq
    have ha₃' := mem_sdiff.mp ha₃
    have ha₃'' := mem_sdiff.mp ha₃'.1
    use a₂, a₃, mem_of_mem_sdiff ha₂, mem_of_mem_sdiff ha₃'.1
    simp at ha₂' ha₃' ha₃''
    refine ⟨ha₂'.2.symm, ha₃''.2.symm, ha₃'.2.symm, ?_⟩
    ext x; simp
    constructor
    · intro hx
      by_cases hx1 : x = v₁
      · left; exact hx1
      · by_cases hx2 : x = a₂
        · right; left; exact hx2
        · right; right
          have : x ∈ (A \ {v₁}) \ {a₂} := mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hx, by simp [hx1]⟩, by simp [hx2]⟩
          rw [ha₃_eq] at this
          exact mem_singleton.mp this
    · intro hx
      rcases hx with rfl | rfl | rfl
      · exact hv₁_in_A
      · exact mem_of_mem_sdiff ha₂
      · exact mem_of_mem_sdiff ha₃'.1
  -- Extract vertices of D = {v₃, d₂, d₃}
  have hv₃_in_D : v₃ ∈ D := by
    have : v₃ ∈ C ∩ D := by rw [hv₃]; simp
    exact mem_of_mem_inter_right this
  obtain ⟨d₂, d₃, hd₂_in_D, hd₃_in_D, hv₃_ne_d₂, hv₃_ne_d₃, hd₂_ne_d₃, hD_eq⟩ :
      ∃ d₂ d₃, d₂ ∈ D ∧ d₃ ∈ D ∧ v₃ ≠ d₂ ∧ v₃ ≠ d₃ ∧ d₂ ≠ d₃ ∧ D = {v₃, d₂, d₃} := by
    have hD_minus_v3 : (D \ {v₃}).card = 2 := by simp [card_sdiff, hv₃_in_D, hD_card]
    obtain ⟨d₂, hd₂⟩ := card_pos.mp (by omega : 0 < (D \ {v₃}).card)
    have hd₂' := mem_sdiff.mp hd₂
    have hrest : ((D \ {v₃}) \ {d₂}).card = 1 := by simp [card_sdiff, hd₂, hD_minus_v3]
    obtain ⟨d₃, hd₃_eq⟩ := card_eq_one.mp hrest
    have hd₃ := mem_of_eq_singleton hd₃_eq
    have hd₃' := mem_sdiff.mp hd₃
    have hd₃'' := mem_sdiff.mp hd₃'.1
    use d₂, d₃, mem_of_mem_sdiff hd₂, mem_of_mem_sdiff hd₃'.1
    simp at hd₂' hd₃' hd₃''
    refine ⟨hd₂'.2.symm, hd₃''.2.symm, hd₃'.2.symm, ?_⟩
    ext x; simp
    constructor
    · intro hx
      by_cases hx1 : x = v₃
      · left; exact hx1
      · by_cases hx2 : x = d₂
        · right; left; exact hx2
        · right; right
          have : x ∈ (D \ {v₃}) \ {d₂} := mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hx, by simp [hx1]⟩, by simp [hx2]⟩
          rw [hd₃_eq] at this
          exact mem_singleton.mp this
    · intro hx
      rcases hx with rfl | rfl | rfl
      · exact hv₃_in_D
      · exact mem_of_mem_sdiff hd₂
      · exact mem_of_mem_sdiff hd₃'.1
  -- Define the 8-edge cover: edges(A) ∪ {v₁v₂, v₂v₃} ∪ edges(D)
  -- A has edges: {v₁,a₂}, {v₁,a₃}, {a₂,a₃}
  -- D has edges: {v₃,d₂}, {v₃,d₃}, {d₂,d₃}
  -- Spine: {v₁,v₂}, {v₂,v₃}
  -- Total: 3 + 2 + 3 = 8
  have hv₁_in_B : v₁ ∈ B := by
    have : v₁ ∈ A ∩ B := by rw [hv₁]; simp
    exact mem_of_mem_inter_right this
  have hv₂_in_B : v₂ ∈ B := by
    have : v₂ ∈ B ∩ C := by rw [hv₂]; simp
    exact mem_of_mem_inter_left this
  have hv₂_in_C : v₂ ∈ C := by
    have : v₂ ∈ B ∩ C := by rw [hv₂]; simp
    exact mem_of_mem_inter_right this
  have hv₃_in_C : v₃ ∈ C := by
    have : v₃ ∈ C ∩ D := by rw [hv₃]; simp
    exact mem_of_mem_inter_left this
  -- Get adjacencies
  have hA_clique := G.mem_cliqueFinset_iff.mp hA_tri
  have hB_clique := G.mem_cliqueFinset_iff.mp hB_tri
  have hC_clique := G.mem_cliqueFinset_iff.mp hC_tri
  have hD_clique := G.mem_cliqueFinset_iff.mp hD_tri
  have hv₁_ne_v₂ : v₁ ≠ v₂ := by
    intro heq
    have hv₂_in_A : v₂ ∈ A := by rw [← heq]; exact hv₁_in_A
    have : v₂ ∈ A ∩ C := mem_inter.mpr ⟨hv₂_in_A, hv₂_in_C⟩
    have hAC : (A ∩ C).card = 0 := hpath.2.2.2.2.2.2.2.2.2.2.1
    rw [Finset.card_eq_zero.mp hAC] at this
    exact not_mem_empty _ this
  have hv₂_ne_v₃ : v₂ ≠ v₃ := by
    intro heq
    have hv₃_in_B : v₃ ∈ B := by rw [← heq]; exact hv₂_in_B
    have : v₃ ∈ B ∩ D := mem_inter.mpr ⟨hv₃_in_B, hv₃_in_D⟩
    have hBD : (B ∩ D).card = 0 := hpath.2.2.2.2.2.2.2.2.2.2.2
    rw [Finset.card_eq_zero.mp hBD] at this
    exact not_mem_empty _ this
  -- The cover construction and verification
  sorry

end