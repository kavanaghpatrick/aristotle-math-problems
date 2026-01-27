/-
  slot439_bridge_containment_aristotle.lean

  TARGET: Prove the bridge containment lemma

  KEY INSIGHT: If T is a bridge between E and F (sharing only vertex v),
  then v ∈ T. This is pure pigeonhole on cardinalities.

  PROOF SKETCH:
  1. T ∩ E ≥ 2 and T ∩ F ≥ 2
  2. E ∩ F = {v}
  3. |T| = 3
  4. By inclusion-exclusion: |T ∩ E| + |T ∩ F| - |T ∩ E ∩ F| ≤ |T| = 3
  5. So: 2 + 2 - |T ∩ E ∩ F| ≤ 3, meaning |T ∩ E ∩ F| ≥ 1
  6. T ∩ E ∩ F ⊆ E ∩ F = {v}, so v ∈ T

  TIER: 1-2 (cardinality bounds + finite case analysis)
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

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

lemma inter_inter_eq (A B C : Finset V) :
    (A ∩ B) ∩ (A ∩ C) = A ∩ (B ∩ C) := by
  ext x; simp only [mem_inter]; tauto

lemma union_inter_subset_left (A B C : Finset V) :
    (A ∩ B) ∪ (A ∩ C) ⊆ A := by
  intro x hx
  simp only [mem_union, mem_inter] at hx
  rcases hx with ⟨hA, _⟩ | ⟨hA, _⟩ <;> exact hA

lemma card_inter_singleton_le_one (A : Finset V) (v : V) :
    (A ∩ {v}).card ≤ 1 := by
  calc (A ∩ {v}).card ≤ ({v} : Finset V).card := card_le_card inter_subset_right
    _ = 1 := card_singleton v

lemma card_inter_singleton_ge_one_iff (A : Finset V) (v : V) :
    (A ∩ {v}).card ≥ 1 ↔ v ∈ A := by
  constructor
  · intro h
    have h_nonempty : (A ∩ {v}).Nonempty := by rwa [one_le_card] at h
    obtain ⟨x, hx⟩ := h_nonempty
    simp only [mem_inter, mem_singleton] at hx
    exact hx.2 ▸ hx.1
  · intro hv
    have : v ∈ A ∩ {v} := by simp [hv]
    rwa [← one_le_card, card_inter_singleton_le_one, le_antisymm_iff, and_iff_right]
    exact card_pos.mpr ⟨v, this⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Bridge contains shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Let T be a triangle with |T ∩ E| ≥ 2 and |T ∩ F| ≥ 2
2. E ∩ F = {v} by hypothesis
3. (T ∩ E) ∪ (T ∩ F) ⊆ T, so |(T ∩ E) ∪ (T ∩ F)| ≤ |T| = 3
4. By inclusion-exclusion:
   |T ∩ E| + |T ∩ F| - |(T ∩ E) ∩ (T ∩ F)| = |(T ∩ E) ∪ (T ∩ F)| ≤ 3
5. (T ∩ E) ∩ (T ∩ F) = T ∩ (E ∩ F) = T ∩ {v}
6. So: 2 + 2 - |T ∩ {v}| ≤ 3
7. Therefore |T ∩ {v}| ≥ 1, which means v ∈ T
-/

theorem bridge_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v : V) (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : (T ∩ E).card ≥ 2) (hTF : (T ∩ F).card ≥ 2) :
    v ∈ T := by
  -- T is a triangle with 3 vertices
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT
    exact hT.2
  -- (T ∩ E) ∪ (T ∩ F) ⊆ T
  have h_union_sub : (T ∩ E) ∪ (T ∩ F) ⊆ T := union_inter_subset_left T E F
  have h_union_card : ((T ∩ E) ∪ (T ∩ F)).card ≤ T.card := card_le_card h_union_sub
  -- Inclusion-exclusion
  have h_ie : (T ∩ E).card + (T ∩ F).card =
      ((T ∩ E) ∪ (T ∩ F)).card + ((T ∩ E) ∩ (T ∩ F)).card := by
    rw [card_union_add_card_inter]
  -- (T ∩ E) ∩ (T ∩ F) = T ∩ (E ∩ F) = T ∩ {v}
  have h_inter_eq : (T ∩ E) ∩ (T ∩ F) = T ∩ {v} := by
    rw [inter_inter_eq, hEF]
  -- Combine inequalities
  have h_calc : (T ∩ {v}).card ≥ 1 := by
    have h1 : ((T ∩ E) ∪ (T ∩ F)).card ≤ 3 := by omega
    have h2 : (T ∩ E).card + (T ∩ F).card ≥ 4 := by omega
    rw [h_ie, h_inter_eq] at h2
    omega
  -- v ∈ T
  rwa [card_inter_singleton_ge_one_iff] at h_calc

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: Any edge of E involving v covers bridges to neighbor F
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_from_shared_vertex_covers_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v u : V) (hv : v ∈ E) (hu : u ∈ E)
    (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : (T ∩ E).card ≥ 2) (hTF : (T ∩ F).card ≥ 2)
    (huT : u ∈ T) :
    s(v, u) ∈ T.sym2 := by
  have hv_T := bridge_contains_shared G E F v hEF T hT hTE hTF
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨hv_T, huT⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- APPLICATION: For PATH_4, spine edge {v₁, v₂} covers bridges to both neighbors
-- ══════════════════════════════════════════════════════════════════════════════

/-
For middle element B = {v₁, v₂, b₃} in A—v₁—B—v₂—C:
- Bridges from B to A contain v₁ (by bridge_contains_shared with A ∩ B = {v₁})
- Bridges from B to C contain v₂ (by bridge_contains_shared with B ∩ C = {v₂})
- Edge {v₁, v₂} covers all bridges: any bridge T contains v₁ or v₂
  - If T is a bridge to A: v₁ ∈ T, and T shares edge with B, so at least one of v₂, b₃ ∈ T
  - If v₂ ∈ T: {v₁, v₂} ⊆ T, so s(v₁, v₂) ∈ T.sym2
  - If b₃ ∈ T (and v₂ ∉ T): then T = {v₁, b₃, x} for some x
    - T ∩ A ≥ 2 means {v₁, b₃, x} ∩ A ≥ 2
    - v₁ ∈ A, so need one of b₃, x ∈ A
    - If b₃ ∈ A: then b₃ ∈ A ∩ B, but A ∩ B = {v₁}, contradiction
    - So x ∈ A, meaning T = {v₁, b₃, x} with x ∈ A, x ≠ v₁
- Similar analysis for bridges to C
-/

theorem spine_edge_covers_middle_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) (v₁ v₂ b₃ : V)
    (hB : B = {v₁, v₂, b₃})
    (hAB : A ∩ B = {v₁}) (hBC : B ∩ C = {v₂})
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ b₃) (h23 : v₂ ≠ b₃)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTB : (T ∩ B).card ≥ 2)
    (hT_bridge : (T ∩ A).card ≥ 2 ∨ (T ∩ C).card ≥ 2) :
    s(v₁, v₂) ∈ T.sym2 := by
  -- v₁ ∈ B and v₂ ∈ B
  have hv1_B : v₁ ∈ B := by simp [hB]
  have hv2_B : v₂ ∈ B := by simp [hB]
  rcases hT_bridge with hTA | hTC
  · -- Bridge to A: v₁ ∈ T
    have hv1_T := bridge_contains_shared G B A v₁ (by rw [inter_comm, hAB]) T hT hTB hTA
    -- T ∩ B ≥ 2, T is triangle, v₁ ∈ T
    -- Need to show v₂ ∈ T or find another way
    -- Actually, T shares edge with B, so contains 2 of {v₁, v₂, b₃}
    -- v₁ ∈ T, so need one of v₂, b₃ ∈ T
    have hT_card : T.card = 3 := by
      rw [SimpleGraph.mem_cliqueFinset_iff] at hT
      exact hT.2
    -- T ∩ B has at least 2 elements, one is v₁
    have h_exists_other : ∃ x ∈ T ∩ B, x ≠ v₁ := by
      by_contra h
      push_neg at h
      have h_sub : T ∩ B ⊆ {v₁} := fun x hx => mem_singleton.mpr (h x hx)
      have h_card : (T ∩ B).card ≤ 1 := by
        calc (T ∩ B).card ≤ ({v₁} : Finset V).card := card_le_card h_sub
          _ = 1 := card_singleton v₁
      omega
    obtain ⟨x, hx_inter, hx_ne_v1⟩ := h_exists_other
    simp only [mem_inter, hB, mem_insert, mem_singleton] at hx_inter
    obtain ⟨hx_T, hx_B⟩ := hx_inter
    rcases hx_B with rfl | rfl | rfl
    · exact absurd rfl hx_ne_v1
    · -- x = v₂, so {v₁, v₂} ⊆ T
      simp only [Finset.mk_mem_sym2_iff]
      exact ⟨hv1_T, hx_T⟩
    · -- x = b₃, need more work
      -- T = {v₁, b₃, y} for some y
      -- T ∩ A ≥ 2, v₁ ∈ A (from A ∩ B = {v₁} means v₁ ∈ A)
      have hv1_A : v₁ ∈ A := by
        have : v₁ ∈ A ∩ B := by rw [hAB]; simp
        exact mem_inter.mp this |>.1
      -- Need another element of T in A
      -- T ∩ A ≥ 2, v₁ ∈ T ∩ A
      have h_exists_a : ∃ a ∈ T ∩ A, a ≠ v₁ := by
        by_contra h
        push_neg at h
        have h_sub : T ∩ A ⊆ {v₁} := fun a ha => mem_singleton.mpr (h a ha)
        have h_card : (T ∩ A).card ≤ 1 := calc
          (T ∩ A).card ≤ ({v₁} : Finset V).card := card_le_card h_sub
          _ = 1 := card_singleton v₁
        omega
      obtain ⟨a, ha_inter, ha_ne_v1⟩ := h_exists_a
      simp only [mem_inter] at ha_inter
      -- a ∈ T, a ∈ A, a ≠ v₁
      -- T contains v₁, b₃, a where a ∈ A
      -- |T| = 3, so T = {v₁, b₃, a}
      -- But we claimed v₂ ∉ T (since x = b₃ was the "other" element)
      -- Actually, we need to check if a = v₂
      by_cases ha_v2 : a = v₂
      · -- a = v₂, so v₂ ∈ T
        simp only [Finset.mk_mem_sym2_iff]
        exact ⟨hv1_T, ha_v2 ▸ ha_inter.1⟩
      · -- a ≠ v₂, so T = {v₁, b₃, a} with a ∉ {v₂, v₁, b₃} except a ≠ v₁
        -- But a ∈ A, and A ∩ B = {v₁}, so a ∉ B \ {v₁}
        -- This means a ≠ v₂ and a ≠ b₃ (since a ∈ A and A ∩ B = {v₁})
        -- So T = {v₁, b₃, a} with three distinct elements
        -- T ∩ B = {v₁, b₃} since a ∉ B
        have ha_not_B : a ∉ B := by
          intro ha_B
          have : a ∈ A ∩ B := mem_inter.mpr ⟨ha_inter.2, ha_B⟩
          rw [hAB] at this
          exact ha_ne_v1 (mem_singleton.mp this)
        -- But we said T ∩ B ≥ 2, and we found v₁, b₃ ∈ T ∩ B
        -- This is consistent: T ∩ B = {v₁, b₃} has card 2
        -- The issue is we need s(v₁, v₂) ∈ T.sym2, but v₂ ∉ T
        -- This means the bridge doesn't contain v₂, only v₁
        -- But wait, we're trying to prove s(v₁, v₂) covers ALL bridges
        -- This case shows that's not always true!
        -- The bridge T = {v₁, b₃, a} with a ∈ A is NOT covered by s(v₁, v₂)
        -- It's covered by s(v₁, b₃) instead
        sorry
  · -- Bridge to C: v₂ ∈ T (symmetric argument)
    have hv2_T := bridge_contains_shared G B C v₂ hBC T hT hTB hTC
    have h_exists_other : ∃ x ∈ T ∩ B, x ≠ v₂ := by
      by_contra h
      push_neg at h
      have h_sub : T ∩ B ⊆ {v₂} := fun x hx => mem_singleton.mpr (h x hx)
      have h_card : (T ∩ B).card ≤ 1 := by
        calc (T ∩ B).card ≤ ({v₂} : Finset V).card := card_le_card h_sub
          _ = 1 := card_singleton v₂
      omega
    obtain ⟨x, hx_inter, hx_ne_v2⟩ := h_exists_other
    simp only [mem_inter, hB, mem_insert, mem_singleton] at hx_inter
    obtain ⟨hx_T, hx_B⟩ := hx_inter
    rcases hx_B with rfl | rfl | rfl
    · -- x = v₁, so {v₁, v₂} ⊆ T
      simp only [Finset.mk_mem_sym2_iff]
      exact ⟨hx_T, hv2_T⟩
    · exact absurd rfl hx_ne_v2
    · -- x = b₃, similar to above
      sorry

end
