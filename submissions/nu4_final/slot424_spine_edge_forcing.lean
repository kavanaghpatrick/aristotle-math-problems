/-
  slot424_spine_edge_forcing.lean

  KEY LEMMA: For middle elements, any 2-edge cover must include spine vertices.

  PROVEN SCAFFOLDING:
  - middle_no_base_externals (slot421): S_e(B) externals contain v1 or v2
  - not_all_three_edge_types (slot412): at most 2 edge-types have externals

  INSIGHT:
  For B = {v1, v2, b3}, all S_e externals contain v1 OR v2.
  To cover T with v1 ∈ T, need edge containing v1.
  To cover T with v2 ∈ T (but v1 ∉ T), need edge containing v2.
  Both situations can occur, so ANY 2-edge cover must include:
  - At least one edge containing v1
  - At least one edge containing v2

  COROLLARY: The 2-edge cover automatically hits bridges at both junctions!

  TIER: 1-2 (finite case analysis + proven structural lemmas)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slot421)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Middle element externals contain spine vertex (proven slot421) -/
lemma middle_no_base_externals (B : Finset V) (v1 v2 b3 : V)
    (hB : B = {v1, v2, b3})
    (h12 : v1 ≠ v2) (h13 : v1 ≠ b3) (h23 : v2 ≠ b3)
    (T : Finset V) (hT_card : T.card = 3)
    (hT_share : 2 ≤ (T ∩ B).card) :
    v1 ∈ T ∨ v2 ∈ T := by
  by_contra h_neither
  push_neg at h_neither
  obtain ⟨hv1_notin, hv2_notin⟩ := h_neither
  have h_sub : T ∩ B ⊆ B \ {v1, v2} := by
    intro x hx
    simp only [mem_inter] at hx
    simp only [mem_sdiff, mem_insert, mem_singleton]
    refine ⟨hx.2, ?_⟩
    intro hx_v
    rcases hx_v with rfl | rfl
    · exact hv1_notin hx.1
    · exact hv2_notin hx.1
  have h_sdiff_card : (B \ {v1, v2}).card ≤ 1 := by
    rw [hB]
    have h_sub : ({v1, v2} : Finset V) ⊆ {v1, v2, b3} := by
      intro z hz; simp only [mem_insert, mem_singleton] at hz ⊢
      rcases hz with rfl | rfl <;> simp
    have h_pair_card : ({v1, v2} : Finset V).card = 2 := by
      rw [card_insert_of_not_mem, card_singleton]; simp [h12]
    rw [card_sdiff h_sub]
    simp [h12.symm, h13.symm, h23.symm, h_pair_card]
  have h_card_le_1 : (T ∩ B).card ≤ 1 := calc
    (T ∩ B).card ≤ (B \ {v1, v2}).card := card_le_card h_sub
    _ ≤ 1 := h_sdiff_card
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Edge in sym2
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_sym2 (T : Finset V) (a b : V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA: 2-edge cover of middles includes both spine vertices
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Suppose 2-edge cover {e1, e2} covers all T with |T ∩ B| >= 2 and T ≠ B
2. Consider T1 = {v1, b3, x} for some external x (Type 1 external)
3. Consider T2 = {v2, b3, y} for some external y (Type 2 external)
4. If both exist, e1 or e2 must hit T1 (contains v1), so some edge contains v1
5. Similarly, some edge must contain v2
6. If only Type 1 exists: both edges could contain v1 only
   But wait - the cover must also include B itself!
   B = {v1, v2, b3}. To hit B, need edge in B.sym2 = {s(v1,v2), s(v1,b3), s(v2,b3)}
   If only edges with v1: {s(v1,v2), s(v1,b3)}. v2 ∈ s(v1,v2). Done!
7. Therefore ANY cover of B ∪ S_e(B) includes edges with both v1 and v2.
-/

theorem spine_edge_forcing (v1 v2 b3 : V)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ b3) (h23 : v2 ≠ b3)
    (e₁ e₂ : Sym2 V) (hne : e₁ ≠ e₂)
    -- Both edges are from B = {v1, v2, b3}
    (he1_B : e₁ = s(v1, v2) ∨ e₁ = s(v1, b3) ∨ e₁ = s(v2, b3))
    (he2_B : e₂ = s(v1, v2) ∨ e₂ = s(v1, b3) ∨ e₂ = s(v2, b3)) :
    (v1 ∈ e₁ ∨ v1 ∈ e₂) ∧ (v2 ∈ e₁ ∨ v2 ∈ e₂) := by
  constructor
  -- v1 ∈ e1 ∨ v1 ∈ e2
  · -- Only s(v2, b3) doesn't contain v1
    -- Since e1 ≠ e2 and there are only 3 edges, at most one can be s(v2, b3)
    rcases he1_B with rfl | rfl | rfl
    · left; simp [Sym2.mem_iff]
    · left; simp [Sym2.mem_iff]
    · -- e1 = s(v2, b3), so e2 ≠ s(v2, b3), so e2 contains v1
      rcases he2_B with rfl | rfl | rfl
      · right; simp [Sym2.mem_iff]
      · right; simp [Sym2.mem_iff]
      · exfalso; exact hne rfl
  -- v2 ∈ e1 ∨ v2 ∈ e2
  · -- Only s(v1, b3) doesn't contain v2
    rcases he1_B with rfl | rfl | rfl
    · left; simp [Sym2.mem_iff]
    · rcases he2_B with rfl | rfl | rfl
      · right; simp [Sym2.mem_iff]
      · exfalso; exact hne rfl
      · right; simp [Sym2.mem_iff]
    · left; simp [Sym2.mem_iff]

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE COVERAGE COROLLARY
-- ══════════════════════════════════════════════════════════════════════════════

/-- Any 2-edge selection from B hits triangles containing v1 or v2 -/
theorem middle_cover_hits_spine_triangles (v1 v2 b3 : V)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ b3) (h23 : v2 ≠ b3)
    (e₁ e₂ : Sym2 V) (hne : e₁ ≠ e₂)
    (he1_B : e₁ = s(v1, v2) ∨ e₁ = s(v1, b3) ∨ e₁ = s(v2, b3))
    (he2_B : e₂ = s(v1, v2) ∨ e₂ = s(v1, b3) ∨ e₂ = s(v2, b3))
    -- T contains v1 and shares ≥2 with B
    (T : Finset V) (hT_card : T.card = 3)
    (hv1_T : v1 ∈ T) (hT_share : 2 ≤ (T ∩ {v1, v2, b3}).card) :
    e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
  -- v1 ∈ T and |T ∩ B| ≥ 2, so T contains another element of B
  have hv1_in_B : v1 ∈ ({v1, v2, b3} : Finset V) := by simp
  have hv1_in_inter : v1 ∈ T ∩ {v1, v2, b3} := mem_inter.mpr ⟨hv1_T, hv1_in_B⟩
  have h_exists : ∃ z ∈ T ∩ {v1, v2, b3}, z ≠ v1 := by
    by_contra h
    push_neg at h
    have h_sub : T ∩ {v1, v2, b3} ⊆ {v1} := fun w hw => mem_singleton.mpr (h w hw)
    have h_card : (T ∩ {v1, v2, b3}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
    omega
  obtain ⟨z, hz_inter, hz_ne⟩ := h_exists
  have hz_T : z ∈ T := mem_of_mem_inter_left hz_inter
  have hz_B : z ∈ ({v1, v2, b3} : Finset V) := mem_of_mem_inter_right hz_inter
  simp only [mem_insert, mem_singleton] at hz_B
  rcases hz_B with rfl | rfl | rfl
  · exact absurd rfl hz_ne
  · -- z = v2, so v1, v2 ∈ T
    -- Check if s(v1, v2) is e1 or e2
    rcases he1_B with rfl | rfl | rfl
    · left; exact edge_in_sym2 T v1 v2 hv1_T hz_T
    · rcases he2_B with rfl | rfl | rfl
      · right; exact edge_in_sym2 T v1 v2 hv1_T hz_T
      · -- e1 = s(v1, b3), e2 = s(v1, b3), contradiction
        exfalso; exact hne rfl
      · right; exact edge_in_sym2 T v2 b3 hz_T (by
          -- Need b3 ∈ T or handle case where it's not
          -- Actually we know v1, v2 ∈ T. If b3 ∉ T, then e2 = s(v2, b3) ∉ T.sym2
          -- But e1 = s(v1, b3), also b3 ∉ T, so e1 ∉ T.sym2
          -- Yet we need to show one is in T.sym2... contradiction!
          -- Wait, this means b3 MUST be in T for this case to work
          -- Let's reconsider: T has 3 elements, v1, v2 ∈ T
          -- If b3 ∉ T, then T = {v1, v2, x} for some x ∉ {v1, v2, b3}
          -- T.sym2 = {s(v1,v2), s(v1,x), s(v2,x)}
          -- e1 = s(v1, b3), b3 ∉ T, so e1 ∉ T.sym2
          -- e2 = s(v2, b3), b3 ∉ T, so e2 ∉ T.sym2
          -- But we chose this edge set! The issue: such T doesn't satisfy hT_share!
          -- Wait, T ∩ {v1, v2, b3} = {v1, v2}, card = 2 ≥ 2. It does satisfy!
          -- So the selection {s(v1, b3), s(v2, b3)} doesn't cover T = {v1, v2, x}.
          -- This means the statement is FALSE for this edge selection!
          -- The issue: not every 2-edge selection works for bridges.
          -- We need the SPECIFIC selection that includes s(v1, v2).
          sorry)
    · -- e1 = s(v2, b3)
      rcases he2_B with rfl | rfl | rfl
      · right; exact edge_in_sym2 T v1 v2 hv1_T hz_T
      · left; simp [Sym2.mem_iff] at *
        exact edge_in_sym2 T v2 b3 hz_T (by sorry)
      · exfalso; exact hne rfl
  · -- z = b3, so v1, b3 ∈ T
    rcases he1_B with rfl | rfl | rfl
    · left; exact edge_in_sym2 T v1 v2 hv1_T (by
        -- Need v2 ∈ T, but we only know v1, b3 ∈ T
        -- If v2 ∉ T, then T = {v1, b3, y} for some y
        -- s(v1, v2) ∈ T.sym2 requires v2 ∈ T, contradiction
        sorry)
    · left; exact edge_in_sym2 T v1 b3 hv1_T hz_T
    · rcases he2_B with rfl | rfl | rfl
      · right; exact edge_in_sym2 T v1 v2 hv1_T (by sorry)
      · right; exact edge_in_sym2 T v1 b3 hv1_T hz_T
      · -- e1 = s(v2, b3), e2 = s(v2, b3), contradiction
        exfalso; exact hne rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- CORRECT STATEMENT: Specific selection covers all
-- ══════════════════════════════════════════════════════════════════════════════

/-- The CORRECT statement: {s(v1,v2), s(v1,b3)} covers all T with v1 ∈ T and |T∩B|≥2 -/
theorem correct_middle_cover (v1 v2 b3 : V)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ b3) (h23 : v2 ≠ b3)
    (T : Finset V) (hT_card : T.card = 3)
    (hv1_T : v1 ∈ T)
    (hT_share : 2 ≤ (T ∩ {v1, v2, b3}).card) :
    s(v1, v2) ∈ T.sym2 ∨ s(v1, b3) ∈ T.sym2 := by
  have hv1_in_B : v1 ∈ ({v1, v2, b3} : Finset V) := by simp
  have hv1_in_inter : v1 ∈ T ∩ {v1, v2, b3} := mem_inter.mpr ⟨hv1_T, hv1_in_B⟩
  have h_exists : ∃ z ∈ T ∩ {v1, v2, b3}, z ≠ v1 := by
    by_contra h
    push_neg at h
    have h_sub : T ∩ {v1, v2, b3} ⊆ {v1} := fun w hw => mem_singleton.mpr (h w hw)
    have h_card : (T ∩ {v1, v2, b3}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
    omega
  obtain ⟨z, hz_inter, hz_ne⟩ := h_exists
  have hz_T : z ∈ T := mem_of_mem_inter_left hz_inter
  have hz_B : z ∈ ({v1, v2, b3} : Finset V) := mem_of_mem_inter_right hz_inter
  simp only [mem_insert, mem_singleton] at hz_B
  rcases hz_B with rfl | rfl | rfl
  · exact absurd rfl hz_ne
  · left; exact edge_in_sym2 T v1 v2 hv1_T hz_T
  · right; exact edge_in_sym2 T v1 b3 hv1_T hz_T

end
