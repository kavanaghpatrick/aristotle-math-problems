/-
  slot418_bridge_coverage.lean

  FOCUSED LEMMA: Any 2-edge selection from middle element B = {v₁, v₂, b₃}
  covers bridges at BOTH junctions (A-B and B-C).

  KEY STRUCTURAL INSIGHT:
  For triangle {v₁, v₂, b₃} with distinct v₁, v₂, b₃:
  - Edges: {v₁,v₂}, {v₁,b₃}, {v₂,b₃}
  - Edge avoiding v₁: only {v₂,b₃}
  - Edge avoiding v₂: only {v₁,b₃}
  - Any 2-edge selection (from 3 edges) must include at least 2 edges
  - By pigeonhole: includes ≥1 edge with v₁ AND ≥1 edge with v₂

  PROOF SKETCH:
  1. There are exactly 3 edges in triangle B
  2. Exactly 1 edge avoids v₁ (the edge {v₂, b₃})
  3. Exactly 1 edge avoids v₂ (the edge {v₁, b₃})
  4. These are DIFFERENT edges
  5. Any 2-edge selection can only avoid ONE edge
  6. Therefore at least one selected edge contains v₁ AND at least one contains v₂

  TIER: 1 (pure combinatorics on Fin 3)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- CORE LEMMA: Pigeonhole on triangle edges
-- ══════════════════════════════════════════════════════════════════════════════

/-- For triangle {a, b, c}, vertex v in triangle, any 2 of 3 edges include one with v -/
lemma two_edges_contain_vertex (a b c v : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hv : v = a ∨ v = b ∨ v = c)
    (e₁ e₂ : Sym2 V) (hne : e₁ ≠ e₂)
    (he₁ : e₁ = s(a, b) ∨ e₁ = s(a, c) ∨ e₁ = s(b, c))
    (he₂ : e₂ = s(a, b) ∨ e₂ = s(a, c) ∨ e₂ = s(b, c)) :
    v ∈ e₁ ∨ v ∈ e₂ := by
  rcases hv with rfl | rfl | rfl
  · -- v = a: the only edge not containing a is s(b,c)
    rcases he₁ with rfl | rfl | rfl
    · left; simp [Sym2.mem_iff]
    · left; simp [Sym2.mem_iff]
    · -- e₁ = s(b,c), so e₂ must contain a (since e₂ ≠ e₁)
      rcases he₂ with rfl | rfl | rfl
      · right; simp [Sym2.mem_iff]
      · right; simp [Sym2.mem_iff]
      · exfalso; exact hne rfl
  · -- v = b: the only edge not containing b is s(a,c)
    rcases he₁ with rfl | rfl | rfl
    · left; simp [Sym2.mem_iff]
    · rcases he₂ with rfl | rfl | rfl
      · right; simp [Sym2.mem_iff]
      · exfalso; exact hne rfl
      · right; simp [Sym2.mem_iff]
    · left; simp [Sym2.mem_iff]
  · -- v = c: the only edge not containing c is s(a,b)
    rcases he₁ with rfl | rfl | rfl
    · rcases he₂ with rfl | rfl | rfl
      · exfalso; exact hne rfl
      · right; simp [Sym2.mem_iff]
      · right; simp [Sym2.mem_iff]
    · left; simp [Sym2.mem_iff]
    · left; simp [Sym2.mem_iff]

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY STRUCTURAL LEMMA: Double pigeonhole for middle element
-- ══════════════════════════════════════════════════════════════════════════════

/-- For B = {v₁, v₂, b₃}, any 2-edge selection covers both v₁ AND v₂ -/
theorem middle_element_covers_both (v₁ v₂ b₃ : V)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ b₃) (h23 : v₂ ≠ b₃)
    (e₁ e₂ : Sym2 V) (hne : e₁ ≠ e₂)
    (he₁ : e₁ = s(v₁, v₂) ∨ e₁ = s(v₁, b₃) ∨ e₁ = s(v₂, b₃))
    (he₂ : e₂ = s(v₁, v₂) ∨ e₂ = s(v₁, b₃) ∨ e₂ = s(v₂, b₃)) :
    (v₁ ∈ e₁ ∨ v₁ ∈ e₂) ∧ (v₂ ∈ e₁ ∨ v₂ ∈ e₂) := by
  constructor
  · -- At least one edge contains v₁
    exact two_edges_contain_vertex v₁ v₂ b₃ v₁ h12 h13 h23 (Or.inl rfl) e₁ e₂ hne he₁ he₂
  · -- At least one edge contains v₂
    exact two_edges_contain_vertex v₁ v₂ b₃ v₂ h12 h13 h23 (Or.inr (Or.inl rfl)) e₁ e₂ hne he₁ he₂

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE PROPERTY: Bridge contains shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- A bridge (triangle sharing ≥2 vertices with both E and F) contains their shared vertex -/
lemma bridge_contains_shared (E F : Finset V) (v : V)
    (hEF : E ∩ F = {v})
    (T : Finset V) (hT_card : T.card = 3)
    (hTE : (T ∩ E).card ≥ 2) (hTF : (T ∩ F).card ≥ 2) :
    v ∈ T := by
  by_contra hv_not
  have h_disj : Disjoint (T ∩ E) (T ∩ F) := by
    rw [Finset.disjoint_left]
    intro x hxE hxF
    have hx_inter : x ∈ E ∩ F := mem_inter.mpr ⟨mem_of_mem_inter_right hxE, mem_of_mem_inter_right hxF⟩
    rw [hEF] at hx_inter
    simp only [mem_singleton] at hx_inter
    rw [hx_inter] at hxE
    exact hv_not (mem_of_mem_inter_left hxE)
  have h_union : (T ∩ E ∪ T ∩ F) ⊆ T := union_subset inter_subset_left inter_subset_left
  have h_card : (T ∩ E ∪ T ∩ F).card ≤ T.card := card_le_card h_union
  rw [card_union_of_disjoint h_disj] at h_card
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- EDGE IN TRIANGLE: Endpoints in triangle → edge in sym2
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_sym2 (T : Finset V) (a b : V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN APPLICATION: Middle element's 2 edges hit bridges at both junctions
-- ══════════════════════════════════════════════════════════════════════════════

/-- For PATH_4 with A-v₁-B-v₂-C-v₃-D, B's any 2-edge selection hits bridges at A-B and B-C -/
theorem middle_edges_hit_bridges (v₁ v₂ b₃ : V)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ b₃) (h23 : v₂ ≠ b₃)
    (e₁ e₂ : Sym2 V) (hne : e₁ ≠ e₂)
    (he₁ : e₁ = s(v₁, v₂) ∨ e₁ = s(v₁, b₃) ∨ e₁ = s(v₂, b₃))
    (he₂ : e₂ = s(v₁, v₂) ∨ e₂ = s(v₁, b₃) ∨ e₂ = s(v₂, b₃))
    -- A bridge at A-B
    (T : Finset V) (hT_card : T.card = 3)
    (hv1_T : v₁ ∈ T)
    -- T shares edge with B (another vertex of B is in T)
    (hT_shares_B : ∃ x ∈ ({v₁, v₂, b₃} : Finset V), x ∈ T ∧ x ≠ v₁) :
    e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
  -- By middle_element_covers_both, v₁ ∈ e₁ ∨ v₁ ∈ e₂
  obtain ⟨hv1_covered, hv2_covered⟩ := middle_element_covers_both v₁ v₂ b₃ h12 h13 h23 e₁ e₂ hne he₁ he₂
  -- Get x ∈ {v₁, v₂, b₃} ∩ T with x ≠ v₁
  obtain ⟨x, hx_B, hx_T, hx_ne_v1⟩ := hT_shares_B
  simp only [mem_insert, mem_singleton] at hx_B
  -- x is v₂ or b₃ (since x ≠ v₁)
  rcases hx_B with rfl | rfl | rfl
  · exact absurd rfl hx_ne_v1
  · -- x = v₂, so v₁, v₂ ∈ T
    -- The edge containing both v₁ and v₂ is s(v₁, v₂)
    -- By he₁ and he₂, at least one of e₁, e₂ is s(v₁, v₂) or contains v₁ or v₂
    -- Actually, we need to show e₁ or e₂ is in T.sym2
    -- Since v₁, v₂ ∈ T, if e = s(v₁, v₂) then e ∈ T.sym2
    rcases he₁ with rfl | rfl | rfl
    · -- e₁ = s(v₁, v₂)
      left
      exact edge_in_sym2 T v₁ v₂ hv1_T hx_T
    · -- e₁ = s(v₁, b₃)
      -- v₁ ∈ T, is b₃ ∈ T?
      -- We know x = v₂ ∈ T and v₁ ∈ T
      -- T has 3 elements. If b₃ ∈ T, then T = {v₁, v₂, b₃}
      -- If b₃ ∉ T, then e₁ = s(v₁, b₃) ∉ T.sym2, but what about e₂?
      -- e₂ ∈ {s(v₁,v₂), s(v₁,b₃), s(v₂,b₃)} and e₂ ≠ e₁ = s(v₁,b₃)
      -- So e₂ = s(v₁,v₂) or e₂ = s(v₂,b₃)
      rcases he₂ with rfl | rfl | rfl
      · -- e₂ = s(v₁, v₂)
        right
        exact edge_in_sym2 T v₁ v₂ hv1_T hx_T
      · -- e₂ = s(v₁, b₃) = e₁, contradiction
        exfalso; exact hne rfl
      · -- e₂ = s(v₂, b₃)
        -- v₂ ∈ T, is b₃ ∈ T?
        by_cases hb3 : b₃ ∈ T
        · right; exact edge_in_sym2 T v₂ b₃ hx_T hb3
        · -- b₃ ∉ T, but we need e₁ or e₂ in T.sym2
          -- e₁ = s(v₁, b₃), b₃ ∉ T, so e₁ ∉ T.sym2
          -- e₂ = s(v₂, b₃), b₃ ∉ T, so e₂ ∉ T.sym2
          -- But wait, s(v₁, v₂) must be in {e₁, e₂} or not selected
          -- e₁ = s(v₁, b₃), e₂ = s(v₂, b₃), and we didn't select s(v₁, v₂)
          -- s(v₁, v₂) ∈ T.sym2 but not in our cover
          -- This seems like a gap! But actually, we're proving for ANY 2-edge selection
          -- The issue: we chose e₁, e₂ that don't include s(v₁, v₂)
          -- But we need the SELECTION to hit T, not just existence

          -- Actually, the selection e₁ = s(v₁, b₃), e₂ = s(v₂, b₃) doesn't hit T
          -- when T = {v₁, v₂, y} for some y ∉ {v₁, v₂, b₃}
          -- Because neither e₁ nor e₂ is in T.sym2

          -- WAIT: T shares edge with B = {v₁, v₂, b₃}
          -- If v₁, v₂ ∈ T and b₃ ∉ T, then T = {v₁, v₂, y} for some y
          -- T ∩ B = {v₁, v₂}, which has 2 elements
          -- So T shares EDGE {v₁, v₂} with B
          -- The edge s(v₁, v₂) IS in T.sym2
          -- But e₁, e₂ don't include s(v₁, v₂)!

          -- This reveals the issue: the statement needs e₁ ∪ e₂ to include all edges
          -- containing the shared vertices v₁ AND v₂, but that's 3 edges, not 2!

          -- RESOLUTION: The statement is wrong. We need a SPECIFIC 2-edge selection
          -- that covers bridges, not ANY 2-edge selection.

          -- For bridges at A-B (containing v₁), we need ≥1 edge with v₁
          -- For bridges at B-C (containing v₂), we need ≥1 edge with v₂
          -- ANY 2-edge selection gives us this!
          -- But the SAME edge might not cover BOTH.

          -- Actually, the double pigeonhole tells us:
          -- - ∃ ei with v₁ ∈ ei
          -- - ∃ ej with v₂ ∈ ej (could be same or different edge)

          -- For this specific case (e₁ = s(v₁, b₃), e₂ = s(v₂, b₃)):
          -- v₁ ∈ e₁ ✓
          -- v₂ ∈ e₂ ✓
          -- But T = {v₁, v₂, y} needs edge s(v₁, v₂) or s(v₁, y) or s(v₂, y)
          -- e₁ = s(v₁, b₃) requires b₃ ∈ T, but b₃ ∉ T
          -- e₂ = s(v₂, b₃) requires b₃ ∈ T, but b₃ ∉ T

          -- So this case is IMPOSSIBLE: if T shares edge with B and b₃ ∉ T,
          -- then T must use edge s(v₁, v₂)
          -- But we need to show this doesn't happen...

          -- Actually, let's reconsider. T is a bridge at A-B.
          -- Bridge means T shares ≥2 vertices with BOTH A and B.
          -- If A ∩ B = {v₁}, then by bridge_contains_shared, v₁ ∈ T.
          -- T also shares ≥2 with B = {v₁, v₂, b₃}, and v₁ ∈ T.
          -- So T must have one of v₂, b₃ in it (to get ≥2 vertices from B).

          -- In this branch, x = v₂ and b₃ ∉ T.
          -- So T shares only {v₁, v₂} with B.
          -- For T to be a bridge, it needs ≥2 vertices from B, which is satisfied.
          -- But the edge s(v₁, v₂) is the only B-edge in T.
          -- e₁ = s(v₁, b₃) ∉ T.sym2 (b₃ ∉ T)
          -- e₂ = s(v₂, b₃) ∉ T.sym2 (b₃ ∉ T)

          -- So our 2-edge selection {s(v₁, b₃), s(v₂, b₃)} doesn't hit T!
          -- This is a REAL gap in the proof.

          -- CONCLUSION: The original conjecture that ANY 2-edge selection covers
          -- bridges is FALSE. We need a SPECIFIC selection.

          -- For B, the selection should be:
          -- - s(v₁, v₂) (covers bridges using this edge)
          -- - s(v₁, b₃) or s(v₂, b₃) (for externals)

          -- Let me state a WEAKER but TRUE lemma instead.

          sorry
    · -- e₁ = s(v₂, b₃)
      -- Similar analysis...
      sorry
  · -- x = b₃
    sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- CORRECTED LEMMA: Specific 2-edge selection covers bridges
-- ══════════════════════════════════════════════════════════════════════════════

/-
The correct statement: If we select {s(v₁, v₂), s(v₁, b₃)} from B,
then any bridge containing v₁ and sharing edge with B is covered.

Proof: Bridge T contains v₁ (by bridge_contains_shared).
       T shares ≥2 vertices with B = {v₁, v₂, b₃}.
       Since v₁ ∈ T, T contains v₂ or b₃ (or both).
       If v₂ ∈ T: s(v₁, v₂) ∈ T.sym2 ✓
       If b₃ ∈ T: s(v₁, b₃) ∈ T.sym2 ✓
-/

/-- Selection {s(v₁, v₂), s(v₁, b₃)} covers bridges at A-B -/
theorem specific_selection_covers_bridge (v₁ v₂ b₃ : V)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ b₃) (h23 : v₂ ≠ b₃)
    (T : Finset V) (hT_card : T.card = 3)
    (hv1_T : v₁ ∈ T)  -- Bridge contains v₁
    (hT_shares_B : (T ∩ {v₁, v₂, b₃}).card ≥ 2) :  -- T shares ≥2 vertices with B
    s(v₁, v₂) ∈ T.sym2 ∨ s(v₁, b₃) ∈ T.sym2 := by
  -- v₁ ∈ T and |T ∩ B| ≥ 2, so there's another element of B in T
  have hv1_in_B : v₁ ∈ ({v₁, v₂, b₃} : Finset V) := by simp
  have hv1_in_inter : v₁ ∈ T ∩ {v₁, v₂, b₃} := mem_inter.mpr ⟨hv1_T, hv1_in_B⟩
  have h_exists : ∃ x ∈ T ∩ {v₁, v₂, b₃}, x ≠ v₁ := by
    by_contra h
    push_neg at h
    have h_sub : T ∩ {v₁, v₂, b₃} ⊆ {v₁} := fun y hy => mem_singleton.mpr (h y hy)
    have h_card : (T ∩ {v₁, v₂, b₃}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
    omega
  obtain ⟨x, hx_inter, hx_ne⟩ := h_exists
  have hx_T : x ∈ T := mem_of_mem_inter_left hx_inter
  have hx_B : x ∈ ({v₁, v₂, b₃} : Finset V) := mem_of_mem_inter_right hx_inter
  simp only [mem_insert, mem_singleton] at hx_B
  rcases hx_B with rfl | rfl | rfl
  · exact absurd rfl hx_ne
  · left; exact edge_in_sym2 T v₁ v₂ hv1_T hx_T
  · right; exact edge_in_sym2 T v₁ b₃ hv1_T hx_T

end
