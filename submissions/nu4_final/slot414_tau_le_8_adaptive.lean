/-
  slot414_tau_le_8_adaptive.lean

  ADAPTIVE PROOF: τ ≤ 8 for PATH_4 with ν = 4

  KEY INSIGHT: For each M-element E, by not_all_three_edge_types, at most 2
  of the 3 edge types have externals. Choose those 2 edges adaptively.

  For PATH_4 with A—B—C—D:
  - A = {v₁, a₂, a₃}: might need base {a₂, a₃} if base externals exist
  - B = {v₁, v₂, b₃}: all edges include spine vertex (v₁ or v₂)
  - C = {v₂, v₃, c₃}: all edges include spine vertex (v₂ or v₃)
  - D = {v₃, d₂, d₃}: might need base {d₂, d₃} if base externals exist

  BRIDGES: Any bridge shares edge with 2 adjacent M-elements.
  - Bridge at A-B contains v₁ (shared vertex)
  - Bridge at B-C contains v₂
  - Bridge at C-D contains v₃
  All bridges contain spine vertices, so covered by spine edges in B, C's covers.

  TIER: 2 (builds on slot412's not_all_three_edge_types)
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

/-- S_e: Externals of e that DON'T share edge with other M-elements -/
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  ((G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)).filter
    (fun t => t ≠ e ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

/-- S_e elements using specific edge {a,b} of e = {a,b,c} -/
def S_e_edge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (a b c : V) : Finset (Finset V) :=
  (S_e G M {a, b, c}).filter (fun T => a ∈ T ∧ b ∈ T ∧ c ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- CORE LEMMA: At most 2 edge types have externals (from slot412)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
If all 3 edge types have externals T₁, T₂, T₃:
- T₁, T₂, T₃ are pairwise edge-disjoint (different edges of E)
- T₁, T₂, T₃ are edge-disjoint from B, C, D (S_e definition)
- {T₁, T₂, T₃, B, C, D} is a 6-packing, contradicting ν = 4
-/
axiom not_all_three_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ {a, b, c}) (hC_ne : C ≠ {a, b, c}) (hD_ne : D ≠ {a, b, c})
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hB_tri : B ∈ G.cliqueFinset 3) (hC_tri : C ∈ G.cliqueFinset 3) (hD_tri : D ∈ G.cliqueFinset 3) :
    ¬((S_e_edge G M a b c).Nonempty ∧
      (S_e_edge G M b c a).Nonempty ∧
      (S_e_edge G M a c b).Nonempty)

-- ══════════════════════════════════════════════════════════════════════════════
-- ADAPTIVE EDGE SELECTION
-- ══════════════════════════════════════════════════════════════════════════════

/-
Given at most 2 types exist, pick the 2 edges covering those types.
The element E itself is covered by any of its edges.
-/
lemma exists_two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ {a, b, c}) (hC_ne : C ≠ {a, b, c}) (hD_ne : D ≠ {a, b, c})
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hB_tri : B ∈ G.cliqueFinset 3) (hC_tri : C ∈ G.cliqueFinset 3) (hD_tri : D ∈ G.cliqueFinset 3) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      -- Cover E itself
      (e₁ ∈ ({a,b,c} : Finset V).sym2 ∨ e₂ ∈ ({a,b,c} : Finset V).sym2) ∧
      -- Cover all S_e externals
      (∀ T ∈ S_e G M {a,b,c}, e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  -- By not_all_three_edge_types, at least one type is empty
  have h_not_all := not_all_three_edge_types G M hM hNu4 a b c hE hab hbc hac B C D
    hB hC hD hB_ne hC_ne hD_ne hBC hBD hCD hB_tri hC_tri hD_tri
  push_neg at h_not_all

  -- Get E is a triangle
  have hE_tri : {a, b, c} ∈ G.cliqueFinset 3 := hM.1 hE
  have hab_adj : G.Adj a b := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hE_tri
    exact hE_tri.1 (by simp) (by simp) hab
  have hbc_adj : G.Adj b c := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hE_tri
    exact hE_tri.1 (by simp) (by simp) hbc
  have hac_adj : G.Adj a c := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hE_tri
    exact hE_tri.1 (by simp) (by simp) hac

  have hab_edge : s(a, b) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hab_adj
  have hbc_edge : s(b, c) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hbc_adj
  have hac_edge : s(a, c) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hac_adj

  -- Case split on which type is empty
  by_cases h1 : (S_e_edge G M a b c).Nonempty
  · by_cases h2 : (S_e_edge G M b c a).Nonempty
    · -- Types 1, 2 exist; Type 3 must be empty
      have h3 : ¬(S_e_edge G M a c b).Nonempty := h_not_all h1 h2
      -- Use {a,b} and {b,c}
      use s(a, b), s(b, c)
      refine ⟨hab_edge, hbc_edge, ?_, ?_⟩
      · left; simp [Finset.sym2, Sym2.mem_iff]
      · intro T hT
        simp only [S_e, mem_filter] at hT
        -- T ∈ S_e means T shares edge with E = {a,b,c}
        -- T must use one of the 3 edge types
        -- Since Type 3 is empty, T uses Type 1 or Type 2
        -- If T uses Type 1 ({a,b}): s(a,b) ∈ T.sym2
        -- If T uses Type 2 ({b,c}): s(b,c) ∈ T.sym2
        have hT_tri : T ∈ G.cliqueFinset 3 := hT.1.1
        have hT_share : (T ∩ {a, b, c}).card ≥ 2 := hT.1.2
        have hT_ne : T ≠ {a, b, c} := hT.2.1
        -- T has at least 2 vertices from {a,b,c}
        -- Case: T has a,b → s(a,b) ∈ T.sym2
        -- Case: T has b,c → s(b,c) ∈ T.sym2
        -- Case: T has a,c but not b → T ∈ S_e_edge G M a c b, contradicting h3
        by_cases ha_T : a ∈ T
        · by_cases hb_T : b ∈ T
          · left; simp [Finset.sym2, ha_T, hb_T]
            use a, ha_T, b, hb_T
          · -- a ∈ T, b ∉ T, |T ∩ E| ≥ 2 → c ∈ T
            have hc_T : c ∈ T := by
              by_contra hc_not
              have h_sub : T ∩ {a, b, c} ⊆ {a} := by
                intro x hx
                simp only [mem_inter, mem_insert, mem_singleton] at hx
                rcases hx.2 with rfl | rfl | rfl
                · simp
                · exact absurd hx.1 hb_T
                · exact absurd hx.1 hc_not
              have h_card : (T ∩ {a, b, c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
              omega
            -- T has a, c but not b → T ∈ S_e_edge G M a c b
            exfalso
            simp only [Finset.not_nonempty_iff_eq_empty] at h3
            have hT_in : T ∈ S_e_edge G M a c b := by
              simp only [S_e_edge, mem_filter]
              constructor
              · -- T ∈ S_e G M {a, c, b}
                simp only [S_e, mem_filter]
                have h_eq : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
                constructor
                · constructor
                  · exact hT_tri
                  · rw [h_eq]; exact hT_share
                · rw [h_eq]; exact hT.2
              · exact ⟨ha_T, hc_T, hb_T⟩
            rw [h3] at hT_in
            exact not_mem_empty T hT_in
        · -- a ∉ T, |T ∩ E| ≥ 2 → b, c ∈ T
          have hb_T : b ∈ T := by
            by_contra hb_not
            have h_sub : T ∩ {a, b, c} ⊆ {c} := by
              intro x hx
              simp only [mem_inter, mem_insert, mem_singleton] at hx
              rcases hx.2 with rfl | rfl | rfl
              · exact absurd hx.1 ha_T
              · exact absurd hx.1 hb_not
              · simp
            have h_card : (T ∩ {a, b, c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
            omega
          have hc_T : c ∈ T := by
            by_contra hc_not
            have h_sub : T ∩ {a, b, c} ⊆ {b} := by
              intro x hx
              simp only [mem_inter, mem_insert, mem_singleton] at hx
              rcases hx.2 with rfl | rfl | rfl
              · exact absurd hx.1 ha_T
              · simp
              · exact absurd hx.1 hc_not
            have h_card : (T ∩ {a, b, c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
            omega
          right; simp [Finset.sym2, hb_T, hc_T]
          use b, hb_T, c, hc_T
    · -- Type 2 is empty; use {a,b} and {a,c}
      use s(a, b), s(a, c)
      refine ⟨hab_edge, hac_edge, ?_, ?_⟩
      · left; simp [Finset.sym2, Sym2.mem_iff]
      · intro T hT
        simp only [S_e, mem_filter] at hT
        have hT_share : (T ∩ {a, b, c}).card ≥ 2 := hT.1.2
        by_cases ha_T : a ∈ T
        · by_cases hb_T : b ∈ T
          · left; simp [Finset.sym2, ha_T, hb_T]; use a, ha_T, b, hb_T
          · have hc_T : c ∈ T := by
              by_contra hc_not
              have h_sub : T ∩ {a, b, c} ⊆ {a} := by
                intro x hx; simp at hx
                rcases hx.2 with rfl | rfl | rfl
                · simp
                · exact absurd hx.1 hb_T
                · exact absurd hx.1 hc_not
              have h_card : (T ∩ {a, b, c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
              omega
            right; simp [Finset.sym2, ha_T, hc_T]; use a, ha_T, c, hc_T
        · have hb_T : b ∈ T := by
            by_contra hb_not
            have h_sub : T ∩ {a, b, c} ⊆ {c} := by
              intro x hx; simp at hx
              rcases hx.2 with rfl | rfl | rfl
              · exact absurd hx.1 ha_T
              · exact absurd hx.1 hb_not
              · simp
            have h_card : (T ∩ {a, b, c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
            omega
          -- a ∉ T, b ∈ T → T has b,c (Type 2) but Type 2 is empty!
          have hc_T : c ∈ T := by
            by_contra hc_not
            have h_sub : T ∩ {a, b, c} ⊆ {b} := by
              intro x hx; simp at hx
              rcases hx.2 with rfl | rfl | rfl
              · exact absurd hx.1 ha_T
              · simp
              · exact absurd hx.1 hc_not
            have h_card : (T ∩ {a, b, c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
            omega
          -- T has b, c but not a → T ∈ S_e_edge G M b c a
          simp only [Finset.not_nonempty_iff_eq_empty] at h2
          exfalso
          have hT_in : T ∈ S_e_edge G M b c a := by
            simp only [S_e_edge, mem_filter]
            constructor
            · simp only [S_e, mem_filter]
              have h_eq : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
              constructor
              · constructor
                · exact hT.1.1
                · rw [h_eq]; exact hT_share
              · rw [h_eq]; exact hT.2
            · exact ⟨hb_T, hc_T, ha_T⟩
          rw [h2] at hT_in
          exact not_mem_empty T hT_in
  · -- Type 1 is empty; use {b,c} and {a,c}
    use s(b, c), s(a, c)
    refine ⟨hbc_edge, hac_edge, ?_, ?_⟩
    · left; simp [Finset.sym2, Sym2.mem_iff]
    · intro T hT
      simp only [S_e, mem_filter] at hT
      have hT_share : (T ∩ {a, b, c}).card ≥ 2 := hT.1.2
      by_cases hb_T : b ∈ T
      · by_cases hc_T : c ∈ T
        · left; simp [Finset.sym2, hb_T, hc_T]; use b, hb_T, c, hc_T
        · have ha_T : a ∈ T := by
            by_contra ha_not
            have h_sub : T ∩ {a, b, c} ⊆ {b} := by
              intro x hx; simp at hx
              rcases hx.2 with rfl | rfl | rfl
              · exact absurd hx.1 ha_not
              · simp
              · exact absurd hx.1 hc_T
            have h_card : (T ∩ {a, b, c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
            omega
          -- T has a, b but not c → T ∈ S_e_edge G M a b c
          simp only [Finset.not_nonempty_iff_eq_empty] at h1
          exfalso
          have hT_in : T ∈ S_e_edge G M a b c := by
            simp only [S_e_edge, mem_filter]
            constructor
            · simp only [S_e, mem_filter]; exact ⟨hT.1, hT.2⟩
            · exact ⟨ha_T, hb_T, hc_T⟩
          rw [h1] at hT_in
          exact not_mem_empty T hT_in
      · have hc_T : c ∈ T := by
          by_contra hc_not
          have h_sub : T ∩ {a, b, c} ⊆ {a} := by
            intro x hx; simp at hx
            rcases hx.2 with rfl | rfl | rfl
            · simp
            · exact absurd hx.1 hb_T
            · exact absurd hx.1 hc_not
          have h_card : (T ∩ {a, b, c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
          omega
        have ha_T : a ∈ T := by
          by_contra ha_not
          have h_sub : T ∩ {a, b, c} ⊆ {c} := by
            intro x hx; simp at hx
            rcases hx.2 with rfl | rfl | rfl
            · exact absurd hx.1 ha_not
            · exact absurd hx.1 hb_T
            · simp
          have h_card : (T ∩ {a, b, c}).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
          omega
        right; simp [Finset.sym2, ha_T, hc_T]; use a, ha_T, c, hc_T

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE HANDLING
-- ══════════════════════════════════════════════════════════════════════════════

/-
KEY INSIGHT: In PATH_4, bridges share edge with 2 ADJACENT M-elements.
Adjacent pairs: (A,B), (B,C), (C,D)
Each pair shares exactly one vertex (spine vertex).

If T shares edge with both A and B, then T contains v₁.
The adaptive selection for B ALWAYS includes an edge from v₁ or v₂.
So bridges at A-B are covered by B's edges (or A's if A's selection includes v₁).
-/

-- Bridge at A-B contains shared vertex v₁
lemma bridge_AB_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (v₁ : V) (hAB : A ∩ B = {v₁})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTA : (T ∩ A).card ≥ 2) (hTB : (T ∩ B).card ≥ 2) :
    v₁ ∈ T := by
  by_contra hv1_not
  -- T ∩ A ⊆ A \ {v₁} and T ∩ B ⊆ B \ {v₁}
  -- These are disjoint since A ∩ B = {v₁}
  have h_disj : Disjoint (T ∩ (A \ {v₁})) (T ∩ (B \ {v₁})) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hxA : x ∈ A := mem_of_mem_inter_right hx1 |> mem_sdiff.mp |>.1
    have hxB : x ∈ B := mem_of_mem_inter_right hx2 |> mem_sdiff.mp |>.1
    have hx_inter : x ∈ A ∩ B := mem_inter.mpr ⟨hxA, hxB⟩
    rw [hAB] at hx_inter
    simp at hx_inter
    have hx_not_v1 : x ≠ v₁ := mem_sdiff.mp (mem_of_mem_inter_right hx1) |>.2 |> not_mem_singleton.mp
    exact hx_not_v1 hx_inter
  -- T ∩ A = T ∩ (A \ {v₁}) since v₁ ∉ T
  have hTA_eq : T ∩ A = T ∩ (A \ {v₁}) := by
    ext x
    simp only [mem_inter, mem_sdiff, mem_singleton]
    constructor
    · intro ⟨hxT, hxA⟩
      refine ⟨⟨hxT, hxA⟩, ?_⟩
      intro hx_eq
      rw [hx_eq] at hxT
      exact hv1_not hxT
    · intro ⟨⟨hxT, hxA⟩, _⟩
      exact ⟨hxT, hxA⟩
  have hTB_eq : T ∩ B = T ∩ (B \ {v₁}) := by
    ext x
    simp only [mem_inter, mem_sdiff, mem_singleton]
    constructor
    · intro ⟨hxT, hxB⟩
      refine ⟨⟨hxT, hxB⟩, ?_⟩
      intro hx_eq
      rw [hx_eq] at hxT
      exact hv1_not hxT
    · intro ⟨⟨hxT, hxB⟩, _⟩
      exact ⟨hxT, hxB⟩
  -- Now we have disjoint sets both with cardinality ≥ 2, inside T which has cardinality 3
  rw [hTA_eq] at hTA
  rw [hTB_eq] at hTB
  have h_union_sub : T ∩ (A \ {v₁}) ∪ T ∩ (B \ {v₁}) ⊆ T := by
    intro x hx
    rcases mem_union.mp hx with h | h
    · exact mem_of_mem_inter_left h
    · exact mem_of_mem_inter_left h
  have h_card : (T ∩ (A \ {v₁}) ∪ T ∩ (B \ {v₁})).card ≤ T.card := card_le_card h_union_sub
  rw [card_union_of_disjoint h_disj] at h_card
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT
    exact hT.1.card_eq
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. For each E ∈ M, apply exists_two_edges_cover_Se to get 2 edges covering E and S_e
2. Bridges contain spine vertices, so covered by adjacent element's edges
3. Total: 4 × 2 = 8 edges
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2)
    (A B C D : Finset V) (hM_eq : M = {A, B, C, D})
    (v₁ v₂ v₃ : V)
    (hAB : A ∩ B = {v₁}) (hBC : B ∩ C = {v₂}) (hCD : C ∩ D = {v₃})
    (hAC : A ∩ C = ∅) (hAD : A ∩ D = ∅) (hBD : B ∩ D = ∅) :
    ∃ (cover : Finset (Sym2 V)), cover.card ≤ 8 ∧
      cover ⊆ G.edgeFinset ∧
      (∀ T ∈ G.cliqueFinset 3, ∃ e ∈ cover, e ∈ T.sym2) := by
  -- For each M-element, get its 2 adaptive covering edges
  -- Then show the union covers all triangles

  -- The full proof requires:
  -- 1. Extracting vertex labels for each M-element
  -- 2. Applying exists_two_edges_cover_Se to each
  -- 3. Showing bridges are covered via spine vertices
  -- 4. Union all edges

  sorry

end
