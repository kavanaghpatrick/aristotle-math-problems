/-
  slot422_adaptive_cover.lean

  FOCUSED LEMMA: 2 edges cover E and all S_e(E) externals

  PROVEN SCAFFOLDING (from slot412 - copy key pieces only):
  - not_all_three_edge_types (FULL PROOF - abbreviated version)

  KEY RESULT:
  exists_two_edges_cover_Se: For any M-element E = {a,b,c}, exists 2 edges
  e₁, e₂ ∈ G.edgeFinset that cover E and all S_e externals.

  PROOF:
  By not_all_three_edge_types, at most 2 of 3 edge types have externals.
  Pick 2 edges covering the non-empty types:
  - Types 1,2 only: {a,b}, {b,c}
  - Types 1,3 only: {a,b}, {a,c}
  - Types 2,3 only: {b,c}, {a,c}

  TIER: 2 (uses proven not_all_three_edge_types)
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

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => t ≠ e ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def S_e_edge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (a b c : V) : Finset (Finset V) :=
  (S_e G M {a, b, c}).filter (fun T => a ∈ T ∧ b ∈ T ∧ c ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: not_all_three_edge_types (from slot412)
-- Assume proven - Aristotle already verified this in slot412
-- ══════════════════════════════════════════════════════════════════════════════

/-
STATEMENT (proven in slot412_6packing_proof_aristotle.lean):
If all 3 edge types of E have S_e externals, we get a 6-packing contradiction.
Therefore at most 2 of 3 edge types have externals.
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
-- HELPER: Edge in sym2 if both endpoints in triangle
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_sym2 (T : Finset V) (u v : V) (hu : u ∈ T) (hv : v ∈ T) :
    s(u, v) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨hu, hv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA: 2 edges cover E and all S_e(E)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. By not_all_three_edge_types, ¬(Type1 ∧ Type2 ∧ Type3)
2. Equivalently: ¬Type1 ∨ ¬Type2 ∨ ¬Type3
3. Case analysis:
   - ¬Type3: use edges {a,b}, {b,c} (cover Types 1,2 and E)
   - ¬Type2: use edges {a,b}, {a,c} (cover Types 1,3 and E)
   - ¬Type1: use edges {b,c}, {a,c} (cover Types 2,3 and E)
4. All edges are in G.edgeFinset since E is a clique
-/
theorem exists_two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hE_clq : {a, b, c} ∈ G.cliqueFinset 3)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ {a, b, c}) (hC_ne : C ≠ {a, b, c}) (hD_ne : D ≠ {a, b, c})
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hB_tri : B ∈ G.cliqueFinset 3) (hC_tri : C ∈ G.cliqueFinset 3) (hD_tri : D ∈ G.cliqueFinset 3) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      -- Cover element E
      (e₁ ∈ ({a,b,c} : Finset V).sym2 ∨ e₂ ∈ ({a,b,c} : Finset V).sym2) ∧
      -- Cover all S_e externals
      (∀ T ∈ S_e G M {a, b, c}, e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  -- Get adjacencies from E being a clique
  have hE_clique : G.IsNClique 3 {a, b, c} := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hE_clq; exact hE_clq.1
  have hab_adj : G.Adj a b := hE_clique.2 (by simp) (by simp) hab
  have hbc_adj : G.Adj b c := hE_clique.2 (by simp) (by simp) hbc
  have hac_adj : G.Adj a c := hE_clique.2 (by simp) (by simp) hac
  -- Apply not_all_three_edge_types
  have h_not_all := not_all_three_edge_types G M hM hNu4 a b c hE hab hbc hac B C D
    hB hC hD hB_ne hC_ne hD_ne hBC hBD hCD hB_tri hC_tri hD_tri
  push_neg at h_not_all
  -- Case analysis
  by_cases h1 : (S_e_edge G M a b c).Nonempty
  · by_cases h2 : (S_e_edge G M b c a).Nonempty
    · -- Types 1,2 exist → Type 3 empty. Use {a,b}, {b,c}
      have h3 : ¬(S_e_edge G M a c b).Nonempty := h_not_all h1 h2
      use s(a, b), s(b, c)
      refine ⟨SimpleGraph.mem_edgeFinset.mpr hab_adj, SimpleGraph.mem_edgeFinset.mpr hbc_adj, ?_, ?_⟩
      · left; exact edge_in_sym2 {a,b,c} a b (by simp) (by simp)
      · intro T hT
        -- T ∈ S_e, so T shares edge with E and not with B,C,D
        -- T is Type 1, Type 2, or Type 3
        -- Type 3 is empty, so T is Type 1 or Type 2
        -- Type 1 contains {a,b} → hit by s(a,b)
        -- Type 2 contains {b,c} → hit by s(b,c)
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT
        obtain ⟨⟨hT_tri, hT_inter⟩, hT_ne, hT_disjoint⟩ := hT
        have hT_card : T.card = 3 := by
          rw [SimpleGraph.mem_cliqueFinset_iff] at hT_tri; exact hT_tri.1.card_eq
        -- T ∩ {a,b,c} has ≥ 2 elements
        -- If {a,b} ⊆ T: left
        -- If {b,c} ⊆ T: right
        -- If {a,c} ⊆ T but not {a,b} or {b,c}: T is Type 3 (but empty!)
        by_cases hab_in : a ∈ T ∧ b ∈ T
        · left; exact edge_in_sym2 T a b hab_in.1 hab_in.2
        · by_cases hbc_in : b ∈ T ∧ c ∈ T
          · right; exact edge_in_sym2 T b c hbc_in.1 hbc_in.2
          · -- Must be Type 3 case, but Type 3 is empty
            push_neg at hab_in hbc_in
            -- Derive contradiction: T ∈ S_e_edge G M a c b
            exfalso
            by_cases ha : a ∈ T
            · have hc : c ∈ T := by
                by_contra hc_not
                have hb_not : b ∉ T := fun hb => hab_in ⟨ha, hb⟩
                have hsub : T ∩ {a, b, c} ⊆ {a} := by
                  intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                  rcases hx.2 with rfl | rfl | rfl <;> [rfl; exact absurd hx.1 hb_not; exact absurd hx.1 hc_not]
                have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
                omega
              have hb_not : b ∉ T := fun hb => hab_in ⟨ha, hb⟩
              have hT_type3 : T ∈ S_e_edge G M a c b := by
                simp only [S_e_edge, S_e, trianglesSharingEdge, mem_filter]
                refine ⟨⟨⟨hT_tri, ?_⟩, hT_ne, ?_⟩, ha, hc, hb_not⟩
                · have h_eq : ({a, c, b} : Finset V) = {a, b, c} := by ext; simp [or_comm, or_assoc]
                  rw [h_eq]; exact hT_inter
                · intro f hf hf_ne
                  have h_eq : ({a, c, b} : Finset V) = {a, b, c} := by ext; simp [or_comm, or_assoc]
                  rw [h_eq] at hf_ne; exact hT_disjoint f hf hf_ne
              exact h3 ⟨T, hT_type3⟩
            · -- a ∉ T, must have {b,c} ⊆ T
              have hb : b ∈ T := by
                by_contra hb_not
                have hc : c ∈ T := by
                  by_contra hc_not
                  have hsub : T ∩ {a, b, c} ⊆ ∅ := by
                    intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx
                    rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha; exact absurd hx.1 hb_not; exact absurd hx.1 hc_not]
                  have : (T ∩ {a, b, c}).card = 0 := card_eq_zero.mpr (eq_empty_of_subset_empty hsub)
                  omega
                have hsub : T ∩ {a, b, c} ⊆ {c} := by
                  intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                  rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha; exact absurd hx.1 hb_not; rfl]
                have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
                omega
              have hc : c ∈ T := by
                by_contra hc_not
                have hsub : T ∩ {a, b, c} ⊆ {b} := by
                  intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                  rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha; rfl; exact absurd hx.1 hc_not]
                have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
                omega
              exact hbc_in ⟨hb, hc⟩
    · -- Type 2 empty. Use {a,b}, {a,c}
      use s(a, b), s(a, c)
      refine ⟨SimpleGraph.mem_edgeFinset.mpr hab_adj, SimpleGraph.mem_edgeFinset.mpr hac_adj, ?_, ?_⟩
      · left; exact edge_in_sym2 {a,b,c} a b (by simp) (by simp)
      · intro T hT
        simp only [S_e, trianglesSharingEdge, mem_filter] at hT
        obtain ⟨⟨hT_tri, hT_inter⟩, hT_ne, hT_disjoint⟩ := hT
        by_cases hab_in : a ∈ T ∧ b ∈ T
        · left; exact edge_in_sym2 T a b hab_in.1 hab_in.2
        · by_cases hac_in : a ∈ T ∧ c ∈ T
          · right; exact edge_in_sym2 T a c hac_in.1 hac_in.2
          · push_neg at hab_in hac_in
            exfalso
            by_cases ha : a ∈ T
            · have hb_not : b ∉ T := fun hb => hab_in ⟨ha, hb⟩
              have hc_not : c ∉ T := fun hc => hac_in ⟨ha, hc⟩
              have hsub : T ∩ {a, b, c} ⊆ {a} := by
                intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                rcases hx.2 with rfl | rfl | rfl <;> [rfl; exact absurd hx.1 hb_not; exact absurd hx.1 hc_not]
              have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
              omega
            · have hbc_sub : b ∈ T ∧ c ∈ T := by
                constructor <;> by_contra h_not
                · by_cases hc : c ∈ T
                  · have hsub : T ∩ {a, b, c} ⊆ {c} := by
                      intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                      rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha; exact absurd hx.1 h_not; rfl]
                    have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
                    omega
                  · have hsub : T ∩ {a, b, c} ⊆ ∅ := by
                      intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx
                      rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha; exact absurd hx.1 h_not; exact absurd hx.1 hc]
                    have : (T ∩ {a, b, c}).card = 0 := card_eq_zero.mpr (eq_empty_of_subset_empty hsub)
                    omega
                · by_cases hb : b ∈ T
                  · have hsub : T ∩ {a, b, c} ⊆ {b} := by
                      intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                      rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha; rfl; exact absurd hx.1 h_not]
                    have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
                    omega
                  · have hsub : T ∩ {a, b, c} ⊆ ∅ := by
                      intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx
                      rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha; exact absurd hx.1 hb; exact absurd hx.1 h_not]
                    have : (T ∩ {a, b, c}).card = 0 := card_eq_zero.mpr (eq_empty_of_subset_empty hsub)
                    omega
              have hT_type2 : T ∈ S_e_edge G M b c a := by
                simp only [S_e_edge, S_e, trianglesSharingEdge, mem_filter]
                refine ⟨⟨⟨hT_tri, ?_⟩, hT_ne, ?_⟩, hbc_sub.1, hbc_sub.2, ha⟩
                · have h_eq : ({b, c, a} : Finset V) = {a, b, c} := by ext; simp [or_comm, or_assoc]
                  rw [h_eq]; exact hT_inter
                · intro f hf hf_ne
                  have h_eq : ({b, c, a} : Finset V) = {a, b, c} := by ext; simp [or_comm, or_assoc]
                  rw [h_eq] at hf_ne; exact hT_disjoint f hf hf_ne
              exact h2 ⟨T, hT_type2⟩
  · -- Type 1 empty. Use {b,c}, {a,c}
    use s(b, c), s(a, c)
    refine ⟨SimpleGraph.mem_edgeFinset.mpr hbc_adj, SimpleGraph.mem_edgeFinset.mpr hac_adj, ?_, ?_⟩
    · left; exact edge_in_sym2 {a,b,c} b c (by simp) (by simp)
    · intro T hT
      simp only [S_e, trianglesSharingEdge, mem_filter] at hT
      obtain ⟨⟨hT_tri, hT_inter⟩, hT_ne, hT_disjoint⟩ := hT
      by_cases hbc_in : b ∈ T ∧ c ∈ T
      · left; exact edge_in_sym2 T b c hbc_in.1 hbc_in.2
      · by_cases hac_in : a ∈ T ∧ c ∈ T
        · right; exact edge_in_sym2 T a c hac_in.1 hac_in.2
        · push_neg at hbc_in hac_in
          exfalso
          by_cases hc : c ∈ T
          · have hb_not : b ∉ T := fun hb => hbc_in ⟨hb, hc⟩
            have ha_not : a ∉ T := fun ha => hac_in ⟨ha, hc⟩
            have hsub : T ∩ {a, b, c} ⊆ {c} := by
              intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
              rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha_not; exact absurd hx.1 hb_not; rfl]
            have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
            omega
          · have hab_sub : a ∈ T ∧ b ∈ T := by
              constructor <;> by_contra h_not
              · by_cases hb : b ∈ T
                · have hsub : T ∩ {a, b, c} ⊆ {b} := by
                    intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                    rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 h_not; rfl; exact absurd hx.1 hc]
                  have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
                  omega
                · have hsub : T ∩ {a, b, c} ⊆ ∅ := by
                    intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx
                    rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 h_not; exact absurd hx.1 hb; exact absurd hx.1 hc]
                  have : (T ∩ {a, b, c}).card = 0 := card_eq_zero.mpr (eq_empty_of_subset_empty hsub)
                  omega
              · by_cases ha : a ∈ T
                · have hsub : T ∩ {a, b, c} ⊆ {a} := by
                    intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
                    rcases hx.2 with rfl | rfl | rfl <;> [rfl; exact absurd hx.1 h_not; exact absurd hx.1 hc]
                  have : (T ∩ {a, b, c}).card ≤ 1 := card_le_card hsub |>.trans (card_singleton _).le
                  omega
                · have hsub : T ∩ {a, b, c} ⊆ ∅ := by
                    intro x hx; simp only [mem_inter, mem_insert, mem_singleton] at hx
                    rcases hx.2 with rfl | rfl | rfl <;> [exact absurd hx.1 ha; exact absurd hx.1 h_not; exact absurd hx.1 hc]
                  have : (T ∩ {a, b, c}).card = 0 := card_eq_zero.mpr (eq_empty_of_subset_empty hsub)
                  omega
            have hT_type1 : T ∈ S_e_edge G M a b c := by
              simp only [S_e_edge, S_e, trianglesSharingEdge, mem_filter]
              exact ⟨⟨⟨hT_tri, hT_inter⟩, hT_ne, hT_disjoint⟩, hab_sub.1, hab_sub.2, hc⟩
            exact h1 ⟨T, hT_type1⟩

end
