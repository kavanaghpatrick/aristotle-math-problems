/-
  slot422_two_real_edges_cover.lean

  CRITICAL FIX: The previous exists_two_edges_cover_Se used SELF-LOOPS (s(w,w))
  which are NOT valid graph edges. This version requires ACTUAL EDGES.

  KEY INSIGHT: By not_all_three_edge_types, at most 2 of 3 edge types have S_e externals.
  So we only need 2 edges to cover all S_e externals.

  For E = {a,b,c}, the S_e externals partition into:
  - S_e^{a,b}: triangles containing a,b but not c (covered by edge s(a,b))
  - S_e^{b,c}: triangles containing b,c but not a (covered by edge s(b,c))
  - S_e^{a,c}: triangles containing a,c but not b (covered by edge s(a,c))

  Since at most 2 groups are nonempty, 2 edges suffice.

  TIER: 2 (depends on not_all_three_edge_types)
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

/-- S_e elements using specific edge {a,b} of E = {a,b,c} -/
def S_e_edge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (a b c : V) : Finset (Finset V) :=
  (S_e G M {a, b, c}).filter (fun T => a ∈ T ∧ b ∈ T ∧ c ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Triangle edges are in G.edgeFinset
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_edge_mem_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset V) (hE : E ∈ G.cliqueFinset 3)
    (a b : V) (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) :
    s(a, b) ∈ G.edgeFinset := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at hE
  have hclique := hE.1
  rw [SimpleGraph.isClique_iff] at hclique
  have hadj : G.Adj a b := hclique ha hb hab
  simp only [SimpleGraph.mem_edgeFinset]
  exact hadj

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Edge covers triangle if both endpoints in triangle
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_covers_triangle (T : Finset V) (a b : V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: S_e external structure
-- ══════════════════════════════════════════════════════════════════════════════

/-- An S_e external shares exactly one of the 3 edge-pairs with E -/
lemma Se_external_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (T : Finset V) (hT : T ∈ S_e G M {a, b, c}) :
    (a ∈ T ∧ b ∈ T) ∨ (b ∈ T ∧ c ∈ T) ∨ (a ∈ T ∧ c ∈ T) := by
  simp only [S_e, trianglesSharingEdge, mem_filter] at hT
  obtain ⟨⟨_, hinter⟩, _, _⟩ := hT
  -- T ∩ {a,b,c} has ≥ 2 elements
  have hT_card : T.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset_iff] at hT
    exact hT.1.1.2
  -- So at least 2 of {a,b,c} are in T
  by_contra h_none
  push_neg at h_none
  obtain ⟨h1, h2, h3⟩ := h_none
  -- Case analysis: which elements are in T?
  have h_sub : T ∩ {a, b, c} ⊆ {a, b, c} := inter_subset_right
  have h_card_le : (T ∩ {a, b, c}).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    simp only [mem_inter, mem_insert, mem_singleton] at hx hy
    rcases hx.2 with rfl | rfl | rfl <;> rcases hy.2 with rfl | rfl | rfl
    all_goals first | rfl | (exfalso; exact h1 ⟨hx.1, hy.1⟩) |
                           (exfalso; exact h2 ⟨hx.1, hy.1⟩) |
                           (exfalso; exact h2 ⟨hy.1, hx.1⟩) |
                           (exfalso; exact h3 ⟨hx.1, hy.1⟩) |
                           (exfalso; exact h3 ⟨hy.1, hx.1⟩)
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Two REAL edges cover E + S_e
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. For E = {a,b,c}, S_e partitions into S_e^{a,b}, S_e^{b,c}, S_e^{a,c}
2. By not_all_three_edge_types (slot412), at most 2 groups are nonempty
3. Case split on which group is empty:
   - S_e^{a,b} empty → use {s(b,c), s(a,c)}
   - S_e^{b,c} empty → use {s(a,b), s(a,c)}
   - S_e^{a,c} empty → use {s(a,b), s(b,c)}
4. These are REAL edges (E is a clique, so all pairs are adjacent)
5. Any 2 edges of a triangle cover the triangle
6. Each edge covers its corresponding S_e subset
-/

theorem exists_two_real_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (E : Finset V) (hE : E ∈ M)
    (a b c : V) (hE_eq : E = {a, b, c}) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    -- Other M-elements for the 6-packing argument
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ E) (hC_ne : C ≠ E) (hD_ne : D ≠ E)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hB_tri : B ∈ G.cliqueFinset 3) (hC_tri : C ∈ G.cliqueFinset 3) (hD_tri : D ∈ G.cliqueFinset 3) :
    ∃ Cover : Finset (Sym2 V),
      Cover ⊆ G.edgeFinset ∧
      Cover.card ≤ 2 ∧
      (∀ T ∈ insert E (S_e G M E), ∃ e ∈ Cover, e ∈ T.sym2) := by
  -- E is a triangle, so all its edges are in G.edgeFinset
  have hE_clique : E ∈ G.cliqueFinset 3 := hM.1 hE
  have hab_edge : s(a, b) ∈ G.edgeFinset := by
    apply triangle_edge_mem_edgeFinset G E hE_clique a b
    · rw [hE_eq]; simp
    · rw [hE_eq]; simp
    · exact hab
  have hbc_edge : s(b, c) ∈ G.edgeFinset := by
    apply triangle_edge_mem_edgeFinset G E hE_clique b c
    · rw [hE_eq]; simp
    · rw [hE_eq]; simp
    · exact hbc
  have hac_edge : s(a, c) ∈ G.edgeFinset := by
    apply triangle_edge_mem_edgeFinset G E hE_clique a c
    · rw [hE_eq]; simp
    · rw [hE_eq]; simp
    · exact hac
  -- At most 2 of 3 edge types have externals (by 6-packing contradiction)
  have h_not_all_three : ¬((S_e_edge G M a b c).Nonempty ∧
                           (S_e_edge G M b c a).Nonempty ∧
                           (S_e_edge G M a c b).Nonempty) := by
    intro ⟨⟨T1, hT1⟩, ⟨T2, hT2⟩, ⟨T3, hT3⟩⟩
    -- This would give a 6-packing: {T1, T2, T3, B, C, D}
    -- Contradicting ν = 4
    -- (Full proof in slot412)
    sorry -- Uses not_all_three_edge_types from slot412
  -- Case split on which edge type is empty
  push_neg at h_not_all_three
  rcases h_not_all_three with h_ab_empty | h_bc_empty | h_ac_empty
  -- Case 1: S_e^{a,b} is empty - use {s(b,c), s(a,c)}
  · use {s(b, c), s(a, c)}
    refine ⟨?_, ?_, ?_⟩
    · -- Subset of G.edgeFinset
      intro e he
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl <;> assumption
    · -- Card ≤ 2
      simp only [card_insert_of_not_mem, card_singleton]
      · omega
      · simp only [mem_singleton, Sym2.eq_iff]
        push_neg; constructor <;> intro h
        · exact hbc h.symm
        · exact hac.symm h.1
    · -- Covers E and all S_e
      intro T hT
      simp only [mem_insert] at hT
      rcases hT with rfl | hT_Se
      · -- T = E: use s(b,c)
        use s(b, c)
        simp only [mem_insert, true_or, and_true]
        rw [hE_eq]
        apply edge_covers_triangle
        · simp
        · simp
      · -- T ∈ S_e: determine which edge pair T uses
        rw [hE_eq] at hT_Se
        have h_shares := Se_external_shares_edge G M a b c hab hbc hac T hT_Se
        rcases h_shares with ⟨ha_T, hb_T⟩ | ⟨hb_T, hc_T⟩ | ⟨ha_T, hc_T⟩
        · -- T uses {a,b} - but S_e^{a,b} is empty!
          exfalso
          apply h_ab_empty
          -- T is in S_e_edge G M a b c
          simp only [S_e_edge, mem_filter]
          refine ⟨hT_Se, ha_T, hb_T, ?_⟩
          -- Need: c ∉ T
          simp only [S_e, trianglesSharingEdge, mem_filter] at hT_Se
          obtain ⟨⟨hT_clique, _⟩, hT_ne, _⟩ := hT_Se
          have hT_card : T.card = 3 := by
            rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clique
            exact hT_clique.2
          intro hc_T
          -- If a,b,c ∈ T and T.card = 3, then T = {a,b,c} = E
          have hT_eq : T = {a, b, c} := by
            apply eq_of_subset_of_card_le
            · intro x hx
              simp only [mem_insert, mem_singleton] at hx
              rcases hx with rfl | rfl | rfl <;> assumption
            · rw [hT_card]
              rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
              · simp [hbc]
              · simp [hab, hac]
          exact hT_ne hT_eq
        · -- T uses {b,c} - covered by s(b,c)
          use s(b, c)
          simp only [mem_insert, true_or, and_true]
          exact edge_covers_triangle T b c hb_T hc_T
        · -- T uses {a,c} - covered by s(a,c)
          use s(a, c)
          simp only [mem_insert, mem_singleton, or_true, and_true]
          exact edge_covers_triangle T a c ha_T hc_T
  -- Case 2: S_e^{b,c} is empty - use {s(a,b), s(a,c)}
  · use {s(a, b), s(a, c)}
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl <;> assumption
    · simp only [card_insert_of_not_mem, card_singleton]
      · omega
      · simp only [mem_singleton, Sym2.eq_iff]
        push_neg; constructor <;> intro h
        · exact hab h.1
        · exact hac h.1
    · intro T hT
      simp only [mem_insert] at hT
      rcases hT with rfl | hT_Se
      · use s(a, b)
        simp only [mem_insert, true_or, and_true]
        rw [hE_eq]
        apply edge_covers_triangle <;> simp
      · rw [hE_eq] at hT_Se
        have h_shares := Se_external_shares_edge G M a b c hab hbc hac T hT_Se
        rcases h_shares with ⟨ha_T, hb_T⟩ | ⟨hb_T, hc_T⟩ | ⟨ha_T, hc_T⟩
        · use s(a, b)
          simp only [mem_insert, true_or, and_true]
          exact edge_covers_triangle T a b ha_T hb_T
        · -- T uses {b,c} - but S_e^{b,c} is empty!
          exfalso
          apply h_bc_empty
          simp only [S_e_edge, mem_filter]
          refine ⟨?_, hb_T, hc_T, ?_⟩
          · -- S_e G M {b,c,a} = S_e G M {a,b,c} (set equality)
            simp only [S_e, trianglesSharingEdge, mem_filter] at hT_Se ⊢
            have h_eq : ({b, c, a} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
            rw [h_eq]
            exact hT_Se
          · -- a ∉ T
            simp only [S_e, trianglesSharingEdge, mem_filter] at hT_Se
            obtain ⟨⟨hT_clique, _⟩, hT_ne, _⟩ := hT_Se
            have hT_card : T.card = 3 := by
              rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clique
              exact hT_clique.2
            intro ha_T
            have hT_eq : T = {a, b, c} := by
              apply eq_of_subset_of_card_le
              · intro x hx
                simp only [mem_insert, mem_singleton] at hx
                rcases hx with rfl | rfl | rfl <;> assumption
              · rw [hT_card]
                rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
                · simp [hbc]
                · simp [hab, hac]
            exact hT_ne hT_eq
        · use s(a, c)
          simp only [mem_insert, mem_singleton, or_true, and_true]
          exact edge_covers_triangle T a c ha_T hc_T
  -- Case 3: S_e^{a,c} is empty - use {s(a,b), s(b,c)}
  · use {s(a, b), s(b, c)}
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl <;> assumption
    · simp only [card_insert_of_not_mem, card_singleton]
      · omega
      · simp only [mem_singleton, Sym2.eq_iff]
        push_neg; constructor <;> intro h
        · exact hab h.1
        · exact hbc.symm h.2
    · intro T hT
      simp only [mem_insert] at hT
      rcases hT with rfl | hT_Se
      · use s(a, b)
        simp only [mem_insert, true_or, and_true]
        rw [hE_eq]
        apply edge_covers_triangle <;> simp
      · rw [hE_eq] at hT_Se
        have h_shares := Se_external_shares_edge G M a b c hab hbc hac T hT_Se
        rcases h_shares with ⟨ha_T, hb_T⟩ | ⟨hb_T, hc_T⟩ | ⟨ha_T, hc_T⟩
        · use s(a, b)
          simp only [mem_insert, true_or, and_true]
          exact edge_covers_triangle T a b ha_T hb_T
        · use s(b, c)
          simp only [mem_insert, mem_singleton, or_true, and_true]
          exact edge_covers_triangle T b c hb_T hc_T
        · -- T uses {a,c} - but S_e^{a,c} is empty!
          exfalso
          apply h_ac_empty
          simp only [S_e_edge, mem_filter]
          refine ⟨?_, ha_T, hc_T, ?_⟩
          · simp only [S_e, trianglesSharingEdge, mem_filter] at hT_Se ⊢
            have h_eq : ({a, c, b} : Finset V) = {a, b, c} := by ext x; simp [or_comm, or_assoc]
            rw [h_eq]
            exact hT_Se
          · simp only [S_e, trianglesSharingEdge, mem_filter] at hT_Se
            obtain ⟨⟨hT_clique, _⟩, hT_ne, _⟩ := hT_Se
            have hT_card : T.card = 3 := by
              rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clique
              exact hT_clique.2
            intro hb_T
            have hT_eq : T = {a, b, c} := by
              apply eq_of_subset_of_card_le
              · intro x hx
                simp only [mem_insert, mem_singleton] at hx
                rcases hx with rfl | rfl | rfl <;> assumption
              · rw [hT_card]
                rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
                · simp [hbc]
                · simp [hab, hac]
            exact hT_ne hT_eq

end
