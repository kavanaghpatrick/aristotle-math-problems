/-
  slot423: Final Assembly for τ ≤ 8 (PATH_4, ν = 4)

  PROVEN SCAFFOLDING (from previous slots):
  1. slot412: not_all_three_edge_types - at most 2 of 3 edge types have S_e externals
  2. slot422: exists_two_edges_cover_Se - 2 edges cover E and all S_e(E)
  3. slot421: middle_no_base_externals - middle elements have no base externals
  4. slot416: bridge_contains_shared - bridges contain shared vertex

  PROOF STRATEGY:
  - 4 M-elements × 2 edges each = 8 edges total
  - Each E's 2 edges cover E itself and all S_e(E) externals
  - Bridges are covered because they contain spine vertices
  - Every triangle is classified as: M-element, S_e external, or bridge

  TIER: 2 (assembly of proven components)
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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA: Bridge contains shared vertex (from slot416)
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridge_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v : V) (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
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
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT
    exact hT.1.card_eq
  have h_union : (T ∩ E ∪ T ∩ F) ⊆ T := union_subset inter_subset_left inter_subset_left
  have h_card : (T ∩ E ∪ T ∩ F).card ≤ T.card := card_le_card h_union
  rw [card_union_of_disjoint h_disj] at h_card
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA: Edge in sym2 if both endpoints in set
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_sym2 (T : Finset V) (u v : V) (hu : u ∈ T) (hv : v ∈ T) :
    s(u, v) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨hu, hv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA: Middle elements have no base externals (from slot421)
-- ══════════════════════════════════════════════════════════════════════════════

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
-- TRIANGLE CLASSIFICATION LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-
For maximality: every triangle T not in M shares edge with some M-element.
Classification:
1. T ∈ M: covered by M-element's own edges
2. T ∈ S_e(E) for some E: covered by E's 2 edges (exists_two_edges_cover_Se)
3. T is bridge (shares edge with 2+ M-elements): covered by bridge_contains_shared
-/

lemma triangle_classification (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨
    (∃ E ∈ M, T ∈ S_e G M E) ∨
    (∃ E F : Finset V, E ∈ M ∧ F ∈ M ∧ E ≠ F ∧ (T ∩ E).card ≥ 2 ∧ (T ∩ F).card ≥ 2) := by
  by_cases hT_M : T ∈ M
  · left; exact hT_M
  · right
    obtain ⟨E, hE_M, hTE⟩ := hMaximal T hT hT_M
    by_cases h_unique : ∀ F ∈ M, F ≠ E → (T ∩ F).card ≤ 1
    · left; use E, hE_M
      simp only [S_e, trianglesSharingEdge, mem_filter]
      exact ⟨⟨hT, hTE⟩, hT_M, h_unique⟩
    · right
      push_neg at h_unique
      obtain ⟨F, hF_M, hF_ne, hTF⟩ := h_unique
      exact ⟨E, F, hE_M, hF_M, hF_ne, hTE, hTF⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Apply exists_two_edges_cover_Se to each of A, B, C, D → get 2 edges each
2. Union of 8 edges forms the cover
3. For any triangle T:
   - If T ∈ M: hit by its own 2 edges
   - If T ∈ S_e(E): hit by E's 2 edges (by exists_two_edges_cover_Se)
   - If T is bridge at E-F: contains shared vertex v (by bridge_contains_shared)
     Adjacent M-element's 2 edges include one with v (by middle_no_base_externals for middles,
     or by spine-edge selection for endpoints)
-/

theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2)
    -- PATH_4 structure
    (A B C D : Finset V) (hM_eq : M = {A, B, C, D})
    (v₁ v₂ v₃ : V)
    -- Intersection structure
    (hAB : A ∩ B = {v₁}) (hBC : B ∩ C = {v₂}) (hCD : C ∩ D = {v₃})
    (hAC : A ∩ C = ∅) (hAD : A ∩ D = ∅) (hBD : B ∩ D = ∅)
    -- Distinctness
    (hAB_ne : A ≠ B) (hAC_ne : A ≠ C) (hAD_ne : A ≠ D)
    (hBC_ne : B ≠ C) (hBD_ne : B ≠ D) (hCD_ne : C ≠ D)
    -- Clique membership
    (hA_clq : A ∈ G.cliqueFinset 3) (hB_clq : B ∈ G.cliqueFinset 3)
    (hC_clq : C ∈ G.cliqueFinset 3) (hD_clq : D ∈ G.cliqueFinset 3)
    -- Element structure
    (a₂ a₃ b₃ c₃ d₂ d₃ : V)
    (hA_eq : A = {v₁, a₂, a₃}) (hB_eq : B = {v₁, v₂, b₃})
    (hC_eq : C = {v₂, v₃, c₃}) (hD_eq : D = {v₃, d₂, d₃})
    -- Distinctness within elements (required for edge selection)
    (hv₁_a₂ : v₁ ≠ a₂) (hv₁_a₃ : v₁ ≠ a₃) (ha₂_a₃ : a₂ ≠ a₃)
    (hv₁_v₂ : v₁ ≠ v₂) (hv₁_b₃ : v₁ ≠ b₃) (hv₂_b₃ : v₂ ≠ b₃)
    (hv₂_v₃ : v₂ ≠ v₃) (hv₂_c₃ : v₂ ≠ c₃) (hv₃_c₃ : v₃ ≠ c₃)
    (hv₃_d₂ : v₃ ≠ d₂) (hv₃_d₃ : v₃ ≠ d₃) (hd₂_d₃ : d₂ ≠ d₃) :
    ∃ (cover : Finset (Sym2 V)), cover.card ≤ 8 ∧
      cover ⊆ G.edgeFinset ∧
      (∀ T ∈ G.cliqueFinset 3, ∃ e ∈ cover, e ∈ T.sym2) := by
  -- The 8-edge cover: 2 edges from each M-element
  -- A: {s(v₁, a₂), s(v₁, a₃)} - spokes from shared vertex
  -- B: {s(v₁, v₂), s(v₂, b₃)} - spine + spoke covering both shared vertices
  -- C: {s(v₂, v₃), s(v₃, c₃)} - spine + spoke covering both shared vertices
  -- D: {s(v₃, d₂), s(v₃, d₃)} - spokes from shared vertex
  sorry

end
