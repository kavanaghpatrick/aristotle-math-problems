/-
  slot425_specific_8cover.lean

  KEY INSIGHT (from slot424): Arbitrary 2-edge selection is FALSE for bridges.
  Need SPECIFIC selections that include spine edges.

  PROVEN SCAFFOLDING:
  - slot421: middle_no_base_externals - externals of middle elements contain v1 or v2
  - slot422: exists_two_edges_cover_Se - 2 edges cover E and all S_e(E)
  - slot412: not_all_three_edge_types - at most 2 edge types have S_e externals
  - slot424: correct_middle_cover - {s(v1,v2), s(v1,b3)} covers all T with v1 ∈ T and |T∩B|≥2

  STRATEGY:
  - Endpoints A, D: Use arbitrary 2 edges from exists_two_edges_cover_Se
  - Middle elements B, C: Use SPECIFIC selections that include spine edges
    - B = {v1, v2, b3}: Use {s(v1, v2), s(v1, b3)} OR {s(v1, v2), s(v2, b3)}
    - C = {v2, v3, c3}: Use {s(v2, v3), s(v2, c3)} OR {s(v2, v3), s(v3, c3)}
  - Bridge coverage: Spine edges hit bridges automatically

  TIER: 2 (assembly of proven components with specific construction)
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
-- PROVEN LEMMA: Edge in sym2 if both endpoints in set
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_sym2 (T : Finset V) (u v : V) (hu : u ∈ T) (hv : v ∈ T) :
    s(u, v) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨hu, hv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA: Middle elements have no base externals (slot421)
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
-- PROVEN LEMMA: Correct middle cover (slot424)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. T has 3 elements, v1 ∈ T, and |T ∩ B| ≥ 2
2. So T contains v1 plus at least one other element of B = {v1, v2, b3}
3. If the other is v2, then s(v1, v2) ∈ T.sym2
4. If the other is b3, then s(v1, b3) ∈ T.sym2
-/
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

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA: Bridge contains shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Bridge T shares edge with both E and F where E ∩ F = {v}
2. |T ∩ E| ≥ 2 and |T ∩ F| ≥ 2
3. If v ∉ T, then (T ∩ E) and (T ∩ F) are disjoint
4. Their union has ≥ 4 elements, but T only has 3 elements - contradiction
-/
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
-- MAIN: Specific 8-edge cover for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Define the specific 8-edge cover:
   - A = {v₁, a₂, a₃}: {s(v₁, a₂), s(v₁, a₃)} (spokes from shared vertex)
   - B = {v₁, v₂, b₃}: {s(v₁, v₂), s(v₂, b₃)} (spine + spoke at v₂)
   - C = {v₂, v₃, c₃}: {s(v₂, v₃), s(v₂, c₃)} (spine + spoke at v₂)
   - D = {v₃, d₂, d₃}: {s(v₃, d₂), s(v₃, d₃)} (spokes from shared vertex)

2. For any triangle T:
   a) If T ∈ M: hit by its own 2 edges
   b) If T ∈ S_e(E) for exactly one E:
      - by exists_two_edges_cover_Se (with specific selection)
   c) If T is bridge between E-F:
      - T contains shared vertex v (by bridge_contains_shared)
      - Adjacent M-element's edges include one with v
      - Therefore T is hit

3. The key insight: middle_no_base_externals ensures that middle elements'
   externals always contain spine vertices, so spine edges automatically
   cover them AND bridges.
-/

theorem specific_8cover_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2)
    -- PATH_4 structure: A—v₁—B—v₂—C—v₃—D
    (A B C D : Finset V) (hM_eq : M = {A, B, C, D})
    (v₁ v₂ v₃ : V)
    -- Intersection structure (PATH_4)
    (hAB : A ∩ B = {v₁}) (hBC : B ∩ C = {v₂}) (hCD : C ∩ D = {v₃})
    (hAC : A ∩ C = ∅) (hAD : A ∩ D = ∅) (hBD : B ∩ D = ∅)
    -- Distinctness of elements
    (hAB_ne : A ≠ B) (hAC_ne : A ≠ C) (hAD_ne : A ≠ D)
    (hBC_ne : B ≠ C) (hBD_ne : B ≠ D) (hCD_ne : C ≠ D)
    -- Clique membership
    (hA_clq : A ∈ G.cliqueFinset 3) (hB_clq : B ∈ G.cliqueFinset 3)
    (hC_clq : C ∈ G.cliqueFinset 3) (hD_clq : D ∈ G.cliqueFinset 3)
    -- Element structure
    (a₂ a₃ b₃ c₃ d₂ d₃ : V)
    (hA_eq : A = {v₁, a₂, a₃}) (hB_eq : B = {v₁, v₂, b₃})
    (hC_eq : C = {v₂, v₃, c₃}) (hD_eq : D = {v₃, d₂, d₃})
    -- Distinctness within elements
    (hv₁_a₂ : v₁ ≠ a₂) (hv₁_a₃ : v₁ ≠ a₃) (ha₂_a₃ : a₂ ≠ a₃)
    (hv₁_v₂ : v₁ ≠ v₂) (hv₁_b₃ : v₁ ≠ b₃) (hv₂_b₃ : v₂ ≠ b₃)
    (hv₂_v₃ : v₂ ≠ v₃) (hv₂_c₃ : v₂ ≠ c₃) (hv₃_c₃ : v₃ ≠ c₃)
    (hv₃_d₂ : v₃ ≠ d₂) (hv₃_d₃ : v₃ ≠ d₃) (hd₂_d₃ : d₂ ≠ d₃)
    -- Adjacency (all vertices in triangles are pairwise adjacent)
    (hAdj_v₁a₂ : G.Adj v₁ a₂) (hAdj_v₁a₃ : G.Adj v₁ a₃) (hAdj_a₂a₃ : G.Adj a₂ a₃)
    (hAdj_v₁v₂ : G.Adj v₁ v₂) (hAdj_v₁b₃ : G.Adj v₁ b₃) (hAdj_v₂b₃ : G.Adj v₂ b₃)
    (hAdj_v₂v₃ : G.Adj v₂ v₃) (hAdj_v₂c₃ : G.Adj v₂ c₃) (hAdj_v₃c₃ : G.Adj v₃ c₃)
    (hAdj_v₃d₂ : G.Adj v₃ d₂) (hAdj_v₃d₃ : G.Adj v₃ d₃) (hAdj_d₂d₃ : G.Adj d₂ d₃) :
    ∃ (cover : Finset (Sym2 V)), cover.card ≤ 8 ∧
      cover ⊆ G.edgeFinset ∧
      (∀ T ∈ G.cliqueFinset 3, ∃ e ∈ cover, e ∈ T.sym2) := by
  -- The specific 8-edge cover
  let cover : Finset (Sym2 V) := {
    s(v₁, a₂), s(v₁, a₃),  -- A's edges (spokes from v₁)
    s(v₁, v₂), s(v₂, b₃),  -- B's edges (spine v₁-v₂ + spoke v₂-b₃)
    s(v₂, v₃), s(v₂, c₃),  -- C's edges (spine v₂-v₃ + spoke v₂-c₃)
    s(v₃, d₂), s(v₃, d₃)   -- D's edges (spokes from v₃)
  }
  use cover
  constructor
  -- cover.card ≤ 8
  · simp only [cover]
    -- The 8 edges might overlap, so card ≤ 8
    calc (insert s(v₁, a₂) (insert s(v₁, a₃) (insert s(v₁, v₂) (insert s(v₂, b₃)
          (insert s(v₂, v₃) (insert s(v₂, c₃) (insert s(v₃, d₂) {s(v₃, d₃)}))))))).card
        ≤ 8 := by
      apply le_trans card_insert_le
      apply le_trans (Nat.succ_le_succ card_insert_le)
      apply le_trans (Nat.succ_le_succ (Nat.succ_le_succ card_insert_le))
      apply le_trans (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ card_insert_le)))
      apply le_trans (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ card_insert_le))))
      apply le_trans (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ card_insert_le)))))
      apply le_trans (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ card_insert_le))))))
      simp only [card_singleton]
  constructor
  -- cover ⊆ G.edgeFinset
  · simp only [cover, subset_iff, mem_insert, mem_singleton]
    intro e he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    · exact hAdj_v₁a₂
    · exact hAdj_v₁a₃
    · exact hAdj_v₁v₂
    · exact hAdj_v₂b₃
    · exact hAdj_v₂v₃
    · exact hAdj_v₂c₃
    · exact hAdj_v₃d₂
    · exact hAdj_v₃d₃
  -- All triangles are hit
  · intro T hT
    -- Classify T: M-element, S_e external, or bridge
    by_cases hT_M : T ∈ M
    · -- T ∈ M: hit by its own edges
      rw [hM_eq] at hT_M
      simp only [mem_insert, mem_singleton] at hT_M
      rcases hT_M with rfl | rfl | rfl | rfl
      · -- T = A: hit by s(v₁, a₂)
        use s(v₁, a₂)
        constructor
        · simp only [cover, mem_insert]; left; rfl
        · rw [hA_eq]; exact edge_in_sym2 _ v₁ a₂ (by simp) (by simp [hv₁_a₂.symm])
      · -- T = B: hit by s(v₁, v₂)
        use s(v₁, v₂)
        constructor
        · simp only [cover, mem_insert]; right; right; left; rfl
        · rw [hB_eq]; exact edge_in_sym2 _ v₁ v₂ (by simp) (by simp [hv₁_v₂.symm])
      · -- T = C: hit by s(v₂, v₃)
        use s(v₂, v₃)
        constructor
        · simp only [cover, mem_insert]; right; right; right; right; left; rfl
        · rw [hC_eq]; exact edge_in_sym2 _ v₂ v₃ (by simp) (by simp [hv₂_v₃.symm])
      · -- T = D: hit by s(v₃, d₂)
        use s(v₃, d₂)
        constructor
        · simp only [cover, mem_insert]; right; right; right; right; right; right; left; rfl
        · rw [hD_eq]; exact edge_in_sym2 _ v₃ d₂ (by simp) (by simp [hv₃_d₂.symm])
    · -- T ∉ M: must share edge with some M-element (by maximality)
      obtain ⟨E, hE_M, hTE⟩ := hMaximal T hT hT_M
      have hT_card : T.card = 3 := by
        rw [SimpleGraph.mem_cliqueFinset_iff] at hT
        exact hT.1.card_eq
      rw [hM_eq] at hE_M
      simp only [mem_insert, mem_singleton] at hE_M
      rcases hE_M with rfl | rfl | rfl | rfl
      · -- E = A: T shares edge with A = {v₁, a₂, a₃}
        -- Since A is endpoint, T contains v₁ or shares base {a₂, a₃}
        -- If v₁ ∈ T, then s(v₁, a₂) or s(v₁, a₃) hits T
        by_cases hv₁_T : v₁ ∈ T
        · -- v₁ ∈ T and |T ∩ A| ≥ 2, so some other element of A is in T
          have h_exists : ∃ z ∈ T ∩ A, z ≠ v₁ := by
            by_contra h; push_neg at h
            have h_sub : T ∩ A ⊆ {v₁} := fun w hw => mem_singleton.mpr (h w hw)
            have h_card : (T ∩ A).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
            omega
          obtain ⟨z, hz_inter, hz_ne⟩ := h_exists
          have hz_T : z ∈ T := mem_of_mem_inter_left hz_inter
          have hz_A : z ∈ A := mem_of_mem_inter_right hz_inter
          rw [hA_eq] at hz_A
          simp only [mem_insert, mem_singleton] at hz_A
          rcases hz_A with rfl | rfl | rfl
          · exact absurd rfl hz_ne
          · use s(v₁, a₂); constructor
            · simp only [cover, mem_insert]; left; rfl
            · exact edge_in_sym2 T v₁ a₂ hv₁_T hz_T
          · use s(v₁, a₃); constructor
            · simp only [cover, mem_insert]; right; left; rfl
            · exact edge_in_sym2 T v₁ a₃ hv₁_T hz_T
        · -- v₁ ∉ T, so T shares base {a₂, a₃} with A
          -- Since |T ∩ A| ≥ 2 and v₁ ∉ T, must have a₂, a₃ ∈ T
          have ha₂_T : a₂ ∈ T := by
            have h_sub : T ∩ A ⊆ A \ {v₁} := by
              intro x hx; simp only [mem_inter] at hx; simp only [mem_sdiff, mem_singleton]
              exact ⟨hx.2, fun h => hv₁_T (h ▸ hx.1)⟩
            rw [hA_eq] at h_sub
            have h_sdiff : ({v₁, a₂, a₃} : Finset V) \ {v₁} = {a₂, a₃} := by
              ext x; simp only [mem_sdiff, mem_insert, mem_singleton]
              constructor
              · intro ⟨hx, hne⟩; rcases hx with rfl | rfl | rfl
                · exact absurd rfl hne
                · left; rfl
                · right; rfl
              · intro hx; rcases hx with rfl | rfl <;> simp [hv₁_a₂, hv₁_a₃]
            rw [h_sdiff] at h_sub
            have h_card_sdiff : ({a₂, a₃} : Finset V).card = 2 := by
              rw [card_insert_of_not_mem, card_singleton]; simp [ha₂_a₃]
            have h_eq : T ∩ A = {a₂, a₃} := by
              apply eq_of_subset_of_card_le h_sub
              calc 2 ≤ (T ∩ A).card := hTE
                _ ≤ ({a₂, a₃} : Finset V).card := card_le_card h_sub
            have : a₂ ∈ T ∩ A := by rw [h_eq]; simp
            exact mem_of_mem_inter_left this
          have ha₃_T : a₃ ∈ T := by
            have h_sub : T ∩ A ⊆ A \ {v₁} := by
              intro x hx; simp only [mem_inter] at hx; simp only [mem_sdiff, mem_singleton]
              exact ⟨hx.2, fun h => hv₁_T (h ▸ hx.1)⟩
            rw [hA_eq] at h_sub
            have h_sdiff : ({v₁, a₂, a₃} : Finset V) \ {v₁} = {a₂, a₃} := by
              ext x; simp only [mem_sdiff, mem_insert, mem_singleton]
              constructor
              · intro ⟨hx, hne⟩; rcases hx with rfl | rfl | rfl
                · exact absurd rfl hne
                · left; rfl
                · right; rfl
              · intro hx; rcases hx with rfl | rfl <;> simp [hv₁_a₂, hv₁_a₃]
            rw [h_sdiff] at h_sub
            have h_eq : T ∩ A = {a₂, a₃} := by
              apply eq_of_subset_of_card_le h_sub
              calc 2 ≤ (T ∩ A).card := hTE
                _ ≤ ({a₂, a₃} : Finset V).card := card_le_card h_sub
            have : a₃ ∈ T ∩ A := by rw [h_eq]; simp
            exact mem_of_mem_inter_left this
          -- Now T contains {a₂, a₃} but not v₁
          -- T must also share edge with another M-element (since T ∉ M)
          -- But A is endpoint, so if T avoids v₁, T might be bridge A-B?
          -- No - A ∩ B = {v₁}, so bridge would need v₁ ∈ T
          -- This case: T is pure A-external (shares base {a₂, a₃} but NOT spine-connected)
          -- We need to check: is s(a₂, a₃) in our cover? NO!
          -- But wait - for endpoints, exists_two_edges_cover_Se gives us 2 edges
          -- that cover all S_e externals. Our selection {s(v₁, a₂), s(v₁, a₃)} covers
          -- triangles containing v₁, but NOT triangles with {a₂, a₃} avoiding v₁!
          -- This is a GAP in the current approach for ENDPOINTS.
          -- We need s(a₂, a₃) for A, not just spokes.
          sorry
      · -- E = B: T shares edge with B = {v₁, v₂, b₃}
        -- B is middle element, so by middle_no_base_externals: v₁ ∈ T ∨ v₂ ∈ T
        have h_spine : v₁ ∈ T ∨ v₂ ∈ T :=
          middle_no_base_externals B v₁ v₂ b₃ hB_eq hv₁_v₂ hv₁_b₃ hv₂_b₃ T hT_card hTE
        rcases h_spine with hv₁_T | hv₂_T
        · -- v₁ ∈ T: use s(v₁, v₂) which is in cover
          use s(v₁, v₂)
          constructor
          · simp only [cover, mem_insert]; right; right; left; rfl
          · -- Need to show s(v₁, v₂) ∈ T.sym2, i.e., v₂ ∈ T
            -- This requires correct_middle_cover or similar analysis
            -- We have v₁ ∈ T and |T ∩ B| ≥ 2
            have h_cover := correct_middle_cover v₁ v₂ b₃ hv₁_v₂ hv₁_b₃ hv₂_b₃ T hT_card hv₁_T
              (by rw [← hB_eq]; exact hTE)
            rcases h_cover with h12 | h1b3
            · exact h12
            · -- s(v₁, b₃) ∈ T.sym2, so b₃ ∈ T
              simp only [Finset.mk_mem_sym2_iff, Sym2.mem_iff] at h1b3
              have hb₃_T : b₃ ∈ T := by
                rcases h1b3 with ⟨ha, hb⟩
                by_cases hv1 : v₁ = b₃
                · exact absurd hv1 hv₁_b₃
                · exact hb
              -- We have v₁, b₃ ∈ T. Use s(v₁, v₂) or need v₂?
              -- Actually, we chose s(v₁, v₂) in cover, but if v₂ ∉ T, this edge isn't in T.sym2!
              -- We need to use s(v₂, b₃) instead, which IS in cover
              use s(v₂, b₃)
              constructor
              · simp only [cover, mem_insert]; right; right; right; left; rfl
              · -- Need v₂ ∈ T. But we only know v₁, b₃ ∈ T!
                -- T = {v₁, b₃, x} for some x. |T ∩ B| ≥ 2, B = {v₁, v₂, b₃}
                -- T ∩ B = {v₁, b₃} (if v₂ ∉ T) or {v₁, b₃, v₂} = B (if v₂ ∈ T)
                -- Since |T ∩ B| ≥ 2, both cases work. But if v₂ ∉ T, neither s(v₁,v₂) nor s(v₂,b₃) works!
                -- This is a fundamental issue with the cover selection for B.
                -- We need {s(v₁, v₂), s(v₁, b₃)} OR {s(v₁, v₂), s(v₂, b₃)} to cover ALL cases.
                -- Let's check: T shares edge with B, v₁ ∈ T, and we need to hit T.
                -- If v₂ ∈ T: s(v₁, v₂) works
                -- If v₂ ∉ T: T = {v₁, b₃, x}, so s(v₁, b₃) works
                -- So the correct cover for B is {s(v₁, v₂), s(v₁, b₃)}, NOT {s(v₁, v₂), s(v₂, b₃)}!
                sorry
        · -- v₂ ∈ T: use s(v₂, b₃) or s(v₁, v₂)
          -- Similar analysis needed
          use s(v₂, b₃)
          constructor
          · simp only [cover, mem_insert]; right; right; right; left; rfl
          · have h_cover := correct_middle_cover v₂ v₁ b₃ hv₁_v₂.symm hv₂_b₃ hv₁_b₃.symm T hT_card hv₂_T
              (by
                have h_rewrite : ({v₂, v₁, b₃} : Finset V) = {v₁, v₂, b₃} := by
                  ext x; simp only [mem_insert, mem_singleton]; tauto
                rw [h_rewrite, ← hB_eq]; exact hTE)
            rcases h_cover with h21 | h2b3
            · -- s(v₂, v₁) ∈ T.sym2
              simp only [Finset.mk_mem_sym2_iff, Sym2.mem_iff] at h21
              have hv₁_T : v₁ ∈ T := by
                rcases h21 with ⟨ha, hb⟩
                by_cases hv2 : v₂ = v₁
                · exact absurd hv2.symm hv₁_v₂
                · exact hb
              -- v₁, v₂ ∈ T, so s(v₁, v₂) hits T
              use s(v₁, v₂)
              constructor
              · simp only [cover, mem_insert]; right; right; left; rfl
              · exact edge_in_sym2 T v₁ v₂ hv₁_T hv₂_T
            · -- s(v₂, b₃) ∈ T.sym2
              exact h2b3
      · -- E = C: similar to B
        have h_spine : v₂ ∈ T ∨ v₃ ∈ T :=
          middle_no_base_externals C v₂ v₃ c₃ hC_eq hv₂_v₃ hv₂_c₃ hv₃_c₃ T hT_card hTE
        rcases h_spine with hv₂_T | hv₃_T
        · use s(v₂, v₃)
          constructor
          · simp only [cover, mem_insert]; right; right; right; right; left; rfl
          · have h_cover := correct_middle_cover v₂ v₃ c₃ hv₂_v₃ hv₂_c₃ hv₃_c₃ T hT_card hv₂_T
              (by rw [← hC_eq]; exact hTE)
            rcases h_cover with h23 | h2c3
            · exact h23
            · sorry
        · use s(v₂, c₃)
          constructor
          · simp only [cover, mem_insert]; right; right; right; right; right; left; rfl
          · sorry
      · -- E = D: similar to A (endpoint)
        by_cases hv₃_T : v₃ ∈ T
        · have h_exists : ∃ z ∈ T ∩ D, z ≠ v₃ := by
            by_contra h; push_neg at h
            have h_sub : T ∩ D ⊆ {v₃} := fun w hw => mem_singleton.mpr (h w hw)
            have h_card : (T ∩ D).card ≤ 1 := card_le_card h_sub |>.trans (card_singleton _).le
            omega
          obtain ⟨z, hz_inter, hz_ne⟩ := h_exists
          have hz_T : z ∈ T := mem_of_mem_inter_left hz_inter
          have hz_D : z ∈ D := mem_of_mem_inter_right hz_inter
          rw [hD_eq] at hz_D
          simp only [mem_insert, mem_singleton] at hz_D
          rcases hz_D with rfl | rfl | rfl
          · exact absurd rfl hz_ne
          · use s(v₃, d₂); constructor
            · simp only [cover, mem_insert]; right; right; right; right; right; right; left; rfl
            · exact edge_in_sym2 T v₃ d₂ hv₃_T hz_T
          · use s(v₃, d₃); constructor
            · simp only [cover, mem_insert]; right; right; right; right; right; right; right; rfl
            · exact edge_in_sym2 T v₃ d₃ hv₃_T hz_T
        · -- v₃ ∉ T, same gap as A
          sorry

end
