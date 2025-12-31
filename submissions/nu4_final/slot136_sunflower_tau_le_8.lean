/-
Tuza ν=4 Cycle_4: τ ≤ 8 via Local Sunflower Covers

Strategy: At each shared vertex v, triangles form a sunflower.
Due to ν=4, at most 2 "directions" at each v suffice.
4 vertices × 2 edges = 8 total.

Key Insight: Every triangle contains at least one shared vertex (cycle4_all_triangles_contain_shared).
So covering triangles at all 4 shared vertices covers ALL triangles.

From AI debate synthesis (Dec 29, 2025):
- Grok's 8-spoke strategy FAILS (misses cycle edges)
- Gemini's sunflower approach is CORRECT
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot113)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 CONFIGURATION
-- ══════════════════════════════════════════════════════════════════════════════

structure Cycle4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A

-- ══════════════════════════════════════════════════════════════════════════════
-- TRIANGLES AT VERTEX
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles containing vertex v -/
def trianglesContaining (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

/-- Shared vertices set -/
def sharedVertices (cfg : Cycle4 G M) : Finset V :=
  {cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da}

-- ══════════════════════════════════════════════════════════════════════════════
-- CORE LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- PROVEN (slot113): Every triangle shares edge with packing -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
  -- By maximality argument (proven in slot113)
  by_contra h_no_triangle
  push_neg at h_no_triangle
  have h_packing : isTrianglePacking G (M ∪ {t}) := by
    constructor
    · have hM_subset : M ⊆ G.cliqueFinset 3 := hM.1.1
      exact Finset.union_subset hM_subset (Finset.singleton_subset_iff.mpr ht)
    · have h_pairwise_M : ∀ t1 t2 : Finset V, t1 ∈ M → t2 ∈ M → t1 ≠ t2 → (t1 ∩ t2).card ≤ 1 := by
        have := hM.1.2; aesop
      intro t1 ht1 t2 ht2 hne
      by_cases h : t1 = t <;> by_cases h' : t2 = t <;> simp_all +decide
      · simpa only [Finset.inter_comm] using Nat.le_of_lt_succ (h_no_triangle _ ht2)
      · simpa only [Finset.inter_comm] using Nat.le_of_lt_succ (h_no_triangle _ ht1)
  have h_card : (M ∪ {t}).card > M.card := by
    have h_not_in_M : t ∉ M := by
      intro h; specialize h_no_triangle t h; simp_all +decide
      exact h_no_triangle.not_le (by rw [ht.card_eq]; decide)
    aesop
  have h_contradiction : trianglePackingNumber G ≥ (M ∪ {t}).card := by
    have h_contradiction : (M ∪ {t}) ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      simp_all +decide [Finset.subset_iff]
      exact fun x hx => Finset.mem_coe.mp (Finset.mem_coe.mpr (h_packing.1 (Finset.mem_insert_of_mem hx))) |> fun h => by simpa using h
    unfold trianglePackingNumber
    have := Finset.le_max (Finset.mem_image_of_mem Finset.card h_contradiction)
    cases h : Finset.max (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)) <;> aesop
  linarith [hM.2]

/-- KEY LEMMA: Every triangle in cycle_4 contains a shared vertex -/
lemma cycle4_all_triangles_contain_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ v ∈ sharedVertices cfg, v ∈ t := by
  -- Every triangle shares edge with some packing element
  obtain ⟨X, hX_mem, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  rw [cfg.hM_eq] at hX_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hX_mem
  -- If t shares 2+ vertices with X, at least one is a shared vertex
  rcases hX_mem with rfl | rfl | rfl | rfl
  all_goals {
    simp only [sharedVertices, Finset.mem_insert, Finset.mem_singleton]
    -- Each packing element contains exactly 2 shared vertices
    -- If t shares 2+ vertices with it, at least one must be shared
    -- This follows from the triangle having card 3 and shared vertices being in A, B, C, D
    sorry -- Aristotle: derive from intersection structure
  }

/-- CRITICAL: Sunflower bound at each shared vertex -/
lemma sunflower_cover_at_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ sharedVertices cfg)
    (h_nu_4 : trianglePackingNumber G = 4) :
    ∃ E_v ⊆ G.edgeFinset, E_v.card ≤ 2 ∧
      (∀ e ∈ E_v, v ∈ Sym2.toFinset e) ∧
      ∀ t ∈ trianglesContaining G v, ∃ e ∈ E_v, e ∈ t.sym2 := by
  /-
  KEY INSIGHT: At shared vertex v, triangles form a "sunflower" structure.

  All triangles at v have form {v, x, y} for some x, y ≠ v.
  These triangles share vertex v, so each pair shares ≥ 1 vertex.
  Thus we cannot add any two triangles at v to the packing simultaneously
  (unless they share only v, which would require card intersection = 1).

  The ν=4 constraint limits how many "directions" we can have:
  - M already uses 4 triangles, 2 of which contain v
  - External triangles at v must intersect these 2 M-triangles

  Due to the intersection structure, at most 2 edge directions from v
  are needed to hit all triangles at v.

  Specifically: if t = {v, x, y} is at v, then edges {v,x} or {v,y} hit t.
  The sunflower property ensures all such t can be hit by ≤ 2 edges.
  -/
  simp only [sharedVertices, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  all_goals {
    -- For each shared vertex, identify the 2 "directions"
    -- These come from the two packing elements containing v
    sorry -- Aristotle: prove via ν=4 sunflower structure
  }

/-- Main theorem: τ ≤ 8 for cycle_4 via sunflower covers -/
theorem tau_le_8_cycle4_sunflower (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (h_nu_4 : trianglePackingNumber G = 4) :
    triangleCoveringNumber G ≤ 8 := by
  -- Get 2-edge covers at each shared vertex
  have h_vab := sunflower_cover_at_vertex G M hM cfg cfg.v_ab (by simp [sharedVertices]) h_nu_4
  have h_vbc := sunflower_cover_at_vertex G M hM cfg cfg.v_bc (by simp [sharedVertices]) h_nu_4
  have h_vcd := sunflower_cover_at_vertex G M hM cfg cfg.v_cd (by simp [sharedVertices]) h_nu_4
  have h_vda := sunflower_cover_at_vertex G M hM cfg cfg.v_da (by simp [sharedVertices]) h_nu_4

  obtain ⟨E_ab, hE_ab_sub, hE_ab_card, _, hE_ab_cover⟩ := h_vab
  obtain ⟨E_bc, hE_bc_sub, hE_bc_card, _, hE_bc_cover⟩ := h_vbc
  obtain ⟨E_cd, hE_cd_sub, hE_cd_card, _, hE_cd_cover⟩ := h_vcd
  obtain ⟨E_da, hE_da_sub, hE_da_card, _, hE_da_cover⟩ := h_vda

  -- Union of all 4 covers
  let E_total := E_ab ∪ E_bc ∪ E_cd ∪ E_da

  -- E_total covers all triangles
  have h_covers_all : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E_total, e ∈ t.sym2 := by
    intro t ht
    obtain ⟨v, hv_shared, hv_in_t⟩ := cycle4_all_triangles_contain_shared G M hM cfg t ht
    have ht_at_v : t ∈ trianglesContaining G v := by
      simp only [trianglesContaining, Finset.mem_filter]
      exact ⟨ht, hv_in_t⟩
    simp only [sharedVertices, Finset.mem_insert, Finset.mem_singleton] at hv_shared
    rcases hv_shared with rfl | rfl | rfl | rfl
    · obtain ⟨e, he_mem, he_in⟩ := hE_ab_cover t ht_at_v
      exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ he_mem)), he_in⟩
    · obtain ⟨e, he_mem, he_in⟩ := hE_bc_cover t ht_at_v
      exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ he_mem)), he_in⟩
    · obtain ⟨e, he_mem, he_in⟩ := hE_cd_cover t ht_at_v
      exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_right _ he_mem), he_in⟩
    · obtain ⟨e, he_mem, he_in⟩ := hE_da_cover t ht_at_v
      exact ⟨e, Finset.mem_union_right _ he_mem, he_in⟩

  -- E_total has card ≤ 8
  have h_card : E_total.card ≤ 8 := by
    calc E_total.card
        = (E_ab ∪ E_bc ∪ E_cd ∪ E_da).card := rfl
      _ ≤ (E_ab ∪ E_bc ∪ E_cd).card + E_da.card := Finset.card_union_le _ _
      _ ≤ (E_ab ∪ E_bc).card + E_cd.card + E_da.card := by linarith [Finset.card_union_le (E_ab ∪ E_bc) E_cd]
      _ ≤ E_ab.card + E_bc.card + E_cd.card + E_da.card := by linarith [Finset.card_union_le E_ab E_bc]
      _ ≤ 2 + 2 + 2 + 2 := by linarith
      _ = 8 := by norm_num

  -- E_total is a valid cover
  have h_valid_cover : isTriangleCover G E_total := by
    constructor
    · exact Finset.union_subset
        (Finset.union_subset
          (Finset.union_subset hE_ab_sub hE_bc_sub)
          hE_cd_sub)
        hE_da_sub
    · exact h_covers_all

  -- Therefore τ ≤ 8
  unfold triangleCoveringNumber
  have h_in_filter : E_total ∈ (G.edgeFinset.powerset.filter (isTriangleCover G)) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h_valid_cover.1, h_valid_cover⟩
  have h_min_le : (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min ≤ E_total.card := by
    exact Finset.min_le (Finset.mem_image_of_mem Finset.card h_in_filter)
  cases h : Finset.min ((G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card) with
  | none => simp [Option.getD]
  | some n =>
    simp only [Option.getD]
    rw [h] at h_min_le
    simp only [WithBot.coe_le_coe] at h_min_le
    linarith

end
