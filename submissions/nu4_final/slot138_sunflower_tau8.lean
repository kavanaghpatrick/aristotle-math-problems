/-
Tuza ν=4 Cycle_4: τ ≤ 8 via Local Sunflower Covers

Based on PROVEN slot113 structure (which gives τ ≤ 12).
Goal: Improve to τ ≤ 8 using sunflower decomposition at shared vertices.

Key insight (from AI debate, Dec 29 2025):
- Every triangle contains at least one shared vertex
- At each shared vertex, ≤ 2 edges suffice to cover all triangles there
- 4 shared vertices × 2 edges = 8 total

This file copies proven code from slot113 and adds the sunflower improvement.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from proven slot113)
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
-- CYCLE_4 CONFIGURATION (from proven slot113)
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

/-- Triangles containing vertex v -/
def trianglesContaining (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMAS (from slot113)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle shares edge with packing (PROVEN in slot113) -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
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
    have h_mem : (M ∪ {t}) ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      simp_all +decide [Finset.subset_iff]
      exact fun x hx => Finset.mem_coe.mp (Finset.mem_coe.mpr (h_packing.1 (Finset.mem_insert_of_mem hx))) |> fun h => by simpa using h
    unfold trianglePackingNumber
    have := Finset.le_max (Finset.mem_image_of_mem Finset.card h_mem)
    cases h : Finset.max (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)) <;> aesop
  linarith [hM.2]

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW: SUNFLOWER DECOMPOSITION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle contains at least one shared vertex -/
lemma cycle4_triangle_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    cfg.v_ab ∈ t ∨ cfg.v_bc ∈ t ∨ cfg.v_cd ∈ t ∨ cfg.v_da ∈ t := by
  obtain ⟨X, hX_mem, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  rw [cfg.hM_eq] at hX_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hX_mem
  -- Each packing element contains 2 shared vertices
  -- If t shares ≥2 vertices with X, at least one is shared
  rcases hX_mem with rfl | rfl | rfl | rfl
  · -- X = A contains v_ab and v_da
    -- t ∩ A has card ≥ 2, and A has card 3 with two shared vertices
    sorry -- Aristotle: pigeonhole on A = {v_ab, v_da, third}
  · -- X = B contains v_ab and v_bc
    sorry
  · -- X = C contains v_bc and v_cd
    sorry
  · -- X = D contains v_cd and v_da
    sorry

/-- At each shared vertex, 2 edges cover all triangles containing it -/
lemma sunflower_cover_at_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V)
    (hv : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da) :
    ∃ E_v : Finset (Sym2 V), E_v ⊆ G.edgeFinset ∧ E_v.card ≤ 2 ∧
      ∀ t ∈ trianglesContaining G v, ∃ e ∈ E_v, e ∈ t.sym2 := by
  /-
  At shared vertex v, two packing elements contain v.
  Any triangle at v has form {v, x, y}.

  Key insight: Due to ν=4 constraint, triangles at v form a "sunflower".
  The "petals" (non-v parts) have limited variety because:
  - Adding two vertex-disjoint triangles at v would increase ν
  - So all triangles at v must share additional structure

  This limits external triangles such that 2 edges from v suffice.
  The two edges are typically the cycle edges from v to adjacent shared vertices.
  -/
  rcases hv with rfl | rfl | rfl | rfl
  all_goals sorry -- Aristotle: construct 2-edge cover at each shared vertex

/-- Main theorem: τ ≤ 8 for cycle_4 -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- Get 2-edge covers at each shared vertex
  obtain ⟨E_ab, hE_ab_sub, hE_ab_card, hE_ab_cover⟩ :=
    sunflower_cover_at_vertex G M hM cfg cfg.v_ab (Or.inl rfl)
  obtain ⟨E_bc, hE_bc_sub, hE_bc_card, hE_bc_cover⟩ :=
    sunflower_cover_at_vertex G M hM cfg cfg.v_bc (Or.inr (Or.inl rfl))
  obtain ⟨E_cd, hE_cd_sub, hE_cd_card, hE_cd_cover⟩ :=
    sunflower_cover_at_vertex G M hM cfg cfg.v_cd (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨E_da, hE_da_sub, hE_da_card, hE_da_cover⟩ :=
    sunflower_cover_at_vertex G M hM cfg cfg.v_da (Or.inr (Or.inr (Or.inr rfl)))

  -- Union covers all triangles
  let E_total := E_ab ∪ E_bc ∪ E_cd ∪ E_da

  have h_covers_all : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E_total, e ∈ t.sym2 := by
    intro t ht
    have h_shared := cycle4_triangle_contains_shared G M hM cfg t ht
    rcases h_shared with hvab | hvbc | hvcd | hvda
    · have ht_v : t ∈ trianglesContaining G cfg.v_ab := by
        simp only [trianglesContaining, Finset.mem_filter]; exact ⟨ht, hvab⟩
      obtain ⟨e, he_mem, he_in⟩ := hE_ab_cover t ht_v
      exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ he_mem)), he_in⟩
    · have ht_v : t ∈ trianglesContaining G cfg.v_bc := by
        simp only [trianglesContaining, Finset.mem_filter]; exact ⟨ht, hvbc⟩
      obtain ⟨e, he_mem, he_in⟩ := hE_bc_cover t ht_v
      exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ he_mem)), he_in⟩
    · have ht_v : t ∈ trianglesContaining G cfg.v_cd := by
        simp only [trianglesContaining, Finset.mem_filter]; exact ⟨ht, hvcd⟩
      obtain ⟨e, he_mem, he_in⟩ := hE_cd_cover t ht_v
      exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_right _ he_mem), he_in⟩
    · have ht_v : t ∈ trianglesContaining G cfg.v_da := by
        simp only [trianglesContaining, Finset.mem_filter]; exact ⟨ht, hvda⟩
      obtain ⟨e, he_mem, he_in⟩ := hE_da_cover t ht_v
      exact ⟨e, Finset.mem_union_right _ he_mem, he_in⟩

  have h_card : E_total.card ≤ 8 := by
    calc E_total.card
        ≤ E_ab.card + E_bc.card + E_cd.card + E_da.card := by
          calc E_total.card
              ≤ (E_ab ∪ E_bc ∪ E_cd).card + E_da.card := Finset.card_union_le _ _
            _ ≤ (E_ab ∪ E_bc).card + E_cd.card + E_da.card := by
                have := Finset.card_union_le (E_ab ∪ E_bc) E_cd; linarith
            _ ≤ E_ab.card + E_bc.card + E_cd.card + E_da.card := by
                have := Finset.card_union_le E_ab E_bc; linarith
      _ ≤ 2 + 2 + 2 + 2 := by linarith
      _ = 8 := by norm_num

  have h_valid : isTriangleCover G E_total := by
    constructor
    · exact Finset.union_subset
        (Finset.union_subset
          (Finset.union_subset hE_ab_sub hE_bc_sub)
          hE_cd_sub)
        hE_da_sub
    · exact h_covers_all

  -- τ ≤ |E_total| ≤ 8
  have h_in : E_total ∈ G.edgeFinset.powerset.filter (isTriangleCover G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h_valid.1, h_valid⟩
  unfold triangleCoveringNumber
  have h_mem_img := Finset.mem_image_of_mem Finset.card h_in
  have h_le := Finset.min_le h_mem_img
  -- The min over valid covers ≤ |E_total| ≤ 8
  sorry -- Aristotle: finish from h_le, h_card, heq

end
