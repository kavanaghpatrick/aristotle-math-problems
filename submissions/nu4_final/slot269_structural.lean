/-
slot269: Structural Lemma for PATH_4 Triangle Coverage

KEY INSIGHT:
Every triangle in a PATH_4 graph (with ν=4) either:
1. Contains one of the spine vertices {v1, v2, v3}, OR
2. Is "endpoint-private": shares edge only with A (avoiding v1) or only with D (avoiding v3)

This structural lemma enables an 8-edge cover:
- 3 edges of A (cover A and endpoint-private A triangles)
- 2 spine edges {v1,v2}, {v2,v3} (cover triangles containing v2)
- 3 edges of D (cover D and endpoint-private D triangles)

Total: 8 edges (possibly fewer due to overlap)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

-- PATH_4 structure
structure Path4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  v1 : V
  v2 : V
  v3 : V
  hAB : A ∩ B = {v1}
  hBC : B ∩ C = {v2}
  hCD : C ∩ D = {v3}
  hAC : A ∩ C = ∅
  hAD : A ∩ D = ∅
  hBD : B ∩ D = ∅

-- ══════════════════════════════════════════════════════════════════════════════
-- BASIC MEMBERSHIP LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

lemma v1_in_A (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v1 ∈ cfg.A := by
  have h := cfg.hAB
  rw [Finset.ext_iff] at h
  have := (h cfg.v1).mpr (by simp)
  exact mem_inter.mp this |>.1

lemma v1_in_B (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v1 ∈ cfg.B := by
  have h := cfg.hAB
  rw [Finset.ext_iff] at h
  have := (h cfg.v1).mpr (by simp)
  exact mem_inter.mp this |>.2

lemma v2_in_B (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v2 ∈ cfg.B := by
  have h := cfg.hBC
  rw [Finset.ext_iff] at h
  have := (h cfg.v2).mpr (by simp)
  exact mem_inter.mp this |>.1

lemma v2_in_C (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v2 ∈ cfg.C := by
  have h := cfg.hBC
  rw [Finset.ext_iff] at h
  have := (h cfg.v2).mpr (by simp)
  exact mem_inter.mp this |>.2

lemma v3_in_C (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v3 ∈ cfg.C := by
  have h := cfg.hCD
  rw [Finset.ext_iff] at h
  have := (h cfg.v3).mpr (by simp)
  exact mem_inter.mp this |>.1

lemma v3_in_D (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v3 ∈ cfg.D := by
  have h := cfg.hCD
  rw [Finset.ext_iff] at h
  have := (h cfg.v3).mpr (by simp)
  exact mem_inter.mp this |>.2

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY STRUCTURAL LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
Let t be any triangle. By maximality of M, t shares an edge with some m ∈ M.
Case m = A: t shares ≥2 vertices with A = {v1, a, a'}
  - If v1 ∈ t: t contains spine vertex ✓
  - If v1 ∉ t: t ∩ A = {a, a'}, so t is endpoint-private to A ✓
Case m = B: t shares ≥2 vertices with B = {v1, v2, b}
  - If v1 ∈ t or v2 ∈ t: t contains spine vertex ✓
  - If neither: t ∩ B ⊆ {b}, so |t ∩ B| ≤ 1, contradiction
Case m = C: similar, t contains v2 or v3 ✓
Case m = D: similar to A ✓
-/

theorem triangle_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    cfg.v1 ∈ t ∨ cfg.v2 ∈ t ∨ cfg.v3 ∈ t ∨
    ((t ∩ cfg.A).card ≥ 2 ∧ cfg.v1 ∉ t) ∨
    ((t ∩ cfg.D).card ≥ 2 ∧ cfg.v3 ∉ t) := by
  by_cases ht_M : t ∈ M
  · -- t is an M-element
    rw [cfg.hM_eq] at ht_M
    simp only [mem_insert, mem_singleton] at ht_M
    rcases ht_M with rfl | rfl | rfl | rfl
    · left; exact v1_in_A G M cfg
    · left; exact v1_in_B G M cfg
    · right; left; exact v2_in_C G M cfg
    · right; right; left; exact v3_in_D G M cfg
  · -- t ∉ M, so by maximality shares edge with some m ∈ M
    obtain ⟨m, hm, hshare⟩ := hM.2 t ht ht_M
    rw [cfg.hM_eq] at hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · -- m = A
      by_cases hv1 : cfg.v1 ∈ t
      · left; exact hv1
      · right; right; right; left; exact ⟨hshare, hv1⟩
    · -- m = B
      by_cases hv1 : cfg.v1 ∈ t
      · left; exact hv1
      · by_cases hv2 : cfg.v2 ∈ t
        · right; left; exact hv2
        · -- t ∩ B ≤ 1, contradiction with hshare
          exfalso
          have hAB := cfg.hAB
          have hBC := cfg.hBC
          -- B = {v1, v2, b} where b is the third vertex
          -- If v1, v2 ∉ t, then t ∩ B ⊆ {b}
          have : (t ∩ cfg.B).card ≤ 1 := by
            -- Need to show t ∩ B has at most 1 element
            -- We know v1 ∉ t and v2 ∉ t
            -- So t ∩ B ⊆ B \ {v1, v2}
            have h_sub : t ∩ cfg.B ⊆ cfg.B \ {cfg.v1, cfg.v2} := by
              intro x hx
              simp only [mem_inter, mem_sdiff, mem_insert, mem_singleton] at hx ⊢
              constructor
              · exact hx.2
              · intro h_contra
                rcases h_contra with rfl | rfl
                · exact hv1 hx.1
                · exact hv2 hx.1
            calc (t ∩ cfg.B).card
                ≤ (cfg.B \ {cfg.v1, cfg.v2}).card := card_le_card h_sub
              _ ≤ cfg.B.card := card_sdiff_le _ _
              _ = 3 := by
                  have := hM.1.1 cfg.hB
                  exact (SimpleGraph.mem_cliqueFinset_iff.mp this).2
              _ ≤ 3 := le_refl 3
            -- Actually need tighter bound. B has 3 vertices, remove 2, get 1.
            sorry
          linarith
    · -- m = C
      by_cases hv2 : cfg.v2 ∈ t
      · right; left; exact hv2
      · by_cases hv3 : cfg.v3 ∈ t
        · right; right; left; exact hv3
        · exfalso
          have : (t ∩ cfg.C).card ≤ 1 := by
            sorry
          linarith
    · -- m = D
      by_cases hv3 : cfg.v3 ∈ t
      · right; right; left; exact hv3
      · right; right; right; right; exact ⟨hshare, hv3⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- COVER CONSTRUCTION AND MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- The 8-edge cover for PATH_4:
    - 3 edges of A
    - Spine edges {v1,v2}, {v2,v3}
    - 3 edges of D
-/
def path4_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4 G M) : Finset (Sym2 V) :=
  cfg.A.sym2.filter (· ∈ G.edgeFinset) ∪
  ({s(cfg.v1, cfg.v2), s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset) ∪
  cfg.D.sym2.filter (· ∈ G.edgeFinset)

lemma path4_cover_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M) :
    path4_cover G cfg ⊆ G.edgeFinset := by
  unfold path4_cover
  intro e he
  simp only [mem_union, mem_filter] at he
  rcases he with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact h

lemma path4_cover_card_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (cfg : Path4 G M) :
    (path4_cover G cfg).card ≤ 8 := by
  unfold path4_cover
  have hA_card : cfg.A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 cfg.hA)).2
  have hD_card : cfg.D.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 cfg.hD)).2
  calc (cfg.A.sym2.filter (· ∈ G.edgeFinset) ∪
        ({s(cfg.v1, cfg.v2), s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset) ∪
        cfg.D.sym2.filter (· ∈ G.edgeFinset)).card
      ≤ (cfg.A.sym2.filter (· ∈ G.edgeFinset)).card +
        (({s(cfg.v1, cfg.v2), s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset)).card +
        (cfg.D.sym2.filter (· ∈ G.edgeFinset)).card := by
          apply le_trans (card_union_le _ _)
          exact add_le_add_right (card_union_le _ _) _
    _ ≤ cfg.A.sym2.card + 2 + cfg.D.sym2.card := by
          apply add_le_add
          apply add_le_add
          · exact card_filter_le _ _
          · exact card_filter_le _ _
          · exact card_filter_le _ _
    _ ≤ 3 + 2 + 3 := by
          have h1 : cfg.A.sym2.card ≤ 3 := by
            simp only [Finset.card_sym2, hA_card]
            norm_num
          have h2 : cfg.D.sym2.card ≤ 3 := by
            simp only [Finset.card_sym2, hD_card]
            norm_num
          linarith
    _ = 8 := by norm_num

/-
PROOF SKETCH for coverage:
By triangle_structure, every triangle t satisfies one of:
1. v1 ∈ t: Covered by edge from A containing v1, or spine edge {v1, v2}
2. v2 ∈ t: Covered by spine edge {v1, v2} or {v2, v3}
3. v3 ∈ t: Covered by edge from D containing v3, or spine edge {v2, v3}
4. Endpoint-private A: t shares {a, a'} with A (avoiding v1), covered by A-edge {a, a'}
5. Endpoint-private D: t shares edge with D (avoiding v3), covered by D-edge
-/

theorem path4_cover_is_valid (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  have h_struct := triangle_structure G M hM cfg t ht
  rcases h_struct with hv1 | hv2 | hv3 | ⟨hA, hv1_not⟩ | ⟨hD, hv3_not⟩
  · -- v1 ∈ t: triangle contains v1, which is in A
    -- t has an edge containing v1 (since t is a clique with v1)
    have ht_clique := SimpleGraph.mem_cliqueFinset_iff.mp ht |>.1
    -- Get another vertex of t
    have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).2
    obtain ⟨x, hx, hx_ne⟩ : ∃ x ∈ t, x ≠ cfg.v1 := by
      by_contra h
      push_neg at h
      have : t ⊆ {cfg.v1} := fun y hy => by simp [h y hy]
      have : t.card ≤ 1 := card_le_card this |>.trans (by simp)
      linarith
    have h_adj : G.Adj cfg.v1 x := ht_clique hv1 hx hx_ne.symm
    by_cases hx_A : x ∈ cfg.A
    · -- Both v1 and x are in A, so {v1, x} is an A-edge
      use s(cfg.v1, x)
      constructor
      · unfold path4_cover
        simp only [mem_union, mem_filter]
        left; left
        constructor
        · simp only [Finset.mem_sym2_iff]
          exact ⟨v1_in_A G M cfg, hx_A⟩
        · exact h_adj.mem_edgeFinset
      · simp only [Finset.mem_sym2_iff]
        exact ⟨hv1, hx⟩
    · -- x ∉ A, use spine edge {v1, v2}
      -- Need: {v1, v2} ∈ t.sym2, i.e., v2 ∈ t
      -- This isn't guaranteed! Need different edge.
      sorry
  · -- v2 ∈ t
    sorry
  · -- v3 ∈ t
    sorry
  · -- Endpoint-private A
    -- t ∩ A has ≥ 2 elements, none is v1
    -- So t shares edge {a, a'} with A, covered by A.sym2
    sorry
  · -- Endpoint-private D
    sorry

theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  use path4_cover G cfg
  exact ⟨path4_cover_card_le_8 G M hM.1 cfg,
         path4_cover_subset G M cfg,
         path4_cover_is_valid G M hM cfg⟩

end
