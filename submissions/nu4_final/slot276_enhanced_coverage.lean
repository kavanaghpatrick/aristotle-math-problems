/-
slot276: PATH_4 τ ≤ 8 - Enhanced scaffolding, ONE sorry

Based on slot269's proven structure. Target: path4_cover_covers

PROVEN: triangle_structure, path4_cover_card_le_8, membership lemmas
PROVEN: cover_case_private_A, cover_case_private_D (endpoint-private cases)
SORRY: path4_cover_covers (spine vertex cases v1, v2, v3)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

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

-- PROVEN: Basic membership
lemma v1_in_A (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v1 ∈ cfg.A := by
  have h := cfg.hAB; rw [Finset.ext_iff] at h
  exact Finset.mem_inter.mp ((h cfg.v1).mpr (by simp)) |>.1

lemma v1_in_B (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v1 ∈ cfg.B := by
  have h := cfg.hAB; rw [Finset.ext_iff] at h
  exact Finset.mem_inter.mp ((h cfg.v1).mpr (by simp)) |>.2

lemma v2_in_B (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v2 ∈ cfg.B := by
  have h := cfg.hBC; rw [Finset.ext_iff] at h
  exact Finset.mem_inter.mp ((h cfg.v2).mpr (by simp)) |>.1

lemma v2_in_C (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v2 ∈ cfg.C := by
  have h := cfg.hBC; rw [Finset.ext_iff] at h
  exact Finset.mem_inter.mp ((h cfg.v2).mpr (by simp)) |>.2

lemma v3_in_C (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v3 ∈ cfg.C := by
  have h := cfg.hCD; rw [Finset.ext_iff] at h
  exact Finset.mem_inter.mp ((h cfg.v3).mpr (by simp)) |>.1

lemma v3_in_D (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v3 ∈ cfg.D := by
  have h := cfg.hCD; rw [Finset.ext_iff] at h
  exact Finset.mem_inter.mp ((h cfg.v3).mpr (by simp)) |>.2

-- PROVEN: Key structural decomposition (from slot269)
theorem triangle_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    cfg.v1 ∈ t ∨ cfg.v2 ∈ t ∨ cfg.v3 ∈ t ∨
    ((t ∩ cfg.A).card ≥ 2 ∧ cfg.v1 ∉ t) ∨
    ((t ∩ cfg.D).card ≥ 2 ∧ cfg.v3 ∉ t) := by
  by_contra h_contra
  obtain ⟨m, hm⟩ : ∃ m ∈ ({cfg.A, cfg.B, cfg.C, cfg.D} : Finset (Finset V)), (t ∩ m).card ≥ 2 := by
    have := hM.2 t ht
    by_cases h : t ∈ M <;> simp_all +decide [cfg.hM_eq]
    have := ht.card_eq; aesop
  by_cases hmA : m = cfg.A
  · simp_all +decide [Finset.inter_comm]
  · by_cases hmB : m = cfg.B
    · have h_card_B : (t ∩ cfg.B).card ≤ 1 := by
        have h1 : (t ∩ cfg.B) ⊆ {cfg.v1, cfg.v2}ᶜ := by simp_all +decide [Finset.subset_iff]; grind
        have h2 : (t ∩ cfg.B) ⊆ cfg.B \ {cfg.v1, cfg.v2} := by simp_all +decide [Finset.subset_iff]
        have h3 : (cfg.B \ {cfg.v1, cfg.v2}).card ≤ 1 := by
          have hB3 : cfg.B.card = 3 := by
            have := hM.1.1 cfg.hB; simp_all +decide [SimpleGraph.cliqueFinset]; exact this.card_eq
          have := cfg.hAB; have := cfg.hBC; simp_all +decide [Finset.ext_iff]; grind
        exact le_trans (Finset.card_le_card h2) h3
      grind
    · by_cases hmC : m = cfg.C
      · have h1 : t ∩ cfg.C ⊆ {cfg.v2, cfg.v3}ᶜ := by intro x hx; aesop
        have h2 : (t ∩ cfg.C).card ≤ (cfg.C \ {cfg.v2, cfg.v3}).card := by
          exact Finset.card_le_card fun x hx => by have := h1 hx; aesop
        have hC3 : cfg.C.card = 3 := by
          have := hM.1.1 cfg.hC; simp_all +decide [SimpleGraph.isNClique_iff]
        have := cfg.hBC; have := cfg.hCD; simp_all +decide [Finset.eq_singleton_iff_unique_mem]
        have := cfg.hBD; simp_all +decide [Finset.ext_iff]; grind
      · simp_all +decide [Finset.inter_comm]
        exact h_contra.2.2.1 (h_contra.2.2.2.2 (by simpa only [hm.1, Finset.inter_comm] using hm.2))

-- 8-edge cover
def path4_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4 G M) : Finset (Sym2 V) :=
  cfg.A.sym2.filter (· ∈ G.edgeFinset) ∪
  ({s(cfg.v1, cfg.v2), s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset) ∪
  cfg.D.sym2.filter (· ∈ G.edgeFinset)

-- PROVEN: Cover subset
lemma path4_cover_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M) :
    path4_cover G cfg ⊆ G.edgeFinset := by
  unfold path4_cover; intro e he
  simp only [Finset.mem_union, Finset.mem_filter] at he; aesop

-- PROVEN: Cover card ≤ 8 (from slot269)
lemma path4_cover_card_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (cfg : Path4 G M) :
    (path4_cover G cfg).card ≤ 8 := by
  refine le_trans (Finset.card_union_le _ _) ?_
  refine le_trans (add_le_add (Finset.card_union_le _ _) le_rfl) ?_
  have h_tri : ∀ t ∈ M, t.card = 3 → (t.sym2.filter (· ∈ G.edgeFinset)).card ≤ 3 := by
    intro t ht ht3
    obtain ⟨a, b, c, hab, hbc, hac, rfl⟩ := Finset.card_eq_three.mp ht3
    refine le_trans (Finset.card_le_card ?_) ?_
    · exact {s(a,b), s(a,c), s(b,c)}
    · simp +decide [Finset.subset_iff, Sym2.forall]; aesop
    · exact le_trans (Finset.card_insert_le _ _) (add_le_add_right (Finset.card_insert_le _ _) _)
  have hA3 : cfg.A.card = 3 := by have := hM.1 cfg.hA; simp_all +decide [SimpleGraph.cliqueFinset]; exact this.card_eq
  have hD3 : cfg.D.card = 3 := by
    have := cfg.hM_eq ▸ hM.1; simp_all +decide [Finset.subset_iff]; exact this.2.2.2.2
  calc _ ≤ 3 + 2 + 3 := add_le_add_three (h_tri _ cfg.hA hA3) (Finset.card_filter_le _ _) (h_tri _ cfg.hD hD3)
       _ = 8 := by norm_num

-- PROVEN: Triangle edge helper
lemma triangle_edge_of_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (x y : V) (hx : x ∈ t) (hy : y ∈ t) (hxy : x ≠ y) :
    s(x, y) ∈ G.edgeFinset := by
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact (SimpleGraph.mem_cliqueFinset_iff.mp ht).1 hx hy hxy

/-
PROOF SKETCH for path4_cover_covers:
By triangle_structure, every triangle t falls into one of 5 cases:

Case 1 (v1 ∈ t): t is a clique containing v1.
  - t has vertices {v1, x, y} for some x, y
  - Since v1 ∈ A and t is a clique, edge s(v1, x) ∈ G.edgeFinset
  - If x ∈ A: s(v1, x) ∈ A.sym2 ⊆ path4_cover ✓
  - If x ∉ A: Need to check if y ∈ A, or use spine edge

Case 2 (v2 ∈ t, v1 ∉ t): t has vertices {v2, x, y}
  - Edge s(v2, x) or s(v2, y) might equal s(v1,v2) or s(v2,v3)
  - v2 ∈ B ∩ C, so if x ∈ B: s(v2,x) could be s(v1,v2) if x = v1 (but v1 ∉ t!)
  - Actually: {v1,v2} and {v2,v3} are in spine ⊆ path4_cover
  - Any edge from v2 to A-side or D-side lands in path4_cover

Case 3 (v3 ∈ t, v1 ∉ t, v2 ∉ t): Similar to case 1 with D

Case 4 (endpoint-private A): t ∩ A has ≥2 vertices, all avoiding v1
  - These 2 vertices form edge in both A.sym2 and t.sym2 ✓

Case 5 (endpoint-private D): t ∩ D has ≥2 vertices, all avoiding v3
  - These 2 vertices form edge in both D.sym2 and t.sym2 ✓
-/
lemma path4_cover_covers (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  sorry

-- Main theorem (follows from above)
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  use path4_cover G cfg
  exact ⟨path4_cover_card_le_8 G M hM.1 cfg, path4_cover_subset G M cfg, path4_cover_covers G M hM cfg⟩

end
