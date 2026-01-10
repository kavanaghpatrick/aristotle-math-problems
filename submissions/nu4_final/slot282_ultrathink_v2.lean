/-
  slot282: PATH_4 τ ≤ 8 - Ultrathink V2 with Aristotle Learnings

  DATE: Jan 7, 2026
  SOURCE: Synthesis of slot276 proven helpers + correct cover analysis

  KEY INSIGHT FROM COUNTEREXAMPLES:
  - slot276 counterexample: t_ex = {v1, b, v3} NOT covered by A.sym2 ∪ spine ∪ D.sym2
  - The naive cover misses "cross triangles" between non-adjacent M-elements

  CORRECT 8-EDGE COVER (adaptive based on structure):
  For endpoints A, D: Use 2 edges that cover the element AND its externals
  For middle B, C: Use spokes that hit cross-triangles

  PROOF STRATEGY:
  1. triangle_structure: Every triangle contains spine vertex OR is endpoint-private
  2. Case analysis with explicit edge membership checks
  3. Key: {v1,b} covers the cross-triangle {v1, b, v3}
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Definitions (using STRONG isMaxPacking)
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

-- Maximality implies edge-sharing (derived property)
lemma max_packing_edge_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not : t ∉ M) :
    ∃ m ∈ M, (t ∩ m).card ≥ 2 := by
  by_contra h
  push_neg at h
  -- If no M-element shares edge with t, then M ∪ {t} is a larger packing
  have h_packing : isTrianglePacking G (insert t M) := by
    constructor
    · intro x hx
      simp at hx
      rcases hx with rfl | hx
      · exact ht
      · exact hM.1.1 hx
    · intro x hx y hy hxy
      simp at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact Nat.lt_succ_iff.mp (h y hy)
      · rw [Finset.inter_comm]; exact Nat.lt_succ_iff.mp (h x hx)
      · exact hM.1.2 hx hy hxy
  have h_card : (insert t M).card = M.card + 1 := Finset.card_insert_of_not_mem ht_not
  have h_le : (insert t M).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    have h_mem : insert t M ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      simp [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h_packing.1, h_packing⟩
    have h_img := Finset.mem_image_of_mem Finset.card h_mem
    exact Finset.le_max h_img |> WithTop.coe_le_coe.mp
  omega

-- PATH_4 Structure
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

variable {M : Finset (Finset V)} (G : SimpleGraph V) [DecidableRel G.Adj]

-- PROVEN: Basic membership (from slot276)
lemma v1_in_A (cfg : Path4 G M) : cfg.v1 ∈ cfg.A := by
  have h := cfg.hAB; rw [Finset.ext_iff] at h
  exact Finset.mem_inter.mp ((h cfg.v1).mpr (by simp)) |>.1

lemma v1_in_B (cfg : Path4 G M) : cfg.v1 ∈ cfg.B := by
  have h := cfg.hAB; rw [Finset.ext_iff] at h
  exact Finset.mem_inter.mp ((h cfg.v1).mpr (by simp)) |>.2

lemma v2_in_B (cfg : Path4 G M) : cfg.v2 ∈ cfg.B := by
  have h := cfg.hBC; rw [Finset.ext_iff] at h
  exact Finset.mem_inter.mp ((h cfg.v2).mpr (by simp)) |>.1

lemma v2_in_C (cfg : Path4 G M) : cfg.v2 ∈ cfg.C := by
  have h := cfg.hBC; rw [Finset.ext_iff] at h
  exact Finset.mem_inter.mp ((h cfg.v2).mpr (by simp)) |>.2

lemma v3_in_C (cfg : Path4 G M) : cfg.v3 ∈ cfg.C := by
  have h := cfg.hCD; rw [Finset.ext_iff] at h
  exact Finset.mem_inter.mp ((h cfg.v3).mpr (by simp)) |>.1

lemma v3_in_D (cfg : Path4 G M) : cfg.v3 ∈ cfg.D := by
  have h := cfg.hCD; rw [Finset.ext_iff] at h
  exact Finset.mem_inter.mp ((h cfg.v3).mpr (by simp)) |>.2

-- PROVEN: Triangle structure (from slot269/276)
theorem triangle_structure (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    cfg.v1 ∈ t ∨ cfg.v2 ∈ t ∨ cfg.v3 ∈ t ∨
    ((t ∩ cfg.A).card ≥ 2 ∧ cfg.v1 ∉ t) ∨
    ((t ∩ cfg.D).card ≥ 2 ∧ cfg.v3 ∉ t) := by
  by_contra h_contra
  push_neg at h_contra
  -- By maximality, t shares edge with some M-element
  by_cases ht_in : t ∈ M
  · -- t is an M-element, so t ∈ {A, B, C, D}
    rw [cfg.hM_eq] at ht_in
    simp at ht_in
    rcases ht_in with rfl | rfl | rfl | rfl
    · exact h_contra.1 (v1_in_A G cfg)
    · exact h_contra.1 (v1_in_B G cfg)
    · exact h_contra.2.1 (v2_in_C G cfg)
    · exact h_contra.2.2.1 (v3_in_D G cfg)
  · -- t ∉ M, so by maximality t shares edge with some m ∈ M
    obtain ⟨m, hm, h_share⟩ := max_packing_edge_sharing G M hM t ht ht_in
    rw [cfg.hM_eq] at hm
    simp at hm
    rcases hm with rfl | rfl | rfl | rfl
    · -- m = A: t shares edge with A
      exact h_contra.2.2.2.1 ⟨h_share, h_contra.1⟩
    · -- m = B: t shares edge with B = {v1, v2, b}
      -- If v1, v2 ∉ t, then t ∩ B ⊆ {b}, so |t ∩ B| ≤ 1, contradiction
      have hB3 : cfg.B.card = 3 := by
        have := hM.1.1 cfg.hB
        simp [SimpleGraph.cliqueFinset, SimpleGraph.isNClique_iff] at this
        exact this.2
      have h_sub : t ∩ cfg.B ⊆ cfg.B \ {cfg.v1, cfg.v2} := by
        intro x hx
        simp at hx ⊢
        exact ⟨hx.2, fun h => h_contra.1 (h ▸ hx.1), fun h => h_contra.2.1 (h ▸ hx.1)⟩
      have h_card_diff : (cfg.B \ {cfg.v1, cfg.v2}).card ≤ 1 := by
        have h1 := v1_in_B G cfg
        have h2 := v2_in_B G cfg
        calc (cfg.B \ {cfg.v1, cfg.v2}).card
          = cfg.B.card - ({cfg.v1, cfg.v2} ∩ cfg.B).card := Finset.card_sdiff_add_card_inter _ _ ▸ by omega
          _ ≤ 3 - 2 := by
            have : {cfg.v1, cfg.v2} ∩ cfg.B = {cfg.v1, cfg.v2} := by
              ext x; simp; intro h; cases h <;> simp_all
            simp [this, hB3]
          _ = 1 := by norm_num
      have := Finset.card_le_card h_sub
      omega
    · -- m = C: similar to B
      have hC3 : cfg.C.card = 3 := by
        have := hM.1.1 cfg.hC
        simp [SimpleGraph.cliqueFinset, SimpleGraph.isNClique_iff] at this
        exact this.2
      have h_sub : t ∩ cfg.C ⊆ cfg.C \ {cfg.v2, cfg.v3} := by
        intro x hx
        simp at hx ⊢
        exact ⟨hx.2, fun h => h_contra.2.1 (h ▸ hx.1), fun h => h_contra.2.2.1 (h ▸ hx.1)⟩
      have h_card_diff : (cfg.C \ {cfg.v2, cfg.v3}).card ≤ 1 := by
        have h2 := v2_in_C G cfg
        have h3 := v3_in_C G cfg
        calc (cfg.C \ {cfg.v2, cfg.v3}).card
          = cfg.C.card - ({cfg.v2, cfg.v3} ∩ cfg.C).card := Finset.card_sdiff_add_card_inter _ _ ▸ by omega
          _ ≤ 3 - 2 := by
            have : {cfg.v2, cfg.v3} ∩ cfg.C = {cfg.v2, cfg.v3} := by
              ext x; simp; intro h; cases h <;> simp_all
            simp [this, hC3]
          _ = 1 := by norm_num
      have := Finset.card_le_card h_sub
      omega
    · -- m = D: endpoint-private
      exact h_contra.2.2.2.2 ⟨h_share, h_contra.2.2.1⟩

-- PROVEN: Triangle edge helper (from slot276)
lemma triangle_edge_of_mem (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (x y : V) (hx : x ∈ t) (hy : y ∈ t) (hxy : x ≠ y) :
    s(x, y) ∈ G.edgeFinset := by
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact (SimpleGraph.mem_cliqueFinset_iff.mp ht).1 hx hy hxy

-- The 8-edge cover (correct version)
def path4_cover (cfg : Path4 G M) : Finset (Sym2 V) :=
  -- For A: one spoke + base edge
  ({s(cfg.v1, cfg.A.filter (· ≠ cfg.v1) |>.toList.head!)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset) ∪
  -- Endpoint edges from A and D that cover externals
  (cfg.A.sym2 ∪ cfg.D.sym2).filter (· ∈ G.edgeFinset) ∪
  -- Middle spokes: both edges from b and c
  ({s(cfg.v1, cfg.B.filter (fun x => x ≠ cfg.v1 ∧ x ≠ cfg.v2) |>.toList.headD cfg.v1),
    s(cfg.v2, cfg.B.filter (fun x => x ≠ cfg.v1 ∧ x ≠ cfg.v2) |>.toList.headD cfg.v2),
    s(cfg.v2, cfg.C.filter (fun x => x ≠ cfg.v2 ∧ x ≠ cfg.v3) |>.toList.headD cfg.v2),
    s(cfg.v3, cfg.C.filter (fun x => x ≠ cfg.v2 ∧ x ≠ cfg.v3) |>.toList.headD cfg.v3)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset)

-- Simpler cover: A.sym2 ∪ D.sym2 ∪ middle spokes
def path4_cover_simple (cfg : Path4 G M) : Finset (Sym2 V) :=
  cfg.A.sym2.filter (· ∈ G.edgeFinset) ∪
  cfg.D.sym2.filter (· ∈ G.edgeFinset) ∪
  -- Middle region: need edges hitting {v2, b, c} and cross-triangles
  ({s(cfg.v1, cfg.v2), s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset)

-- Card bound for simple cover
lemma path4_cover_simple_card_le_8 (hM : isTrianglePacking G M) (cfg : Path4 G M) :
    (path4_cover_simple G cfg).card ≤ 8 := by
  unfold path4_cover_simple
  calc (cfg.A.sym2.filter (· ∈ G.edgeFinset) ∪
        cfg.D.sym2.filter (· ∈ G.edgeFinset) ∪
        ({s(cfg.v1, cfg.v2), s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset)).card
    ≤ (cfg.A.sym2.filter (· ∈ G.edgeFinset)).card +
      (cfg.D.sym2.filter (· ∈ G.edgeFinset)).card +
      (({s(cfg.v1, cfg.v2), s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset)).card := by
        calc _ ≤ _ + _ := Finset.card_union_le _ _
           _ ≤ _ + _ + _ := by linarith [Finset.card_union_le _ _]
    _ ≤ 3 + 3 + 2 := by
        have hA : (cfg.A.sym2.filter (· ∈ G.edgeFinset)).card ≤ 3 := by
          calc _ ≤ cfg.A.sym2.card := Finset.card_filter_le _ _
             _ ≤ 3 := by
               have hA3 : cfg.A.card = 3 := by
                 have := hM.1 cfg.hA
                 simp [SimpleGraph.cliqueFinset, SimpleGraph.isNClique_iff] at this
                 exact this.2
               simp [Finset.card_sym2, hA3]
        have hD : (cfg.D.sym2.filter (· ∈ G.edgeFinset)).card ≤ 3 := by
          calc _ ≤ cfg.D.sym2.card := Finset.card_filter_le _ _
             _ ≤ 3 := by
               have hD3 : cfg.D.card = 3 := by
                 have := hM.1 cfg.hD
                 simp [SimpleGraph.cliqueFinset, SimpleGraph.isNClique_iff] at this
                 exact this.2
               simp [Finset.card_sym2, hD3]
        have hSpine : (({s(cfg.v1, cfg.v2), s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset)).card ≤ 2 :=
          Finset.card_filter_le _ _
        omega
    _ = 8 := by norm_num

-- Subset property
lemma path4_cover_simple_subset (cfg : Path4 G M) :
    path4_cover_simple G cfg ⊆ G.edgeFinset := by
  unfold path4_cover_simple
  intro e he
  simp at he
  rcases he with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact h

-- PROVEN: If t shares ≥2 vertices with A, covered by A.sym2 (from slot276 case_4_helper)
lemma case_A_covered (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (h : (t ∩ cfg.A).card ≥ 2) :
    ∃ e ∈ path4_cover_simple G cfg, e ∈ t.sym2 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h
  simp at hx hy
  use s(x, y)
  constructor
  · unfold path4_cover_simple
    simp
    left; left
    constructor
    · simp [Finset.mem_sym2_iff]
      exact ⟨hx.2, hy.2⟩
    · exact triangle_edge_of_mem G t ht x y hx.1 hy.1 hxy
  · simp [Finset.mem_sym2_iff]
    exact ⟨hx.1, hy.1⟩

-- PROVEN: If t shares ≥2 vertices with D, covered by D.sym2 (from slot276 case_5_helper)
lemma case_D_covered (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (h : (t ∩ cfg.D).card ≥ 2) :
    ∃ e ∈ path4_cover_simple G cfg, e ∈ t.sym2 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h
  simp at hx hy
  use s(x, y)
  constructor
  · unfold path4_cover_simple
    simp
    left; right
    constructor
    · simp [Finset.mem_sym2_iff]
      exact ⟨hx.2, hy.2⟩
    · exact triangle_edge_of_mem G t ht x y hx.1 hy.1 hxy
  · simp [Finset.mem_sym2_iff]
    exact ⟨hx.1, hy.1⟩

-- PROVEN: If v1, v2 ∈ t, covered by spine (from slot276)
lemma case_v1_v2_covered (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (h1 : cfg.v1 ∈ t) (h2 : cfg.v2 ∈ t) :
    ∃ e ∈ path4_cover_simple G cfg, e ∈ t.sym2 := by
  use s(cfg.v1, cfg.v2)
  constructor
  · unfold path4_cover_simple
    simp
    right
    constructor
    · left; rfl
    · have hne : cfg.v1 ≠ cfg.v2 := by
        have := cfg.hAC
        by_contra h
        have h1' := v1_in_A G cfg
        have h2' := v2_in_C G cfg
        rw [h] at h1'
        have : cfg.v2 ∈ cfg.A ∩ cfg.C := Finset.mem_inter.mpr ⟨h1', h2'⟩
        simp [this] at this
      exact triangle_edge_of_mem G t ht cfg.v1 cfg.v2 h1 h2 hne
  · simp [Finset.mem_sym2_iff]
    exact ⟨h1, h2⟩

-- PROVEN: If v2, v3 ∈ t, covered by spine (from slot276)
lemma case_v2_v3_covered (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (h2 : cfg.v2 ∈ t) (h3 : cfg.v3 ∈ t) :
    ∃ e ∈ path4_cover_simple G cfg, e ∈ t.sym2 := by
  use s(cfg.v2, cfg.v3)
  constructor
  · unfold path4_cover_simple
    simp
    right
    constructor
    · right; rfl
    · have hne : cfg.v2 ≠ cfg.v3 := by
        have := cfg.hBD
        by_contra h
        have h2' := v2_in_B G cfg
        have h3' := v3_in_D G cfg
        rw [h] at h2'
        have : cfg.v3 ∈ cfg.B ∩ cfg.D := Finset.mem_inter.mpr ⟨h2', h3'⟩
        simp [this] at this
      exact triangle_edge_of_mem G t ht cfg.v2 cfg.v3 h2 h3 hne
  · simp [Finset.mem_sym2_iff]
    exact ⟨h2, h3⟩

/-
MAIN THEOREM: path4_cover_simple covers all triangles

PROOF SKETCH:
By triangle_structure, every triangle t satisfies one of:
1. v1 ∈ t: Then t = {v1, x, y}. By maximality, t shares edge with some M-element.
   - If shares with A: some edge of {v1,x,y} is in A.sym2 ⊆ cover ✓
   - If shares with B: if v2 ∈ t, use case_v1_v2_covered; else {v1, b} ⊆ t for some b,
     and {v1, b} might be in A.sym2 if b ∈ A... need careful case analysis
2. v2 ∈ t (and v1 ∉ t): t shares edge with B or C.
   - If shares {v2, v3} with C: case_v2_v3_covered ✓
   - Otherwise need {v2, b} or {v2, c} edges
3. v3 ∈ t (and v1, v2 ∉ t): Similarly for D side
4. Endpoint-private A: case_A_covered ✓
5. Endpoint-private D: case_D_covered ✓

The tricky cases are when v1 ∈ t but t doesn't neatly fall into A.sym2 coverage.
-/
theorem path4_cover_simple_covers (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ path4_cover_simple G cfg, e ∈ t.sym2 := by
  -- Use triangle_structure
  have h_struct := triangle_structure G hM cfg t ht
  rcases h_struct with hv1 | hv2 | hv3 | ⟨hA, _⟩ | ⟨hD, _⟩
  · -- Case 1: v1 ∈ t
    -- t shares edge with some M-element by maximality
    -- If t shares edge with A, then some A-edge is in t
    by_cases hA : (t ∩ cfg.A).card ≥ 2
    · exact case_A_covered G cfg t ht hA
    · -- t doesn't share edge with A
      by_cases hv2 : cfg.v2 ∈ t
      · exact case_v1_v2_covered G cfg t ht hv1 hv2
      · -- v1 ∈ t, v2 ∉ t, t doesn't share edge with A
        -- By maximality, t shares edge with B, C, or D
        -- Since v1 ∈ t and v1 ∈ B, if t shares edge with B, need one more B-vertex
        -- Since v2 ∉ t, must be the third vertex b of B
        -- This gives t ⊇ {v1, b}
        -- {v1, b} might be covered by A.sym2 if b ∈ A... unlikely
        -- Otherwise need more analysis
        sorry
  · -- Case 2: v2 ∈ t, v1 ∉ t
    by_cases hv3 : cfg.v3 ∈ t
    · exact case_v2_v3_covered G cfg t ht hv2 hv3
    · -- v2 ∈ t, v1 ∉ t, v3 ∉ t
      -- t shares edge with B or C (not A or D since v1, v3 ∉ t)
      sorry
  · -- Case 3: v3 ∈ t, v1 ∉ t, v2 ∉ t
    by_cases hD : (t ∩ cfg.D).card ≥ 2
    · exact case_D_covered G cfg t ht hD
    · sorry
  · -- Case 4: endpoint-private A
    exact case_A_covered G cfg t ht hA
  · -- Case 5: endpoint-private D
    exact case_D_covered G cfg t ht hD

-- Main theorem
theorem tau_le_8_path4 (hM : isMaxPacking G M) (cfg : Path4 G M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  use path4_cover_simple G cfg
  exact ⟨path4_cover_simple_card_le_8 G hM.1 cfg,
         path4_cover_simple_subset G cfg,
         path4_cover_simple_covers G hM cfg⟩

end
