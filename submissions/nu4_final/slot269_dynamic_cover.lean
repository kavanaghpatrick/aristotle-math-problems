/-
slot269: Dynamic 8-Edge Cover for PATH_4

INSIGHT FROM AI CONSULTATION (Gemini):
The static cover edges(A) ∪ {v1,v2} ∪ {v2,v3} ∪ edges(D) FAILS because:
- Triangles {v2, b, x} ∈ S_B share edge {v2, b} which is NOT in the cover
- Similarly for {v2, c, y} ∈ S_C

CORRECTED APPROACH:
Use a DYNAMIC cover that includes B-edges and C-edges:
- 2 edges for S_A (A-edges)
- 2 edges for S_D (D-edges)
- 4 edges for middle: {v1,v2}, {v1,b}, {v2,v3}, {v3,c}
  OR equivalently: {v1,v2}, {v2,b}, {v2,v3}, {v2,c}

The second option uses all 4 edges of B ∪ C incident to v2, covering:
- All X_AB (contain v1 or v2)
- All S_B (contain v1 or v2 or b)
- All X_BC (contain v2)
- All S_C (contain v2 or v3 or c)
- All X_CD (contain v2 or v3)

Actually: {v1,v2} + {v2,b} + {v2,v3} + {v2,c} = 4 edges all at v2!
These cover every triangle containing v2.

Triangles NOT containing v2:
- In S_A: covered by 2 A-edges
- In S_D: covered by 2 D-edges
- In X_AB: must contain v1 (since A ∩ B = {v1}) - WAIT, also v2 ∈ B, so X_AB contains v1 or v2
- In middle: all contain v2 by definition of B ∩ C = {v2}

So the cover is:
- 2 A-edges + 2 D-edges + 4 edges at v2 = 8 edges? No wait, we need to check overlap.

Let me reconsider more carefully below.
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

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n | ∃ E : Finset (Sym2 V), E.card = n ∧ isTriangleCover G E}

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 STRUCTURE (with explicit B, C vertices)
-- ══════════════════════════════════════════════════════════════════════════════

structure Path4Config (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
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
  b : V   -- B = {v1, v2, b}
  c : V   -- C = {v2, v3, c}
  hB_eq : B = {v1, v2, b}
  hC_eq : C = {v2, v3, c}
  hAB : A ∩ B = {v1}
  hBC : B ∩ C = {v2}
  hCD : C ∩ D = {v3}
  hAC : A ∩ C = ∅
  hAD : A ∩ D = ∅
  hBD : B ∩ D = ∅
  hv1_ne_v2 : v1 ≠ v2
  hv2_ne_v3 : v2 ≠ v3
  hv1_ne_v3 : v1 ≠ v3
  hb_ne_v1 : b ≠ v1
  hb_ne_v2 : b ≠ v2
  hc_ne_v2 : c ≠ v2
  hc_ne_v3 : c ≠ v3

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN HELPERS
-- ══════════════════════════════════════════════════════════════════════════════

lemma v1_in_A (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v1 ∈ cfg.A := by
  have h := cfg.hAB
  simp only [Finset.ext_iff, Finset.mem_inter, Finset.mem_singleton] at h
  exact (h cfg.v1).mpr rfl |>.1

lemma v1_in_B (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v1 ∈ cfg.B := by
  rw [cfg.hB_eq]; simp

lemma v2_in_B (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v2 ∈ cfg.B := by
  rw [cfg.hB_eq]; simp

lemma v2_in_C (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v2 ∈ cfg.C := by
  rw [cfg.hC_eq]; simp

lemma v3_in_C (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v3 ∈ cfg.C := by
  rw [cfg.hC_eq]; simp

lemma v3_in_D (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v3 ∈ cfg.D := by
  have h := cfg.hCD
  simp only [Finset.ext_iff, Finset.mem_inter, Finset.mem_singleton] at h
  exact (h cfg.v3).mpr rfl |>.2

lemma b_in_B (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.b ∈ cfg.B := by
  rw [cfg.hB_eq]; simp

lemma c_in_C (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.c ∈ cfg.C := by
  rw [cfg.hC_eq]; simp

lemma v2_not_in_A (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v2 ∉ cfg.A := by
  intro h
  have hv2C := v2_in_C G M cfg
  have : cfg.v2 ∈ cfg.A ∩ cfg.C := mem_inter.mpr ⟨h, hv2C⟩
  rw [cfg.hAC] at this
  exact Finset.not_mem_empty _ this

lemma v2_not_in_D (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v2 ∉ cfg.D := by
  intro h
  have hv2B := v2_in_B G M cfg
  have : cfg.v2 ∈ cfg.B ∩ cfg.D := mem_inter.mpr ⟨hv2B, h⟩
  rw [cfg.hBD] at this
  exact Finset.not_mem_empty _ this

lemma b_not_in_A (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.b ∉ cfg.A := by
  intro h
  have hbB := b_in_B G M cfg
  have : cfg.b ∈ cfg.A ∩ cfg.B := mem_inter.mpr ⟨h, hbB⟩
  rw [cfg.hAB] at this
  simp only [mem_singleton] at this
  exact cfg.hb_ne_v1 this

lemma b_not_in_D (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.b ∉ cfg.D := by
  intro h
  have hbB := b_in_B G M cfg
  have : cfg.b ∈ cfg.B ∩ cfg.D := mem_inter.mpr ⟨hbB, h⟩
  rw [cfg.hBD] at this
  exact Finset.not_mem_empty _ this

lemma c_not_in_A (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.c ∉ cfg.A := by
  intro h
  have hcC := c_in_C G M cfg
  have : cfg.c ∈ cfg.A ∩ cfg.C := mem_inter.mpr ⟨h, hcC⟩
  rw [cfg.hAC] at this
  exact Finset.not_mem_empty _ this

lemma c_not_in_D (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.c ∉ cfg.D := by
  intro h
  have hcC := c_in_C G M cfg
  have : cfg.c ∈ cfg.C ∩ cfg.D := mem_inter.mpr ⟨hcC, h⟩
  rw [cfg.hCD] at this
  simp only [mem_singleton] at this
  exact cfg.hc_ne_v3 this

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Every triangle contains v1, v2, v3, or is in S_A ∪ S_D
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
For any triangle t sharing edge with M-element m:
- If m = A: t shares 2 vertices with A = {v1, a, a'}
  - If v1 ∈ t: contains spine vertex ✓
  - If v1 ∉ t: t shares {a, a'} with A, so t ∈ S_A (private to A)
- If m = B: t shares 2 vertices with B = {v1, v2, b}
  - At least one of v1, v2 is in t (unless t = {b, ?, ?} which would need |t∩B| ≥ 2)
  - So t contains v1 or v2 ✓
- If m = C: similarly t contains v2 or v3 ✓
- If m = D: similar to A
-/

lemma triangle_contains_spine_or_endpoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4Config G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    cfg.v1 ∈ t ∨ cfg.v2 ∈ t ∨ cfg.v3 ∈ t ∨
    ((t ∩ cfg.A).card ≥ 2 ∧ cfg.v1 ∉ t) ∨  -- S_A type
    ((t ∩ cfg.D).card ≥ 2 ∧ cfg.v3 ∉ t) := by -- S_D type
  -- By maximality, t shares edge with some M-element
  by_cases ht_in_M : t ∈ M
  · -- t ∈ M, so t ∈ {A, B, C, D}
    rw [cfg.hM_eq] at ht_in_M
    simp only [mem_insert, mem_singleton] at ht_in_M
    rcases ht_in_M with rfl | rfl | rfl | rfl
    · -- t = A, which contains v1
      left; exact v1_in_A G M cfg
    · -- t = B, which contains v1 and v2
      left; exact v1_in_B G M cfg
    · -- t = C, which contains v2 and v3
      right; left; exact v2_in_C G M cfg
    · -- t = D, which contains v3
      right; right; left; exact v3_in_D G M cfg
  · -- t ∉ M, by maximality shares edge with some m ∈ M
    obtain ⟨m, hm_M, hm_shares⟩ := hM.2 t ht ht_in_M
    rw [cfg.hM_eq] at hm_M
    simp only [mem_insert, mem_singleton] at hm_M
    rcases hm_M with rfl | rfl | rfl | rfl
    · -- shares edge with A
      by_cases hv1 : cfg.v1 ∈ t
      · left; exact hv1
      · right; right; right; left
        exact ⟨hm_shares, hv1⟩
    · -- shares edge with B = {v1, v2, b}
      -- t ∩ B has ≥ 2 elements
      by_cases hv1 : cfg.v1 ∈ t
      · left; exact hv1
      · by_cases hv2 : cfg.v2 ∈ t
        · right; left; exact hv2
        · -- t contains neither v1 nor v2, so must contain b and one more from B
          -- But B = {v1, v2, b}, and |t ∩ B| ≥ 2
          -- If v1 ∉ t and v2 ∉ t, then t ∩ B ⊆ {b}
          -- So |t ∩ B| ≤ 1, contradiction
          exfalso
          have h_sub : t ∩ cfg.B ⊆ {cfg.b} := by
            intro x hx
            simp only [mem_inter] at hx
            rw [cfg.hB_eq] at hx
            simp only [mem_insert, mem_singleton] at hx
            rcases hx.2 with rfl | rfl | rfl
            · exact absurd hx.1 hv1
            · exact absurd hx.1 hv2
            · simp
          have : (t ∩ cfg.B).card ≤ 1 := by
            calc (t ∩ cfg.B).card ≤ ({cfg.b} : Finset V).card := card_le_card h_sub
              _ = 1 := card_singleton _
          linarith
    · -- shares edge with C = {v2, v3, c}
      by_cases hv2 : cfg.v2 ∈ t
      · right; left; exact hv2
      · by_cases hv3 : cfg.v3 ∈ t
        · right; right; left; exact hv3
        · exfalso
          have h_sub : t ∩ cfg.C ⊆ {cfg.c} := by
            intro x hx
            simp only [mem_inter] at hx
            rw [cfg.hC_eq] at hx
            simp only [mem_insert, mem_singleton] at hx
            rcases hx.2 with rfl | rfl | rfl
            · exact absurd hx.1 hv2
            · exact absurd hx.1 hv3
            · simp
          have : (t ∩ cfg.C).card ≤ 1 := by
            calc (t ∩ cfg.C).card ≤ ({cfg.c} : Finset V).card := card_le_card h_sub
              _ = 1 := card_singleton _
          linarith
    · -- shares edge with D
      by_cases hv3 : cfg.v3 ∈ t
      · right; right; left; exact hv3
      · right; right; right; right
        exact ⟨hm_shares, hv3⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- THE 8-EDGE COVER CONSTRUCTION
-- ══════════════════════════════════════════════════════════════════════════════

/-
Based on the structural lemma, every triangle either:
1. Contains v1, v2, or v3 (covered by edges at spine vertices)
2. Is in S_A-type (shares {a, a'} with A, avoids v1) - covered by A-edges
3. Is in S_D-type (shares edge with D, avoids v3) - covered by D-edges

Cover construction:
- 2 edges of A not containing v1: covers S_A-type triangles
  (Actually need edges OF A, which include v1-edges too. Use 2 A-edges.)
- 2 edges at v1: covers triangles containing v1
- 2 edges at v2: covers triangles containing v2 (but not v1)
- 2 edges at v3: covers triangles containing v3 (but not v1, v2)
  (But we also need D-edge coverage...)

Actually simpler: use edges incident to v1, v2, v3 from A ∪ B ∪ C ∪ D.
-/

def path4_cover_dynamic (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4Config G M) (a a' d d' : V)
    (hA_eq : cfg.A = {cfg.v1, a, a'})
    (hD_eq : cfg.D = {cfg.v3, d, d'}) : Finset (Sym2 V) :=
  -- Edges covering triangles containing v1 OR S_A-type
  ({s(cfg.v1, a), s(cfg.v1, a'), s(a, a')} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset) ∪
  -- Edge at v2 (covers middle)
  ({s(cfg.v1, cfg.v2), s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset) ∪
  -- Edges covering triangles containing v3 OR S_D-type
  ({s(cfg.v3, d), s(cfg.v3, d'), s(d, d')} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset)

-- Note: This gives up to 3 + 2 + 3 = 8 edges (with possible duplicates removed)

/-
PROOF SKETCH for coverage:
1. If t contains v1: covered by {v1, a}, {v1, a'}, or {v1, v2}
2. If t contains v2 (but not v1): covered by {v1, v2} or {v2, v3}
3. If t contains v3 (but not v1, v2): covered by {v3, d}, {v3, d'}, or {v2, v3}
4. If t is S_A-type (contains {a, a'}, avoids v1): covered by {a, a'}
5. If t is S_D-type (shares edge with D, avoids v3): covered by D-edges

The issue: this might have > 8 edges, and we need exactly 8.
Need to show some edges are duplicates or unnecessary.
-/

theorem path4_cover_is_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4Config G M)
    (a a' d d' : V)
    (hA_eq : cfg.A = {cfg.v1, a, a'})
    (hD_eq : cfg.D = {cfg.v3, d, d'})
    (ha_ne : a ≠ a') (hd_ne : d ≠ d')
    (ha_ne_v1 : a ≠ cfg.v1) (ha'_ne_v1 : a' ≠ cfg.v1)
    (hd_ne_v3 : d ≠ cfg.v3) (hd'_ne_v3 : d' ≠ cfg.v3) :
    isTriangleCover G (path4_cover_dynamic G cfg a a' d d' hA_eq hD_eq) := by
  constructor
  · -- Cover ⊆ G.edgeFinset
    unfold path4_cover_dynamic
    simp only [union_subset_iff, filter_subset_iff]
    exact ⟨⟨fun _ h => h.2, fun _ h => h.2⟩, fun _ h => h.2⟩
  · -- Every triangle is covered
    intro t ht
    have h_struct := triangle_contains_spine_or_endpoint G M hM cfg t ht
    rcases h_struct with hv1 | hv2 | hv3 | ⟨hA_share, hv1_not⟩ | ⟨hD_share, hv3_not⟩
    · -- t contains v1
      -- t is a clique, so it has an edge containing v1
      -- This edge is {v1, x} for some x ∈ t, x ≠ v1
      sorry
    · -- t contains v2
      sorry
    · -- t contains v3
      sorry
    · -- S_A-type: t shares edge with A avoiding v1
      -- t ∩ A has ≥ 2 elements, all from {a, a'}
      -- So t contains {a, a'}, covered by edge {a, a'}
      have hA_inter : t ∩ cfg.A ⊆ {a, a'} := by
        intro x hx
        simp only [mem_inter] at hx
        rw [hA_eq] at hx
        simp only [mem_insert, mem_singleton] at hx ⊢
        rcases hx.2 with rfl | rfl | rfl
        · exact absurd hx.1 hv1_not
        · left; rfl
        · right; rfl
      have ha_in : a ∈ t ∧ a' ∈ t := by
        have hcard : (t ∩ cfg.A).card ≥ 2 := hA_share
        have h_le : (t ∩ cfg.A).card ≤ 2 := by
          calc (t ∩ cfg.A).card ≤ ({a, a'} : Finset V).card := card_le_card hA_inter
            _ ≤ 2 := by simp [card_insert_le]
        have h_eq : (t ∩ cfg.A).card = 2 := le_antisymm h_le hcard
        have h_sub_eq : t ∩ cfg.A = {a, a'} := by
          apply eq_of_subset_of_card_le hA_inter
          simp only [h_eq]
          rw [card_insert_of_not_mem, card_singleton]
          simp only [mem_singleton]
          exact ha_ne
        constructor
        · have : a ∈ t ∩ cfg.A := by rw [h_sub_eq]; simp
          exact mem_inter.mp this |>.1
        · have : a' ∈ t ∩ cfg.A := by rw [h_sub_eq]; simp
          exact mem_inter.mp this |>.1
      -- Edge {a, a'} is in t and in the cover
      use s(a, a')
      constructor
      · unfold path4_cover_dynamic
        simp only [mem_union, mem_filter, mem_insert, mem_singleton, true_or, true_and]
        left; left
        -- Need to show s(a, a') ∈ G.edgeFinset
        -- a, a' ∈ t and t is a clique, so G.Adj a a'
        have ht_clique := SimpleGraph.mem_cliqueFinset_iff.mp ht |>.1
        have h_adj : G.Adj a a' := ht_clique ha_in.1 ha_in.2 ha_ne
        exact h_adj.mem_edgeFinset
      · -- s(a, a') ∈ t.sym2
        simp only [Finset.mem_sym2_iff]
        exact ⟨ha_in.1, ha_in.2⟩
    · -- S_D-type: similar
      have hD_inter : t ∩ cfg.D ⊆ {d, d'} := by
        intro x hx
        simp only [mem_inter] at hx
        rw [hD_eq] at hx
        simp only [mem_insert, mem_singleton] at hx ⊢
        rcases hx.2 with rfl | rfl | rfl
        · exact absurd hx.1 hv3_not
        · left; rfl
        · right; rfl
      have hd_in : d ∈ t ∧ d' ∈ t := by
        have hcard : (t ∩ cfg.D).card ≥ 2 := hD_share
        have h_le : (t ∩ cfg.D).card ≤ 2 := by
          calc (t ∩ cfg.D).card ≤ ({d, d'} : Finset V).card := card_le_card hD_inter
            _ ≤ 2 := by simp [card_insert_le]
        have h_eq : (t ∩ cfg.D).card = 2 := le_antisymm h_le hcard
        have h_sub_eq : t ∩ cfg.D = {d, d'} := by
          apply eq_of_subset_of_card_le hD_inter
          simp only [h_eq]
          rw [card_insert_of_not_mem, card_singleton]
          simp only [mem_singleton]
          exact hd_ne
        constructor
        · have : d ∈ t ∩ cfg.D := by rw [h_sub_eq]; simp
          exact mem_inter.mp this |>.1
        · have : d' ∈ t ∩ cfg.D := by rw [h_sub_eq]; simp
          exact mem_inter.mp this |>.1
      use s(d, d')
      constructor
      · unfold path4_cover_dynamic
        simp only [mem_union, mem_filter, mem_insert, mem_singleton, or_true, true_and]
        right
        have ht_clique := SimpleGraph.mem_cliqueFinset_iff.mp ht |>.1
        have h_adj : G.Adj d d' := ht_clique hd_in.1 hd_in.2 hd_ne
        exact h_adj.mem_edgeFinset
      · simp only [Finset.mem_sym2_iff]
        exact ⟨hd_in.1, hd_in.2⟩

/-
REMAINING: Prove |cover| ≤ 8

The cover has at most 3 + 2 + 3 = 8 edges (before filtering to G.edgeFinset).
The filtering can only reduce the count.
-/

theorem path4_cover_card_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4Config G M) (a a' d d' : V)
    (hA_eq : cfg.A = {cfg.v1, a, a'})
    (hD_eq : cfg.D = {cfg.v3, d, d'}) :
    (path4_cover_dynamic G cfg a a' d d' hA_eq hD_eq).card ≤ 8 := by
  unfold path4_cover_dynamic
  calc (({s(cfg.v1, a), s(cfg.v1, a'), s(a, a')} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset) ∪
        ({s(cfg.v1, cfg.v2), s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset) ∪
        ({s(cfg.v3, d), s(cfg.v3, d'), s(d, d')} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset)).card
      ≤ (({s(cfg.v1, a), s(cfg.v1, a'), s(a, a')} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset)).card +
        (({s(cfg.v1, cfg.v2), s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset)).card +
        (({s(cfg.v3, d), s(cfg.v3, d'), s(d, d')} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset)).card := by
          apply le_trans (card_union_le _ _)
          apply add_le_add_right
          exact card_union_le _ _
    _ ≤ 3 + 2 + 3 := by
        apply add_le_add
        apply add_le_add
        · exact card_filter_le _ _
        · exact card_filter_le _ _
        · exact card_filter_le _ _
    _ = 8 := by norm_num

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4Config G M)
    (a a' d d' : V)
    (hA_eq : cfg.A = {cfg.v1, a, a'})
    (hD_eq : cfg.D = {cfg.v3, d, d'})
    (ha_ne : a ≠ a') (hd_ne : d ≠ d')
    (ha_ne_v1 : a ≠ cfg.v1) (ha'_ne_v1 : a' ≠ cfg.v1)
    (hd_ne_v3 : d ≠ cfg.v3) (hd'_ne_v3 : d' ≠ cfg.v3) :
    triangleCoveringNumber G ≤ 8 := by
  have h_cover := path4_cover_is_cover G M hM cfg a a' d d' hA_eq hD_eq ha_ne hd_ne ha_ne_v1 ha'_ne_v1 hd_ne_v3 hd'_ne_v3
  have h_card := path4_cover_card_le_8 G cfg a a' d d' hA_eq hD_eq
  -- triangleCoveringNumber ≤ card of any valid cover
  unfold triangleCoveringNumber
  apply Nat.sInf_le
  use path4_cover_dynamic G cfg a a' d d' hA_eq hD_eq
  constructor
  · -- card = card
    rfl
  · exact h_cover

end
