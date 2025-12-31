/-
Tuza ν=4 Cycle_4: τ ≤ 8 via Diagonal Spokes (GREEDY APPROACH)

Strategy: At each shared vertex v, select 2 diagonal spokes.
- At v_ab: {v_ab, v_da} and {v_ab, v_bc} (diagonal spokes)
- At v_bc: {v_bc, v_ab} and {v_bc, v_cd}
- At v_cd: {v_cd, v_bc} and {v_cd, v_da}
- At v_da: {v_da, v_cd} and {v_da, v_ab}

Total: 8 edges (unique diagonal edges between consecutive corners).

Key insight (Round 6 consensus):
1. External triangles at v MUST share edge with M-element containing v
2. Since external x,y can't form edge (violates triangle_shares_edge_with_packing)
3. Link graph L_v is star forest → König gives τ(L_v) ≤ 2
4. Diagonal spokes from v cover all triangles through v

From AI debate synthesis (Dec 30, 2025):
- All AIs recommend distinctness axioms in Cycle4 structure
- Pigeonhole then becomes trivial with Finset.card_sdiff
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
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
-- CYCLE_4 CONFIGURATION WITH DISTINCTNESS AXIOMS
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
  -- Intersection structure
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  -- Membership
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A
  -- DISTINCTNESS AXIOMS (critical for pigeonhole!)
  h_distinct_ab_bc : v_ab ≠ v_bc
  h_distinct_ab_cd : v_ab ≠ v_cd
  h_distinct_ab_da : v_ab ≠ v_da
  h_distinct_bc_cd : v_bc ≠ v_cd
  h_distinct_bc_da : v_bc ≠ v_da
  h_distinct_cd_da : v_cd ≠ v_da

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA: Every triangle shares edge with packing
-- ══════════════════════════════════════════════════════════════════════════════

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
-- SHARED VERTICES SET
-- ══════════════════════════════════════════════════════════════════════════════

/-- The 4 shared vertices of the cycle configuration -/
def sharedVertices (cfg : Cycle4 G M) : Finset V :=
  {cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da}

/-- Shared vertices has cardinality 4 (using distinctness) -/
lemma sharedVertices_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4 G M) :
    (sharedVertices cfg).card = 4 := by
  simp only [sharedVertices]
  rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
      Finset.card_insert_of_not_mem, Finset.card_singleton]
  · -- v_cd ∉ {v_da}
    simp only [Finset.mem_singleton]
    exact cfg.h_distinct_cd_da
  · -- v_bc ∉ {v_cd, v_da}
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cfg.h_distinct_bc_cd, cfg.h_distinct_bc_da⟩
  · -- v_ab ∉ {v_bc, v_cd, v_da}
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cfg.h_distinct_ab_bc, cfg.h_distinct_ab_cd, cfg.h_distinct_ab_da⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PIGEONHOLE: Every triangle contains a shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle must contain at least one shared vertex -/
lemma cycle4_triangle_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ v ∈ sharedVertices cfg, v ∈ t := by
  -- Get the packing element X that t shares ≥ 2 vertices with
  obtain ⟨X, hX_mem, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht

  -- Case on which element X is
  rw [cfg.hM_eq] at hX_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hX_mem

  rcases hX_mem with rfl | rfl | rfl | rfl

  -- Case X = A: A = {v_ab, v_da, a_priv}, shared = {v_ab, v_da}
  · by_contra h_avoid
    push_neg at h_avoid
    -- If t avoids all shared vertices, t ∩ A ⊆ A \ {v_ab, v_da}
    have h_subset : t ∩ cfg.A ⊆ cfg.A \ {cfg.v_ab, cfg.v_da} := by
      intro x hx
      simp only [Finset.mem_inter] at hx
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hx.2, ?_, ?_⟩
      · -- x ≠ v_ab
        intro heq; subst heq
        exact h_avoid cfg.v_ab (by simp [sharedVertices]) hx.1
      · -- x ≠ v_da
        intro heq; subst heq
        exact h_avoid cfg.v_da (by simp [sharedVertices]) hx.1
    -- |A \ {v_ab, v_da}| = 1 (just the private vertex)
    have h_A_card : cfg.A.card = 3 := by
      have := hM.1.1; simp at this; exact (this cfg.A cfg.hA).card_eq
    have h_remove_card : (cfg.A \ {cfg.v_ab, cfg.v_da}).card = 1 := by
      have h1 : cfg.v_ab ∈ cfg.A := cfg.h_vab_A
      have h2 : cfg.v_da ∈ cfg.A := cfg.h_vda_A
      have h3 : cfg.v_ab ≠ cfg.v_da := cfg.h_distinct_ab_da
      -- |A \ {v_ab, v_da}| = |A| - |{v_ab, v_da}| = 3 - 2 = 1
      have h_pair_card : ({cfg.v_ab, cfg.v_da} : Finset V).card = 2 := by
        rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
        simp [h3]
      have h_pair_subset : ({cfg.v_ab, cfg.v_da} : Finset V) ⊆ cfg.A := by
        simp [h1, h2]
      rw [Finset.card_sdiff h_pair_subset, h_A_card, h_pair_card]
    -- Contradiction: |t ∩ A| ≥ 2 but |t ∩ A| ≤ |A \ {shared}| = 1
    have h_card_le : (t ∩ cfg.A).card ≤ 1 := by
      calc (t ∩ cfg.A).card ≤ (cfg.A \ {cfg.v_ab, cfg.v_da}).card := Finset.card_le_card h_subset
        _ = 1 := h_remove_card
    omega

  -- Case X = B: B = {v_ab, v_bc, b_priv}, shared = {v_ab, v_bc}
  · by_contra h_avoid
    push_neg at h_avoid
    have h_subset : t ∩ cfg.B ⊆ cfg.B \ {cfg.v_ab, cfg.v_bc} := by
      intro x hx
      simp only [Finset.mem_inter] at hx
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hx.2, ?_, ?_⟩
      · intro heq; subst heq
        exact h_avoid cfg.v_ab (by simp [sharedVertices]) hx.1
      · intro heq; subst heq
        exact h_avoid cfg.v_bc (by simp [sharedVertices]) hx.1
    have h_B_card : cfg.B.card = 3 := by
      have := hM.1.1; simp at this; exact (this cfg.B cfg.hB).card_eq
    have h_remove_card : (cfg.B \ {cfg.v_ab, cfg.v_bc}).card = 1 := by
      have h1 : cfg.v_ab ∈ cfg.B := cfg.h_vab_B
      have h2 : cfg.v_bc ∈ cfg.B := cfg.h_vbc_B
      have h3 : cfg.v_ab ≠ cfg.v_bc := cfg.h_distinct_ab_bc
      have h_pair_card : ({cfg.v_ab, cfg.v_bc} : Finset V).card = 2 := by
        rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
        simp [h3]
      have h_pair_subset : ({cfg.v_ab, cfg.v_bc} : Finset V) ⊆ cfg.B := by
        simp [h1, h2]
      rw [Finset.card_sdiff h_pair_subset, h_B_card, h_pair_card]
    have h_card_le : (t ∩ cfg.B).card ≤ 1 := by
      calc (t ∩ cfg.B).card ≤ (cfg.B \ {cfg.v_ab, cfg.v_bc}).card := Finset.card_le_card h_subset
        _ = 1 := h_remove_card
    omega

  -- Case X = C: C = {v_bc, v_cd, c_priv}, shared = {v_bc, v_cd}
  · by_contra h_avoid
    push_neg at h_avoid
    have h_subset : t ∩ cfg.C ⊆ cfg.C \ {cfg.v_bc, cfg.v_cd} := by
      intro x hx
      simp only [Finset.mem_inter] at hx
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hx.2, ?_, ?_⟩
      · intro heq; subst heq
        exact h_avoid cfg.v_bc (by simp [sharedVertices]) hx.1
      · intro heq; subst heq
        exact h_avoid cfg.v_cd (by simp [sharedVertices]) hx.1
    have h_C_card : cfg.C.card = 3 := by
      have := hM.1.1; simp at this; exact (this cfg.C cfg.hC).card_eq
    have h_remove_card : (cfg.C \ {cfg.v_bc, cfg.v_cd}).card = 1 := by
      have h1 : cfg.v_bc ∈ cfg.C := cfg.h_vbc_C
      have h2 : cfg.v_cd ∈ cfg.C := cfg.h_vcd_C
      have h3 : cfg.v_bc ≠ cfg.v_cd := cfg.h_distinct_bc_cd
      have h_pair_card : ({cfg.v_bc, cfg.v_cd} : Finset V).card = 2 := by
        rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
        simp [h3]
      have h_pair_subset : ({cfg.v_bc, cfg.v_cd} : Finset V) ⊆ cfg.C := by
        simp [h1, h2]
      rw [Finset.card_sdiff h_pair_subset, h_C_card, h_pair_card]
    have h_card_le : (t ∩ cfg.C).card ≤ 1 := by
      calc (t ∩ cfg.C).card ≤ (cfg.C \ {cfg.v_bc, cfg.v_cd}).card := Finset.card_le_card h_subset
        _ = 1 := h_remove_card
    omega

  -- Case X = D: D = {v_cd, v_da, d_priv}, shared = {v_cd, v_da}
  · by_contra h_avoid
    push_neg at h_avoid
    have h_subset : t ∩ cfg.D ⊆ cfg.D \ {cfg.v_cd, cfg.v_da} := by
      intro x hx
      simp only [Finset.mem_inter] at hx
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hx.2, ?_, ?_⟩
      · intro heq; subst heq
        exact h_avoid cfg.v_cd (by simp [sharedVertices]) hx.1
      · intro heq; subst heq
        exact h_avoid cfg.v_da (by simp [sharedVertices]) hx.1
    have h_D_card : cfg.D.card = 3 := by
      have := hM.1.1; simp at this; exact (this cfg.D cfg.hD).card_eq
    have h_remove_card : (cfg.D \ {cfg.v_cd, cfg.v_da}).card = 1 := by
      have h1 : cfg.v_cd ∈ cfg.D := cfg.h_vcd_D
      have h2 : cfg.v_da ∈ cfg.D := cfg.h_vda_D
      have h3 : cfg.v_cd ≠ cfg.v_da := cfg.h_distinct_cd_da
      have h_pair_card : ({cfg.v_cd, cfg.v_da} : Finset V).card = 2 := by
        rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
        simp [h3]
      have h_pair_subset : ({cfg.v_cd, cfg.v_da} : Finset V) ⊆ cfg.D := by
        simp [h1, h2]
      rw [Finset.card_sdiff h_pair_subset, h_D_card, h_pair_card]
    have h_card_le : (t ∩ cfg.D).card ≤ 1 := by
      calc (t ∩ cfg.D).card ≤ (cfg.D \ {cfg.v_cd, cfg.v_da}).card := Finset.card_le_card h_subset
        _ = 1 := h_remove_card
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- DIAGONAL SPOKES COVER
-- ══════════════════════════════════════════════════════════════════════════════

/-- Diagonal spokes: 8 edges connecting consecutive corners -/
def diagonalSpokes (cfg : Cycle4 G M) : Finset (Sym2 V) :=
  { s(cfg.v_ab, cfg.v_da), s(cfg.v_ab, cfg.v_bc),  -- at v_ab
    s(cfg.v_bc, cfg.v_ab), s(cfg.v_bc, cfg.v_cd),  -- at v_bc
    s(cfg.v_cd, cfg.v_bc), s(cfg.v_cd, cfg.v_da),  -- at v_cd
    s(cfg.v_da, cfg.v_cd), s(cfg.v_da, cfg.v_ab) } -- at v_da

/-- The diagonal spokes reduce to just 4 unique edges -/
lemma diagonalSpokes_eq_four (cfg : Cycle4 G M) :
    diagonalSpokes cfg = { s(cfg.v_ab, cfg.v_da), s(cfg.v_ab, cfg.v_bc),
                           s(cfg.v_bc, cfg.v_cd), s(cfg.v_cd, cfg.v_da) } := by
  simp only [diagonalSpokes]
  ext e
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor <;> intro h
  · -- LTR: use Sym2 commutativity
    rcases h with h | h | h | h | h | h | h | h
    all_goals { simp only [Sym2.eq_swap] at h ⊢; aesop }
  · -- RTL
    rcases h with h | h | h | h
    all_goals { simp only [Sym2.eq_swap] at h ⊢; aesop }

/-- Diagonal spokes have cardinality exactly 4 -/
lemma diagonalSpokes_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4 G M)
    (h_ab_da : G.Adj cfg.v_ab cfg.v_da)
    (h_ab_bc : G.Adj cfg.v_ab cfg.v_bc)
    (h_bc_cd : G.Adj cfg.v_bc cfg.v_cd)
    (h_cd_da : G.Adj cfg.v_cd cfg.v_da) :
    (diagonalSpokes cfg).card ≤ 4 := by
  rw [diagonalSpokes_eq_four]
  simp only [Finset.card_insert_of_not_mem, Finset.card_singleton]
  sorry -- Aristotle: just need to show elements are distinct using distinctness axioms

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: External triangles at v share edge with M-element containing v
-- ══════════════════════════════════════════════════════════════════════════════

/-- External vertices at v cannot form edges (would create uncoverable triangle) -/
lemma no_external_edge_at_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ sharedVertices cfg)
    (x y : V) (hx : G.Adj v x) (hy : G.Adj v y)
    (hxy : G.Adj x y)
    (h_x_not_in_M : ∀ X ∈ M, x ∉ X ∨ v ∉ X)
    (h_y_not_in_M : ∀ X ∈ M, y ∉ X ∨ v ∉ X) :
    False := by
  -- Triangle {v, x, y} exists
  -- But it doesn't share edge with any M-element (contradiction)
  sorry -- Aristotle: construct triangle, apply triangle_shares_edge_with_packing

-- ══════════════════════════════════════════════════════════════════════════════
-- SUNFLOWER COVER AT VERTEX
-- ══════════════════════════════════════════════════════════════════════════════

/-- At each shared vertex, 2 edges suffice to cover all triangles through it -/
lemma sunflower_cover_at_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ sharedVertices cfg) :
    ∃ E_v : Finset (Sym2 V), E_v.card ≤ 2 ∧
      ∀ t ∈ G.cliqueFinset 3, v ∈ t → ∃ e ∈ E_v, e ∈ t.sym2 := by
  -- Key insight: Link graph L_v is bipartite (no external-external edges)
  -- By König's theorem, τ(L_v) = ν(L_v) ≤ 2
  -- The 2 diagonal spokes at v cover all triangles

  -- Case on which shared vertex v is
  simp only [sharedVertices, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl

  -- v = v_ab: use {v_ab, v_da} and {v_ab, v_bc}
  · use {s(cfg.v_ab, cfg.v_da), s(cfg.v_ab, cfg.v_bc)}
    constructor
    · -- cardinality ≤ 2
      simp only [Finset.card_insert_of_not_mem, Finset.card_singleton]
      sorry -- Aristotle: show s(v_ab, v_da) ≠ s(v_ab, v_bc)
    · -- covers all triangles through v_ab
      intro t ht hvt
      -- t contains v_ab and some x, y with xy edge
      -- Either {v_ab, x} ∈ M-edge (covered by diagonal) or external (impossible)
      sorry -- Aristotle: main case analysis using no_external_edge_at_v

  -- v = v_bc: use {v_bc, v_ab} and {v_bc, v_cd}
  · use {s(cfg.v_bc, cfg.v_ab), s(cfg.v_bc, cfg.v_cd)}
    constructor
    · simp only [Finset.card_insert_of_not_mem, Finset.card_singleton]
      sorry
    · intro t ht hvt
      sorry

  -- v = v_cd: use {v_cd, v_bc} and {v_cd, v_da}
  · use {s(cfg.v_cd, cfg.v_bc), s(cfg.v_cd, cfg.v_da)}
    constructor
    · simp only [Finset.card_insert_of_not_mem, Finset.card_singleton]
      sorry
    · intro t ht hvt
      sorry

  -- v = v_da: use {v_da, v_cd} and {v_da, v_ab}
  · use {s(cfg.v_da, cfg.v_cd), s(cfg.v_da, cfg.v_ab)}
    constructor
    · simp only [Finset.card_insert_of_not_mem, Finset.card_singleton]
      sorry
    · intro t ht hvt
      sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 (via sunflower covers)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle is covered by the union of sunflower covers at shared vertices -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- Get sunflower cover at each shared vertex
  obtain ⟨E_ab, h_ab_card, h_ab_cover⟩ := sunflower_cover_at_vertex G M hM cfg cfg.v_ab
    (by simp [sharedVertices])
  obtain ⟨E_bc, h_bc_card, h_bc_cover⟩ := sunflower_cover_at_vertex G M hM cfg cfg.v_bc
    (by simp [sharedVertices])
  obtain ⟨E_cd, h_cd_card, h_cd_cover⟩ := sunflower_cover_at_vertex G M hM cfg cfg.v_cd
    (by simp [sharedVertices])
  obtain ⟨E_da, h_da_card, h_da_cover⟩ := sunflower_cover_at_vertex G M hM cfg cfg.v_da
    (by simp [sharedVertices])

  -- Union of all covers
  let E := E_ab ∪ E_bc ∪ E_cd ∪ E_da

  -- E has cardinality ≤ 8
  have h_card : E.card ≤ 8 := by
    calc E.card = (E_ab ∪ E_bc ∪ E_cd ∪ E_da).card := rfl
      _ ≤ (E_ab ∪ E_bc ∪ E_cd).card + E_da.card := Finset.card_union_le _ _
      _ ≤ (E_ab ∪ E_bc).card + E_cd.card + E_da.card := by
          have := Finset.card_union_le (E_ab ∪ E_bc) E_cd; omega
      _ ≤ E_ab.card + E_bc.card + E_cd.card + E_da.card := by
          have := Finset.card_union_le E_ab E_bc; omega
      _ ≤ 2 + 2 + 2 + 2 := by omega
      _ = 8 := by norm_num

  -- E covers all triangles (every triangle contains a shared vertex)
  have h_cover : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
    intro t ht
    obtain ⟨v, hv_shared, hv_in_t⟩ := cycle4_triangle_contains_shared G M hM cfg t ht
    simp only [sharedVertices, Finset.mem_insert, Finset.mem_singleton] at hv_shared
    rcases hv_shared with rfl | rfl | rfl | rfl
    · obtain ⟨e, he_in, he_cover⟩ := h_ab_cover t ht hv_in_t
      exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ he_in)), he_cover⟩
    · obtain ⟨e, he_in, he_cover⟩ := h_bc_cover t ht hv_in_t
      exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ he_in)), he_cover⟩
    · obtain ⟨e, he_in, he_cover⟩ := h_cd_cover t ht hv_in_t
      exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_right _ he_in), he_cover⟩
    · obtain ⟨e, he_in, he_cover⟩ := h_da_cover t ht hv_in_t
      exact ⟨e, Finset.mem_union_right _ he_in, he_cover⟩

  -- E is a valid cover (need to show E ⊆ G.edgeFinset)
  have h_subset : E ⊆ G.edgeFinset := by
    -- The sunflower covers contain edges from triangles at shared vertices
    -- These are all graph edges
    sorry -- Aristotle: need to track that E_v ⊆ G.edgeFinset from sunflower_cover_at_vertex

  have h_valid : isTriangleCover G E := ⟨h_subset, h_cover⟩

  -- Extract minimum
  have h_in : E ∈ G.edgeFinset.powerset.filter (isTriangleCover G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h_subset, h_valid⟩

  unfold triangleCoveringNumber
  have h_nonempty : (G.edgeFinset.powerset.filter (isTriangleCover G)).Nonempty := ⟨E, h_in⟩
  have h_img_nonempty : (Finset.image Finset.card (G.edgeFinset.powerset.filter (isTriangleCover G))).Nonempty :=
    Finset.Nonempty.image h_nonempty Finset.card
  obtain ⟨n, hn⟩ := Finset.Nonempty.min_eq_some h_img_nonempty
  rw [hn]
  simp only [Option.getD]
  have h_n_le : n ≤ E.card := by
    have := Finset.min_le (Finset.mem_image_of_mem Finset.card h_in)
    rw [hn] at this
    simp at this
    exact this
  omega

end
