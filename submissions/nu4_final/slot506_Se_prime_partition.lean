/-
  slot506_Se_prime_partition.lean

  S_e' PARTITION WITH MIN-INDEX BRIDGE ASSIGNMENT

  Multi-Agent Debate Consensus (Jan 23, 2026):
  - Grok, Gemini, Codex all agreed: bridges escape original S_e
  - Solution: Min-index assignment assigns each bridge to exactly one S_e'
  - Constrained edge selection: include bridge's shared edge in cover

  KEY INSIGHT (Grok Round 2):
  "Constrain edge selection to include at least one edge from each bridge's
   shared set. Feasible by Hall's Marriage Theorem when bridges ≤ 2 per element."

  TIER: 2 (partition + constrained selection)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- CORE DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaximalPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ e ∈ M, (T ∩ e).card ≥ 2

/-- Original S_e: Triangles sharing edge with e, edge-disjoint from other M-elements -/
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧
    2 ≤ (T ∩ e).card ∧
    ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

/-- Bridge: Triangle sharing ≥2 vertices with multiple M-elements -/
def isBridge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧
  T ∉ M ∧
  ∃ e f : Finset V, e ∈ M ∧ f ∈ M ∧ e ≠ f ∧ 2 ≤ (T ∩ e).card ∧ 2 ≤ (T ∩ f).card

/-- Elements that T shares edge with (has ≥2 vertex intersection) -/
def sharesEdgeWith (M : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  M.filter (fun e => 2 ≤ (T ∩ e).card)

/-- S_e': Extended S_e including bridges via min-index assignment -/
def S_e' (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V)
    (idx : Finset V → ℕ) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧
    2 ≤ (T ∩ e).card ∧
    -- T is assigned to e if e has the minimum index among all M-elements T shares edge with
    (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 1: S_e ⊆ S_e'
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. If T ∈ S_e, then T shares edge only with e (among M-elements)
2. Therefore sharesEdgeWith M T = {e}
3. No f with idx f < idx e exists in sharesEdgeWith
4. So T ∈ S_e'
-/
lemma S_e_subset_S_e' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e ∈ M)
    (idx : Finset V → ℕ) :
    S_e G M e ⊆ S_e' G M e idx := by
  intro T hT
  simp only [S_e, S_e', mem_filter] at hT ⊢
  refine ⟨hT.1, hT.2.1, hT.2.2.1, ?_⟩
  -- T only shares edge with e, so no f with smaller index exists
  ext f
  simp only [mem_filter, not_mem_empty, iff_false, not_and]
  intro hf_shares hf_lt
  -- f ∈ sharesEdgeWith M T means 2 ≤ (T ∩ f).card
  simp only [sharesEdgeWith, mem_filter] at hf_shares
  have hf_M := hf_shares.1
  have hf_inter := hf_shares.2
  -- But T ∈ S_e means (T ∩ f).card ≤ 1 for f ≠ e
  by_cases hfe : f = e
  · -- f = e contradicts idx f < idx e
    subst hfe
    exact Nat.lt_irrefl _ hf_lt
  · -- f ≠ e means (T ∩ f).card ≤ 1
    have := hT.2.2.2 f hf_M hfe
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 2: Bridges are in exactly one S_e'
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Bridge T shares edge with ≥2 M-elements
2. Let e = argmin { idx f | T shares edge with f }
3. T ∈ S_e' by definition (no f with smaller index)
4. T ∉ S_f' for any f ≠ e with idx f > idx e (e would be in the filter)
-/
lemma bridge_in_unique_Se' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (T : Finset V) (hT_bridge : isBridge G M T) :
    ∃! e, e ∈ M ∧ T ∈ S_e' G M e idx := by
  obtain ⟨hT_clique, hT_notM, e, f, he, hf, hef, he_inter, hf_inter⟩ := hT_bridge
  -- sharesEdgeWith M T is nonempty (contains e and f)
  have h_nonempty : (sharesEdgeWith M T).Nonempty := by
    use e
    simp only [sharesEdgeWith, mem_filter]
    exact ⟨he, he_inter⟩
  -- Let e_min be the element with minimum idx in sharesEdgeWith
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 3: Every non-M triangle is in some S_e'
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. If T ∉ M and T is a triangle, maximality gives some e ∈ M with (T ∩ e).card ≥ 2
2. So sharesEdgeWith M T is nonempty
3. Let e_min = argmin { idx f | f ∈ sharesEdgeWith M T }
4. Then T ∈ S_e_min' by definition
-/
lemma non_M_triangle_in_some_Se' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) (hT_notM : T ∉ M) :
    ∃ e ∈ M, T ∈ S_e' G M e idx := by
  -- By maximality, T shares edge with some M-element
  obtain ⟨e, he, he_inter⟩ := hM.2 T hT hT_notM
  -- sharesEdgeWith M T is nonempty
  have h_nonempty : (sharesEdgeWith M T).Nonempty := by
    use e
    simp only [sharesEdgeWith, mem_filter]
    exact ⟨he, he_inter⟩
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 4: S_e' sets are disjoint
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. If T ∈ S_e' ∩ S_f' for e ≠ f
2. WLOG idx e < idx f
3. T ∈ S_f' means no g with idx g < idx f shares edge with T
4. But T ∈ S_e' means T shares edge with e, and idx e < idx f
5. Contradiction
-/
lemma S_e'_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx) :
    Disjoint (S_e' G M e idx) (S_e' G M f idx) := by
  rw [Finset.disjoint_iff_ne]
  intro T hT_e T' hT_f hTT'
  subst hTT'
  simp only [S_e', mem_filter] at hT_e hT_f
  -- T shares edge with both e and f
  -- But one of idx e, idx f is smaller
  by_cases h : idx e < idx f
  · -- idx e < idx f, so e ∈ (sharesEdgeWith M T).filter (idx · < idx f)
    have : e ∈ (sharesEdgeWith M T).filter (fun g => idx g < idx f) := by
      simp only [mem_filter, sharesEdgeWith, mem_filter]
      exact ⟨⟨he, hT_e.2.2.1⟩, h⟩
    -- But hT_f says this filter is empty
    rw [hT_f.2.2.2] at this
    exact not_mem_empty e this
  · push_neg at h
    have h' : idx f < idx e ∨ idx f = idx e := Nat.lt_or_eq_of_le h
    rcases h' with h_lt | h_eq
    · -- idx f < idx e, so f ∈ (sharesEdgeWith M T).filter (idx · < idx e)
      have : f ∈ (sharesEdgeWith M T).filter (fun g => idx g < idx e) := by
        simp only [mem_filter, sharesEdgeWith, mem_filter]
        exact ⟨⟨hf, hT_f.2.2.1⟩, h_lt⟩
      rw [hT_e.2.2.2] at this
      exact not_mem_empty f this
    · -- idx e = idx f contradicts injectivity (e ≠ f)
      have := h_inj h_eq
      exact hef this

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 5: Bridge contains shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH (from slot441, PROVEN):
1. If T shares ≥2 vertices with e AND ≥2 vertices with f
2. And e ∩ f = {v} (single shared vertex)
3. Then v ∈ T by cardinality argument
-/
lemma bridge_contains_shared_vertex (e f T : Finset V)
    (he3 : e.card = 3) (hf3 : f.card = 3) (hT3 : T.card = 3)
    (he_inter : 2 ≤ (T ∩ e).card) (hf_inter : 2 ≤ (T ∩ f).card)
    (hef_inter : (e ∩ f).card = 1) :
    ∃ v, e ∩ f = {v} ∧ v ∈ T := by
  -- e ∩ f is a singleton
  obtain ⟨v, hv⟩ := card_eq_one.mp hef_inter
  use v
  constructor
  · exact hv
  · -- T ∩ e has ≥2 elements, T ∩ f has ≥2 elements
    -- (T ∩ e) ∩ (T ∩ f) = T ∩ (e ∩ f) = T ∩ {v}
    -- If v ∉ T, then T ∩ {v} = ∅
    -- But |T ∩ e| + |T ∩ f| ≥ 4, and |T| = 3
    -- By inclusion-exclusion: |T ∩ e ∪ T ∩ f| = |T ∩ e| + |T ∩ f| - |T ∩ e ∩ f|
    -- ≤ |T| = 3, so |T ∩ e ∩ f| ≥ 4 - 3 = 1
    -- Therefore T ∩ (e ∩ f) ≠ ∅, so v ∈ T
    by_contra hv_notT
    have h1 : (T ∩ e ∩ f).card ≥ 1 := by
      have h_union : (T ∩ e ∪ T ∩ f).card ≤ T.card := card_le_card (union_subset (inter_subset_left) (inter_subset_left))
      have h_ie : (T ∩ e ∪ T ∩ f).card = (T ∩ e).card + (T ∩ f).card - (T ∩ e ∩ T ∩ f).card := by
        rw [card_union_eq_card_add_card_sub_card_inter]
        simp only [inter_inter_distrib_left]
      simp only [inter_inter_distrib_left] at h_ie
      rw [hT3] at h_union
      omega
    have h2 : T ∩ e ∩ f = T ∩ (e ∩ f) := inter_inter_distrib_left T e f
    rw [h2, hv] at h1
    simp only [inter_singleton_of_not_mem hv_notT, card_empty] at h1
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 6: Spoke from shared vertex covers bridge
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Bridge T contains shared vertex v (by lemma 5)
2. T = {v, x, y} for some x, y
3. Edge {v, x} or {v, y} is in T.sym2
4. If our cover includes any spoke from v, it hits T
-/
lemma spoke_covers_bridge (T e : Finset V) (v : V)
    (hT3 : T.card = 3) (hv_T : v ∈ T) (hv_e : v ∈ e) :
    ∃ u ∈ T, u ≠ v ∧ Sym2.mk v u ∈ T.sym2 := by
  -- T has 3 elements including v, so there exist x, y ∈ T with x ≠ v, y ≠ v
  have h_card : (T.erase v).card = 2 := by
    rw [card_erase_of_mem hv_T, hT3]
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < (T.erase v).card)
  use x
  simp only [mem_erase] at hx
  refine ⟨erase_subset v T hx, hx.1, ?_⟩
  rw [Finset.mem_sym2_iff]
  exact ⟨hv_T, erase_subset v T hx⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 7: Two edges cover 3-vertex set
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. For any 3-vertex set {a, b, c}, any 2 edges cover all 3 vertices
2. By pigeonhole: 2 edges have 4 endpoint slots, 3 vertices, so some vertex hit twice
3. All 3 must be hit (each edge is between 2 of them)
-/
lemma two_edges_cover_all_vertices (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (e1 e2 : Sym2 V) (he1 : e1 ∈ ({a, b, c} : Finset V).sym2) (he2 : e2 ∈ ({a, b, c} : Finset V).sym2)
    (hne : e1 ≠ e2) :
    ∀ v ∈ ({a, b, c} : Finset V), v ∈ e1 ∨ v ∈ e2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 8: At most 2 edge-types have externals (6-packing)
-- ══════════════════════════════════════════════════════════════════════════════

-- AXIOM from slot412 (PROVEN, 0 sorry there)
axiom not_all_three_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬(∃ T1 T2 T3 : Finset V,
      T1 ∈ S_e G M {a, b, c} ∧ a ∈ T1 ∧ b ∈ T1 ∧ c ∉ T1 ∧
      T2 ∈ S_e G M {a, b, c} ∧ b ∈ T2 ∧ c ∈ T2 ∧ a ∉ T2 ∧
      T3 ∈ S_e G M {a, b, c} ∧ a ∈ T3 ∧ c ∈ T3 ∧ b ∉ T3)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 9: 2 edges suffice for S_e
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. At most 2 of 3 edge-types have externals (by 6-packing)
2. Select 1 edge per populated type
3. These 2 edges cover all S_e externals
-/
lemma two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ ∀ T ∈ S_e G M e, ∃ edge ∈ E, edge ∈ T.sym2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 10: Bridges ≤ 2 per element in PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. In PATH_4 (A-B-C-D), bridges only between adjacent pairs
2. A-B bridges share v1, B-C bridges share v2, C-D bridges share v3
3. Under min-index, A gets A-B bridges, B gets B-C bridges (not A-B), etc.
4. Each element gets bridges from at most 1 junction → ≤2 bridges
-/
lemma bridges_le_2_per_element_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hM : M = {A, B, C, D})
    (hAB : (A ∩ B).card = 1) (hBC : (B ∩ C).card = 1) (hCD : (C ∩ D).card = 1)
    (hAC : (A ∩ C).card = 0) (hAD : (A ∩ D).card = 0) (hBD : (B ∩ D).card = 0)
    (idx : Finset V → ℕ) (hidx : idx A < idx B ∧ idx B < idx C ∧ idx C < idx D)
    (e : Finset V) (he : e ∈ M) :
    (S_e' G M e idx \ S_e G M e).card ≤ 2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 11: Constrained selection exists
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. S_e externals use at most 2 edge-types (6-packing)
2. Bridges share edge with e, which is one of 3 edge-types
3. If bridges ≤ 2, we can select 2 edges covering:
   - Both populated external types
   - The bridge's shared edge type
4. By Hall's, such selection exists when demands ≤ 3 and edges = 3
-/
lemma constrained_selection_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M)
    (idx : Finset V → ℕ)
    (h_bridges_le_2 : (S_e' G M e idx \ S_e G M e).card ≤ 2) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧
      E ⊆ e.sym2 ∧
      (∀ T ∈ S_e' G M e idx, ∃ edge ∈ E, edge ∈ T.sym2) := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: PARTITION LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Every triangle T is either in M or shares edge with some M-element (maximality)
2. If T ∉ M, let e_min = argmin { idx f | T shares edge with f }
3. By definition, T ∈ S_e_min'
4. Uniqueness: S_e' sets are disjoint (lemma 4)
-/
theorem triangle_in_some_Se'_or_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨ ∃ e ∈ M, T ∈ S_e' G M e idx := by
  by_cases hT_M : T ∈ M
  · left; exact hT_M
  · right
    exact non_M_triangle_in_some_Se' G M hM idx h_inj T hT hT_M

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ(S_e') ≤ 2
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. By constrained_selection_exists, get 2 edges E covering S_e'
2. These are actual graph edges (from e.sym2 ⊆ G.edgeFinset since e is clique)
3. Therefore τ(S_e') ≤ 2
-/
theorem tau_Se'_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M)
    (idx : Finset V → ℕ)
    (h_bridges_le_2 : (S_e' G M e idx \ S_e G M e).card ≤ 2) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧
      (∀ T ∈ S_e' G M e idx, ∃ edge ∈ E, edge ∈ T.sym2) :=
  constrained_selection_exists G M hM hNu4 e he idx h_bridges_le_2

-- ══════════════════════════════════════════════════════════════════════════════
-- ASSEMBLY: τ ≤ 8 from partition
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Every triangle is in M or some S_e' (partition lemma)
2. M-elements covered by their own edges
3. Each S_e' covered by ≤2 edges
4. Total: ≤ 4 × 2 = 8 edges
-/
theorem tau_le_8_from_Se'_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hM4 : M.card = 4)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (h_bridges_bound : ∀ e ∈ M, (S_e' G M e idx \ S_e G M e).card ≤ 2) :
    ∃ Cover : Finset (Sym2 V), Cover.card ≤ 8 ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ edge ∈ Cover, edge ∈ T.sym2 := by
  sorry

end
