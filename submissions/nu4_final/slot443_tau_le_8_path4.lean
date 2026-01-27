/-
  slot443_tau_le_8_path4.lean

  MAIN THEOREM: τ ≤ 8 for PATH_4 (ν = 4)

  FIXED: Explicit type class parameters (Aristotle can't propagate `variable` properly)

  MULTI-AGENT DEBATE CONSENSUS (Jan 16, 2026):
  - Key insight: ANY 2-edge selection from triangle covers all 3 vertices (pigeonhole)
  - Bridges containing shared vertices are automatically covered
  - ADAPTIVE selection via slot422 case-split

  STRATEGY: Component-wise Adaptive Assembly
  Cover = C_A ∪ C_B ∪ C_C ∪ C_D where each C_i has ≤ 2 edges

  TIER: 2 (uses proven scaffolding)
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Finset

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (with explicit type class parameters)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def trianglesSharingEdge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def S_e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => t ≠ e ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def S_e_edge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (a b c : V) : Finset (Finset V) :=
  (S_e G M {a, b, c}).filter (fun T => a ∈ T ∧ b ∈ T ∧ c ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Bridge contains shared vertex (from slot441)
-- ══════════════════════════════════════════════════════════════════════════════

theorem bridge_contains_shared {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v : V) (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : 2 ≤ (T ∩ E).card) (hTF : 2 ≤ (T ∩ F).card) :
    v ∈ T := by
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT; exact hT.2
  have h_inter : (T ∩ E) ∩ (T ∩ F) = T ∩ {v} := by
    ext x; simp only [mem_inter, mem_singleton]; constructor
    · intro ⟨⟨hxT, hxE⟩, _, hxF⟩
      have hx_both : x ∈ E ∩ F := mem_inter.mpr ⟨hxE, hxF⟩
      rw [hEF] at hx_both
      exact ⟨hxT, mem_singleton.mp hx_both⟩
    · intro ⟨hxT, hxv⟩
      have hv_mem : v ∈ E ∩ F := by rw [hEF]; exact mem_singleton_self v
      rw [hxv]
      exact ⟨⟨hxT, (mem_inter.mp hv_mem).1⟩, hxT, (mem_inter.mp hv_mem).2⟩
  have h_sub : (T ∩ E) ∪ (T ∩ F) ⊆ T := by
    intro x hx; simp only [mem_union, mem_inter] at hx
    cases hx with | inl h => exact h.1 | inr h => exact h.1
  have h_ie := card_union_add_card_inter (T ∩ E) (T ∩ F)
  have h_pos : 0 < (T ∩ {v}).card := by
    rw [← h_inter]
    have h_union_le : ((T ∩ E) ∪ (T ∩ F)).card ≤ 3 := by
      calc ((T ∩ E) ∪ (T ∩ F)).card ≤ T.card := card_le_card h_sub
        _ = 3 := hT_card
    omega
  rw [card_pos] at h_pos
  obtain ⟨x, hx⟩ := h_pos
  simp only [mem_inter, mem_singleton] at hx
  exact hx.2 ▸ hx.1

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Two edges cover all vertices (pigeonhole)
-- ══════════════════════════════════════════════════════════════════════════════

lemma two_edges_cover_all_vertices {V : Type*} [DecidableEq V] (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (e1 e2 : Sym2 V)
    (he1 : e1 = s(a, b) ∨ e1 = s(a, c) ∨ e1 = s(b, c))
    (he2 : e2 = s(a, b) ∨ e2 = s(a, c) ∨ e2 = s(b, c))
    (hne : e1 ≠ e2) :
    (∃ x ∈ ({a, b, c} : Finset V), s(a, x) = e1 ∨ s(a, x) = e2) ∧
    (∃ x ∈ ({a, b, c} : Finset V), s(b, x) = e1 ∨ s(b, x) = e2) ∧
    (∃ x ∈ ({a, b, c} : Finset V), s(c, x) = e1 ∨ s(c, x) = e2) := by
  rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl <;>
  simp_all [Sym2.eq_iff]

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Triangle sharing edge hit by two edges
-- ══════════════════════════════════════════════════════════════════════════════

lemma sharing_triangle_hit_by_two_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hX_clq : {a, b, c} ∈ G.cliqueFinset 3)
    (e1 e2 : Sym2 V)
    (he1_in : e1 ∈ G.edgeFinset)
    (he2_in : e2 ∈ G.edgeFinset)
    (he1_X : e1 = s(a, b) ∨ e1 = s(a, c) ∨ e1 = s(b, c))
    (he2_X : e2 = s(a, b) ∨ e2 = s(a, c) ∨ e2 = s(b, c))
    (hne : e1 ≠ e2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTX : 2 ≤ (T ∩ {a, b, c}).card) :
    e1 ∈ T.sym2 ∨ e2 ∈ T.sym2 := by
  -- T shares at least 2 vertices with {a,b,c}
  -- So T shares at least one EDGE with {a,b,c}
  have h_two : ∃ u v : V, u ∈ ({a, b, c} : Finset V) ∧ v ∈ ({a, b, c} : Finset V) ∧
               u ≠ v ∧ u ∈ T ∧ v ∈ T := by
    have h2 := hTX
    simp only [ge_iff_le] at h2
    have hT_card : T.card = 3 := by
      rw [SimpleGraph.mem_cliqueFinset_iff] at hT; exact hT.2
    by_contra h_contra
    push_neg at h_contra
    have h_sub : T ∩ {a, b, c} ⊆ ({a, b, c} : Finset V) := inter_subset_right
    have h_card_bound : (T ∩ {a, b, c}).card ≤ 1 := by
      by_contra h_gt
      push_neg at h_gt
      have h_two_mem := Finset.one_lt_card.mp h_gt
      obtain ⟨u, hu, v, hv, huv⟩ := h_two_mem
      simp only [mem_inter] at hu hv
      exact h_contra u v hu.2 hv.2 huv hu.1 hv.1
    omega
  obtain ⟨u, v, hu_abc, hv_abc, huv_ne, hu_T, hv_T⟩ := h_two
  simp only [mem_insert, mem_singleton] at hu_abc hv_abc
  rcases hu_abc with rfl | rfl | rfl <;> rcases hv_abc with rfl | rfl | rfl <;>
    try exact absurd rfl huv_ne
  all_goals (
    rcases he1_X with rfl | rfl | rfl <;> rcases he2_X with rfl | rfl | rfl <;>
    simp_all [Sym2.eq_iff, Finset.mk_mem_sym2_iff]
  )

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH (ADAPTIVE ASSEMBLY):

PATH_4 structure: A-v1-B-v2-C-v3-D where:
  A = {a1, a2, v1}, B = {v1, b, v2}, C = {v2, c, v3}, D = {v3, d1, d2}
  A ∩ B = {v1}, B ∩ C = {v2}, C ∩ D = {v3}
  Non-adjacent pairs (A,C), (A,D), (B,D) are disjoint

CONSTRUCTION:
Apply exists_two_edges_cover_Se (slot422) to each element to get 2-edge covers:
  C_A covers A and S_e(A), C_B covers B and S_e(B), etc.
Cover = C_A ∪ C_B ∪ C_C ∪ C_D

CARDINALITY: |Cover| ≤ 2+2+2+2 = 8

COVERAGE:
1. T ∈ M: Any 2 edges cover the triangle
2. T ∈ S_e(E): slot422 guarantees coverage
3. T is bridge (shares edge with adjacent pair):
   - By bridge_contains_shared, T contains shared vertex v
   - By two_edges_cover_all_vertices, our 2 edges cover all 3 vertices of E
   - So v is incident to one of our edges → T is hit
-/

theorem tau_le_8_path4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    -- PATH_4 elements
    (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V)
    -- Triangle definitions
    (hA_eq : A = {a1, a2, v1})
    (hB_eq : B = {v1, b, v2})
    (hC_eq : C = {v2, c, v3})
    (hD_eq : D = {v3, d1, d2})
    -- All are cliques
    (hA_clq : A ∈ G.cliqueFinset 3)
    (hB_clq : B ∈ G.cliqueFinset 3)
    (hC_clq : C ∈ G.cliqueFinset 3)
    (hD_clq : D ∈ G.cliqueFinset 3)
    -- PATH structure
    (hAB : A ∩ B = {v1})
    (hBC : B ∩ C = {v2})
    (hCD : C ∩ D = {v3})
    (hAC : Disjoint A C)
    (hAD : Disjoint A D)
    (hBD : Disjoint B D)
    -- Distinctness
    (h_A_dist : a1 ≠ a2 ∧ a1 ≠ v1 ∧ a2 ≠ v1)
    (h_B_dist : v1 ≠ b ∧ v1 ≠ v2 ∧ b ≠ v2)
    (h_C_dist : v2 ≠ c ∧ v2 ≠ v3 ∧ c ≠ v3)
    (h_D_dist : v3 ≠ d1 ∧ v3 ≠ d2 ∧ d1 ≠ d2)
    -- Packing
    (M : Finset (Finset V)) (hM : M = {A, B, C, D})
    (hPacking : isTrianglePacking G M)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, 2 ≤ (T ∩ E).card)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    -- 6-packing constraint
    (h_6pack : ∀ E ∈ M, ∀ x y z : V, E = {x, y, z} →
      ¬((S_e_edge G M x y z).Nonempty ∧ (S_e_edge G M y z x).Nonempty ∧ (S_e_edge G M x z y).Nonempty)) :
    ∃ Cover : Finset (Sym2 V),
      Cover.card ≤ 8 ∧
      Cover ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ Cover, e ∈ T.sym2 := by
  sorry

end
