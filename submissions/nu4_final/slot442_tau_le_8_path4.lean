/-
  slot442_tau_le_8_path4.lean (CORRECTED v2)

  MAIN THEOREM: τ ≤ 8 for PATH_4 (ν = 4)

  MULTI-AGENT DEBATE CONSENSUS (Jan 16, 2026):
  - Grok, Gemini, Codex all agree τ ≤ 8 is achievable
  - Key insight: ANY 2-edge selection from triangle covers all 3 vertices (pigeonhole)
  - This means bridges (which contain shared vertices) are automatically covered

  CRITICAL FIX (v2): Edge selection must be ADAPTIVE, not FIXED
  - v1 bug: Fixed spokes for endpoints, spine+leg for middles
  - v1 failure: Doesn't cover S_e externals on unselected edge types
  - v2 fix: Use slot422's adaptive case-split based on which S_e types exist

  STRATEGY: Component-wise Adaptive Assembly
  Cover = C_A ∪ C_B ∪ C_C ∪ C_D where each C_i has ≤ 2 edges (adaptive selection)

  PROVEN COMPONENTS:
  - slot412: not_all_three_edge_types (at most 2 S_e external types exist)
  - slot422: exists_two_edges_cover_Se (2 edges ADAPTIVELY cover S_e externals)
  - slot441: bridge_contains_shared (bridges contain shared vertex)

  TIER: 2 (uses proven scaffolding, assembly theorem)
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

/-- S_e: Externals of e that DON'T share edge with other M-elements -/
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => t ≠ e ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

/-- S_e elements using specific edge {a,b} of e = {a,b,c} -/
def S_e_edge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (a b c : V) : Finset (Finset V) :=
  (S_e G M {a, b, c}).filter (fun T => a ∈ T ∧ b ∈ T ∧ c ∉ T)

/-- Valid edge cover: subset of G.edgeFinset that hits every triangle -/
def isValidCover (G : SimpleGraph V) [DecidableRel G.Adj] (Cover : Finset (Sym2 V)) : Prop :=
  Cover ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ Cover, e ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

/-- PATH_4: Four triangles sharing vertices in a path: A—v₁—B—v₂—C—v₃—D -/
structure Path4Config (G : SimpleGraph V) [DecidableRel G.Adj] where
  A B C D : Finset V
  v₁ v₂ v₃ : V
  a₁ a₂ b c d₁ d₂ : V
  -- Triangle definitions
  hA_eq : A = {a₁, a₂, v₁}
  hB_eq : B = {v₁, b, v₂}
  hC_eq : C = {v₂, c, v₃}
  hD_eq : D = {v₃, d₁, d₂}
  -- All are cliques
  hA_clq : A ∈ G.cliqueFinset 3
  hB_clq : B ∈ G.cliqueFinset 3
  hC_clq : C ∈ G.cliqueFinset 3
  hD_clq : D ∈ G.cliqueFinset 3
  -- PATH structure: adjacent elements share exactly one vertex
  hAB : A ∩ B = {v₁}
  hBC : B ∩ C = {v₂}
  hCD : C ∩ D = {v₃}
  -- Non-adjacent elements are disjoint (or share at most one vertex)
  hAC_disjoint : Disjoint A C
  hAD_disjoint : Disjoint A D
  hBD_disjoint : Disjoint B D
  -- Distinctness within each triangle
  h_A_dist : a₁ ≠ a₂ ∧ a₁ ≠ v₁ ∧ a₂ ≠ v₁
  h_B_dist : v₁ ≠ b ∧ v₁ ≠ v₂ ∧ b ≠ v₂
  h_C_dist : v₂ ≠ c ∧ v₂ ≠ v₃ ∧ c ≠ v₃
  h_D_dist : v₃ ≠ d₁ ∧ v₃ ≠ d₂ ∧ d₁ ≠ d₂

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Bridge contains shared vertex (from slot441)
-- ══════════════════════════════════════════════════════════════════════════════

theorem bridge_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
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

/-
PROOF SKETCH (from debate consensus):
A triangle X = {a, b, c} has 3 edges: {a,b}, {a,c}, {b,c}.
Any 2 edges from X cover all 3 vertices (by pigeonhole).
Therefore any T with |T ∩ X| ≥ 2 shares at least one of the 2 selected edges.
-/

lemma two_edges_cover_all_vertices (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (e₁ e₂ : Sym2 V)
    (he₁ : e₁ = s(a, b) ∨ e₁ = s(a, c) ∨ e₁ = s(b, c))
    (he₂ : e₂ = s(a, b) ∨ e₂ = s(a, c) ∨ e₂ = s(b, c))
    (hne : e₁ ≠ e₂) :
    (∃ x ∈ ({a, b, c} : Finset V), s(a, x) = e₁ ∨ s(a, x) = e₂) ∧
    (∃ x ∈ ({a, b, c} : Finset V), s(b, x) = e₁ ∨ s(b, x) = e₂) ∧
    (∃ x ∈ ({a, b, c} : Finset V), s(c, x) = e₁ ∨ s(c, x) = e₂) := by
  -- Two distinct edges from 3 must cover all 3 vertices
  -- Case analysis on which edges are selected
  rcases he₁ with rfl | rfl | rfl <;> rcases he₂ with rfl | rfl | rfl <;>
  simp_all [Sym2.eq_iff]

/-
PROOF SKETCH:
If T shares edge with X (|T ∩ X| ≥ 2), and our 2 edges cover all 3 vertices of X,
then T shares at least one of those edges.
-/

lemma sharing_triangle_hit_by_two_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (a b c : V)
    (hX_eq : X = {a, b, c})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hX_clq : X ∈ G.cliqueFinset 3)
    (e₁ e₂ : Sym2 V)
    (he₁_in : e₁ ∈ G.edgeFinset)
    (he₂_in : e₂ ∈ G.edgeFinset)
    (he₁_X : e₁ = s(a, b) ∨ e₁ = s(a, c) ∨ e₁ = s(b, c))
    (he₂_X : e₂ = s(a, b) ∨ e₂ = s(a, c) ∨ e₂ = s(b, c))
    (hne : e₁ ≠ e₂)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTX : 2 ≤ (T ∩ X).card) :
    e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
  -- T shares at least 2 vertices with X = {a,b,c}
  -- So T shares at least one EDGE with X
  -- Our two edges cover 2 of the 3 edges of X
  -- Therefore T is hit by e₁ or e₂
  rw [hX_eq] at hTX
  -- Get which vertices of {a,b,c} are in T
  have h_two : ∃ u v : V, u ∈ ({a, b, c} : Finset V) ∧ v ∈ ({a, b, c} : Finset V) ∧
               u ≠ v ∧ u ∈ T ∧ v ∈ T := by
    have h2 := hTX
    simp only [ge_iff_le] at h2
    have hT_card : T.card = 3 := by
      rw [SimpleGraph.mem_cliqueFinset_iff] at hT; exact hT.2
    -- Two elements from {a,b,c} must be in T
    by_contra h_contra
    push_neg at h_contra
    -- Count elements of T ∩ {a,b,c}
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
  -- The edge {u, v} is one of {a,b}, {a,c}, {b,c}
  simp only [mem_insert, mem_singleton] at hu_abc hv_abc
  -- Case analysis: which pair is it?
  rcases hu_abc with rfl | rfl | rfl <;> rcases hv_abc with rfl | rfl | rfl <;>
    try exact absurd rfl huv_ne
  all_goals (
    -- Now we have a specific pair (u, v) in T
    -- Check if e₁ or e₂ equals s(u, v)
    rcases he₁_X with rfl | rfl | rfl <;> rcases he₂_X with rfl | rfl | rfl <;>
    simp_all [Sym2.eq_iff, Finset.mk_mem_sym2_iff]
  )

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH (ADAPTIVE ASSEMBLY - per multi-agent debate consensus):

CONSTRUCTION (existential via slot422):
For each E ∈ {A, B, C, D}, apply slot422 (exists_two_edges_cover_Se) to get:
  - C_A = {e₁_A, e₂_A} covering A and S_e(A)
  - C_B = {e₁_B, e₂_B} covering B and S_e(B)
  - C_C = {e₁_C, e₂_C} covering C and S_e(C)
  - C_D = {e₁_D, e₂_D} covering D and S_e(D)

Let Cover = C_A ∪ C_B ∪ C_C ∪ C_D

EDGE SELECTION IS ADAPTIVE (NOT FIXED):
- If S_e^{a,b} empty → use {s(b,c), s(a,c)}
- If S_e^{b,c} empty → use {s(a,b), s(a,c)}
- If S_e^{a,c} empty → use {s(a,b), s(b,c)}
slot422 case-splits on which type is empty (at most 2 of 3 are nonempty by h_6pack).

CARDINALITY: |Cover| ≤ |C_A| + |C_B| + |C_C| + |C_D| ≤ 2 + 2 + 2 + 2 = 8

COVERAGE PROOF:
1. T ∈ M (self-coverage): slot422 guarantees C_E covers E
2. T ∈ S_e(E) (pure externals): slot422 guarantees C_E covers all S_e(E)
3. T is bridge between adjacent E,F (shares edge with both):
   - T contains shared vertex v (by bridge_contains_shared + PATH_4 intersection hypotheses)
   - Any 2 edges from E cover all 3 vertices of E (by two_edges_cover_all_vertices)
   - Therefore v is incident to at least one edge in C_E
   - T contains v → T shares that edge → T is covered
4. Non-adjacent elements (A-C, A-D, B-D) are disjoint → no bridges between them
-/

theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Path4Config G)
    (M : Finset (Finset V)) (hM : M = {P.A, P.B, P.C, P.D})
    (hPacking : isTrianglePacking G M)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, 2 ≤ (T ∩ E).card)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    -- Hypothesis from slot412: At most 2 of 3 edge types have externals
    (h_6pack : ∀ E ∈ M, ∀ a b c : V, E = {a, b, c} →
      ¬((S_e_edge G M a b c).Nonempty ∧ (S_e_edge G M b c a).Nonempty ∧ (S_e_edge G M a c b).Nonempty)) :
    ∃ Cover : Finset (Sym2 V),
      Cover.card ≤ 8 ∧
      Cover ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ Cover, e ∈ T.sym2 := by
  /-
  Step 1: Apply slot422 to each M-element to get 2-edge covers
  Step 2: Form union Cover = C_A ∪ C_B ∪ C_C ∪ C_D
  Step 3: Prove |Cover| ≤ 8 by subadditivity
  Step 4: Prove Cover ⊆ G.edgeFinset (each C_i is)
  Step 5: Prove coverage by cases:
    - T ∈ M → covered by construction (any 2 edges cover the triangle)
    - T ∈ S_e(E) → covered by slot422 guarantee
    - T is bridge → by bridge_contains_shared, T contains shared vertex
                   → by two_edges_cover_all_vertices, our 2 edges cover that vertex
                   → T is hit
  -/
  sorry

end
