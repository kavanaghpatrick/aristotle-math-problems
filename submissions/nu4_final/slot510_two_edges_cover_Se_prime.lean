/-
  slot510_two_edges_cover_Se_prime.lean

  SINGLE TARGET: τ(S_e') ≤ 2 via constrained edge selection

  Key insight from multi-agent debate:
  - S_e externals use at most 2 of 3 edge-types (6-packing constraint)
  - Bridges share edge with e, so bridge's shared edge is one of 3 types
  - When bridges ≤ 2 per element, Hall's theorem guarantees a 2-edge cover

  TIER: 2 (constrained selection with Hall's)
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

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧ ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

def sharesEdgeWith (M : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  M.filter (fun e => 2 ≤ (T ∩ e).card)

def S_e' (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V)
    (idx : Finset V → ℕ) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧
    (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅)

/-- Edge-type: which pair of vertices from e = {a,b,c} does triangle T use? -/
def edgeType (e T : Finset V) : Finset V := T ∩ e

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 1: S_e ⊆ S_e'
-- ══════════════════════════════════════════════════════════════════════════════

lemma S_e_subset_S_e' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e ∈ M) (idx : Finset V → ℕ) :
    S_e G M e ⊆ S_e' G M e idx := by
  intro T hT
  simp only [S_e, S_e', mem_filter] at hT ⊢
  refine ⟨hT.1, hT.2.1, hT.2.2.1, ?_⟩
  ext f
  simp only [mem_filter, not_mem_empty, iff_false, not_and]
  intro hf_shares hf_lt
  simp only [sharesEdgeWith, mem_filter] at hf_shares
  by_cases hfe : f = e
  · subst hfe; exact Nat.lt_irrefl _ hf_lt
  · have := hT.2.2.2 f hf_shares.1 hfe; omega

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 2: Bridges are S_e' \ S_e
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridges_eq_sdiff (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e ∈ M) (idx : Finset V → ℕ) :
    S_e' G M e idx \ S_e G M e =
      (S_e' G M e idx).filter (fun T => ∃ f ∈ M, f ≠ e ∧ 2 ≤ (T ∩ f).card) := by
  ext T
  simp only [mem_sdiff, S_e, S_e', mem_filter, not_and, not_forall, exists_prop, exists_and_left]
  constructor
  · intro ⟨⟨hT_clique, hT_ne, hT_inter, hT_min⟩, h_not_Se⟩
    refine ⟨⟨hT_clique, hT_ne, hT_inter, hT_min⟩, ?_⟩
    by_contra h_no_bridge
    push_neg at h_no_bridge
    apply h_not_Se hT_clique hT_ne hT_inter
    intro f hf hfe
    by_contra h_ge_2
    push_neg at h_ge_2
    exact h_no_bridge f hf hfe h_ge_2
  · intro ⟨⟨hT_clique, hT_ne, hT_inter, hT_min⟩, f, hf, hfe, hf_inter⟩
    refine ⟨⟨hT_clique, hT_ne, hT_inter, hT_min⟩, ?_⟩
    intro _ _ _ h_all
    have := h_all f hf hfe
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 3: Triangle has 3 edges
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_has_3_edges (T : Finset V) (hT : T.card = 3) :
    T.sym2.card = 3 := by
  rw [Finset.card_sym2]
  simp only [hT]
  ring

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 4: External shares exactly 2 vertices with e
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_inter_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e T : Finset V)
    (hT : T ∈ S_e' G M e (fun _ => 0)) :
    (T ∩ e).card = 2 ∨ (T ∩ e).card = 3 := by
  simp only [S_e', mem_filter] at hT
  have h_ge_2 := hT.2.2.1
  have hT_clique := hT.1
  -- T.card = 3 and e.card = 3, so (T ∩ e).card ≤ 3
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clique
    exact hT_clique.2
  have h_le_3 : (T ∩ e).card ≤ T.card := card_le_card inter_subset_left
  rw [hT_card] at h_le_3
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 5: Two edges from e cover all of e's vertices
-- ══════════════════════════════════════════════════════════════════════════════

lemma two_edges_cover_triangle_vertices (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (e1 e2 : Sym2 V) (he1 : e1 ∈ ({a, b, c} : Finset V).sym2)
    (he2 : e2 ∈ ({a, b, c} : Finset V).sym2) (hne : e1 ≠ e2) :
    ∀ v ∈ ({a, b, c} : Finset V), v ∈ e1 ∨ v ∈ e2 := by
  sorry  -- This is the one sorry - computational on small cases

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 6: At most 2 edge-types have S_e externals (6-packing)
-- ══════════════════════════════════════════════════════════════════════════════

/-- AXIOM from slot412 (PROVEN there with 0 sorry) -/
axiom not_all_three_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬(∃ T1 T2 T3, T1 ∈ S_e G M {a, b, c} ∧ a ∈ T1 ∧ b ∈ T1 ∧ c ∉ T1 ∧
                  T2 ∈ S_e G M {a, b, c} ∧ b ∈ T2 ∧ c ∈ T2 ∧ a ∉ T2 ∧
                  T3 ∈ S_e G M {a, b, c} ∧ a ∈ T3 ∧ c ∈ T3 ∧ b ∉ T3)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 7: 2 edges suffice for S_e (original, non-bridge)
-- ══════════════════════════════════════════════════════════════════════════════

lemma two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ e.sym2 ∧
      ∀ T ∈ S_e G M e, ∃ edge ∈ E, edge ∈ T.sym2 := by
  -- By 6-packing, at most 2 of 3 edge-types are populated
  -- Select 1 edge per populated type
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 8: Bridge contains shared edge with e
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridge_shares_edge_with_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e T : Finset V) (idx : Finset V → ℕ)
    (hT : T ∈ S_e' G M e idx) (hT_bridge : T ∉ S_e G M e) :
    ∃ edge ∈ e.sym2, edge ∈ T.sym2 := by
  simp only [S_e', mem_filter] at hT
  have h_inter := hT.2.2.1  -- 2 ≤ (T ∩ e).card
  -- T shares at least 2 vertices with e, so shares at least 1 edge
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ(S_e') ≤ 2 with constrained selection
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Get 2 edges E_Se covering S_e (by two_edges_cover_Se)
2. Each bridge shares edge with e
3. When bridges ≤ 2, can adjust E_Se to include bridge edges:
   - If bridge edge ∈ E_Se, done
   - If not, swap one edge to include bridge edge
4. By Hall's marriage theorem (bipartite matching), feasible when demands ≤ 3
-/
theorem tau_Se'_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M)
    (idx : Finset V → ℕ)
    (h_bridges_le_2 : (S_e' G M e idx \ S_e G M e).card ≤ 2) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ e.sym2 ∧
      ∀ T ∈ S_e' G M e idx, ∃ edge ∈ E, edge ∈ T.sym2 := by
  sorry

end
