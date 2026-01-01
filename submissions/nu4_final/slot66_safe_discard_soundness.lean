/-
Tuza ν=4 Strategy - Slot 66: Safe Discard Soundness

TARGET: If we can safely discard 4 M-edges, τ ≤ 8

THEOREM (safe_discard_soundness):
  Given a 4-element safe discard set D ⊆ M_edges,
  the remaining 8 edges cover all triangles.

PROOF STRATEGY:
1. D is safe means: no singletons, and at most one of each conflict pair
2. For any triangle T:
   - If T ∈ M: covered by M's own edges (at most 1 discarded by safe property)
   - If T ∉ M (external): has 1-3 M-edges, and since D has at most one of any pair,
     at least one M-edge of T survives in the remaining 8

STATUS: Key lemma - Aristotle should prove this
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING (from slot64a, slot65)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

def externalTriangles (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => t ∉ M ∧ ∃ e ∈ M_edges G M, e ∈ t.sym2)

def M_edges_in (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (t : Finset V) : Finset (Sym2 V) :=
  (M_edges G M).filter (fun e => e ∈ t.sym2)

def SingletonEdge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (e : Sym2 V) : Prop :=
  e ∈ M_edges G M ∧
  ∃ t ∈ externalTriangles G M, M_edges_in G M t = {e}

def ConflictPair (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (e₁ e₂ : Sym2 V) : Prop :=
  e₁ ∈ M_edges G M ∧
  e₂ ∈ M_edges G M ∧
  e₁ ≠ e₂ ∧
  ∃ t ∈ externalTriangles G M, M_edges_in G M t = {e₁, e₂}

def SafeDiscardSet (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (D : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ D, ¬SingletonEdge G M e) ∧
  (∀ e₁ e₂, ConflictPair G M e₁ e₂ → ¬(e₁ ∈ D ∧ e₂ ∈ D))

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧
    (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card = n}

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Packing elements are triangles -/
lemma packing_is_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (m : Finset V) (hm : m ∈ M) :
    m ∈ G.cliqueFinset 3 :=
  hM.1 hm

/-- Each M-element has exactly 3 edges -/
lemma M_element_has_3_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (m : Finset V) (hm : m ∈ M) :
    m.sym2.card = 3 := by
  have hm_clique := packing_is_triangle G M hM m hm
  have hm_card : m.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hm_clique).card_eq
  rw [Finset.card_sym2]
  omega

/-- M-edges are graph edges -/
lemma M_edges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    M_edges G M ⊆ G.edgeFinset := by
  intro e he
  simp only [M_edges, Finset.mem_biUnion, Finset.mem_filter] at he
  exact he.2.2

/-- Each M-edge belongs to exactly one M-element (proven in slot63/slot64c) -/
lemma M_edge_unique (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m₁ m₂ : Finset V) (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    (he₁ : e ∈ m₁.sym2) (he₂ : e ∈ m₂.sym2) :
    m₁ = m₂ := by
  by_contra hne
  -- e ∈ m₁.sym2 ∩ m₂.sym2 means m₁ ∩ m₂ contains both endpoints of e
  rw [Finset.mem_sym2_iff] at he₁ he₂
  obtain ⟨u, v, huv, hu₁, hv₁, rfl⟩ := he₁
  obtain ⟨u', v', _, hu₂, hv₂, heq⟩ := he₂
  simp only [Sym2.eq, Sym2.rel_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h_card : (m₁ ∩ m₂).card ≥ 2 := by
      have hsub : ({u, v} : Finset V) ⊆ m₁ ∩ m₂ := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hu₁, hu₂⟩
        · exact Finset.mem_inter.mpr ⟨hv₁, hv₂⟩
      calc 2 = ({u, v} : Finset V).card := (Finset.card_pair huv).symm
        _ ≤ (m₁ ∩ m₂).card := Finset.card_le_card hsub
    have := hM.2 hm₁ hm₂ hne
    omega
  · have h_card : (m₁ ∩ m₂).card ≥ 2 := by
      have hsub : ({u, v} : Finset V) ⊆ m₁ ∩ m₂ := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hu₁, hv₂⟩
        · exact Finset.mem_inter.mpr ⟨hv₁, hu₂⟩
      calc 2 = ({u, v} : Finset V).card := (Finset.card_pair huv).symm
        _ ≤ (m₁ ∩ m₂).card := Finset.card_le_card hsub
    have := hM.2 hm₁ hm₂ hne
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- The remaining edges after removing a safe discard set -/
def remainingEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (D : Finset (Sym2 V)) : Finset (Sym2 V) :=
  (M_edges G M) \ D

/-- Remaining edges cover an external triangle if it has ≥2 M-edges or has a non-discarded edge -/
lemma remaining_covers_external (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (D : Finset (Sym2 V)) (hD_safe : SafeDiscardSet G M D)
    (t : Finset V) (ht : t ∈ externalTriangles G M) :
    ∃ e ∈ remainingEdges G M D, e ∈ t.sym2 := by
  -- M_edges_in t has 1, 2, or 3 elements
  have ⟨e, he⟩ := by
    simp only [externalTriangles, Finset.mem_filter] at ht
    obtain ⟨_, _, e, he_M, he_t⟩ := ht.2.2
    exact ⟨e, Finset.mem_filter.mpr ⟨he_M, he_t⟩⟩
  -- Case split on the size of M_edges_in
  have h_nonempty : (M_edges_in G M t).Nonempty := ⟨e, he⟩
  by_cases h1 : (M_edges_in G M t).card = 1
  · -- Singleton case: e is the only M-edge in t
    have heq : M_edges_in G M t = {e} := Finset.card_eq_one.mp h1 ▸ by
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro hx
        have := Finset.card_eq_one.mp h1
        obtain ⟨y, hy⟩ := this
        simp only [hy, Finset.mem_singleton] at hx ⊢
        exact hx
      · intro hx
        rw [hx]; exact he
    -- But D is safe, so e ∉ D (no singletons)
    have he_M : e ∈ M_edges G M := (Finset.mem_filter.mp he).1
    have h_single : SingletonEdge G M e := ⟨he_M, t, ht, heq⟩
    have he_not_D : e ∉ D := hD_safe.1 e ▸ fun hcontra => hcontra h_single
    exact ⟨e, Finset.mem_sdiff.mpr ⟨he_M, he_not_D⟩, (Finset.mem_filter.mp he).2⟩
  by_cases h2 : (M_edges_in G M t).card = 2
  · -- Conflict pair case: two M-edges e₁, e₂
    obtain ⟨e₁, e₂, hne, heq⟩ := Finset.card_eq_two.mp h2
    have he₁ : e₁ ∈ M_edges_in G M t := heq ▸ Finset.mem_insert_self _ _
    have he₂ : e₂ ∈ M_edges_in G M t := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have he₁_M : e₁ ∈ M_edges G M := (Finset.mem_filter.mp he₁).1
    have he₂_M : e₂ ∈ M_edges G M := (Finset.mem_filter.mp he₂).1
    -- D is safe, so at most one of e₁, e₂ is in D
    have h_conflict : ConflictPair G M e₁ e₂ := ⟨he₁_M, he₂_M, hne, t, ht, heq⟩
    have h_not_both := hD_safe.2 e₁ e₂ h_conflict
    push_neg at h_not_both
    by_cases h_e1 : e₁ ∈ D
    · have := h_not_both h_e1
      exact ⟨e₂, Finset.mem_sdiff.mpr ⟨he₂_M, this⟩, (Finset.mem_filter.mp he₂).2⟩
    · exact ⟨e₁, Finset.mem_sdiff.mpr ⟨he₁_M, h_e1⟩, (Finset.mem_filter.mp he₁).2⟩
  · -- 3-edge case: t has all 3 edges in M
    -- Since |D| = 4 and each M-element contributes 3 edges, at most 1 is discarded
    -- (by pigeonhole on the unique M-element containing these edges)
    -- Actually this case shouldn't happen: external triangles are NOT in M
    -- But they can share 3 edges with M if those edges come from multiple M-elements
    -- However, with |D|=4 and at most 3 M-edges in t, at least one survives
    have h_ge3 : (M_edges_in G M t).card ≥ 3 := by
      have h_le3 : (M_edges_in G M t).card ≤ 3 := by
        simp only [externalTriangles, Finset.mem_filter] at ht
        have ht_clique := ht.1
        calc (M_edges_in G M t).card ≤ t.sym2.card := Finset.card_filter_le _ _
          _ = 3 := by
            have h_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht_clique).card_eq
            rw [Finset.card_sym2]; omega
      omega
    -- At most 2 edges from D can be in t (since D has 4 edges, t has 3)
    -- Actually need more careful argument here
    sorry -- Aristotle: at least one of 3 M-edges survives when D has 4 elements

/-- Remaining edges cover packing elements -/
lemma remaining_covers_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (h_nu4 : M.card = 4)
    (D : Finset (Sym2 V)) (hD : D ⊆ M_edges G M) (hD_card : D.card = 4)
    (hD_one_per : ∀ m ∈ M, (D.filter (fun e => e ∈ m.sym2)).card ≤ 1)
    (m : Finset V) (hm : m ∈ M) :
    ∃ e ∈ remainingEdges G M D, e ∈ m.sym2 := by
  -- m has 3 edges, at most 1 in D, so ≥2 remain
  have h3 := M_element_has_3_edges G M hM m hm
  have h_edges : (m.sym2.filter (fun e => e ∈ G.edgeFinset)).card = 3 := by
    -- All edges of m are in G.edgeFinset since m is a clique
    have h_clique := packing_is_triangle G M hM m hm
    have h_is_clique := SimpleGraph.mem_cliqueFinset_iff.mp h_clique
    suffices h : m.sym2.filter (fun e => e ∈ G.edgeFinset) = m.sym2 by rw [h]; exact h3
    ext e
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro he
    rw [Finset.mem_sym2_iff] at he
    obtain ⟨u, v, huv, hu, hv, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset]
    exact h_is_clique.2 hu hv huv
  -- At most 1 discarded from m
  have h_D_in_m := hD_one_per m hm
  -- Count remaining
  have h_M_edges_of_m : (M_edges G M).filter (fun e => e ∈ m.sym2) =
      m.sym2.filter (fun e => e ∈ G.edgeFinset) := by
    ext e
    simp only [M_edges, Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · intro ⟨⟨m', hm', he_m', he_G⟩, he_m⟩
      exact ⟨he_m, he_G⟩
    · intro ⟨he_m, he_G⟩
      exact ⟨⟨m, hm, Finset.mem_filter.mpr ⟨he_m, he_G⟩, he_G⟩, he_m⟩
  have h_remain : ((M_edges G M) \ D).filter (fun e => e ∈ m.sym2) =
      (M_edges G M).filter (fun e => e ∈ m.sym2) \ D.filter (fun e => e ∈ m.sym2) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [h_M_edges_of_m] at h_remain
  have h_card_remain : ((M_edges G M) \ D).filter (fun e => e ∈ m.sym2) |>.card ≥ 2 := by
    rw [h_remain]
    have := Finset.card_sdiff_add_card (D.filter (fun e => e ∈ m.sym2))
      (m.sym2.filter (fun e => e ∈ G.edgeFinset))
    calc ((m.sym2.filter fun e => e ∈ G.edgeFinset) \ D.filter fun e => e ∈ m.sym2).card
        = (m.sym2.filter (fun e => e ∈ G.edgeFinset)).card - (D.filter fun e => e ∈ m.sym2).card := by
          rw [Finset.card_sdiff]
          · intro e he
            simp only [Finset.mem_filter] at he ⊢
            exact ⟨he.2, (hD he.1).2⟩
      _ ≥ 3 - 1 := by omega
      _ = 2 := by omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < ((M_edges G M) \ D).filter (fun e => e ∈ m.sym2) |>.card)
  exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN SOUNDNESS THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- CORE THEOREM: If D is a safe 4-edge discard set with one edge per M-element,
    then the remaining 8 M-edges cover all triangles. -/
theorem safe_discard_soundness (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (h_nu4 : M.card = 4)
    (D : Finset (Sym2 V)) (hD : D ⊆ M_edges G M) (hD_card : D.card = 4)
    (hD_safe : SafeDiscardSet G M D)
    (hD_one_per : ∀ m ∈ M, (D.filter (fun e => e ∈ m.sym2)).card ≤ 1) :
    triangleCoveringNumber G ≤ 8 := by
  -- The remaining edges form an 8-edge cover
  have h_remain_card : (remainingEdges G M D).card = 8 := by
    unfold remainingEdges
    have h_M_card : (M_edges G M).card ≤ 12 := by
      -- Each M-element contributes 3 edges, pairwise disjoint by packing
      sorry -- Aristotle: proven in slot64b
    have h_M_card_eq : (M_edges G M).card = 12 := by
      sorry -- Aristotle: equality when packing is maximal with ν=4
    rw [Finset.card_sdiff hD]
    omega
  -- The remaining edges are in G.edgeFinset
  have h_remain_sub : remainingEdges G M D ⊆ G.edgeFinset :=
    Finset.sdiff_subset.trans (M_edges_subset G M hM)
  -- The remaining edges cover all triangles
  have h_covers : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ remainingEdges G M D, e ∈ t.sym2 := by
    intro t ht
    by_cases h_in_M : t ∈ M
    · exact remaining_covers_packing G M hM h_nu4 D hD hD_card hD_one_per t h_in_M
    · -- t is external
      have h_ext : t ∈ externalTriangles G M ∨ (M_edges_in G M t = ∅) := by
        by_cases h : ∃ e ∈ M_edges G M, e ∈ t.sym2
        · left
          simp only [externalTriangles, Finset.mem_filter]
          exact ⟨ht, h_in_M, h⟩
        · right
          push_neg at h
          ext e
          simp only [M_edges_in, Finset.mem_filter, Finset.not_mem_empty, iff_false, not_and]
          intro he_M
          exact h e he_M
      rcases h_ext with h_ext | h_empty
      · exact remaining_covers_external G M hM D hD_safe t h_ext
      · -- No M-edges in t: need to show t is still covered
        -- By maximality, t shares edge with some M-element
        -- So there's some e ∈ M_edges with e ∈ t.sym2, contradicting h_empty
        -- This is actually the case where t is vertex-disjoint from M (shouldn't happen with max packing)
        sorry -- Aristotle: maximality argument
  -- Conclude τ ≤ 8
  apply Nat.sInf_le
  exact ⟨remainingEdges G M D, h_remain_sub, h_covers, h_remain_card⟩

end
