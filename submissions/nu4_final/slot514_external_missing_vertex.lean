/-
  slot514_external_missing_vertex.lean

  SINGLE TARGET: S_e external T = {a, b, w} for some w ∉ e

  Since (T ∩ e).card = 2 and T.card = 3, exactly one vertex of T is outside e.

  TIER: 1 (set difference cardinality)
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

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 1: Triangle card
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_3 (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V)
    (hT : T ∈ G.cliqueFinset 3) : T.card = 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at hT
  exact hT.2

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 2: Set difference card
-- ══════════════════════════════════════════════════════════════════════════════

lemma sdiff_card (A B : Finset V) : (A \ B).card = A.card - (A ∩ B).card := by
  rw [card_sdiff_eq_card_sub_card_inter]

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 3: card 1 means singleton
-- ══════════════════════════════════════════════════════════════════════════════

lemma card_1_singleton (S : Finset V) (h : S.card = 1) : ∃ w, S = {w} :=
  card_eq_one.mp h

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 4: Element of sdiff is in first, not second
-- ══════════════════════════════════════════════════════════════════════════════

lemma mem_sdiff_iff (A B : Finset V) (x : V) : x ∈ A \ B ↔ x ∈ A ∧ x ∉ B :=
  Finset.mem_sdiff

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 5: External inter card = 2 (from slot513)
-- ══════════════════════════════════════════════════════════════════════════════

axiom external_inter_card_eq_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e T : Finset V) (he : e ∈ M) (hT : T ∈ S_e G M e) :
    (T ∩ e).card = 2

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 6: S_e membership
-- ══════════════════════════════════════════════════════════════════════════════

lemma mem_S_e_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e T : Finset V) (hT : T ∈ S_e G M e) :
    T ∈ G.cliqueFinset 3 := by
  simp only [S_e, mem_filter] at hT
  exact hT.1

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: External has unique vertex outside e
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. T.card = 3 (T is a triangle)
2. (T ∩ e).card = 2 (by external_inter_card_eq_2)
3. (T \ e).card = T.card - (T ∩ e).card = 3 - 2 = 1
4. So T \ e = {w} for some w
5. w ∈ T and w ∉ e
-/
theorem external_has_unique_outside_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e T : Finset V) (he : e ∈ M) (hT : T ∈ S_e G M e) :
    ∃ w, w ∈ T ∧ w ∉ e ∧ (T \ e) = {w} := by
  have hT_clique := mem_S_e_clique G M e T hT
  have hT_card := triangle_card_3 G T hT_clique
  have h_inter := external_inter_card_eq_2 G M hM e T he hT
  have h_sdiff : (T \ e).card = 1 := by
    rw [sdiff_card]
    omega
  obtain ⟨w, hw⟩ := card_1_singleton (T \ e) h_sdiff
  use w
  have hw_mem : w ∈ T \ e := by rw [hw]; exact mem_singleton_self w
  rw [mem_sdiff_iff] at hw_mem
  exact ⟨hw_mem.1, hw_mem.2, hw⟩

end
