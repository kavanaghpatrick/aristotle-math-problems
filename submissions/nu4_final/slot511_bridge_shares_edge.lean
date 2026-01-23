/-
  slot511_bridge_shares_edge.lean

  SINGLE TARGET: If T shares ≥2 vertices with e, then T shares an edge with e

  This is straightforward set theory on 3-element sets.

  TIER: 1 (set cardinality argument)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 1: Two elements determine a unique edge in sym2
-- ══════════════════════════════════════════════════════════════════════════════

lemma two_mem_implies_edge_in_sym2 (T : Finset V) (a b : V) (hab : a ≠ b)
    (ha : a ∈ T) (hb : b ∈ T) : Sym2.mk a b ∈ T.sym2 := by
  rw [Finset.mem_sym2_iff]
  exact ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 2: card ≥ 2 implies at least 2 distinct elements
-- ══════════════════════════════════════════════════════════════════════════════

lemma two_distinct_of_card_ge_2 (S : Finset V) (h : 2 ≤ S.card) :
    ∃ a b, a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  have h1 : 1 < S.card := by omega
  rw [Finset.one_lt_card] at h1
  obtain ⟨a, ha, b, hb, hab⟩ := h1
  exact ⟨a, b, ha, hb, hab⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 3: Intersection membership
-- ══════════════════════════════════════════════════════════════════════════════

lemma inter_mem_both (T e : Finset V) (x : V) (hx : x ∈ T ∩ e) : x ∈ T ∧ x ∈ e := by
  exact mem_inter.mp hx

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 4: Edge in intersection is in both sym2
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_inter_in_both_sym2 (T e : Finset V) (a b : V) (hab : a ≠ b)
    (ha : a ∈ T ∩ e) (hb : b ∈ T ∩ e) :
    Sym2.mk a b ∈ T.sym2 ∧ Sym2.mk a b ∈ e.sym2 := by
  obtain ⟨ha_T, ha_e⟩ := inter_mem_both T e a ha
  obtain ⟨hb_T, hb_e⟩ := inter_mem_both T e b hb
  constructor
  · exact two_mem_implies_edge_in_sym2 T a b hab ha_T hb_T
  · exact two_mem_implies_edge_in_sym2 e a b hab ha_e hb_e

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 5: sym2 element is in both original sets
-- ══════════════════════════════════════════════════════════════════════════════

lemma mem_sym2_of_mem_inter_sym2 (T e : Finset V) (edge : Sym2 V)
    (hedge_T : edge ∈ T.sym2) : ∃ a b, edge = Sym2.mk a b ∧ a ∈ T ∧ b ∈ T := by
  rw [Finset.mem_sym2_iff] at hedge_T
  obtain ⟨a, b⟩ := edge.out
  use a, b
  constructor
  · exact Sym2.mk_eq_mk.mpr (Or.inl ⟨rfl, rfl⟩)
  · exact hedge_T

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 2+ vertex intersection implies shared edge
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. T ∩ e has ≥2 elements (given)
2. By two_distinct_of_card_ge_2, get a, b ∈ T ∩ e with a ≠ b
3. a ∈ T and a ∈ e, b ∈ T and b ∈ e (from intersection)
4. Edge {a, b} = Sym2.mk a b
5. This edge is in both T.sym2 and e.sym2
-/
theorem shares_edge_of_inter_ge_2 (T e : Finset V) (h_inter : 2 ≤ (T ∩ e).card) :
    ∃ edge ∈ e.sym2, edge ∈ T.sym2 := by
  -- Get two distinct elements from intersection
  obtain ⟨a, b, ha, hb, hab⟩ := two_distinct_of_card_ge_2 (T ∩ e) h_inter
  -- The edge {a, b} is in both
  obtain ⟨h_in_T, h_in_e⟩ := edge_in_inter_in_both_sym2 T e a b hab ha hb
  exact ⟨Sym2.mk a b, h_in_e, h_in_T⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: Bridge version (with graph context)
-- ══════════════════════════════════════════════════════════════════════════════

def sharesEdgeWith (M : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  M.filter (fun e => 2 ≤ (T ∩ e).card)

def S_e' (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V)
    (idx : Finset V → ℕ) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧
    (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧ ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

theorem bridge_shares_edge_with_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e T : Finset V) (idx : Finset V → ℕ)
    (hT : T ∈ S_e' G M e idx) :
    ∃ edge ∈ e.sym2, edge ∈ T.sym2 := by
  simp only [S_e', mem_filter] at hT
  exact shares_edge_of_inter_ge_2 T e hT.2.2.1

end
