/-
  slot512_two_edges_cover_Se.lean

  SINGLE TARGET: 2 edges from e cover all S_e externals

  Key: 6-packing constraint says at most 2 of 3 edge-types are populated.
  So selecting 1 edge per populated type gives a 2-edge cover.

  TIER: 2 (case analysis on edge-types)
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
-- SCAFFOLDING: Edge-type classification
-- ══════════════════════════════════════════════════════════════════════════════

/-- The 3 edge-types of a triangle e = {a,b,c} -/
def edgeTypes (a b c : V) : Finset (Finset V) :=
  {{a, b}, {b, c}, {a, c}}

/-- Which edge-type does external T use? (T ∩ e has exactly 2 elements) -/
def usedEdgeType (T e : Finset V) : Finset V := T ∩ e

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 1: External uses exactly one edge-type
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_uses_one_edge_type (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e T : Finset V) (a b c : V)
    (he : e = {a, b, c}) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hT : T ∈ S_e G M e) :
    (usedEdgeType T e = {a, b} ∧ c ∉ T) ∨
    (usedEdgeType T e = {b, c} ∧ a ∉ T) ∨
    (usedEdgeType T e = {a, c} ∧ b ∉ T) := by
  simp only [S_e, mem_filter] at hT
  -- T ∩ e has ≥2 elements, and T.card = 3, e.card = 3
  -- So T ∩ e has exactly 2 elements (T ≠ e rules out 3)
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 2: Populated edge-types
-- ══════════════════════════════════════════════════════════════════════════════

def hasTypeAB (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) (a b c : V) : Prop :=
  ∃ T ∈ S_e G M e, a ∈ T ∧ b ∈ T ∧ c ∉ T

def hasTypeBC (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) (a b c : V) : Prop :=
  ∃ T ∈ S_e G M e, b ∈ T ∧ c ∈ T ∧ a ∉ T

def hasTypeAC (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) (a b c : V) : Prop :=
  ∃ T ∈ S_e G M e, a ∈ T ∧ c ∈ T ∧ b ∉ T

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 3: 6-packing constraint (AXIOM from slot412)
-- ══════════════════════════════════════════════════════════════════════════════

axiom not_all_three_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬(hasTypeAB G M {a,b,c} a b c ∧ hasTypeBC G M {a,b,c} a b c ∧ hasTypeAC G M {a,b,c} a b c)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 4: Edge covers all externals of its type
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_covers_its_type (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e T : Finset V) (a b : V) (hab : a ≠ b)
    (hT : T ∈ S_e G M e) (ha : a ∈ T) (hb : b ∈ T) :
    Sym2.mk a b ∈ T.sym2 := by
  rw [Finset.mem_sym2_iff]
  exact ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 5: At most 2 types → 2 edges suffice
-- ══════════════════════════════════════════════════════════════════════════════

lemma two_types_two_edges (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (types : Finset (Finset V))
    (h_types : types ⊆ {{a, b}, {b, c}, {a, c}})
    (h_card : types.card ≤ 2) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧
      ∀ τ ∈ types, ∃ edge ∈ E, ∀ v ∈ τ, v ∈ edge := by
  -- Select one edge per type
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 2 edges cover S_e
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Let e = {a, b, c} with distinct a, b, c
2. S_e externals use edge-types from {{a,b}, {b,c}, {a,c}}
3. By 6-packing (not_all_three_types), at most 2 types are populated
4. Select 1 edge per populated type (≤2 edges total)
5. Each external T contains its edge-type, so selected edge hits T
-/
theorem two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ e.sym2 ∧
      ∀ T ∈ S_e G M e, ∃ edge ∈ E, edge ∈ T.sym2 := by
  sorry

end
