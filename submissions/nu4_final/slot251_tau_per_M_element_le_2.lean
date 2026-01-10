/-
  slot251_tau_per_M_element_le_2.lean

  TARGET: For each M-element A with apex x, we can cover A and all its externals
  with at most 2 edges: one M-edge + one apex edge.

  Key insight: All externals share apex x (from slot250).
  - Pick any edge {a, x} where a ∈ A
  - This covers all externals (since each contains both a and x... wait, that's not right)

  Actually, let me reconsider:
  - External T = {a, b, x} where {a, b} ⊆ A
  - T is covered by edge {a, b} (M-edge), or {a, x}, or {b, x}
  - To cover A = {a, b, c} AND all externals with 2 edges:
    - Edge 1: {a, b} covers A and externals using edge {a, b}
    - Edge 2: {c, x} covers externals using edges {a, c} or {b, c}

  This gives τ(A ∪ Ext(A)) ≤ 2 for each M-element!
  Total: 4 × 2 = 8 edges for τ ≤ 8!

  1 SORRY expected.
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

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

def externalsOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (isExternalOf G M A)

def trianglesOfA (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  {A} ∪ externalsOf G M A

def isTriangleCoverOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOM: All externals share apex (from slot250)
-- ══════════════════════════════════════════════════════════════════════════════

axiom all_externals_share_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (h_nonempty : (externalsOf G M A).Nonempty) :
    ∃ x : V, x ∉ A ∧ ∀ T ∈ externalsOf G M A, x ∈ T

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: A 3-element set can be written as {a, b, c}
-- ══════════════════════════════════════════════════════════════════════════════

lemma card_3_triple (A : Finset V) (hA : A.card = 3) :
    ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ A = {a, b, c} := by
  obtain ⟨a, b, c, hab, hac, hbc, h_eq⟩ := Finset.card_eq_three.mp hA
  exact ⟨a, b, c, hab, hac, hbc, h_eq⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 2 edges cover A and all its externals
-- ══════════════════════════════════════════════════════════════════════════════

/--
  For each M-element A with apex x, we can cover A and all its externals
  with exactly 2 edges: one M-edge {a, b} and one apex edge {c, x}.

  - {a, b} covers A itself and all externals using edge {a, b}
  - {c, x} covers externals using edges {a, c} or {b, c}
    (since all externals contain x, and those not using {a,b} must use c)
-/
theorem tau_trianglesOfA_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (hG_adj_x : ∀ x : V, x ∉ A → ∀ a ∈ A, (∃ T ∈ externalsOf G M A, x ∈ T ∧ a ∈ T) → G.Adj a x) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ isTriangleCoverOn G (trianglesOfA G M A) E' := by
  -- Handle empty externals case
  by_cases h_empty : (externalsOf G M A) = ∅
  · -- No externals: just need to cover A with 1 edge
    obtain ⟨a, b, c, hab, hac, hbc, h_A_eq⟩ := card_3_triple A hA_3
    use {s(a, b)}
    constructor
    · simp
    · intro t ht
      simp only [trianglesOfA, Finset.mem_union, Finset.mem_singleton] at ht
      rcases ht with rfl | ht_ext
      · -- t = A
        use s(a, b)
        constructor
        · simp
        · rw [Finset.mem_sym2_iff]
          rw [h_A_eq]
          simp [hab]
      · -- t ∈ externalsOf (but externalsOf is empty)
        rw [h_empty] at ht_ext
        exact absurd ht_ext (Finset.not_mem_empty t)
  · -- Non-empty externals: use apex structure
    have h_nonempty : (externalsOf G M A).Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
    obtain ⟨x, hx_not_A, hx_in_all⟩ := all_externals_share_apex G M hM hM_card hν A hA hA_3 h_nonempty
    -- Get vertices of A = {a, b, c}
    obtain ⟨a, b, c, hab, hac, hbc, h_A_eq⟩ := card_3_triple A hA_3
    -- Our 2-edge cover: {a, b} and {c, x}
    use {s(a, b), s(c, x)}
    constructor
    · -- Card ≤ 2
      have h_ne : s(a, b) ≠ s(c, x) := by
        intro h_eq
        -- If s(a,b) = s(c,x), then {a,b} = {c,x} as sets
        have := Sym2.eq_iff.mp h_eq
        rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · -- a = c and b = x
          exact hac h1
        · -- a = x and b = c
          rw [h_A_eq] at hx_not_A
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx_not_A
          exact hx_not_A.1 h1.symm
      rw [Finset.card_insert_of_not_mem (Finset.not_mem_singleton.mpr h_ne)]
      simp
    · -- Cover property
      intro t ht
      simp only [trianglesOfA, Finset.mem_union, Finset.mem_singleton] at ht
      rcases ht with rfl | ht_ext
      · -- t = A: covered by {a, b}
        use s(a, b)
        constructor
        · simp
        · rw [Finset.mem_sym2_iff, h_A_eq]
          simp [hab]
      · -- t is an external
        have ht_ext' : isExternalOf G M A t := Finset.mem_filter.mp ht_ext |>.2
        have ht_3 : t.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp ht_ext'.1 |>.2
        have hx_t : x ∈ t := hx_in_all t ht_ext
        -- t shares an edge with A
        obtain ⟨u, v, huv, hu_t, hv_t, hu_A, hv_A⟩ := ht_ext'.2.2.1
        -- The shared edge is one of {a,b}, {a,c}, {b,c}
        rw [h_A_eq] at hu_A hv_A
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu_A hv_A
        -- Case analysis on which edge t uses
        sorry -- Aristotle fills: show {a,b} or {c,x} covers t

end
