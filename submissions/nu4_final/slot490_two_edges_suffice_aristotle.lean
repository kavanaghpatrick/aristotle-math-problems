/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 329e0818-7450-4d1c-a11e-db1c0e18ad52

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Aristotle encountered an error processing this file.
Lean errors:
At line 87, column 2:
  unexpected token '/--'; expected 'lemma'

At line 97, column 2:
  failed to synthesize
  Decidable
    (∃ x x_1 x_2,
      isExternalForEdge x m (mkEdge m.a m.b) m0 m1 m2 m3 ∧
        isExternalForEdge x_1 m (mkEdge m.a m.c) m0 m1 m2 m3 ∧ isExternalForEdge x_2 m (mkEdge m.b m.c) m0 m1 m2 m3)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

At line 186, column 0:
  Invalid `end`: There is no current scope to end

Note: Scopes are introduced using `namespace` and `section`
-/

/-
  slot490_two_edges_suffice.lean

  FOCUSED: Prove that 2 edges per m suffice to cover externals.

  Given slot412 (not_all_three_edge_types), we know at most 2 of 3 edges
  have external triangles. This lemma selects those 2 edges.

  TIER: 2 (direct consequence of 6-packing)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- SETUP ON Fin 9
-- ══════════════════════════════════════════════════════════════════════════════

abbrev V9 := Fin 9

/-- Triangle as 3 distinct vertices -/
structure Tri9 where
  a : V9
  b : V9
  c : V9
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  deriving DecidableEq

/-- Normalize edge to ordered pair -/
def mkEdge (x y : V9) : V9 × V9 := if x ≤ y then (x, y) else (y, x)

/-- The 3 edges of a triangle -/
def Tri9.edges (t : Tri9) : Finset (V9 × V9) :=
  {mkEdge t.a t.b, mkEdge t.a t.c, mkEdge t.b t.c}

/-- Edge disjointness -/
def edgeDisj (t1 t2 : Tri9) : Prop := Disjoint t1.edges t2.edges

instance (t1 t2 : Tri9) : Decidable (edgeDisj t1 t2) :=
  inferInstanceAs (Decidable (Disjoint _ _))

/-- 4-packing -/
def is4Pack (m0 m1 m2 m3 : Tri9) : Prop :=
  edgeDisj m0 m1 ∧ edgeDisj m0 m2 ∧ edgeDisj m0 m3 ∧
  edgeDisj m1 m2 ∧ edgeDisj m1 m3 ∧ edgeDisj m2 m3

instance (m0 m1 m2 m3 : Tri9) : Decidable (is4Pack m0 m1 m2 m3) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

-- ══════════════════════════════════════════════════════════════════════════════
-- EXTERNAL TRIANGLES
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangle t shares edge e with m -/
def sharesEdge (t : Tri9) (e : V9 × V9) : Prop := e ∈ t.edges

instance (t : Tri9) (e : V9 × V9) : Decidable (sharesEdge t e) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- Triangle t is external to m (shares edge with m, disjoint from others) -/
def isExternal (t m m0 m1 m2 m3 : Tri9) : Prop :=
  ¬edgeDisj t m ∧ edgeDisj t m0 ∧ edgeDisj t m1 ∧ edgeDisj t m2 ∧ edgeDisj t m3

/-- External for edge e: triangle shares exactly edge e with m -/
def isExternalForEdge (t m : Tri9) (e : V9 × V9) (m0 m1 m2 m3 : Tri9) : Prop :=
  sharesEdge t e ∧ sharesEdge m e ∧
  edgeDisj t m0 ∧ edgeDisj t m1 ∧ edgeDisj t m2 ∧ edgeDisj t m3

-- ══════════════════════════════════════════════════════════════════════════════
-- 6-PACKING CONSTRAINT
-- ══════════════════════════════════════════════════════════════════════════════

/--
If edge e of m has an external triangle T_e, then {m, T_e} share edge e.
If all 3 edges of m have externals {T_ab, T_ac, T_bc}, these 3 triangles
are pairwise edge-disjoint (they share different edges with m).
Together with M \ {m} (3 triangles), we get 6 edge-disjoint triangles.
This contradicts ν = 4.
-/
/-
ERROR 1:
unexpected token '/--'; expected 'lemma'
-/

/-- All 3 edges of m have external triangles -/
def allThreeHaveExternals (m m0 m1 m2 m3 : Tri9) : Prop :=
  ∃ t_ab t_ac t_bc : Tri9,
    isExternalForEdge t_ab m (mkEdge m.a m.b) m0 m1 m2 m3 ∧
    isExternalForEdge t_ac m (mkEdge m.a m.c) m0 m1 m2 m3 ∧
    isExternalForEdge t_bc m (mkEdge m.b m.c) m0 m1 m2 m3

instance (m m0 m1 m2 m3 : Tri9) : Decidable (allThreeHaveExternals m m0 m1 m2 m3) :=
  inferInstanceAs (Decidable (∃ _ _ _, _))
/-
ERROR 1:
failed to synthesize
  Decidable
    (∃ x x_1 x_2,
      isExternalForEdge x m (mkEdge m.a m.b) m0 m1 m2 m3 ∧
        isExternalForEdge x_1 m (mkEdge m.a m.c) m0 m1 m2 m3 ∧ isExternalForEdge x_2 m (mkEdge m.b m.c) m0 m1 m2 m3)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/

/--
KEY THEOREM: In a 4-packing, not all 3 edges of m can have externals.

Proof: If they did, we'd have a 6-packing (contradiction with ν=4).
-/
theorem not_all_three_have_externals (m0 m1 m2 m3 : Tri9) (hpack : is4Pack m0 m1 m2 m3) :
    ¬allThreeHaveExternals m0 m0 m1 m2 m3 ∧
    ¬allThreeHaveExternals m1 m0 m1 m2 m3 ∧
    ¬allThreeHaveExternals m2 m0 m1 m2 m3 ∧
    ¬allThreeHaveExternals m3 m0 m1 m2 m3 := by
  constructor
  all_goals {
    intro h
    obtain ⟨t_ab, t_ac, t_bc, hab, hac, hbc⟩ := h
    -- These 3 externals + 3 other packing elements = 6 disjoint triangles
    -- But ν = 4, contradiction
    sorry
  }

-- ══════════════════════════════════════════════════════════════════════════════
-- TWO EDGES SUFFICE
-- ══════════════════════════════════════════════════════════════════════════════

/--
Since at most 2 edges have externals, those 2 edges cover all externals for m.
-/
theorem two_edges_cover_externals (m0 m1 m2 m3 m : Tri9) (hpack : is4Pack m0 m1 m2 m3)
    (hm : m = m0 ∨ m = m1 ∨ m = m2 ∨ m = m3) :
    ∃ E : Finset (V9 × V9), E ⊆ m.edges ∧ E.card ≤ 2 ∧
      ∀ t : Tri9, (¬edgeDisj t m ∧ edgeDisj t m0 ∧ edgeDisj t m1 ∧ edgeDisj t m2 ∧ edgeDisj t m3) →
        ∃ e ∈ E, e ∈ t.edges := by
  -- By not_all_three_have_externals, at most 2 edges have externals
  -- Select those edges
  -- Any external triangle shares one of them
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN: τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

/--
τ ≤ 8: Select 2 edges from each of 4 packing elements.
-/
theorem tau_le_8_fin9 (m0 m1 m2 m3 : Tri9) (hpack : is4Pack m0 m1 m2 m3) :
    ∃ E : Finset (V9 × V9), E.card ≤ 8 ∧
      E ⊆ m0.edges ∪ m1.edges ∪ m2.edges ∪ m3.edges ∧
      ∀ t : Tri9, (¬edgeDisj t m0 ∨ ¬edgeDisj t m1 ∨ ¬edgeDisj t m2 ∨ ¬edgeDisj t m3) →
        ∃ e ∈ E, e ∈ t.edges := by
  -- Get 2-edge covers for each m_i
  obtain ⟨E0, hE0_sub, hE0_card, hE0_cov⟩ := two_edges_cover_externals m0 m1 m2 m3 m0 hpack (Or.inl rfl)
  obtain ⟨E1, hE1_sub, hE1_card, hE1_cov⟩ := two_edges_cover_externals m0 m1 m2 m3 m1 hpack (Or.inr (Or.inl rfl))
  obtain ⟨E2, hE2_sub, hE2_card, hE2_cov⟩ := two_edges_cover_externals m0 m1 m2 m3 m2 hpack (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨E3, hE3_sub, hE3_card, hE3_cov⟩ := two_edges_cover_externals m0 m1 m2 m3 m3 hpack (Or.inr (Or.inr (Or.inr rfl)))
  use E0 ∪ E1 ∪ E2 ∪ E3
  refine ⟨?_, ?_, ?_⟩
  · -- Card ≤ 8
    calc (E0 ∪ E1 ∪ E2 ∪ E3).card
        ≤ E0.card + E1.card + E2.card + E3.card := by
          calc (E0 ∪ E1 ∪ E2 ∪ E3).card
              ≤ (E0 ∪ E1 ∪ E2).card + E3.card := card_union_le _ _
            _ ≤ (E0 ∪ E1).card + E2.card + E3.card := by linarith [card_union_le (E0 ∪ E1) E2]
            _ ≤ E0.card + E1.card + E2.card + E3.card := by linarith [card_union_le E0 E1]
      _ ≤ 2 + 2 + 2 + 2 := by linarith
      _ = 8 := by norm_num
  · -- Subset
    intro e he
    simp only [mem_union] at he ⊢
    rcases he with ((he0 | he1) | he2) | he3
    · left; left; left; exact hE0_sub he0
    · left; left; right; exact hE1_sub he1
    · left; right; exact hE2_sub he2
    · right; exact hE3_sub he3
  · -- Coverage
    intro t ht
    rcases ht with h0 | h1 | h2 | h3
    · -- t shares with m0
      by_cases hext : edgeDisj t m1 ∧ edgeDisj t m2 ∧ edgeDisj t m3
      · -- t is external to m0
        obtain ⟨e, he, hcov⟩ := hE0_cov t ⟨h0, hext.1, hext.2.1, hext.2.2⟩
        exact ⟨e, mem_union_left _ (mem_union_left _ (mem_union_left _ he)), hcov⟩
      · -- t shares with another, use that edge
        push_neg at hext
        sorry
    · sorry -- Similar for m1
    · sorry -- Similar for m2
    · sorry -- Similar for m3

end
/-
ERROR 1:
Invalid `end`: There is no current scope to end

Note: Scopes are introduced using `namespace` and `section`
-/
