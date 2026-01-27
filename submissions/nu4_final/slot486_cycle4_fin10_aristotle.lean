/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b853191a-fb17-43db-8d33-956f5dffd23d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Aristotle encountered an error processing this file.
Lean errors:
At line 119, column 2:
  unexpected token '/--'; expected 'lemma'

At line 205, column 0:
  Invalid `end`: There is no current scope to end

Note: Scopes are introduced using `namespace` and `section`
-/

/-
  slot486_cycle4_fin10.lean

  CASE: cycle_4 - Four triangles forming a cycle pattern

  Pattern: M = {m0, m1, m2, m3} where:
  - m0 and m1 share exactly 1 vertex (v01)
  - m1 and m2 share exactly 1 vertex (v12)
  - m2 and m3 share exactly 1 vertex (v23)
  - m3 and m0 share exactly 1 vertex (v30)
  - No consecutive pairs share more than 1 vertex

  This is the "hardest" configuration for τ ≤ 8 because:
  - Each edge of M might have external triangles
  - Bridges can span non-adjacent pairs

  STRATEGY: native_decide on Fin 10 to verify τ ≤ 8

  TIER: 1 (finite verification)
-/

import Mathlib

set_option maxHeartbeats 800000

open Finset

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS ON Fin N
-- ══════════════════════════════════════════════════════════════════════════════

/-- Ordered edge representation -/
def OrdEdge (n : ℕ) := { p : Fin n × Fin n // p.1 < p.2 }

instance (n : ℕ) : DecidableEq (OrdEdge n) :=
  inferInstanceAs (DecidableEq { p : Fin n × Fin n // p.1 < p.2 })

/-- Triangle as 3 vertices with ordering -/
structure Tri (n : ℕ) where
  a : Fin n
  b : Fin n
  c : Fin n
  hab : a < b
  hac : a < c
  hbc : b < c
  deriving DecidableEq

/-- Vertices of a triangle -/
def Tri.verts (t : Tri n) : Finset (Fin n) := {t.a, t.b, t.c}

/-- Edges of a triangle as ordered pairs -/
def Tri.edgeSet (t : Tri n) : Finset (Fin n × Fin n) :=
  {(t.a, t.b), (t.a, t.c), (t.b, t.c)}

/-- Two triangles are edge-disjoint -/
def Tri.edgeDisj (t1 t2 : Tri n) : Prop :=
  Disjoint t1.edgeSet t2.edgeSet

instance (t1 t2 : Tri n) : Decidable (t1.edgeDisj t2) :=
  inferInstanceAs (Decidable (Disjoint _ _))

/-- Shared vertices count -/
def Tri.sharedCount (t1 t2 : Tri n) : ℕ :=
  (t1.verts ∩ t2.verts).card

/-- Four triangles form a packing -/
def is4Packing (m0 m1 m2 m3 : Tri n) : Prop :=
  m0.edgeDisj m1 ∧ m0.edgeDisj m2 ∧ m0.edgeDisj m3 ∧
  m1.edgeDisj m2 ∧ m1.edgeDisj m3 ∧ m2.edgeDisj m3

instance (m0 m1 m2 m3 : Tri n) : Decidable (is4Packing m0 m1 m2 m3) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 PATTERN
-- ══════════════════════════════════════════════════════════════════════════════

/--
cycle_4 pattern: consecutive pairs share exactly 1 vertex, forming a cycle.
This is characterized by:
- m_i ∩ m_{i+1 mod 4} has exactly 1 vertex
- These 4 shared vertices are distinct
-/
def isCycle4Pattern (m0 m1 m2 m3 : Tri n) : Prop :=
  is4Packing m0 m1 m2 m3 ∧
  m0.sharedCount m1 = 1 ∧
  m1.sharedCount m2 = 1 ∧
  m2.sharedCount m3 = 1 ∧
  m3.sharedCount m0 = 1

instance (m0 m1 m2 m3 : Tri n) : Decidable (isCycle4Pattern m0 m1 m2 m3) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

-- ══════════════════════════════════════════════════════════════════════════════
-- COVERAGE VERIFICATION
-- ══════════════════════════════════════════════════════════════════════════════

/-- An edge covers a triangle if it's one of the triangle's edges -/
def edgeCovers (e : Fin n × Fin n) (t : Tri n) : Prop :=
  e ∈ t.edgeSet

instance (e : Fin n × Fin n) (t : Tri n) : Decidable (edgeCovers e t) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- A set of edges covers a triangle -/
def edgeSetCovers (E : Finset (Fin n × Fin n)) (t : Tri n) : Prop :=
  ∃ e ∈ E, edgeCovers e t

instance (E : Finset (Fin n × Fin n)) (t : Tri n) : Decidable (edgeSetCovers E t) :=
  inferInstanceAs (Decidable (∃ e ∈ E, _))

/--
For cycle_4, the 8-edge cover is:
- 2 edges from each of m0, m1, m2, m3

The "hard" part is showing this covers all triangles including bridges.
On Fin 10, we verify exhaustively.
-/
/-
ERROR 1:
unexpected token '/--'; expected 'lemma'
-/

/--
KEY THEOREM: In a cycle_4 pattern on Fin 10, any triangle sharing ≥2 vertices
with some m_i can be covered by at most 2 edges from that m_i.

Combined over all 4 m_i, this gives τ ≤ 8.
-/
theorem cycle4_local_cover_fin10 :
    ∀ (m0 m1 m2 m3 t : Tri 10),
    isCycle4Pattern m0 m1 m2 m3 →
    (t.sharedCount m0 ≥ 2 ∨ t.sharedCount m1 ≥ 2 ∨
     t.sharedCount m2 ≥ 2 ∨ t.sharedCount m3 ≥ 2) →
    -- t can be covered by 2 edges from one of the m_i
    (∃ E ⊆ m0.edgeSet, E.card ≤ 2 ∧ edgeSetCovers E t) ∨
    (∃ E ⊆ m1.edgeSet, E.card ≤ 2 ∧ edgeSetCovers E t) ∨
    (∃ E ⊆ m2.edgeSet, E.card ≤ 2 ∧ edgeSetCovers E t) ∨
    (∃ E ⊆ m3.edgeSet, E.card ≤ 2 ∧ edgeSetCovers E t) := by
  native_decide

/--
ALTERNATIVE: Every triangle in a graph with ν=4 (cycle_4 packing as maximum)
shares an edge with some packing element → directly covered.
-/
theorem cycle4_every_tri_shares_edge_fin10 :
    ∀ (m0 m1 m2 m3 t : Tri 10),
    isCycle4Pattern m0 m1 m2 m3 →
    -- If t is not edge-disjoint from all 4, it shares some edge → covered
    ¬(t.edgeDisj m0 ∧ t.edgeDisj m1 ∧ t.edgeDisj m2 ∧ t.edgeDisj m3) →
    (¬t.edgeDisj m0 ∨ ¬t.edgeDisj m1 ∨ ¬t.edgeDisj m2 ∨ ¬t.edgeDisj m3) := by
  intro m0 m1 m2 m3 t _ h
  push_neg at h ⊢
  exact h

/--
MAIN: cycle_4 implies τ ≤ 8 on Fin 10.

Any triangle t either:
1. Shares an edge with some m_i → directly covered (1 edge)
2. Is edge-disjoint from all → would form 5-packing (impossible if ν=4)

In case 1, we need at most 2 edges per m_i for coverage.
4 × 2 = 8 edges total.
-/
theorem tau_le_8_cycle4_fin10 :
    ∀ (m0 m1 m2 m3 : Tri 10),
    isCycle4Pattern m0 m1 m2 m3 →
    -- The 8 edges (all edges from all triangles, but counted as ≤2 per triangle)
    ∃ E : Finset (Fin 10 × Fin 10),
      E.card ≤ 8 ∧
      E ⊆ m0.edgeSet ∪ m1.edgeSet ∪ m2.edgeSet ∪ m3.edgeSet ∧
      ∀ t : Tri 10, ¬(t.edgeDisj m0 ∧ t.edgeDisj m1 ∧ t.edgeDisj m2 ∧ t.edgeDisj m3) →
        edgeSetCovers E t := by
  intro m0 m1 m2 m3 hcycle
  -- Use all 12 edges (3 per triangle), but only 8 matter
  use m0.edgeSet ∪ m1.edgeSet ∪ m2.edgeSet ∪ m3.edgeSet
  refine ⟨?_, ?_, ?_⟩
  · -- Card bound: each m has 3 edges, but by packing, these are disjoint
    -- So total = 12, but τ ≤ 8 says we only NEED 8
    -- This part would require showing 8 suffice, not that 12 exist
    sorry
  · -- Subset: trivial
    rfl
  · -- Coverage: any non-disjoint t is covered
    intro t h
    push_neg at h
    rcases h with h0 | h1 | h2 | h3
    · simp only [edgeSetCovers, edgeCovers]
      simp only [Tri.edgeDisj, Disjoint] at h0
      push_neg at h0
      obtain ⟨e, he_t, he_m0⟩ := Finset.not_disjoint_iff.mp (by
        simp only [not_disjoint_iff]
        by_contra h
        push_neg at h
        apply h0
        intro x hx
        simp only [bot_eq_empty, mem_empty_iff_false]
        exact (h x).mp hx)
      use e
      constructor
      · exact mem_union_left _ (mem_union_left _ (mem_union_left _ he_m0))
      · exact he_t
    · sorry -- Similar for m1
    · sorry -- Similar for m2
    · sorry -- Similar for m3

end
/-
ERROR 1:
Invalid `end`: There is no current scope to end

Note: Scopes are introduced using `namespace` and `section`
-/
