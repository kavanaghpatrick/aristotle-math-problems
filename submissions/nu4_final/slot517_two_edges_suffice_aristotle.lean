/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0e11c465-942d-4433-85dc-191b26330db2

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot517_two_edges_suffice.lean

  SINGLE TARGET: For any S_e', 2 edges from e suffice to cover all externals

  Key: 6-packing says ≤2 edge-types populated, and each external
  is covered by its shared edge (from slot515).

  TIER: 2 (edge-type analysis)
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['external_inter_card_eq_2', 'shared_edge_covers_external', 'harmonicSorry769062']-/
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

def sharesEdgeWith (M : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  M.filter (fun e => 2 ≤ (T ∩ e).card)

def S_e' (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V)
    (idx : Finset V → ℕ) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧
    (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅)

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOMS FROM PROVEN SLOTS
-- ══════════════════════════════════════════════════════════════════════════════

-- From slot513: External has exactly 2-intersection
axiom external_inter_card_eq_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e T : Finset V) (he : e ∈ M) (idx : Finset V → ℕ)
    (hT : T ∈ S_e' G M e idx) :
    (T ∩ e).card = 2

-- From slot515: External covered by its shared edge
axiom shared_edge_covers_external (T e : Finset V) (h_inter : (T ∩ e).card = 2) :
    ∃ edge ∈ e.sym2, edge ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 1: e has exactly 3 edges
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_has_3_edges (e : Finset V) (he : e.card = 3) : e.sym2.card = 3 := by
  rw [Finset.card_sym2, he]
  ring

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 2: Each external's shared edge is from e.sym2
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_edge_from_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e T : Finset V) (he : e ∈ M) (idx : Finset V → ℕ)
    (hT : T ∈ S_e' G M e idx) :
    ∃ edge ∈ e.sym2, edge ∈ T.sym2 := by
  have h_inter := external_inter_card_eq_2 G M hM e T he idx hT
  exact shared_edge_covers_external T e h_inter

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 3: Subset of 3-element set with card ≤ 2
-- ══════════════════════════════════════════════════════════════════════════════

lemma subset_3_card_le_2 (S : Finset (Sym2 V)) (e : Finset V) (he : e.card = 3)
    (hS : S ⊆ e.sym2) (hS2 : S.card ≤ 2) :
    S.card ≤ 2 := hS2

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 4: Packing element has card 3
-- ══════════════════════════════════════════════════════════════════════════════

lemma packing_element_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (e : Finset V) (he : e ∈ M) :
    e.card = 3 := by
  have : e ∈ G.cliqueFinset 3 := hM.1 he
  rw [SimpleGraph.mem_cliqueFinset_iff] at this
  exact this.2

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 5: Image of externals' shared edges
-- ══════════════════════════════════════════════════════════════════════════════

/-- The set of shared edges for all externals in S_e' -/
def sharedEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (idx : Finset V → ℕ) : Finset (Sym2 V) :=
  (S_e' G M e idx).biUnion (fun T => (T ∩ e).sym2)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 6: Shared edges ⊆ e.sym2
-- ══════════════════════════════════════════════════════════════════════════════

lemma sharedEdges_subset_e_sym2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (idx : Finset V → ℕ) :
    sharedEdges G M e idx ⊆ e.sym2 := by
  intro edge hedge
  simp only [sharedEdges, mem_biUnion] at hedge
  obtain ⟨T, _, hedge_inter⟩ := hedge
  rw [Finset.mem_sym2_iff] at hedge_inter ⊢
  exact ⟨inter_subset_right hedge_inter.1, inter_subset_right hedge_inter.2⟩

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isTrianglePacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isTrianglePacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Invalid field notation: Type of
  S
is not known; cannot resolve field `card`
Function expected at
  S_e'
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Invalid field notation: Type of
  T
is not known; cannot resolve field `sym2`-/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 2 edges suffice for S_e'
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Each external T ∈ S_e' has (T ∩ e).card = 2 (slot513)
2. T ∩ e determines an edge in e.sym2 that covers T (slot515)
3. All such edges form a subset of e.sym2 (which has 3 edges)
4. By 6-packing constraint, ≤2 distinct edge-types are used
5. Therefore ≤2 edges suffice
-/
theorem two_edges_suffice_for_Se' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M)
    (idx : Finset V → ℕ) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ e.sym2 ∧
      ∀ T ∈ S_e' G M e idx, ∃ edge ∈ E, edge ∈ T.sym2 := by
  sorry

end