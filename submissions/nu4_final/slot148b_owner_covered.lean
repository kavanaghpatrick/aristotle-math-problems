/-
Tuza ν=4 Strategy - Slot 148b: Owner Coverage Lemma

TARGET: Every triangle owned by A contains at least one edge from A.

This is TRIVIALLY TRUE by definition:
- If t = A: all 3 edges of t are in A.sym2
- If t shares edge with A: by definition, some edge is in both t.sym2 and A.sym2

PROVEN SCAFFOLDING: All from slot148a

ZERO SORRIES EXPECTED - pure definitional unfolding
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

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ e, e ∈ t.sym2 ∧ e ∈ S.sym2

def trianglesOwnedBy (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => t = A ∨ (t ∉ M ∧ sharesEdgeWith t A))

def edgeSetCovers (E : Finset (Sym2 V)) (t : Finset V) : Prop :=
  ∃ e ∈ E, e ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle owns itself via its own edges -/
lemma self_covered (A : Finset V) (hA_card : A.card = 3) :
    ∃ e ∈ A.sym2, e ∈ A.sym2 := by
  have h_ne : A.sym2.Nonempty := by
    rw [Finset.sym2_nonempty]; omega
  obtain ⟨e, he⟩ := h_ne
  exact ⟨e, he, he⟩

/-- Every triangle owned by A contains an A-edge -/
lemma owned_contains_A_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A : Finset V) (hA : A ∈ M) :
    ∀ t ∈ trianglesOwnedBy G M A, ∃ e ∈ A.sym2, e ∈ t.sym2 := by
  intro t ht
  simp only [trianglesOwnedBy, Finset.mem_filter] at ht
  obtain ⟨ht_clique, ht_owned⟩ := ht
  rcases ht_owned with rfl | ⟨_, h_share⟩
  · -- Case: t = A
    have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hA)).card_eq
    exact self_covered A hA_card
  · -- Case: t shares edge with A
    obtain ⟨e, he_t, he_A⟩ := h_share
    exact ⟨e, he_A, he_t⟩

/-- A's 3 edges cover all triangles owned by A -/
lemma A_edges_cover_owned (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A : Finset V) (hA : A ∈ M) :
    ∀ t ∈ trianglesOwnedBy G M A, edgeSetCovers A.sym2 t := by
  intro t ht
  obtain ⟨e, he_A, he_t⟩ := owned_contains_A_edge G M hM A hA t ht
  exact ⟨e, he_A, he_t⟩

/-- Corollary: τ(trianglesOwnedBy A) ≤ 3 -/
lemma tau_owned_by_A_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A : Finset V) (hA : A ∈ M) :
    ∃ E ⊆ A.sym2, E.card ≤ 3 ∧ ∀ t ∈ trianglesOwnedBy G M A, edgeSetCovers E t := by
  use A.sym2
  constructor
  · exact Finset.Subset.refl _
  constructor
  · have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hA)).card_eq
    rw [Finset.card_sym2]; omega
  · exact A_edges_cover_owned G M hM A hA

end
