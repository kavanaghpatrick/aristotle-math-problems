/-
  slot516_tau_le_8_assembly.lean

  SINGLE TARGET: τ ≤ 8 from S_e' partition

  Assembly theorem using all the scaffolded lemmas:
  - Every triangle in M or some S_e' (slot508)
  - S_e' sets are disjoint (slot509)
  - Each S_e' covered by ≤2 edges from e

  TIER: 2 (union bound assembly)
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

def isMaximalPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ e ∈ M, (T ∩ e).card ≥ 2

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

-- From slot508: Every non-M triangle is in some S_e'
axiom non_M_triangle_in_some_Se' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) (hT_notM : T ∉ M) :
    ∃ e ∈ M, T ∈ S_e' G M e idx

-- From slot509: S_e' sets are disjoint
axiom S_e'_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx) :
    Disjoint (S_e' G M e idx) (S_e' G M f idx)

-- From slot515: Each external covered by an edge from e
axiom Se'_covered_by_e_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e T : Finset V) (he : e ∈ M) (idx : Finset V → ℕ)
    (hT : T ∈ S_e' G M e idx) :
    ∃ edge ∈ e.sym2, edge ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 1: Partition completeness
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_in_M_or_Se' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨ ∃ e ∈ M, T ∈ S_e' G M e idx := by
  by_cases hT_M : T ∈ M
  · left; exact hT_M
  · right; exact non_M_triangle_in_some_Se' G M hM idx h_inj T hT hT_M

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 2: Union of 2-edge covers
-- ══════════════════════════════════════════════════════════════════════════════

lemma union_card_le (A B C D : Finset (Sym2 V))
    (hA : A.card ≤ 2) (hB : B.card ≤ 2) (hC : C.card ≤ 2) (hD : D.card ≤ 2) :
    (A ∪ B ∪ C ∪ D).card ≤ 8 := by
  calc (A ∪ B ∪ C ∪ D).card
      ≤ (A ∪ B ∪ C).card + D.card := card_union_le _ _
    _ ≤ (A ∪ B).card + C.card + D.card := by linarith [card_union_le (A ∪ B) C]
    _ ≤ A.card + B.card + C.card + D.card := by linarith [card_union_le A B]
    _ ≤ 2 + 2 + 2 + 2 := by linarith
    _ = 8 := by ring

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 3: Cover hits triangle
-- ══════════════════════════════════════════════════════════════════════════════

lemma cover_hits_triangle (T : Finset V) (Cover : Finset (Sym2 V))
    (h : ∃ edge ∈ Cover, edge ∈ T.sym2) :
    ∃ edge ∈ Cover, edge ∈ T.sym2 := h

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 4: Packing element covered by its edges
-- ══════════════════════════════════════════════════════════════════════════════

lemma packing_element_self_covered (e : Finset V) (he : e.card = 3) :
    ∃ edge ∈ e.sym2, edge ∈ e.sym2 := by
  have h : e.sym2.Nonempty := by
    rw [Finset.sym2_nonempty]
    omega
  obtain ⟨edge, hedge⟩ := h
  exact ⟨edge, hedge, hedge⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 5: M-element has 3 vertices
-- ══════════════════════════════════════════════════════════════════════════════

lemma packing_element_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (e : Finset V) (he : e ∈ M) :
    e.card = 3 := by
  have : e ∈ G.cliqueFinset 3 := hM.1 he
  rw [SimpleGraph.mem_cliqueFinset_iff] at this
  exact this.2

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 from partition
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Every triangle is in M or some S_e' (partition completeness)
2. For each e ∈ M, S_e' covered by ≤2 edges from e.sym2
3. M has 4 elements, so union of 4 covers has ≤8 edges
4. M-elements themselves are hit by their own edges
5. Non-M triangles are hit by their S_e' assignment's cover
-/
theorem tau_le_8_from_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (hM4 : M.card = 4)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (h_covers : ∀ e ∈ M, ∃ C : Finset (Sym2 V), C.card ≤ 2 ∧ C ⊆ e.sym2 ∧
      ∀ T ∈ S_e' G M e idx, ∃ edge ∈ C, edge ∈ T.sym2) :
    ∃ Cover : Finset (Sym2 V), Cover.card ≤ 8 ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ edge ∈ Cover, edge ∈ T.sym2 := by
  sorry

end
