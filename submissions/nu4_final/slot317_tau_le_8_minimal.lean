/-
  slot317: τ ≤ 8 for ν = 4 - Minimal scaffolded version

  Minimal proven scaffolding for Aristotle.
  Focus: definitions + key helper lemmas that compile cleanly.
-/

import Mathlib

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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
    (M : Finset (Finset V)) (X : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 1: Triangle in cliqueFinset 3 has card 3
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 := by
  have := SimpleGraph.mem_cliqueFinset_iff.mp hT
  exact this.2

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 2: sharesEdgeWith ↔ intersection ≥ 2
-- ══════════════════════════════════════════════════════════════════════════════

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩,
                                   v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 3: External has exactly 2 vertices in X
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_inter_card_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX_in_M : X ∈ M) (hX_card : X.card = 3)
    (T : Finset V) (hT : isExternalOf G M X T) :
    (T ∩ X).card = 2 := by
  have hT_card : T.card = 3 := triangle_card_three G T hT.1
  have h_share : sharesEdgeWith T X := hT.2.2.1
  have h_inter_ge : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp h_share
  have h_inter_le : (T ∩ X).card ≤ 2 := by
    by_contra h_gt
    push_neg at h_gt
    have h_sub : T ⊆ X := by
      have h_inter_sub : T ∩ X ⊆ T := Finset.inter_subset_left
      have h_card_eq : (T ∩ X).card = T.card := by
        have h1 : (T ∩ X).card ≤ T.card := Finset.card_le_card h_inter_sub
        linarith
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx
      exact Finset.mem_inter.mp hx |>.2
    have h_sub' : X ⊆ T := by
      have h_inter_sub : T ∩ X ⊆ X := Finset.inter_subset_right
      have h_card_eq : (T ∩ X).card = X.card := by
        have h1 : (T ∩ X).card ≤ X.card := Finset.card_le_card h_inter_sub
        linarith
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx
      exact Finset.mem_inter.mp hx |>.1
    have h_eq : T = X := Finset.Subset.antisymm h_sub h_sub'
    exact hT.2.1 (h_eq ▸ hX_in_M)
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 4: Packing elements share at most 1 vertex
-- ══════════════════════════════════════════════════════════════════════════════

lemma packing_inter_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hne : X ≠ Y) :
    (X ∩ Y).card ≤ 1 := hM.2 hX hY hne

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 5: Non-packing triangle shares edge with some packing element
-- ══════════════════════════════════════════════════════════════════════════════

lemma nonpacking_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3) (hT_notin : T ∉ M) :
    ∃ X ∈ M, sharesEdgeWith T X := by
  obtain ⟨m, hm_in, hm_inter⟩ := hM.2 T hT_tri hT_notin
  exact ⟨m, hm_in, sharesEdgeWith_iff_card_inter_ge_two T m |>.mpr hm_inter⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER 6: Edge in triangle sym2 means both endpoints in triangle
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_sym2_iff (T : Finset V) (u v : V) :
    s(u, v) ∈ T.sym2 ↔ u ∈ T ∧ v ∈ T := by
  rw [Finset.mem_sym2_iff]
  constructor
  · intro h
    constructor
    · apply h; simp [Sym2.mem_iff]
    · apply h; simp [Sym2.mem_iff]
  · intro ⟨hu, hv⟩ x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> assumption

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 (SINGLE SORRY)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8:

Given a maximum packing M with |M| = 4, we construct a cover of size ≤ 8.

Key insight: For each X ∈ M, we can cover X and all its "externals" (triangles
that share an edge with X but no other packing element) using ≤ 2 edges.

Construction: For each X = {a,b,c} ∈ M, include edges {a,b} and {a,c}.
This gives 4 × 2 = 8 edges total.

Why this works:
1. Each X ∈ M is covered by {a,b} (or {a,c}).
2. Each X-external T shares exactly 2 vertices with X. Since T ∩ X is some
   edge of X, and our edges {a,b}, {a,c} cover 2 of the 3 edges of X that
   contain vertex a, we need to show T ∩ X contains a.
3. For externals: If T ∩ X = {b,c} (not containing a), we can choose a
   different hub vertex (b or c) for X to ensure coverage.
4. Bridge triangles (sharing edges with 2+ packing elements) are covered
   because they share an edge with SOME packing element.

The key lemma (proven separately): All externals of X share a common vertex v.
Using v as the hub ensures all externals are covered by 2 edges through v.
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end
