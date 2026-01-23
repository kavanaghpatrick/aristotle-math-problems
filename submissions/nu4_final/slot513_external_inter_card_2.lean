/-
  slot513_external_inter_card_2.lean

  SINGLE TARGET: S_e external T has (T ∩ e).card = 2 (not 3)

  Key: T ≠ e and both have 3 elements, so intersection is at most 2
  Combined with ≥2 requirement gives exactly 2.

  TIER: 1 (cardinality arithmetic)
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
-- SCAFFOLDING LEMMA 1: Triangle has card 3
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_3 (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V)
    (hT : T ∈ G.cliqueFinset 3) : T.card = 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at hT
  exact hT.2

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 2: Intersection ≤ smaller set
-- ══════════════════════════════════════════════════════════════════════════════

lemma inter_card_le_left (A B : Finset V) : (A ∩ B).card ≤ A.card :=
  card_le_card inter_subset_left

lemma inter_card_le_right (A B : Finset V) : (A ∩ B).card ≤ B.card :=
  card_le_card inter_subset_right

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 3: card = 3 and inter = 3 implies equal
-- ══════════════════════════════════════════════════════════════════════════════

lemma eq_of_card_3_inter_3 (A B : Finset V) (hA : A.card = 3) (hB : B.card = 3)
    (h_inter : (A ∩ B).card = 3) : A = B := by
  have h1 : A ∩ B ⊆ A := inter_subset_left
  have h2 : A ∩ B ⊆ B := inter_subset_right
  have h3 : (A ∩ B).card = A.card := by omega
  have h4 : (A ∩ B).card = B.card := by omega
  have h5 : A ∩ B = A := eq_of_subset_of_card_le h1 (by omega)
  have h6 : A ∩ B = B := eq_of_subset_of_card_le h2 (by omega)
  rw [← h5, h6]

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 4: T ≠ e with both card 3 implies inter ≤ 2
-- ══════════════════════════════════════════════════════════════════════════════

lemma inter_le_2_of_ne (T e : Finset V) (hT : T.card = 3) (he : e.card = 3) (hne : T ≠ e) :
    (T ∩ e).card ≤ 2 := by
  by_contra h
  push_neg at h
  have h_le : (T ∩ e).card ≤ T.card := inter_card_le_left T e
  rw [hT] at h_le
  interval_cases (T ∩ e).card
  · omega
  · omega
  · omega
  · exact hne (eq_of_card_3_inter_3 T e hT he rfl)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 5: S_e membership unpacked
-- ══════════════════════════════════════════════════════════════════════════════

lemma mem_S_e_iff (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e T : Finset V) :
    T ∈ S_e G M e ↔ T ∈ G.cliqueFinset 3 ∧ T ≠ e ∧ 2 ≤ (T ∩ e).card ∧
      ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1 := by
  simp only [S_e, mem_filter, and_assoc]

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: External has exactly 2-vertex intersection
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. T ∈ S_e means T ∈ cliqueFinset 3, so T.card = 3
2. e ∈ M ⊆ cliqueFinset 3, so e.card = 3
3. T ≠ e (from S_e definition)
4. By inter_le_2_of_ne, (T ∩ e).card ≤ 2
5. By S_e definition, 2 ≤ (T ∩ e).card
6. Therefore (T ∩ e).card = 2
-/
theorem external_inter_card_eq_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e T : Finset V) (he : e ∈ M) (hT : T ∈ S_e G M e) :
    (T ∩ e).card = 2 := by
  rw [mem_S_e_iff] at hT
  obtain ⟨hT_clique, hT_ne, hT_ge2, _⟩ := hT
  have hT_card := triangle_card_3 G T hT_clique
  have he_clique : e ∈ G.cliqueFinset 3 := hM.1 he
  have he_card := triangle_card_3 G e he_clique
  have h_le2 := inter_le_2_of_ne T e hT_card he_card hT_ne
  omega

end
