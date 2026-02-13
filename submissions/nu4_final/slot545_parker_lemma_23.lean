/-
  slot545_parker_lemma_23.lean

  PARKER'S LEMMA 2.3 FOR ν=4:
  If some element A of a maximal 4-packing has τ(T_A) ≤ 2,
  then τ(G) ≤ 8.

  PROOF:
  1. Cover T_A with 2 edges (hypothesis, from slot544)
  2. Remaining triangles = those not sharing edge with A
  3. Remaining has ν ≤ 3 (adding A back would give 5-packing)
  4. By Parker's result (ν ≤ 3 → τ ≤ 6): cover remaining with 6 edges
  5. Total: 2 + 6 = 8

  TIER: 2 (packing insertion + Parker axiom)
-/

import Mathlib

set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

/-- T_e: all triangles sharing an edge (≥2 vertices) with e -/
def T_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T => 2 ≤ (T ∩ e).card)

/-- Remaining: triangles NOT sharing edge with e -/
def remaining (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T => (T ∩ e).card ≤ 1)

-- ═══════════════════════════════════════════════════════════════════════
-- HELPERS
-- ═══════════════════════════════════════════════════════════════════════

lemma triangle_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at hT; exact hT.1.card_eq

/-- Remaining triangles are graph triangles -/
lemma remaining_subset_cliques (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : remaining G A ⊆ G.cliqueFinset 3 := by
  intro T hT; simp only [remaining, mem_filter] at hT; exact hT.1

/-- A clique with self-intersection 3 is NOT in remaining -/
lemma clique_not_in_remaining (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (hA : A ∈ G.cliqueFinset 3) :
    A ∉ remaining G A := by
  simp only [remaining, mem_filter, not_and, not_le]
  intro _
  rw [inter_self]
  have := triangle_card_3 G A hA
  omega

/-- Every triangle is in T_e or remaining (partition) -/
lemma triangle_in_Te_or_remaining (G : SimpleGraph V) [DecidableRel G.Adj]
    (A T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ T_e G A ∨ T ∈ remaining G A := by
  by_cases h : 2 ≤ (T ∩ A).card
  · left; simp only [T_e, mem_filter]; exact ⟨hT, h⟩
  · right; simp only [remaining, mem_filter]; push_neg at h; exact ⟨hT, by omega⟩

/-- Inserting an element disjoint from all of P preserves packing -/
lemma packing_insert (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) (A : Finset V)
    (hP : isTrianglePacking G P) (hA : A ∈ G.cliqueFinset 3)
    (hA_not_P : A ∉ P)
    (hA_disj : ∀ T ∈ P, (T ∩ A).card ≤ 1) :
    isTrianglePacking G (insert A P) := by
  constructor
  · -- All elements are cliques
    intro T hT
    rw [mem_insert] at hT
    rcases hT with rfl | hT
    · exact hA
    · exact hP.1 hT
  · -- Pairwise edge-disjoint
    intro t1 ht1 t2 ht2 h12
    rw [Finset.mem_coe, mem_insert] at ht1 ht2
    rcases ht1 with rfl | ht1 <;> rcases ht2 with rfl | ht2
    · exact absurd rfl h12
    · -- A vs t2 ∈ P
      have := hA_disj t2 ht2
      rwa [inter_comm] at this
    · -- t1 ∈ P vs A
      exact hA_disj t1 ht1
    · -- Both in P
      exact hP.2 (Finset.mem_coe.mpr ht1) (Finset.mem_coe.mpr ht2) h12

/-- Card of insert when element not present -/
lemma card_insert_eq (P : Finset (Finset V)) (A : Finset V) (h : A ∉ P) :
    (insert A P).card = P.card + 1 :=
  card_insert_of_not_mem h

-- ═══════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Remaining triangles have packing number ≤ 3
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
Suppose P ⊆ remaining(A) is a packing with |P| ≥ 4.
1. A ∉ remaining(A) since |A ∩ A| = 3 > 1, so A ∉ P.
2. Every T ∈ P has |T ∩ A| ≤ 1 (definition of remaining).
3. By packing_insert: insert A P is a valid packing.
4. |insert A P| = |P| + 1 ≥ 5, contradicting ν ≤ 4.
-/
theorem remaining_packing_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (P : Finset (Finset V)) (hP_sub : P ⊆ remaining G A)
    (hP_pack : isTrianglePacking G P) :
    P.card ≤ 3 := by
  by_contra h
  push_neg at h
  -- A is a clique
  have hA_clique : A ∈ G.cliqueFinset 3 := hM.1 hA
  -- A ∉ remaining, so A ∉ P
  have hA_not_rem := clique_not_in_remaining G A hA_clique
  have hA_not_P : A ∉ P := fun hp => hA_not_rem (hP_sub hp)
  -- All P elements are edge-disjoint from A
  have hA_disj : ∀ T ∈ P, (T ∩ A).card ≤ 1 := by
    intro T hT
    have hT_rem := hP_sub hT
    simp only [remaining, mem_filter] at hT_rem
    exact hT_rem.2
  -- Insert A into P
  have hP' := packing_insert G P A hP_pack hA_clique hA_not_P hA_disj
  -- Card of insert A P ≥ 5
  have hcard : (insert A P).card ≥ 5 := by
    rw [card_insert_eq P A hA_not_P]; omega
  -- Contradicts ν ≤ 4
  have := hNu4 (insert A P) hP'
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- PARKER'S AXIOM: Tuza for ν ≤ 3 (Parker 2024, published result)
-- ═══════════════════════════════════════════════════════════════════════

/-- Parker (2024): For any subset S of graph triangles with packing number ≤ 3,
    at most 6 edges suffice to cover S. -/
axiom parker_tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS_tri : S ⊆ G.cliqueFinset 3)
    (hS_nu3 : ∀ P ⊆ S, isTrianglePacking G P → P.card ≤ 3) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 6 ∧ ∀ T ∈ S, ∃ e ∈ E, e ∈ T.sym2

-- ═══════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Parker's Lemma 2.3 for ν=4
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
1. We have E₁ covering T_e(G,A) with |E₁| ≤ 2 (hypothesis from slot544).
2. remaining(G,A) ⊆ G.cliqueFinset 3 (by remaining_subset_cliques).
3. remaining has ν ≤ 3 (by remaining_packing_le_3).
4. By parker_tuza_nu_le_3: ∃ E₂ ⊆ G.edgeFinset with |E₂| ≤ 6 covering remaining.
5. Let E = E₁ ∪ E₂.
6. E ⊆ G.edgeFinset (union of subsets of edgeFinset).
7. |E| ≤ |E₁| + |E₂| ≤ 2 + 6 = 8 (by card_union_le).
8. For any triangle T:
   - If |T ∩ A| ≥ 2: T ∈ T_e(G,A), covered by E₁ ⊆ E.
   - If |T ∩ A| ≤ 1: T ∈ remaining(G,A), covered by E₂ ⊆ E.
-/
theorem parker_lemma_23_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    -- From slot544: 2 edges cover T_e
    (E₁ : Finset (Sym2 V)) (hE₁_sub : E₁ ⊆ G.edgeFinset)
    (hE₁_card : E₁.card ≤ 2)
    (hE₁_cover : ∀ T ∈ T_e G A, ∃ e ∈ E₁, e ∈ T.sym2) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 8 ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2 := by
  -- Step 2-3: remaining has ν ≤ 3
  have hrem_sub := remaining_subset_cliques G A
  have hrem_nu3 : ∀ P ⊆ remaining G A, isTrianglePacking G P → P.card ≤ 3 :=
    remaining_packing_le_3 G M hM hM_card hNu4 A hA
  -- Step 4: Parker axiom gives E₂
  obtain ⟨E₂, hE₂_sub, hE₂_card, hE₂_cover⟩ :=
    parker_tuza_nu_le_3 G (remaining G A) hrem_sub hrem_nu3
  -- Step 5-8: assemble
  refine ⟨E₁ ∪ E₂, ?_, ?_, ?_⟩
  · -- E ⊆ G.edgeFinset
    exact union_subset hE₁_sub hE₂_sub
  · -- |E| ≤ 8
    calc (E₁ ∪ E₂).card ≤ E₁.card + E₂.card := card_union_le E₁ E₂
      _ ≤ 2 + 6 := by omega
      _ = 8 := by norm_num
  · -- Covers all triangles
    intro T hT
    rcases triangle_in_Te_or_remaining G A T hT with hTe | hTrem
    · obtain ⟨e, he, he_cov⟩ := hE₁_cover T hTe
      exact ⟨e, mem_union_left E₂ he, he_cov⟩
    · obtain ⟨e, he, he_cov⟩ := hE₂_cover T hTrem
      exact ⟨e, mem_union_right E₁ he, he_cov⟩

end
