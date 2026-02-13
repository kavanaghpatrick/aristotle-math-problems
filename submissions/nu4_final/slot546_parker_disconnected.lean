/-
  slot546_parker_disconnected.lean

  PARKER'S LEMMA 2.4 FOR ν=4:
  If the intersection graph of a maximal 4-packing M is disconnected
  (M = P₁ ⊔ P₂ with P₁, P₂ vertex-disjoint), then τ(G) ≤ 8.

  KEY INSIGHTS:
  1. No triangle shares edges with elements from BOTH groups
     (would need ≥4 vertices in a 3-element set)
  2. Every packing within S_i can be extended by M \ P_i,
     so ν(S_i) ≤ |P_i|
  3. By Parker: τ(S_i) ≤ 2|P_i|
  4. Total: 2|P₁| + 2|P₂| = 2·4 = 8

  TIER: 2 (pigeonhole + packing extension)
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

/-- Triangles associated with a group: share edge with some group element -/
def groupTriangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T => ∃ e ∈ P, 2 ≤ (T ∩ e).card)

-- ═══════════════════════════════════════════════════════════════════════
-- HELPERS
-- ═══════════════════════════════════════════════════════════════════════

lemma triangle_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at hT; exact hT.1.card_eq

lemma groupTriangles_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) : groupTriangles G P ⊆ G.cliqueFinset 3 := by
  intro T hT; simp only [groupTriangles, mem_filter] at hT; exact hT.1

-- ═══════════════════════════════════════════════════════════════════════
-- KEY LEMMA 1: No triangle shares edges with both groups
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
If T shares edge with e₁ ∈ P₁ and e₂ ∈ P₂ (vertex-disjoint groups),
then |T ∩ e₁| ≥ 2 and |T ∩ e₂| ≥ 2.
Since e₁ ∩ e₂ = ∅ (vertex-disjoint), T ∩ e₁ and T ∩ e₂ are disjoint.
So |T| ≥ |T ∩ e₁| + |T ∩ e₂| ≥ 4, contradicting |T| = 3.
-/
theorem no_cross_group_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (P₁ P₂ : Finset (Finset V))
    (h_vdisj : ∀ e₁ ∈ P₁, ∀ e₂ ∈ P₂, Disjoint e₁ e₂)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    ¬(T ∈ groupTriangles G P₁ ∧ T ∈ groupTriangles G P₂) := by
  intro ⟨h1, h2⟩
  simp only [groupTriangles, mem_filter] at h1 h2
  obtain ⟨_, e₁, he₁, hTe₁⟩ := h1
  obtain ⟨_, e₂, he₂, hTe₂⟩ := h2
  -- e₁ and e₂ are vertex-disjoint
  have h_disj := h_vdisj e₁ he₁ e₂ he₂
  -- T ∩ e₁ and T ∩ e₂ are disjoint
  have h_inter_disj : Disjoint (T ∩ e₁) (T ∩ e₂) := by
    exact Disjoint.mono inter_subset_right inter_subset_right h_disj
  -- Their union is subset of T
  have h_sub : (T ∩ e₁) ∪ (T ∩ e₂) ⊆ T :=
    union_subset inter_subset_left inter_subset_left
  -- Cardinality contradiction
  have hcard := card_union_of_disjoint h_inter_disj
  have := card_le_card h_sub
  have hT3 := triangle_card_3 G T hT
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- KEY LEMMA 2: Every triangle is in some group (by maximality)
-- ═══════════════════════════════════════════════════════════════════════

lemma triangle_in_some_group (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (P₁ P₂ : Finset (Finset V)) (hP : P₁ ∪ P₂ = M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ groupTriangles G P₁ ∨ T ∈ groupTriangles G P₂ := by
  by_cases hTM : T ∈ M
  · -- T is in M, so T ∈ P₁ or T ∈ P₂
    rw [← hP] at hTM
    rcases mem_union.mp hTM with h | h
    · left; simp only [groupTriangles, mem_filter]
      refine ⟨hT, T, h, ?_⟩
      rw [inter_self]; have := triangle_card_3 G T hT; omega
    · right; simp only [groupTriangles, mem_filter]
      refine ⟨hT, T, h, ?_⟩
      rw [inter_self]; have := triangle_card_3 G T hT; omega
  · -- T ∉ M, so by maximality, T shares edge with some m ∈ M
    obtain ⟨m, hm, hmT⟩ := hM.2 T hT hTM
    rw [← hP] at hm
    rcases mem_union.mp hm with h | h
    · left; simp only [groupTriangles, mem_filter]
      exact ⟨hT, m, h, hmT⟩
    · right; simp only [groupTriangles, mem_filter]
      exact ⟨hT, m, h, hmT⟩

-- ═══════════════════════════════════════════════════════════════════════
-- KEY LEMMA 3: ν(S_i) ≤ |P_i| (packing extension argument)
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
Let Q ⊆ S_i be a packing. We show |Q| ≤ |P_i|.
Key: Q ∪ (M \ P_i) is a valid packing in G.

1. Q elements are pairwise edge-disjoint (Q is a packing).
2. M \ P_i elements are pairwise edge-disjoint (M is a packing).
3. Cross: For T ∈ Q and f ∈ M \ P_i:
   T ∈ S_i means T shares edge with some e ∈ P_i.
   f ∈ M \ P_i means f is vertex-disjoint from all P_i elements.
   If T also shared edge with f, then T would have ≥2 vertices
   in e ∈ P_i and ≥2 in f (vertex-disjoint from e), needing ≥4 vertices.
   Contradiction with |T| = 3. So |T ∩ f| ≤ 1.
4. |Q ∪ (M \ P_i)| = |Q| + |M \ P_i| ≤ ν = 4.
5. |M \ P_i| = 4 - |P_i|, so |Q| ≤ |P_i|.
-/
theorem group_packing_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM_pack : isTrianglePacking G M)
    (hM_card : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (P₁ P₂ : Finset (Finset V))
    (hP : P₁ ∪ P₂ = M) (hP_disj : Disjoint P₁ P₂)
    (h_vdisj : ∀ e₁ ∈ P₁, ∀ e₂ ∈ P₂, Disjoint e₁ e₂)
    -- For group P₁:
    (Q : Finset (Finset V)) (hQ_sub : Q ⊆ groupTriangles G P₁)
    (hQ_pack : isTrianglePacking G Q) :
    Q.card ≤ P₁.card := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════
-- PARKER AXIOM (parameterized)
-- ═══════════════════════════════════════════════════════════════════════

/-- Parker (2024): For triangle subset with ν ≤ k ≤ 3, τ ≤ 2k -/
axiom parker_tuza_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS_tri : S ⊆ G.cliqueFinset 3)
    (k : ℕ) (hk : k ≤ 3)
    (hS_nu : ∀ P ⊆ S, isTrianglePacking G P → P.card ≤ k) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 2 * k ∧ ∀ T ∈ S, ∃ e ∈ E, e ∈ T.sym2

-- ═══════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Disconnected matching → τ ≤ 8
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
1. All triangles partition into groupTriangles(P₁) and groupTriangles(P₂)
   (by triangle_in_some_group + no_cross_group_triangle).
2. ν(S₁) ≤ |P₁| and ν(S₂) ≤ |P₂| (by group_packing_le).
3. Since |P₁|, |P₂| ≤ 3 (both nonempty, sum = 4):
   By parker_tuza_bound: ∃ E₁ with |E₁| ≤ 2|P₁| covering S₁.
   By parker_tuza_bound: ∃ E₂ with |E₂| ≤ 2|P₂| covering S₂.
4. E = E₁ ∪ E₂ covers all triangles.
5. |E| ≤ |E₁| + |E₂| ≤ 2|P₁| + 2|P₂| = 2·4 = 8.
-/
theorem parker_lemma_24_disconnected (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hM_card : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (P₁ P₂ : Finset (Finset V))
    (hP : P₁ ∪ P₂ = M) (hP_disj : Disjoint P₁ P₂)
    (hP₁_ne : P₁.Nonempty) (hP₂_ne : P₂.Nonempty)
    (h_vdisj : ∀ e₁ ∈ P₁, ∀ e₂ ∈ P₂, Disjoint e₁ e₂) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 8 ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2 := by
  -- Part sizes
  have hP₁_le : P₁.card ≤ 3 := by
    have := hP₂_ne
    have hcard : P₁.card + P₂.card = 4 := by
      rw [← card_union_of_disjoint hP_disj, hP, hM_card]
    omega
  have hP₂_le : P₂.card ≤ 3 := by
    have := hP₁_ne
    have hcard : P₁.card + P₂.card = 4 := by
      rw [← card_union_of_disjoint hP_disj, hP, hM_card]
    omega
  -- Get covers for each group
  have hS₁_sub := groupTriangles_subset G P₁
  have hS₂_sub := groupTriangles_subset G P₂
  have hS₁_nu : ∀ Q ⊆ groupTriangles G P₁, isTrianglePacking G Q → Q.card ≤ P₁.card :=
    fun Q hQ hQp => group_packing_le G M hM.1 hM_card hNu4 P₁ P₂ hP hP_disj h_vdisj Q hQ hQp
  have hS₂_nu : ∀ Q ⊆ groupTriangles G P₂, isTrianglePacking G Q → Q.card ≤ P₂.card :=
    fun Q hQ hQp => group_packing_le G M hM.1 hM_card hNu4 P₂ P₁
      (by rw [union_comm]; exact hP) (Disjoint.symm hP_disj)
      (fun e₂ he₂ e₁ he₁ => Disjoint.symm (h_vdisj e₁ he₁ e₂ he₂)) Q hQ hQp
  obtain ⟨E₁, hE₁_sub, hE₁_card, hE₁_cover⟩ :=
    parker_tuza_bound G (groupTriangles G P₁) hS₁_sub P₁.card hP₁_le hS₁_nu
  obtain ⟨E₂, hE₂_sub, hE₂_card, hE₂_cover⟩ :=
    parker_tuza_bound G (groupTriangles G P₂) hS₂_sub P₂.card hP₂_le hS₂_nu
  -- Assemble
  refine ⟨E₁ ∪ E₂, ?_, ?_, ?_⟩
  · exact union_subset hE₁_sub hE₂_sub
  · have hcard_sum : P₁.card + P₂.card = 4 := by
      rw [← card_union_of_disjoint hP_disj, hP, hM_card]
    calc (E₁ ∪ E₂).card ≤ E₁.card + E₂.card := card_union_le E₁ E₂
      _ ≤ 2 * P₁.card + 2 * P₂.card := by omega
      _ = 2 * (P₁.card + P₂.card) := by ring
      _ = 2 * 4 := by rw [hcard_sum]
      _ = 8 := by norm_num
  · intro T hT
    rcases triangle_in_some_group G M hM P₁ P₂ hP T hT with h1 | h2
    · obtain ⟨e, he, hcov⟩ := hE₁_cover T h1
      exact ⟨e, mem_union_left E₂ he, hcov⟩
    · obtain ⟨e, he, hcov⟩ := hE₂_cover T h2
      exact ⟨e, mem_union_right E₁ he, hcov⟩

end
