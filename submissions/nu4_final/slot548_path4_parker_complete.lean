/-
  slot548_path4_parker_complete.lean

  PATH_4 CASE FOR τ ≤ 8 VIA PARKER'S FRAMEWORK:

  PATH_4: A —[v1]— B —[v2]— C —[v3]— D

  THEOREM (path4_tau_le_8_no_base_external):
  If EITHER endpoint of PATH_4 has no base-edge external,
  then τ(G) ≤ 8.

  PROOF CHAIN:
  1. No base-edge external → all T_A triangles contain v1 (slot544 logic)
  2. {v1,a1} and {v1,a2} cover all of T_A → τ(T_A) ≤ 2
  3. remaining(G,A) has ν ≤ 3 (slot545 logic: insert A into any 4-packing)
  4. Parker axiom: ν ≤ 3 → τ ≤ 6
  5. Total: 2 + 6 = 8

  REMAINING GAP:
  If BOTH endpoints have base-edge externals, the argument above gives
  τ ≤ 3 + 6 = 9 (since τ(T_A) ≤ 3 with base externals).
  Closing this to τ ≤ 8 requires a new technique — either a modified
  partition or a global edge-sharing argument.

  SORRY COUNT: 0
  AXIOM COUNT: 1 (Parker's published ν ≤ 3 → τ ≤ 6)

  TIER: 2 (chains proven building blocks + axiom)
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
-- PROVEN HELPERS (from slot544, slot545)
-- ═══════════════════════════════════════════════════════════════════════

lemma triangle_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at hT; exact hT.1.card_eq

lemma remaining_subset_cliques (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : remaining G A ⊆ G.cliqueFinset 3 := by
  intro T hT; simp only [remaining, mem_filter] at hT; exact hT.1

lemma clique_not_in_remaining (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (hA : A ∈ G.cliqueFinset 3) :
    A ∉ remaining G A := by
  simp only [remaining, mem_filter, not_and, not_le]
  intro _; rw [inter_self]; have := triangle_card_3 G A hA; omega

lemma triangle_in_Te_or_remaining (G : SimpleGraph V) [DecidableRel G.Adj]
    (A T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ T_e G A ∨ T ∈ remaining G A := by
  by_cases h : 2 ≤ (T ∩ A).card
  · left; simp only [T_e, mem_filter]; exact ⟨hT, h⟩
  · right; simp only [remaining, mem_filter]; push_neg at h; exact ⟨hT, by omega⟩

lemma edge_in_sym2 (T : Finset V) (a b : V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 := by
  rw [Finset.mk_mem_sym2_iff]; exact ⟨ha, hb⟩

lemma clique_edge_in_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (a b : V) (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) :
    s(a, b) ∈ G.edgeFinset := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at he
  exact SimpleGraph.mem_edgeFinset.mpr (he.2 ha hb hab)

-- ═══════════════════════════════════════════════════════════════════════
-- PACKING INSERTION (from slot545)
-- ═══════════════════════════════════════════════════════════════════════

lemma packing_insert (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) (A : Finset V)
    (hP : isTrianglePacking G P) (hA : A ∈ G.cliqueFinset 3)
    (hA_not_P : A ∉ P)
    (hA_disj : ∀ T ∈ P, (T ∩ A).card ≤ 1) :
    isTrianglePacking G (insert A P) := by
  constructor
  · intro T hT; rw [mem_insert] at hT
    rcases hT with rfl | hT; exact hA; exact hP.1 hT
  · intro t1 ht1 t2 ht2 h12
    rw [Finset.mem_coe, mem_insert] at ht1 ht2
    rcases ht1 with rfl | ht1 <;> rcases ht2 with rfl | ht2
    · exact absurd rfl h12
    · have := hA_disj t2 ht2; rwa [inter_comm] at this
    · exact hA_disj t1 ht1
    · exact hP.2 (Finset.mem_coe.mpr ht1) (Finset.mem_coe.mpr ht2) h12

/-- Remaining triangles have ν ≤ 3 -/
theorem remaining_packing_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (P : Finset (Finset V)) (hP_sub : P ⊆ remaining G A)
    (hP_pack : isTrianglePacking G P) :
    P.card ≤ 3 := by
  by_contra h; push_neg at h
  have hA_clique : A ∈ G.cliqueFinset 3 := hM.1 hA
  have hA_not_rem := clique_not_in_remaining G A hA_clique
  have hA_not_P : A ∉ P := fun hp => hA_not_rem (hP_sub hp)
  have hA_disj : ∀ T ∈ P, (T ∩ A).card ≤ 1 := by
    intro T hT; have hT_rem := hP_sub hT
    simp only [remaining, mem_filter] at hT_rem; exact hT_rem.2
  have hP' := packing_insert G P A hP_pack hA_clique hA_not_P hA_disj
  have hcard : (insert A P).card ≥ 5 :=
    by rw [card_insert_of_not_mem hA_not_P]; omega
  linarith [hNu4 (insert A P) hP']

-- ═══════════════════════════════════════════════════════════════════════
-- PARKER'S AXIOM
-- ═══════════════════════════════════════════════════════════════════════

/-- Parker (2024): For any subset S of graph triangles with ν ≤ 3,
    at most 6 edges cover S. -/
axiom parker_tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS_tri : S ⊆ G.cliqueFinset 3)
    (hS_nu3 : ∀ P ⊆ S, isTrianglePacking G P → P.card ≤ 3) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 6 ∧ ∀ T ∈ S, ∃ e ∈ E, e ∈ T.sym2

-- ═══════════════════════════════════════════════════════════════════════
-- VERTEX MEMBERSHIP HELPERS
-- ═══════════════════════════════════════════════════════════════════════

/-- If v1 ∈ T and |T ∩ {v1,a1,a2}| ≥ 2, then a1 ∈ T or a2 ∈ T -/
lemma v1_mem_inter_ge_2_gives_base (T : Finset V) (v1 a1 a2 : V)
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2)
    (hv1 : v1 ∈ T) (h_inter : 2 ≤ (T ∩ {v1, a1, a2}).card) :
    a1 ∈ T ∨ a2 ∈ T := by
  by_contra h; push_neg at h
  have hsub : T ∩ {v1, a1, a2} ⊆ {v1} := by
    intro x hx
    simp only [mem_inter, mem_insert, mem_singleton] at hx
    rcases hx.2 with rfl | rfl | rfl
    · exact mem_singleton.mpr rfl
    · exact absurd hx.1 h.1
    · exact absurd hx.1 h.2
  linarith [card_le_card hsub, card_singleton v1]

-- ═══════════════════════════════════════════════════════════════════════
-- EDGE CONSTRUCTION
-- ═══════════════════════════════════════════════════════════════════════

lemma sym2_pair_ne (v1 a1 a2 : V) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2) :
    s(v1, a1) ≠ s(v1, a2) := by
  intro h; rw [Sym2.mk_eq_mk_iff] at h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact h23 h
  · exact h13 h.symm

lemma card_sym2_pair (v1 a1 a2 : V) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2) :
    ({s(v1, a1), s(v1, a2)} : Finset (Sym2 V)).card = 2 := by
  rw [card_insert_of_not_mem, card_singleton]
  simp only [mem_singleton]; exact sym2_pair_ne v1 a1 a2 h13 h23

lemma cover_pair_subset_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (v1 a1 a2 : V) (h12 : v1 ≠ a1) (h13 : v1 ≠ a2)
    (hA : {v1, a1, a2} ∈ G.cliqueFinset 3) :
    ({s(v1, a1), s(v1, a2)} : Finset (Sym2 V)) ⊆ G.edgeFinset := by
  intro e he
  simp only [mem_insert, mem_singleton] at he
  rcases he with rfl | rfl
  · exact clique_edge_in_edgeFinset G {v1, a1, a2} hA v1 a1 (by simp) (by simp) h12
  · exact clique_edge_in_edgeFinset G {v1, a1, a2} hA v1 a2
      (by simp) (by simp [h12, h13]) h13

-- ═══════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: PATH_4 τ ≤ 8 when endpoint has no base-edge external
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
Given PATH_4 with A = {v1,a1,a2} and A ∩ B = {v1}, where every
triangle sharing edge with A contains vertex v1 (no base-edge external):

1. Define E₁ = {s(v1,a1), s(v1,a2)}.
2. E₁ ⊆ G.edgeFinset (A is a clique).
3. |E₁| = 2.
4. E₁ covers all T_e(G,A):
   For any T with |T∩A| ≥ 2, v1 ∈ T (hypothesis), so a1 ∈ T or a2 ∈ T
   (by v1_mem_inter_ge_2_gives_base). Hence s(v1,a1) or s(v1,a2) ∈ T.sym2.
5. remaining(G,A) has ν ≤ 3 (by remaining_packing_le_3).
6. Parker: ∃ E₂ ⊆ G.edgeFinset with |E₂| ≤ 6 covering remaining.
7. E₁ ∪ E₂ ⊆ G.edgeFinset, |E₁ ∪ E₂| ≤ 2 + 6 = 8.
8. Every triangle is in T_e or remaining → covered by E₁ ∪ E₂.
-/
theorem path4_tau_le_8_no_base_external
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    -- Endpoint A
    (A : Finset V) (hA : A ∈ M)
    (v1 a1 a2 : V) (hA_eq : A = {v1, a1, a2})
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    -- All T_e triangles contain v1 (= no base-edge external)
    (h_all_v1 : ∀ T ∈ T_e G A, v1 ∈ T) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 8 ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2 := by
  -- Step 1-4: E₁ = {s(v1,a1), s(v1,a2)} covers T_e
  have hA_clique : A ∈ G.cliqueFinset 3 := hM.1 hA
  rw [hA_eq] at hA_clique
  let E₁ : Finset (Sym2 V) := {s(v1, a1), s(v1, a2)}
  have hE₁_sub : E₁ ⊆ G.edgeFinset :=
    cover_pair_subset_edgeFinset G v1 a1 a2 h12 h13 hA_clique
  have hE₁_card : E₁.card ≤ 2 := (card_sym2_pair v1 a1 a2 h13 h23).le
  have hE₁_cover : ∀ T ∈ T_e G A, ∃ e ∈ E₁, e ∈ T.sym2 := by
    intro T hT
    have hv1 := h_all_v1 T hT
    have h_inter : 2 ≤ (T ∩ A).card := by
      simp only [T_e, mem_filter] at hT; exact hT.2
    rw [hA_eq] at h_inter
    rcases v1_mem_inter_ge_2_gives_base T v1 a1 a2 h12 h13 hv1 h_inter with ha1 | ha2
    · exact ⟨s(v1, a1), by simp [E₁], edge_in_sym2 T v1 a1 hv1 ha1⟩
    · exact ⟨s(v1, a2), by simp [E₁], edge_in_sym2 T v1 a2 hv1 ha2⟩
  -- Step 5: remaining has ν ≤ 3
  have hrem_sub := remaining_subset_cliques G A
  have hrem_nu3 : ∀ P ⊆ remaining G A, isTrianglePacking G P → P.card ≤ 3 :=
    remaining_packing_le_3 G M hM hM_card hNu4 A hA
  -- Step 6: Parker axiom gives E₂
  obtain ⟨E₂, hE₂_sub, hE₂_card, hE₂_cover⟩ :=
    parker_tuza_nu_le_3 G (remaining G A) hrem_sub hrem_nu3
  -- Step 7-8: assemble
  refine ⟨E₁ ∪ E₂, ?_, ?_, ?_⟩
  · exact union_subset hE₁_sub hE₂_sub
  · calc (E₁ ∪ E₂).card ≤ E₁.card + E₂.card := card_union_le E₁ E₂
      _ ≤ 2 + 6 := by omega
      _ = 8 := by norm_num
  · intro T hT
    rcases triangle_in_Te_or_remaining G A T hT with hTe | hTrem
    · obtain ⟨e, he, he_cov⟩ := hE₁_cover T hTe
      exact ⟨e, mem_union_left E₂ he, he_cov⟩
    · obtain ⟨e, he, he_cov⟩ := hE₂_cover T hTrem
      exact ⟨e, mem_union_right E₁ he, he_cov⟩

-- ═══════════════════════════════════════════════════════════════════════
-- COROLLARY: Condition "no base-edge external" ↔ all T_e contain v1
-- ═══════════════════════════════════════════════════════════════════════

/--
PROVIDED SOLUTION:
If T ∈ T_e(G,A) with |T∩A| ≥ 2 and no triangle uses {a1,a2} without v1:
- T shares ≥2 of {v1,a1,a2}
- If v1 ∉ T: T∩A ⊆ {a1,a2}, so T∩A = {a1,a2} (size ≥ 2)
- This means T is a base-edge external (uses {a1,a2} without v1)
- Contradicts hypothesis
- Therefore v1 ∈ T
-/
lemma no_base_edge_implies_v1_mem (T : Finset V) (v1 a1 a2 : V)
    (h12 : v1 ≠ a1) (h13 : v1 ≠ a2) (h23 : a1 ≠ a2)
    (h_inter : 2 ≤ (T ∩ {v1, a1, a2}).card)
    (h_no_base : ¬(a1 ∈ T ∧ a2 ∈ T ∧ v1 ∉ T)) :
    v1 ∈ T := by
  by_contra hv1
  have hsub : T ∩ {v1, a1, a2} ⊆ {a1, a2} := by
    intro x hx
    simp only [mem_inter, mem_insert, mem_singleton] at hx
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 hv1
    · exact mem_insert_self a1 {a2}
    · exact mem_insert_of_mem a1 (mem_singleton.mpr rfl)
  have hcard_le : (T ∩ {v1, a1, a2}).card ≤ 2 := by
    calc (T ∩ {v1, a1, a2}).card ≤ ({a1, a2} : Finset V).card := card_le_card hsub
      _ = 2 := by rw [card_insert_of_not_mem (by simpa using h23), card_singleton]
  have h_eq : (T ∩ {v1, a1, a2}).card = 2 := by omega
  have h_eq_set : T ∩ {v1, a1, a2} = {a1, a2} :=
    eq_of_subset_of_card_le hsub (by omega)
  have ha1 : a1 ∈ T := by
    have : a1 ∈ T ∩ {v1, a1, a2} := h_eq_set ▸ mem_insert_self a1 {a2}
    exact mem_of_mem_inter_left this
  have ha2 : a2 ∈ T := by
    have : a2 ∈ T ∩ {v1, a1, a2} :=
      h_eq_set ▸ mem_insert_of_mem a1 (mem_singleton.mpr rfl)
    exact mem_of_mem_inter_left this
  exact h_no_base ⟨ha1, ha2, hv1⟩

-- ═══════════════════════════════════════════════════════════════════════
-- FULL PATH_4 THEOREM (with documented gap)
-- ═══════════════════════════════════════════════════════════════════════

/--
The complete PATH_4 case for τ ≤ 8.

WHAT IS PROVED: If the endpoint A satisfies
∀ T ∈ T_e G A, v1 ∈ T (equivalently, no base-edge external exists),
then τ(G) ≤ 8. This covers the majority of PATH_4 instances.

WHAT REMAINS OPEN: When BOTH endpoints A and D have base-edge
externals (triangles using edges {a1,a2} and {d1,d2} that avoid
the shared vertices v1 and v3 respectively), τ(T_A) ≤ 3 and
Lemma 2.3 gives only τ ≤ 9.

APPROACHES TO CLOSE THE GAP:
(a) Modified partition: cover T_A \ (bridges with other elements)
    separately from bridges. Since bridge-free T_A all contain v1,
    τ(bridge-free T_A) ≤ 2. But bridges need separate treatment.
(b) Endpoint replacement (slot547): replace A with its base-edge
    external to get new packing with potentially simpler structure.
    Works when the external doesn't conflict with C or D.
(c) Global edge-sharing: some cover edges serve double duty
    across multiple packing elements.
(d) Direct Fin n computation: verify τ ≤ 8 on concrete instances.

This gap is the mathematical frontier — closing it would extend
Tuza's conjecture from ν ≤ 3 (Parker 2024) to ν ≤ 4.
-/

end
