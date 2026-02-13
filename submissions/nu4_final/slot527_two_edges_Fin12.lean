/-
  slot527_two_edges_Fin12.lean

  SIMPLIFIED VERSION: Concrete Fin 12 instead of generic V

  KEY FIX: Aristotle does better with decidable Fin n types
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS on Fin 12
-- ══════════════════════════════════════════════════════════════════════════════

abbrev V12 := Fin 12

def isTrianglePacking12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V12)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def S_e12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12) : Finset (Finset V12) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧ ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

/-- Externals using specific edges of e = {a,b,c} -/
def S_e_type12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12) (x y z : V12) : Finset (Finset V12) :=
  (S_e12 G M e).filter (fun T => x ∈ T ∧ y ∈ T ∧ z ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Clique edges are graph edges
-- ══════════════════════════════════════════════════════════════════════════════

lemma clique_adj12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (e : Finset V12) (he : e ∈ G.cliqueFinset 3)
    (a b : V12) (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) :
    G.Adj a b := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at he
  exact he.2 ha hb hab

lemma clique_edge_mem12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (e : Finset V12) (he : e ∈ G.cliqueFinset 3)
    (a b : V12) (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) :
    s(a, b) ∈ G.edgeFinset :=
  SimpleGraph.mem_edgeFinset.mpr (clique_adj12 G e he a b ha hb hab)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Edge covers triangle
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_sym2_12 (T : Finset V12) (a b : V12) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 :=
  Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: S_e external shares exactly 2 vertices
-- ══════════════════════════════════════════════════════════════════════════════

lemma Se_inter_eq_2_12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12) (he3 : e.card = 3)
    (T : Finset V12) (hT : T ∈ S_e12 G M e) :
    (T ∩ e).card = 2 := by
  simp only [S_e12, mem_filter] at hT
  obtain ⟨hT_tri, hT_ne, hT_inter, _⟩ := hT
  have hT3 : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT_tri
    exact hT_tri.1.card_eq
  have hle3 : (T ∩ e).card ≤ 3 := (card_le_card inter_subset_right).trans he3.le
  interval_cases (T ∩ e).card <;> [omega; omega; rfl; skip]
  have heq : T ∩ e = e := eq_of_subset_of_card_le inter_subset_right (by omega)
  have he_sub_T : e ⊆ T := fun x hx => mem_of_mem_inter_left (heq ▸ mem_inter.mpr ⟨?_, hx⟩)
  · have hTeq : T = e := eq_of_subset_of_card_le he_sub_T (by omega)
    exact absurd hTeq hT_ne
  · rw [heq]; exact mem_inter.mpr ⟨mem_of_mem_inter_left (heq.symm ▸ mem_inter_self hx), hx⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- 6-PACKING: At most 2 edge-types have externals
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH (6-packing argument):
If all 3 edge-types {ab}, {bc}, {ac} have externals T_ab, T_bc, T_ac:
1. T_ab, T_bc, T_ac are pairwise edge-disjoint (they share different pairs of {a,b,c})
2. With B, C, D ∈ M (other 3 elements of M), we get 6 edge-disjoint triangles:
   {A, T_ab, T_bc, T_ac, B, C, D} minus A gives 6 triangles
3. But M.card = 4, so M = {A, B, C, D}
4. The 3 externals T_ab, T_bc, T_ac plus B, C, D gives 6 edge-disjoint triangles
5. This contradicts ν = 4
-/

lemma not_all_three_types12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (hM4 : M.card = 4)  -- CRITICAL: must be maximal 4-packing, not arbitrary
    (hNu4 : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M) (he3 : e.card = 3)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬((S_e_type12 G M e a b c).Nonempty ∧
      (S_e_type12 G M e b c a).Nonempty ∧
      (S_e_type12 G M e a c b).Nonempty) := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: External uses one edge-type
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_uses_one_type12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (he3 : e.card = 3)
    (T : Finset V12) (hT : T ∈ S_e12 G M e) :
    T ∈ S_e_type12 G M e a b c ∨ T ∈ S_e_type12 G M e b c a ∨ T ∈ S_e_type12 G M e a c b := by
  have hinter := Se_inter_eq_2_12 G M e he3 T hT
  simp only [S_e_type12, mem_filter]
  -- T ∩ e has exactly 2 elements, so exactly one of {a,b,c} is not in T
  by_cases haT : a ∈ T <;> by_cases hbT : b ∈ T <;> by_cases hcT : c ∈ T
  · -- all 3 in T: impossible since |T ∩ e| = 2
    have h3 : ({a, b, c} : Finset V12) ⊆ T ∩ e := by
      intro x hx; simp at hx
      rcases hx with rfl | rfl | rfl
      · exact mem_inter.mpr ⟨haT, ha⟩
      · exact mem_inter.mpr ⟨hbT, hb⟩
      · exact mem_inter.mpr ⟨hcT, hc⟩
    have hcard : 3 ≤ (T ∩ e).card := by
      calc 3 = ({a, b, c} : Finset V12).card := by
              simp only [card_insert_of_not_mem, card_singleton, not_mem_singleton]
              simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
           _ ≤ (T ∩ e).card := card_le_card h3
    omega
  · -- a, b in T, c not in T: type ab
    left; exact ⟨hT, haT, hbT, hcT⟩
  · -- a, c in T, b not in T: type ac
    right; right; exact ⟨hT, haT, hcT, hbT⟩
  · -- a in T, b, c not: impossible since |T ∩ e| = 2
    have h1 : (T ∩ e).card ≤ 1 := by
      have hsub : T ∩ e ⊆ {a} := by
        intro x hx
        simp at hx ⊢
        have hxe := hx.2
        -- x ∈ e means x is a, b, or c
        -- x ∈ T and x ∈ e
        -- But b ∉ T and c ∉ T
        -- So x must be a
        -- Need to show e = {a,b,c} first
        sorry
      calc (T ∩ e).card ≤ ({a} : Finset V12).card := card_le_card hsub
           _ = 1 := card_singleton a
    omega
  · -- b, c in T, a not in T: type bc
    right; left; exact ⟨hT, hbT, hcT, haT⟩
  · -- b in T, a, c not: impossible since |T ∩ e| = 2
    sorry
  · -- c in T, a, b not: impossible since |T ∩ e| = 2
    sorry
  · -- none in T: impossible since |T ∩ e| = 2
    have h0 : (T ∩ e).card = 0 := by
      rw [card_eq_zero]
      ext x
      simp only [mem_inter, not_mem_empty, iff_false, not_and]
      intro hxT hxe
      sorry
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 2 edges cover S_e (with valid edges)
-- ══════════════════════════════════════════════════════════════════════════════

theorem two_edges_cover_Se12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (hM4 : M.card = 4)  -- CRITICAL: must be maximal 4-packing
    (hNu4 : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M) (he3 : e.card = 3)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ E : Finset (Sym2 V12),
      E ⊆ G.edgeFinset ∧
      E.card ≤ 2 ∧
      ∀ T ∈ S_e12 G M e, ∃ edge ∈ E, edge ∈ T.sym2 := by
  -- Get that e is a clique, so its edges are in G.edgeFinset
  have he_clq : e ∈ G.cliqueFinset 3 := hM.1 he
  have hab_edge := clique_edge_mem12 G e he_clq a b ha hb hab
  have hbc_edge := clique_edge_mem12 G e he_clq b c hb hc hbc
  have hac_edge := clique_edge_mem12 G e he_clq a c ha hc hac
  -- At most 2 of {ab, bc, ac} have externals
  have h_not_all := not_all_three_types12 G M hM hM4 hNu4 e he he3 a b c ha hb hc hab hbc hac
  push_neg at h_not_all
  -- Case split on which types are empty
  by_cases h_ab : (S_e_type12 G M e a b c).Nonempty
  · by_cases h_bc : (S_e_type12 G M e b c a).Nonempty
    · -- ab, bc nonempty → ac empty. Use {ab, bc}
      have h_ac : ¬(S_e_type12 G M e a c b).Nonempty := h_not_all h_ab h_bc
      use {s(a, b), s(b, c)}
      refine ⟨?_, ?_, ?_⟩
      · intro e' he'; simp at he'; rcases he' with rfl | rfl <;> assumption
      · simp only [card_insert_of_not_mem, card_singleton, Nat.reduceAdd]
        intro h
        have := Sym2.eq_iff.mp h
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hbc rfl; exact hab rfl]
      · intro T hT
        rcases external_uses_one_type12 G M e a b c ha hb hc hab hbc hac he3 T hT with h | h | h
        · simp only [S_e_type12, mem_filter] at h
          exact ⟨s(a, b), by simp, edge_in_sym2_12 T a b h.2.1 h.2.2.1⟩
        · simp only [S_e_type12, mem_filter] at h
          exact ⟨s(b, c), by simp, edge_in_sym2_12 T b c h.2.1 h.2.2.1⟩
        · exfalso; exact h_ac ⟨T, h⟩
    · -- ab nonempty, bc empty. Use {ab, ac}
      use {s(a, b), s(a, c)}
      refine ⟨?_, ?_, ?_⟩
      · intro e' he'; simp at he'; rcases he' with rfl | rfl <;> assumption
      · simp only [card_insert_of_not_mem, card_singleton, Nat.reduceAdd]
        intro h
        have := Sym2.eq_iff.mp h
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hac rfl; exact hac rfl]
      · intro T hT
        rcases external_uses_one_type12 G M e a b c ha hb hc hab hbc hac he3 T hT with h | h | h
        · simp only [S_e_type12, mem_filter] at h
          exact ⟨s(a, b), by simp, edge_in_sym2_12 T a b h.2.1 h.2.2.1⟩
        · exfalso; exact h_bc ⟨T, h⟩
        · simp only [S_e_type12, mem_filter] at h
          exact ⟨s(a, c), by simp, edge_in_sym2_12 T a c h.2.1 h.2.2.1⟩
  · -- ab empty
    by_cases h_bc : (S_e_type12 G M e b c a).Nonempty
    · -- bc nonempty, ab empty. Use {bc, ac}
      use {s(b, c), s(a, c)}
      refine ⟨?_, ?_, ?_⟩
      · intro e' he'; simp at he'; rcases he' with rfl | rfl <;> assumption
      · simp only [card_insert_of_not_mem, card_singleton, Nat.reduceAdd]
        intro h
        have := Sym2.eq_iff.mp h
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hab rfl; exact (hbc rfl).elim]
      · intro T hT
        rcases external_uses_one_type12 G M e a b c ha hb hc hab hbc hac he3 T hT with h | h | h
        · exfalso; exact h_ab ⟨T, h⟩
        · simp only [S_e_type12, mem_filter] at h
          exact ⟨s(b, c), by simp, edge_in_sym2_12 T b c h.2.1 h.2.2.1⟩
        · simp only [S_e_type12, mem_filter] at h
          exact ⟨s(a, c), by simp, edge_in_sym2_12 T a c h.2.1 h.2.2.1⟩
    · -- ab empty, bc empty. Use {ac, ab} (covers only ac type if any)
      use {s(a, c), s(a, b)}
      refine ⟨?_, ?_, ?_⟩
      · intro e' he'; simp at he'; rcases he' with rfl | rfl <;> assumption
      · simp only [card_insert_of_not_mem, card_singleton, Nat.reduceAdd]
        intro h
        have := Sym2.eq_iff.mp h
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hac rfl; exact hac.symm rfl]
      · intro T hT
        rcases external_uses_one_type12 G M e a b c ha hb hc hab hbc hac he3 T hT with h | h | h
        · exfalso; exact h_ab ⟨T, h⟩
        · exfalso; exact h_bc ⟨T, h⟩
        · simp only [S_e_type12, mem_filter] at h
          exact ⟨s(a, c), by simp, edge_in_sym2_12 T a c h.2.1 h.2.2.1⟩
