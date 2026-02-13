/-
  slot526_two_edges_clean.lean

  CLEANED VERSION: Fix type inference issues for Aristotle

  KEY FIX: Add noncomputable section and proper Fintype instances
-/

import Mathlib

set_option maxHeartbeats 400000

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

/-- Externals using specific edges of e = {a,b,c} -/
def S_e_type (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (x y z : V) : Finset (Finset V) :=
  (S_e G M {x, y, z}).filter (fun T => x ∈ T ∧ y ∈ T ∧ z ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Clique edges are graph edges
-- ══════════════════════════════════════════════════════════════════════════════

lemma clique_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (a b : V) (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) :
    G.Adj a b := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at he
  exact he.2 ha hb hab

lemma clique_edge_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (a b : V) (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) :
    s(a, b) ∈ G.edgeFinset :=
  SimpleGraph.mem_edgeFinset.mpr (clique_adj G e he a b ha hb hab)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Edge covers triangle
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_in_sym2 (T : Finset V) (a b : V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 :=
  Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: S_e external shares exactly 2 vertices
-- ══════════════════════════════════════════════════════════════════════════════

lemma Se_inter_eq_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he3 : e.card = 3)
    (T : Finset V) (hT : T ∈ S_e G M e) :
    (T ∩ e).card = 2 := by
  simp only [S_e, mem_filter] at hT
  obtain ⟨hT_tri, hT_ne, hT_inter, _⟩ := hT
  have hT3 : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT_tri
    exact hT_tri.1.card_eq
  -- (T ∩ e).card ∈ {2, 3} since ≥2 and ≤3
  have hle3 : (T ∩ e).card ≤ 3 := (card_le_card inter_subset_right).trans he3.le
  interval_cases (T ∩ e).card <;> [omega; omega; rfl; skip]
  -- Case: (T ∩ e).card = 3
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
1. T_ab, T_bc, T_ac are pairwise edge-disjoint
2. With B, C, D ∈ M (other 3 elements), get 6 edge-disjoint triangles
3. Contradicts ν = 4
-/

axiom not_all_three_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬((S_e_type G M a b c).Nonempty ∧ (S_e_type G M b c a).Nonempty ∧ (S_e_type G M a c b).Nonempty)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: External uses one edge-type
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_uses_one_type (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (T : Finset V) (hT : T ∈ S_e G M {a, b, c}) :
    T ∈ S_e_type G M a b c ∨ T ∈ S_e_type G M b c a ∨ T ∈ S_e_type G M a c b := by
  have he3 : ({a, b, c} : Finset V).card = 3 := by
    simp only [card_insert_of_not_mem, card_singleton]
    · rfl
    · simp [hbc]
    · simp [hab, hac]
  have hinter := Se_inter_eq_2 G M {a, b, c} he3 T hT
  simp only [S_e_type, mem_filter]
  -- T ∩ {a,b,c} has exactly 2 elements
  by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;> by_cases hc : c ∈ T
  all_goals try {
    -- Count elements in T ∩ {a,b,c}
    have hcount : (T ∩ {a, b, c}).card = (if a ∈ T then 1 else 0) + (if b ∈ T then 1 else 0) + (if c ∈ T then 1 else 0) := by
      simp only [card_inter_of_mem_filter, card_insert_of_not_mem, card_singleton]
      sorry -- Finset counting
    simp only [ha, hb, hc, if_true, if_false] at hcount
    omega
  }
  · -- a ∈ T, b ∈ T, c ∉ T: type ab
    left; exact ⟨hT, ha, hb, hc⟩
  · -- a ∈ T, b ∉ T, c ∈ T: type ac
    right; right; exact ⟨hT, ha, hc, hb⟩
  · -- a ∉ T, b ∈ T, c ∈ T: type bc
    right; left; exact ⟨hT, hb, hc, ha⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 2 edges cover S_e (with valid edges)
-- ══════════════════════════════════════════════════════════════════════════════

theorem two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M)
    (a b c : V) (he_eq : e = {a, b, c}) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ E : Finset (Sym2 V),
      E ⊆ G.edgeFinset ∧
      E.card ≤ 2 ∧
      ∀ T ∈ S_e G M e, ∃ edge ∈ E, edge ∈ T.sym2 := by
  -- Get that e is a clique, so its edges are in G.edgeFinset
  have he_clq : e ∈ G.cliqueFinset 3 := hM.1 he
  rw [he_eq] at he_clq he
  have hab_edge := clique_edge_mem G {a,b,c} he_clq a b (by simp) (by simp) hab
  have hbc_edge := clique_edge_mem G {a,b,c} he_clq b c (by simp) (by simp) hbc
  have hac_edge := clique_edge_mem G {a,b,c} he_clq a c (by simp) (by simp) hac
  -- At most 2 of {ab, bc, ac} have externals
  have h_not_all := not_all_three_types G M hM hNu4 a b c he hab hbc hac
  push_neg at h_not_all
  -- Case split on which types are empty
  by_cases h_ab : (S_e_type G M a b c).Nonempty
  · by_cases h_bc : (S_e_type G M b c a).Nonempty
    · -- ab, bc nonempty → ac empty. Use {ab, bc}
      have h_ac : ¬(S_e_type G M a c b).Nonempty := h_not_all h_ab h_bc
      use {s(a, b), s(b, c)}
      refine ⟨?_, ?_, ?_⟩
      · intro e' he'; simp at he'; rcases he' with rfl | rfl <;> assumption
      · simp [card_insert_of_not_mem, hab]
      · intro T hT; rw [he_eq] at hT
        rcases external_uses_one_type G M a b c hab hbc hac T hT with h | h | h
        · simp only [S_e_type, mem_filter] at h
          exact ⟨s(a, b), by simp, edge_in_sym2 T a b h.2.1 h.2.2.1⟩
        · simp only [S_e_type, mem_filter] at h
          exact ⟨s(b, c), by simp, edge_in_sym2 T b c h.2.1 h.2.2.1⟩
        · exfalso; exact h_ac ⟨T, h⟩
    · -- ab nonempty, bc empty. Use {ab, ac}
      use {s(a, b), s(a, c)}
      refine ⟨?_, ?_, ?_⟩
      · intro e' he'; simp at he'; rcases he' with rfl | rfl <;> assumption
      · simp [card_insert_of_not_mem, hac]
      · intro T hT; rw [he_eq] at hT
        rcases external_uses_one_type G M a b c hab hbc hac T hT with h | h | h
        · simp only [S_e_type, mem_filter] at h
          exact ⟨s(a, b), by simp, edge_in_sym2 T a b h.2.1 h.2.2.1⟩
        · exfalso; exact h_bc ⟨T, h⟩
        · simp only [S_e_type, mem_filter] at h
          exact ⟨s(a, c), by simp, edge_in_sym2 T a c h.2.1 h.2.2.1⟩
  · -- ab empty
    by_cases h_bc : (S_e_type G M b c a).Nonempty
    · -- bc nonempty, ab empty. Use {bc, ac}
      use {s(b, c), s(a, c)}
      refine ⟨?_, ?_, ?_⟩
      · intro e' he'; simp at he'; rcases he' with rfl | rfl <;> assumption
      · simp [card_insert_of_not_mem]
        intro h; have := Sym2.mk.inj h; exact hab this.1.symm
      · intro T hT; rw [he_eq] at hT
        rcases external_uses_one_type G M a b c hab hbc hac T hT with h | h | h
        · exfalso; exact h_ab ⟨T, h⟩
        · simp only [S_e_type, mem_filter] at h
          exact ⟨s(b, c), by simp, edge_in_sym2 T b c h.2.1 h.2.2.1⟩
        · simp only [S_e_type, mem_filter] at h
          exact ⟨s(a, c), by simp, edge_in_sym2 T a c h.2.1 h.2.2.1⟩
    · -- ab empty, bc empty. Use {ac, ab} (covers only ac type if any)
      use {s(a, c), s(a, b)}
      refine ⟨?_, ?_, ?_⟩
      · intro e' he'; simp at he'; rcases he' with rfl | rfl <;> assumption
      · simp [card_insert_of_not_mem, hac.symm]
      · intro T hT; rw [he_eq] at hT
        rcases external_uses_one_type G M a b c hab hbc hac T hT with h | h | h
        · exfalso; exact h_ab ⟨T, h⟩
        · exfalso; exact h_bc ⟨T, h⟩
        · simp only [S_e_type, mem_filter] at h
          exact ⟨s(a, c), by simp, edge_in_sym2 T a c h.2.1 h.2.2.1⟩

end
