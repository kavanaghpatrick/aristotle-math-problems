/-
  slot253_covering_per_M_element.lean

  NEW APPROACH: Instead of proving externals share an apex,
  prove a COVERING bound directly.

  Key insight:
  - Externals using SAME A-edge {a,b} → covered by {a,b}
  - Externals using DIFFERENT A-edges → share apex x (proven in slot224f)
    → covered by edge containing x

  GOAL: τ(A ∪ externals(A)) ≤ 3 for each M-element A

  This gives τ ≤ 12 for ν=4, which we already have.
  But with synergies between M-elements, maybe we can do better.

  1 SORRY expected.
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

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

def externalsOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (isExternalOf G M A)

def trianglesOfA (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  {A} ∪ externalsOf G M A

def isTriangleCoverOn (S : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMAS (from slot182, slot224f)
-- ══════════════════════════════════════════════════════════════════════════════

lemma shares_edge_implies_two_vertices (t m : Finset V)
    (h_share : sharesEdgeWith t m) :
    (t ∩ m).card ≥ 2 := by
  obtain ⟨u, v, huv, hu_t, hv_t, hu_m, hv_m⟩ := h_share
  have hu_inter : u ∈ t ∩ m := Finset.mem_inter.mpr ⟨hu_t, hu_m⟩
  have hv_inter : v ∈ t ∩ m := Finset.mem_inter.mpr ⟨hv_t, hv_m⟩
  exact Finset.one_lt_card.mpr ⟨u, hu_inter, v, hv_inter, huv⟩

-- External has exactly 2 vertices in A
lemma external_inter_A_card_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3)
    (T : Finset V) (hT : isExternalOf G M A T)
    (hT_3 : T.card = 3) :
    (T ∩ A).card = 2 := by
  have h_ge : (T ∩ A).card ≥ 2 := shares_edge_implies_two_vertices T A hT.2.2.1
  have h_le : (T ∩ A).card ≤ 2 := by
    by_contra h; push_neg at h
    have h_sub : T ⊆ A := by
      have h_inter_sub : T ∩ A ⊆ T := Finset.inter_subset_left
      have h_card_eq : (T ∩ A).card = T.card := by
        have h1 : (T ∩ A).card ≤ T.card := Finset.card_le_card h_inter_sub; linarith
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx; exact Finset.mem_inter.mp hx |>.2
    have h_sub' : A ⊆ T := by
      have h_inter_sub : T ∩ A ⊆ A := Finset.inter_subset_right
      have h_card_eq : (T ∩ A).card = A.card := by
        have h1 : (T ∩ A).card ≤ A.card := Finset.card_le_card h_inter_sub; linarith
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx; exact Finset.mem_inter.mp hx |>.1
    exact hT.2.1 (Finset.Subset.antisymm h_sub h_sub' ▸ hA)
  linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY OBSERVATION: Same-edge externals are covered by that edge
-- ══════════════════════════════════════════════════════════════════════════════

/-- If T uses edge {a,b} from A (i.e., T ∩ A = {a,b}), then s(a,b) ∈ T.sym2 -/
lemma same_edge_covers (T A : Finset V) (a b : V)
    (hab : a ≠ b) (h_inter : T ∩ A = {a, b}) :
    s(a, b) ∈ T.sym2 := by
  have ha_T : a ∈ T := by
    have : a ∈ T ∩ A := by rw [h_inter]; simp
    exact Finset.mem_inter.mp this |>.1
  have hb_T : b ∈ T := by
    have : b ∈ T ∩ A := by rw [h_inter]; simp [hab.symm]
    exact Finset.mem_inter.mp this |>.1
  rw [Finset.mem_sym2_iff]
  intro x hx
  simp only [Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · exact ha_T
  · exact hb_T

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 3 edges cover A and all its externals
-- ══════════════════════════════════════════════════════════════════════════════

/--
  For each M-element A = {a, b, c}, we can cover A and all its externals
  with at most 3 edges: the 3 edges of A itself.

  Each external T uses exactly one edge {u,v} from A (where T ∩ A = {u,v}).
  That edge {u,v} covers T.

  So the 3 edges {a,b}, {a,c}, {b,c} cover A and all externals.
-/
theorem tau_trianglesOfA_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 3 ∧ isTriangleCoverOn (trianglesOfA G M A) E' := by
  -- Get vertices of A = {a, b, c}
  obtain ⟨a, b, c, hab, hac, hbc, h_A_eq⟩ := Finset.card_eq_three.mp hA_3
  -- Use the 3 edges of A
  use {s(a, b), s(a, c), s(b, c)}
  constructor
  · -- Card ≤ 3
    have h1 : s(a, b) ≠ s(a, c) := by
      intro h
      have := Sym2.eq_iff.mp h
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hbc h2
      · exact hab h1
    have h2 : s(a, b) ≠ s(b, c) := by
      intro h
      have := Sym2.eq_iff.mp h
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hab h1
      · exact hac h2.symm
    have h3 : s(a, c) ≠ s(b, c) := by
      intro h
      have := Sym2.eq_iff.mp h
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hab h1.symm
      · exact hac h2
    simp only [Finset.card_insert_of_not_mem, Finset.mem_insert, Finset.mem_singleton,
               Finset.card_singleton, h1, h2, h3, not_or, not_false_eq_true, and_self]
  · -- Cover property
    intro t ht
    simp only [trianglesOfA, Finset.mem_union, Finset.mem_singleton] at ht
    rcases ht with rfl | ht_ext
    · -- t = A: covered by any of the 3 edges, say {a, b}
      use s(a, b)
      constructor
      · simp
      · rw [h_A_eq, Finset.mem_sym2_iff]
        intro x hx
        simp only [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl <;> simp [hab.symm]
    · -- t is an external
      have ht_ext' : isExternalOf G M A t := Finset.mem_filter.mp ht_ext |>.2
      have ht_3 : t.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp ht_ext'.1 |>.2
      have h_inter_2 := external_inter_A_card_2 G M hM A hA hA_3 t ht_ext' ht_3
      -- t ∩ A is a 2-element subset of A = {a, b, c}
      -- So t ∩ A ∈ {{a,b}, {a,c}, {b,c}}
      rw [h_A_eq] at h_inter_2
      -- The edge t ∩ A covers t
      have h_inter_sub : t ∩ A ⊆ t := Finset.inter_subset_left
      -- One of the 3 edges must be t ∩ A
      sorry -- Aristotle: case analysis on which edge t uses

end
