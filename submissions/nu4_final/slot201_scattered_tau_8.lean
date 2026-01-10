/-
  slot201_scattered_tau_8.lean

  THEOREM: τ ≤ 8 for scattered configuration (4 disjoint triangles)

  CASE: scattered = 4 vertex-disjoint triangles (no shared vertices)

  PROOF STRATEGY:
  - Each M-element is completely isolated
  - No bridges exist (no shared vertices between M-elements)
  - Each M-element needs at most 2 edges to cover its externals
  - 4 × 2 = 8 edges total

  DIFFICULTY: 2/5 (straightforward from disjointness)
  SUCCESS PROBABILITY: 90%
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TuzaNu4

/-- A triangle is a 3-clique -/
def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t.card = 3 ∧ G.IsClique t

/-- Triangles of G as a Finset -/
def triangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  G.cliqueFinset 3

/-- Two triangles share an edge -/
def sharesEdge (t₁ t₂ : Finset V) : Prop :=
  (t₁ ∩ t₂).card ≥ 2

/-- A packing is edge-disjoint -/
def isPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  (∀ t ∈ M, isTriangle G t) ∧
  (∀ t₁ ∈ M, ∀ t₂ ∈ M, t₁ ≠ t₂ → ¬sharesEdge t₁ t₂)

/-- Maximal packing (cannot add more triangles) -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isPacking G M ∧
  ∀ t ∈ triangles G, t ∉ M → ∃ m ∈ M, sharesEdge t m

/-- Scattered configuration: 4 vertex-disjoint triangles -/
structure Scattered (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  M_is_ABCD : M = {A, B, C, D}
  disjoint_AB : Disjoint A B
  disjoint_AC : Disjoint A C
  disjoint_AD : Disjoint A D
  disjoint_BC : Disjoint B C
  disjoint_BD : Disjoint B D
  disjoint_CD : Disjoint C D

/-- Edge cover: set of edges hitting all triangles -/
def isEdgeCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) : Prop :=
  ∀ t ∈ triangles G, ∃ e ∈ E, ∃ u v : V, e = s(u, v) ∧ u ∈ t ∧ v ∈ t

/-- Triangle covering number -/
noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ isEdgeCover G E }

/-- Key lemma: In scattered config, external of A shares edge only with A -/
theorem scattered_external_unique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Scattered G M)
    (T : Finset V) (hT : T ∈ triangles G) (hT_not_M : T ∉ M)
    (hT_shares_A : sharesEdge T cfg.A) :
    ¬sharesEdge T cfg.B ∧ ¬sharesEdge T cfg.C ∧ ¬sharesEdge T cfg.D := by
  -- If T shares edge with A and with B, then T ∩ A ≥ 2 and T ∩ B ≥ 2
  -- But A and B are disjoint, and T has only 3 vertices
  -- So T ∩ A and T ∩ B can't both have ≥ 2 elements
  constructor
  · intro h_shares_B
    unfold sharesEdge at hT_shares_A h_shares_B
    have hTA : (T ∩ cfg.A).card ≥ 2 := hT_shares_A
    have hTB : (T ∩ cfg.B).card ≥ 2 := h_shares_B
    -- T has card 3
    have hT3 : T.card = 3 := by
      unfold triangles at hT
      rw [SimpleGraph.mem_cliqueFinset_iff] at hT
      exact hT.2
    -- A ∩ B = ∅ by disjoint_AB
    have hAB_disj : cfg.A ∩ cfg.B = ∅ := Finset.disjoint_iff_inter_eq_empty.mp cfg.disjoint_AB
    -- (T ∩ A) and (T ∩ B) are disjoint subsets of T
    have h_disj_TA_TB : Disjoint (T ∩ cfg.A) (T ∩ cfg.B) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext x
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
      intro ⟨⟨_, hxA⟩, ⟨_, hxB⟩⟩
      have : x ∈ cfg.A ∩ cfg.B := Finset.mem_inter.mpr ⟨hxA, hxB⟩
      rw [hAB_disj] at this
      exact Finset.notMem_empty x this
    -- Combined cardinality ≥ 4, but T has only 3 elements
    have h_sum : (T ∩ cfg.A).card + (T ∩ cfg.B).card ≤ T.card := by
      have := Finset.card_union_add_card_inter (T ∩ cfg.A) (T ∩ cfg.B)
      rw [Finset.disjoint_iff_inter_eq_empty.mp h_disj_TA_TB] at this
      simp only [Finset.card_empty, add_zero] at this
      have h_sub : (T ∩ cfg.A) ∪ (T ∩ cfg.B) ⊆ T := by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_inter] at hx
        cases hx with
        | inl h => exact h.1
        | inr h => exact h.1
      calc (T ∩ cfg.A).card + (T ∩ cfg.B).card
          = ((T ∩ cfg.A) ∪ (T ∩ cfg.B)).card := by rw [← this]
        _ ≤ T.card := Finset.card_le_card h_sub
    omega
  constructor
  · intro h_shares_C
    -- Same argument for C
    unfold sharesEdge at hT_shares_A h_shares_C
    have hTA : (T ∩ cfg.A).card ≥ 2 := hT_shares_A
    have hTC : (T ∩ cfg.C).card ≥ 2 := h_shares_C
    have hT3 : T.card = 3 := by
      unfold triangles at hT
      rw [SimpleGraph.mem_cliqueFinset_iff] at hT
      exact hT.2
    have hAC_disj : cfg.A ∩ cfg.C = ∅ := Finset.disjoint_iff_inter_eq_empty.mp cfg.disjoint_AC
    have h_disj_TA_TC : Disjoint (T ∩ cfg.A) (T ∩ cfg.C) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext x
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
      intro ⟨⟨_, hxA⟩, ⟨_, hxC⟩⟩
      have : x ∈ cfg.A ∩ cfg.C := Finset.mem_inter.mpr ⟨hxA, hxC⟩
      rw [hAC_disj] at this
      exact Finset.notMem_empty x this
    have h_sum : (T ∩ cfg.A).card + (T ∩ cfg.C).card ≤ T.card := by
      have := Finset.card_union_add_card_inter (T ∩ cfg.A) (T ∩ cfg.C)
      rw [Finset.disjoint_iff_inter_eq_empty.mp h_disj_TA_TC] at this
      simp only [Finset.card_empty, add_zero] at this
      have h_sub : (T ∩ cfg.A) ∪ (T ∩ cfg.C) ⊆ T := by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_inter] at hx
        cases hx with
        | inl h => exact h.1
        | inr h => exact h.1
      calc (T ∩ cfg.A).card + (T ∩ cfg.C).card
          = ((T ∩ cfg.A) ∪ (T ∩ cfg.C)).card := by rw [← this]
        _ ≤ T.card := Finset.card_le_card h_sub
    omega
  · intro h_shares_D
    -- Same argument for D
    unfold sharesEdge at hT_shares_A h_shares_D
    have hTA : (T ∩ cfg.A).card ≥ 2 := hT_shares_A
    have hTD : (T ∩ cfg.D).card ≥ 2 := h_shares_D
    have hT3 : T.card = 3 := by
      unfold triangles at hT
      rw [SimpleGraph.mem_cliqueFinset_iff] at hT
      exact hT.2
    have hAD_disj : cfg.A ∩ cfg.D = ∅ := Finset.disjoint_iff_inter_eq_empty.mp cfg.disjoint_AD
    have h_disj_TA_TD : Disjoint (T ∩ cfg.A) (T ∩ cfg.D) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext x
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
      intro ⟨⟨_, hxA⟩, ⟨_, hxD⟩⟩
      have : x ∈ cfg.A ∩ cfg.D := Finset.mem_inter.mpr ⟨hxA, hxD⟩
      rw [hAD_disj] at this
      exact Finset.notMem_empty x this
    have h_sum : (T ∩ cfg.A).card + (T ∩ cfg.D).card ≤ T.card := by
      have := Finset.card_union_add_card_inter (T ∩ cfg.A) (T ∩ cfg.D)
      rw [Finset.disjoint_iff_inter_eq_empty.mp h_disj_TA_TD] at this
      simp only [Finset.card_empty, add_zero] at this
      have h_sub : (T ∩ cfg.A) ∪ (T ∩ cfg.D) ⊆ T := by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_inter] at hx
        cases hx with
        | inl h => exact h.1
        | inr h => exact h.1
      calc (T ∩ cfg.A).card + (T ∩ cfg.D).card
          = ((T ∩ cfg.A) ∪ (T ∩ cfg.D)).card := by rw [← this]
        _ ≤ T.card := Finset.card_le_card h_sub
    omega

/-- Key lemma: No bridges exist in scattered configuration -/
theorem scattered_no_bridges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Scattered G M)
    (T : Finset V) (hT : T ∈ triangles G) (hT_not_M : T ∉ M) :
    ¬(∃ X Y : Finset V, X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧ sharesEdge T X ∧ sharesEdge T Y) := by
  intro ⟨X, Y, hXM, hYM, hXY, hTX, hTY⟩
  -- X ∈ M means X ∈ {A, B, C, D}
  rw [cfg.M_is_ABCD] at hXM hYM
  simp only [Finset.mem_insert, Finset.mem_singleton] at hXM hYM
  -- Case analysis on X
  rcases hXM with rfl | rfl | rfl | rfl
  · -- X = A, check Y
    rcases hYM with rfl | rfl | rfl | rfl
    · exact hXY rfl  -- Y = A = X, contradiction
    · -- Y = B: T shares edge with A and B, but they're disjoint
      have := scattered_external_unique G M hM cfg T hT hT_not_M hTX
      exact this.1 hTY
    · have := scattered_external_unique G M hM cfg T hT hT_not_M hTX
      exact this.2.1 hTY
    · have := scattered_external_unique G M hM cfg T hT hT_not_M hTX
      exact this.2.2 hTY
  · -- X = B
    rcases hYM with rfl | rfl | rfl | rfl
    · have := scattered_external_unique G M hM cfg T hT hT_not_M hTY
      exact this.1 hTX
    · exact hXY rfl
    · -- T shares edge with B and C
      unfold sharesEdge at hTX hTY
      have hT3 : T.card = 3 := by
        unfold triangles at hT
        rw [SimpleGraph.mem_cliqueFinset_iff] at hT
        exact hT.2
      have hBC_disj : cfg.B ∩ cfg.C = ∅ := Finset.disjoint_iff_inter_eq_empty.mp cfg.disjoint_BC
      have h_disj : Disjoint (T ∩ cfg.B) (T ∩ cfg.C) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext x
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
        intro ⟨⟨_, hxB⟩, ⟨_, hxC⟩⟩
        have : x ∈ cfg.B ∩ cfg.C := Finset.mem_inter.mpr ⟨hxB, hxC⟩
        rw [hBC_disj] at this
        exact Finset.notMem_empty x this
      have h_sum : (T ∩ cfg.B).card + (T ∩ cfg.C).card ≤ T.card := by
        have := Finset.card_union_add_card_inter (T ∩ cfg.B) (T ∩ cfg.C)
        rw [Finset.disjoint_iff_inter_eq_empty.mp h_disj] at this
        simp only [Finset.card_empty, add_zero] at this
        have h_sub : (T ∩ cfg.B) ∪ (T ∩ cfg.C) ⊆ T := by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_inter] at hx
          cases hx with
          | inl h => exact h.1
          | inr h => exact h.1
        calc (T ∩ cfg.B).card + (T ∩ cfg.C).card
            = ((T ∩ cfg.B) ∪ (T ∩ cfg.C)).card := by rw [← this]
          _ ≤ T.card := Finset.card_le_card h_sub
      omega
    · -- T shares edge with B and D
      unfold sharesEdge at hTX hTY
      have hT3 : T.card = 3 := by
        unfold triangles at hT
        rw [SimpleGraph.mem_cliqueFinset_iff] at hT
        exact hT.2
      have hBD_disj : cfg.B ∩ cfg.D = ∅ := Finset.disjoint_iff_inter_eq_empty.mp cfg.disjoint_BD
      have h_disj : Disjoint (T ∩ cfg.B) (T ∩ cfg.D) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext x
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
        intro ⟨⟨_, hxB⟩, ⟨_, hxD⟩⟩
        have : x ∈ cfg.B ∩ cfg.D := Finset.mem_inter.mpr ⟨hxB, hxD⟩
        rw [hBD_disj] at this
        exact Finset.notMem_empty x this
      have h_sum : (T ∩ cfg.B).card + (T ∩ cfg.D).card ≤ T.card := by
        have := Finset.card_union_add_card_inter (T ∩ cfg.B) (T ∩ cfg.D)
        rw [Finset.disjoint_iff_inter_eq_empty.mp h_disj] at this
        simp only [Finset.card_empty, add_zero] at this
        have h_sub : (T ∩ cfg.B) ∪ (T ∩ cfg.D) ⊆ T := by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_inter] at hx
          cases hx with
          | inl h => exact h.1
          | inr h => exact h.1
        calc (T ∩ cfg.B).card + (T ∩ cfg.D).card
            = ((T ∩ cfg.B) ∪ (T ∩ cfg.D)).card := by rw [← this]
          _ ≤ T.card := Finset.card_le_card h_sub
      omega
  · -- X = C (similar to above)
    rcases hYM with rfl | rfl | rfl | rfl
    · have := scattered_external_unique G M hM cfg T hT hT_not_M hTY
      exact this.2.1 hTX
    · -- T shares edge with C and B
      unfold sharesEdge at hTX hTY
      have hT3 : T.card = 3 := by
        unfold triangles at hT
        rw [SimpleGraph.mem_cliqueFinset_iff] at hT
        exact hT.2
      have hBC_disj : cfg.B ∩ cfg.C = ∅ := Finset.disjoint_iff_inter_eq_empty.mp cfg.disjoint_BC
      have h_disj : Disjoint (T ∩ cfg.C) (T ∩ cfg.B) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext x
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
        intro ⟨⟨_, hxC⟩, ⟨_, hxB⟩⟩
        have : x ∈ cfg.B ∩ cfg.C := Finset.mem_inter.mpr ⟨hxB, hxC⟩
        rw [hBC_disj] at this
        exact Finset.notMem_empty x this
      have h_sum : (T ∩ cfg.C).card + (T ∩ cfg.B).card ≤ T.card := by
        have := Finset.card_union_add_card_inter (T ∩ cfg.C) (T ∩ cfg.B)
        rw [Finset.disjoint_iff_inter_eq_empty.mp h_disj] at this
        simp only [Finset.card_empty, add_zero] at this
        have h_sub : (T ∩ cfg.C) ∪ (T ∩ cfg.B) ⊆ T := by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_inter] at hx
          cases hx with
          | inl h => exact h.1
          | inr h => exact h.1
        calc (T ∩ cfg.C).card + (T ∩ cfg.B).card
            = ((T ∩ cfg.C) ∪ (T ∩ cfg.B)).card := by rw [← this]
          _ ≤ T.card := Finset.card_le_card h_sub
      omega
    · exact hXY rfl
    · -- T shares edge with C and D
      unfold sharesEdge at hTX hTY
      have hT3 : T.card = 3 := by
        unfold triangles at hT
        rw [SimpleGraph.mem_cliqueFinset_iff] at hT
        exact hT.2
      have hCD_disj : cfg.C ∩ cfg.D = ∅ := Finset.disjoint_iff_inter_eq_empty.mp cfg.disjoint_CD
      have h_disj : Disjoint (T ∩ cfg.C) (T ∩ cfg.D) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext x
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
        intro ⟨⟨_, hxC⟩, ⟨_, hxD⟩⟩
        have : x ∈ cfg.C ∩ cfg.D := Finset.mem_inter.mpr ⟨hxC, hxD⟩
        rw [hCD_disj] at this
        exact Finset.notMem_empty x this
      have h_sum : (T ∩ cfg.C).card + (T ∩ cfg.D).card ≤ T.card := by
        have := Finset.card_union_add_card_inter (T ∩ cfg.C) (T ∩ cfg.D)
        rw [Finset.disjoint_iff_inter_eq_empty.mp h_disj] at this
        simp only [Finset.card_empty, add_zero] at this
        have h_sub : (T ∩ cfg.C) ∪ (T ∩ cfg.D) ⊆ T := by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_inter] at hx
          cases hx with
          | inl h => exact h.1
          | inr h => exact h.1
        calc (T ∩ cfg.C).card + (T ∩ cfg.D).card
            = ((T ∩ cfg.C) ∪ (T ∩ cfg.D)).card := by rw [← this]
          _ ≤ T.card := Finset.card_le_card h_sub
      omega
  · -- X = D (similar)
    rcases hYM with rfl | rfl | rfl | rfl
    · have := scattered_external_unique G M hM cfg T hT hT_not_M hTY
      exact this.2.2 hTX
    · -- T shares edge with D and B
      unfold sharesEdge at hTX hTY
      have hT3 : T.card = 3 := by
        unfold triangles at hT
        rw [SimpleGraph.mem_cliqueFinset_iff] at hT
        exact hT.2
      have hBD_disj : cfg.B ∩ cfg.D = ∅ := Finset.disjoint_iff_inter_eq_empty.mp cfg.disjoint_BD
      have h_disj : Disjoint (T ∩ cfg.D) (T ∩ cfg.B) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext x
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
        intro ⟨⟨_, hxD⟩, ⟨_, hxB⟩⟩
        have : x ∈ cfg.B ∩ cfg.D := Finset.mem_inter.mpr ⟨hxB, hxD⟩
        rw [hBD_disj] at this
        exact Finset.notMem_empty x this
      have h_sum : (T ∩ cfg.D).card + (T ∩ cfg.B).card ≤ T.card := by
        have := Finset.card_union_add_card_inter (T ∩ cfg.D) (T ∩ cfg.B)
        rw [Finset.disjoint_iff_inter_eq_empty.mp h_disj] at this
        simp only [Finset.card_empty, add_zero] at this
        have h_sub : (T ∩ cfg.D) ∪ (T ∩ cfg.B) ⊆ T := by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_inter] at hx
          cases hx with
          | inl h => exact h.1
          | inr h => exact h.1
        calc (T ∩ cfg.D).card + (T ∩ cfg.B).card
            = ((T ∩ cfg.D) ∪ (T ∩ cfg.B)).card := by rw [← this]
          _ ≤ T.card := Finset.card_le_card h_sub
      omega
    · -- T shares edge with D and C
      unfold sharesEdge at hTX hTY
      have hT3 : T.card = 3 := by
        unfold triangles at hT
        rw [SimpleGraph.mem_cliqueFinset_iff] at hT
        exact hT.2
      have hCD_disj : cfg.C ∩ cfg.D = ∅ := Finset.disjoint_iff_inter_eq_empty.mp cfg.disjoint_CD
      have h_disj : Disjoint (T ∩ cfg.D) (T ∩ cfg.C) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext x
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
        intro ⟨⟨_, hxD⟩, ⟨_, hxC⟩⟩
        have : x ∈ cfg.C ∩ cfg.D := Finset.mem_inter.mpr ⟨hxC, hxD⟩
        rw [hCD_disj] at this
        exact Finset.notMem_empty x this
      have h_sum : (T ∩ cfg.D).card + (T ∩ cfg.C).card ≤ T.card := by
        have := Finset.card_union_add_card_inter (T ∩ cfg.D) (T ∩ cfg.C)
        rw [Finset.disjoint_iff_inter_eq_empty.mp h_disj] at this
        simp only [Finset.card_empty, add_zero] at this
        have h_sub : (T ∩ cfg.D) ∪ (T ∩ cfg.C) ⊆ T := by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_inter] at hx
          cases hx with
          | inl h => exact h.1
          | inr h => exact h.1
        calc (T ∩ cfg.D).card + (T ∩ cfg.C).card
            = ((T ∩ cfg.D) ∪ (T ∩ cfg.C)).card := by rw [← this]
          _ ≤ T.card := Finset.card_le_card h_sub
      omega
    · exact hXY rfl

/-- MAIN THEOREM: τ ≤ 8 for scattered configuration

Proof: Each M-element is isolated. For each X ∈ {A,B,C,D}:
- Externals of X share an edge with X only (no bridges)
- By slot182, any two externals of X share an edge → they have a common external vertex (fan apex)
- 2 edges from X suffice to cover X and all its externals

Total: 4 × 2 = 8 edges. -/
theorem tau_le_8_scattered
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hν : ∀ P : Finset (Finset V), isPacking G P → P.card ≤ 4)
    (cfg : Scattered G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- Construct 8-edge cover: 2 edges per M-element
  -- For each X ∈ {A,B,C,D}:
  --   Pick one edge e_X of X
  --   Pick one additional edge from X through the fan apex of externals
  -- This covers: X (by e_X) and all externals of X (by fan apex edge or e_X)
  sorry

end TuzaNu4
