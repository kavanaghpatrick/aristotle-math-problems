/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7130b121-0fc2-4655-9fad-6fdfc1400bcd
-/

/-
  slot344: EXTERNALS SHARE EDGE (not just apex) in ν=4

  BREAKTHROUGH INSIGHT (Grok verified):

  In a graph with ν = 4, all X-externals must share an EDGE with each other
  (not just a common vertex).

  PROOF BY CONTRADICTION:
  If X-externals T1, T2 share only 1 vertex (the apex), then:
  - T1 ∩ T2 = {apex} = 1 vertex
  - {T1, T2, B, C, D} would be a valid packing of size 5
  - This contradicts ν = 4

  CONSEQUENCE:
  All X-externals share a common edge e with X.
  The apex is one endpoint of e.
  Any apex-based edge selection includes edges incident to apex.
  For bridges: bridge shares edge {v, x} with X where v ∈ X ∩ Y.
  If all externals share edge {apex, w}, then apex ∈ {v, x, third_vertex_of_X}.

  CRITICAL: If apex ∈ {v, x}, then apex-based edges hit the bridge!

  The only remaining case: apex = third_vertex (not on bridge edge).
  But then externals share edge {apex, ?} where ? ∈ {v, x}.
  So apex-based edges include {apex, v} or {apex, x}.
  {apex, v} or {apex, x} might not hit bridge {v, x, y}...

  Wait, we need to be more careful. Let me formalize.
-/

import Mathlib


set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

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

-- ═══════════════════ PROVEN SCAFFOLDING ═══════════════════

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩,
                                   v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

-- ═══════════════════ KEY NEW LEMMA ═══════════════════

/-
PROOF SKETCH for externals_share_edge:

1. Let T1, T2 be X-externals with T1 ∩ T2 = {apex} (1 vertex)
2. Construct packing P = {T1, T2} ∪ (M \ {X})
3. Show P is a valid packing:
   - T1, T2 share only 1 vertex (by assumption)
   - T1, T2 don't share edge with Y ∈ M, Y ≠ X (by external definition)
   - Elements of M \ {X} share at most 1 vertex with each other
4. P has |M| + 1 elements
5. This contradicts ν = 4

Therefore, if ν = 4, any two X-externals share ≥ 2 vertices.
-/
theorem externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T1 T2 : Finset V) (hT1 : isExternalOf G M X T1) (hT2 : isExternalOf G M X T2)
    (hT1_ne_T2 : T1 ≠ T2) :
    2 ≤ (T1 ∩ T2).card := by
  -- Proof by contradiction
  by_contra h_lt_2
  push_neg at h_lt_2
  -- T1 ∩ T2 has at most 1 element
  have h_le_1 : (T1 ∩ T2).card ≤ 1 := Nat.lt_succ_iff.mp h_lt_2

  -- Construct the replacement packing: remove X, add T1 and T2
  let M' := (M.erase X) ∪ {T1, T2}

  -- M' is a valid packing
  have hM'_pack : isTrianglePacking G M' := by
    constructor
    -- All elements are triangles
    · intro t ht
      simp only [mem_union, mem_erase, mem_insert, mem_singleton] at ht
      rcases ht with ⟨_, ht'⟩ | rfl | rfl
      · exact hM.1.1 ht'
      · exact hT1.1
      · exact hT2.1
    -- Pairwise share at most 1 vertex
    · intro a ha b hb hab
      simp only [coe_union, coe_erase, coe_insert, coe_singleton,
                 Set.mem_union, Set.mem_diff, Set.mem_singleton_iff,
                 Set.mem_insert_iff] at ha hb
      rcases ha with ⟨ha1, ha2⟩ | rfl | rfl <;> rcases hb with ⟨hb1, hb2⟩ | rfl | rfl
      -- Both from M \ {X}
      · exact hM.1.2 ha1 hb1 hab
      -- One from M \ {X}, one is T1
      · -- T1 doesn't share edge with Y ∈ M, Y ≠ X
        have hT1_not_a := hT1.2.2.2 a ha1 (Ne.symm ha2)
        exact Nat.lt_one_iff.mp (Nat.not_le.mp (mt (sharesEdgeWith_iff_card_inter_ge_two T1 a).mpr hT1_not_a))
      -- One from M \ {X}, one is T2
      · have hT2_not_a := hT2.2.2.2 a ha1 (Ne.symm ha2)
        exact Nat.lt_one_iff.mp (Nat.not_le.mp (mt (sharesEdgeWith_iff_card_inter_ge_two T2 a).mpr hT2_not_a))
      -- T1 and one from M \ {X}
      · have hT1_not_b := hT1.2.2.2 b hb1 (Ne.symm hb2)
        rw [inter_comm]
        exact Nat.lt_one_iff.mp (Nat.not_le.mp (mt (sharesEdgeWith_iff_card_inter_ge_two T1 b).mpr hT1_not_b))
      -- T1 and T1
      · exact hab.elim rfl
      -- T1 and T2
      · exact h_le_1
      -- T2 and one from M \ {X}
      · have hT2_not_b := hT2.2.2.2 b hb1 (Ne.symm hb2)
        rw [inter_comm]
        exact Nat.lt_one_iff.mp (Nat.not_le.mp (mt (sharesEdgeWith_iff_card_inter_ge_two T2 b).mpr hT2_not_b))
      -- T2 and T1
      · rw [inter_comm]; exact h_le_1
      -- T2 and T2
      · exact hab.elim rfl

  -- M' has more than 4 elements
  have hM'_card : M'.card > 4 := by
    have hT1_notin : T1 ∉ M := hT1.2.1
    have hT2_notin : T2 ∉ M := hT2.2.1
    simp only [card_union_of_disjoint, card_erase_of_mem hX, card_insert_of_not_mem,
               card_singleton, hM_card]
    · omega
    · simp [hT1_ne_T2]
    · simp only [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
      intro x hx
      simp only [mem_inter, mem_erase, mem_insert, mem_singleton] at hx
      rcases hx.2 with rfl | rfl
      · exact hT1_notin hx.1.2
      · exact hT2_notin hx.1.2

  -- Contradiction with ν = 4
  exact Nat.not_lt.mpr (hν M' hM'_pack) hM'_card

-- ═══════════════════ COROLLARY: APEX ON SHARED EDGE ═══════════════════

/-
If all X-externals share an edge, that edge is the "universal shared edge".
The apex (common to all externals) is an endpoint of this edge.
Therefore, apex-based edges include the shared edge.
-/
theorem apex_on_shared_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (apex : V) (hApex_in : apex ∈ X)
    (hApex_universal : ∀ T, isExternalOf G M X T → apex ∈ T)
    (T1 T2 : Finset V) (hT1 : isExternalOf G M X T1) (hT2 : isExternalOf G M X T2)
    (hT1_ne_T2 : T1 ≠ T2) :
    -- The shared edge contains apex
    ∃ v ∈ X, v ≠ apex ∧ v ∈ T1 ∧ v ∈ T2 := by
  -- T1 ∩ T2 has at least 2 elements
  have h_ge_2 := externals_share_edge G M hM hM_card hν X hX T1 T2 hT1 hT2 hT1_ne_T2
  -- T1 and T2 are triangles, so T1 ∩ T2 has at most 2 elements (otherwise equal)
  -- apex is in both T1 and T2
  have hApex_T1 := hApex_universal T1 hT1
  have hApex_T2 := hApex_universal T2 hT2
  -- T1 ∩ T2 contains apex, so there's another element
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.mp h_ge_2
  -- One of v, w is apex, the other is the second vertex
  by_cases hv_apex : v = apex
  · use w
    constructor
    · -- w ∈ X because T2 shares edge with X, and w ∈ T2
      -- T2 ∩ X ≥ 2 (shares edge), apex ∈ T2 ∩ X, w ∈ T2 ∩ X
      have hT2_share := hT2.2.2.1
      have hT2_X_ge_2 := (sharesEdgeWith_iff_card_inter_ge_two T2 X).mp hT2_share
      -- T2 is a triangle with 3 vertices
      have hT2_card := triangle_card_three G T2 hT2.1
      -- T2 ∩ X has exactly 2 vertices (otherwise T2 ⊆ X, but T2 ∉ M and X ∈ M)
      have hT2_X_eq_2 : (T2 ∩ X).card = 2 := by
        have h_le_3 : (T2 ∩ X).card ≤ 3 := by
          calc (T2 ∩ X).card ≤ T2.card := card_le_card inter_subset_left
                           _ = 3

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token ':='; expected command-/
:= hT2_card
        interval_cases (T2 ∩ X).card
        · omega
        · omega
        · -- (T2 ∩ X).card = 2
          rfl
        · -- (T2 ∩ X).card = 3 means T2 ⊆ X
          have h_sub : T2 ⊆ X := by
            intro x hx
            have h_inter : T2 ∩ X = T2 := by
              apply eq_of_subset_of_card_le inter_subset_left
              simp [hT2_card]
            simp only [← h_inter, mem_inter] at hx
            exact hx.2
          -- T2 is a triangle, X is a triangle, T2 ⊆ X with same cardinality → T2 = X
          have hT2_eq_X : T2 = X := by
            apply eq_of_subset_of_card_le h_sub
            simp [hT2_card, hX_card]
          -- But T2 ∉ M and X ∈ M, contradiction
          exact hT2.2.1 (hT2_eq_X ▸ hX)
      -- apex ∈ T2 ∩ X, w ∈ T2 (from T1 ∩ T2)
      -- We need w ∈ X. Since T2 ∩ X has 2 elements and apex ∈ T2 ∩ X...
      -- Actually, w ∈ T1 ∩ T2, so w ∈ T2. We need w ∈ T2 ∩ X.
      -- Hmm, this needs more work. Let me use the fact that T1 ∩ X and T2 ∩ X both = 2
      -- and both contain apex.
      sorry
    constructor
    · subst hv_apex; exact hvw.symm
    constructor
    · exact Finset.mem_of_mem_inter_left hw
    · exact Finset.mem_of_mem_inter_right hw
  · use v
    constructor
    · sorry -- Similar reasoning
    constructor
    · exact hv_apex
    constructor
    · exact Finset.mem_of_mem_inter_left hv
    · exact Finset.mem_of_mem_inter_right hv

end