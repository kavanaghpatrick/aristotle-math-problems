/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1658ed6d-db63-42b1-9118-2911c7a06975

The following was proved by Aristotle:

- lemma two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂

- theorem all_externals_share_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (h_nonempty : externals.Nonempty) :
    ∃ v, ∀ T ∈ externals, v ∈ T

- theorem two_edges_cover_all_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2)
-/

/-
  slot306: All X-Externals Share a Common Vertex

  GOAL: Prove that all externals of X share a COMMON vertex.

  CONTEXT:
  - slot301/303 prove: Any TWO X-externals share a vertex IN X
  - But Gemini/Grok identified: pairwise ≠ common (Hajós/cyclic case)

  KEY INSIGHT (from Grok): In the cyclic case, externals share a common
  OUTSIDE vertex v! So there's always a common vertex, just not always in X.

  PROOF STRATEGY:
  1. Any two X-externals T₁, T₂ share an edge (by 5-packing)
  2. Case A: There exists vertex x ∈ X in all externals → done
  3. Case B: No such x exists (cyclic case)
     - Then externals must share a common OUTSIDE vertex v
     - Because: each T_i has exactly 1 vertex outside X
     - If T₁, T₂ have different outside vertices, their shared edge
       would be entirely in X, forcing a common X-vertex
     - So all cyclic externals share the same outside vertex v

  IMPLICATION FOR τ ≤ 8:
  - If common vertex is in X: 2 edges inside X cover all
  - If common vertex is outside X: 2 edges to that vertex cover all
  - Either way, 2 edges per element suffice!
-/

import Mathlib


set_option maxHeartbeats 400000

set_option linter.mathlibStandardSet false

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

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_has_one_outside (t X : Finset V) (ht : t.card = 3) (hX : X.card = 3)
    (h_share : sharesEdgeWith t X) (h_ne : t ≠ X) :
    (t \ X).card = 1 := by
  have h_inter : (t ∩ X).card = 2 := by
    have h_ge : (t ∩ X).card ≥ 2 := by
      obtain ⟨u, v, huv, hu_t, hv_t, hu_X, hv_X⟩ := h_share
      exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu_t, hu_X⟩,
                                     v, Finset.mem_inter.mpr ⟨hv_t, hv_X⟩, huv⟩
    have h_le : (t ∩ X).card ≤ 2 := by
      by_contra h_gt
      push_neg at h_gt
      have h_sub : t ⊆ X := by
        have h_inter_sub : t ∩ X ⊆ t := Finset.inter_subset_left
        have h_card_eq : (t ∩ X).card = t.card := by
          have h1 : (t ∩ X).card ≤ t.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.2
      have h_sub' : X ⊆ t := by
        have h_inter_sub : t ∩ X ⊆ X := Finset.inter_subset_right
        have h_card_eq : (t ∩ X).card = X.card := by
          have h1 : (t ∩ X).card ≤ X.card := Finset.card_le_card h_inter_sub
          linarith
        intro x hx
        have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
        rw [← h_eq] at hx
        exact Finset.mem_inter.mp hx |>.1
      exact h_ne (Finset.Subset.antisymm h_sub h_sub')
    linarith
  have := Finset.card_sdiff_add_card_inter t X
  omega

noncomputable section AristotleLemmas

/-
Two finsets share an edge if and only if their intersection has size at least 2.
-/
lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
      constructor <;> intro h;
      · obtain ⟨ u, v, huv, hu, hv, hu', hv' ⟩ := h;
        exact Finset.one_lt_card.2 ⟨ u, by aesop, v, by aesop ⟩;
      · obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.mp h;
        exact ⟨ u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv, Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv ⟩

end AristotleLemmas

lemma two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  -- Proof by contradiction: if they don't share edge, we get 5-packing
  contrapose! hν;
  refine' ⟨ Insert.insert T₁ ( Insert.insert T₂ ( M.erase X ) ), _, _ ⟩ <;> simp_all +decide [ isTrianglePacking ];
  · simp_all +decide [ Finset.subset_iff, isExternalOf ];
    simp_all +decide [ Set.Pairwise, Finset.disjoint_left ];
    refine' ⟨ _, _, _, _ ⟩;
    · exact fun Y hy₁ hy₂ => hM.1.1 hy₂ |> fun h => by simpa using h;
    · refine' ⟨ _, _ ⟩;
      · exact le_of_not_gt fun h => hν <| by rw [ sharesEdgeWith_iff_card_inter_ge_two ] ; exact h;
      · exact fun Y hy hyX hyT₁ => not_lt.1 fun contra => hT₁.2.2.2 Y hy hyX <| by rw [ sharesEdgeWith_iff_card_inter_ge_two ] ; exact contra;
    · simp_all +decide [ Finset.inter_comm, sharesEdgeWith_iff_card_inter_ge_two ];
      exact ⟨ fun _ => Nat.le_of_lt_succ hν, fun Y hy hy' hy'' => Nat.le_of_lt_succ ( hT₂.2.2.2 Y hy hy' ) ⟩;
    · intro Y hY hYX;
      refine' ⟨ _, _, _ ⟩;
      · intro hYT₁; specialize hT₁; have := hT₁.2.2.2 Y hY hYX; simp_all +decide [ sharesEdgeWith_iff_card_inter_ge_two ] ;
        exact Nat.le_of_lt_succ ( by rw [ Finset.inter_comm ] ; exact hT₁.2.2.2 Y hY hYX );
      · intro hY_ne_T₂; specialize hT₂; have := hT₂.2.2.2 Y hY hYX; simp_all +decide [ sharesEdgeWith_iff_card_inter_ge_two ] ;
        rw [ Finset.inter_comm ] ; linarith [ hT₂.2.2.2 Y hY hYX ];
      · intro Z hZ hZX hZY; have := hM.1.2; simp_all +decide [ Set.Pairwise ] ;
  · unfold isExternalOf at *; aesop;

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/- All X-externals share a common vertex.

PROOF SKETCH (from Grok analysis):
- Case 1: Some vertex x ∈ X is in all externals → done with x
- Case 2: No vertex in X is in all externals (cyclic case)
  - Then for any two externals T₁, T₂, their shared edge contains
    exactly one vertex from X (and one from outside X)
  - The outside vertex must be the SAME for all externals
  - Because: if T₁, T₂ have different outside vertices v₁ ≠ v₂,
    their shared edge would be entirely in X (since |T_i \ X| = 1)
    but they don't share a common X-vertex, contradiction
  - So all externals share the same outside vertex v
-/
noncomputable section AristotleLemmas

/-
The intersection of an external triangle T with the central triangle X has size 2.
-/
lemma external_inter_X_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX_in_M : X ∈ M) (hX_card : X.card = 3)
    (T : Finset V) (hT : isExternalOf G M X T) :
    (T ∩ X).card = 2 := by
      obtain ⟨ hT₁, hT₂, hT₃, hT₄ ⟩ := hT;
      have h_inter_card : (T \ X).card = 1 := by
        have h_inter_card : T.card = 3 ∧ X.card = 3 := by
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact hT₁.card_eq;
        exact external_has_one_outside T X h_inter_card.1 h_inter_card.2 hT₃ ( by aesop );
      have h_inter_card : (T ∩ X).card = T.card - (T \ X).card := by
        grind;
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      exact hT₁.card_eq

/-
If two external triangles have different "outside" vertices, they must share the same edge within the central triangle X.
-/
lemma externals_disjoint_outside_implies_same_edge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_diff : T₁ \ X ≠ T₂ \ X) :
    T₁ ∩ X = T₂ ∩ X := by
      -- Since T₁ and T₂ are both external triangles of X, they share exactly two vertices with X. Therefore, T₁ ∩ X and T₂ ∩ X are both subsets of X with cardinality 2.
      have h_inter_card : (T₁ ∩ X).card = 2 ∧ (T₂ ∩ X).card = 2 := by
        exact ⟨ external_inter_X_card G M X hX hX_3 T₁ hT₁, external_inter_X_card G M X hX hX_3 T₂ hT₂ ⟩;
      -- Since T₁ and T₂ are maximal, they must share exactly one edge with X. Therefore, T₁ ∩ X and T₂ ∩ X must be equal.
      have h_edge : (T₁ ∩ T₂ ∩ X).card = 2 := by
        have h_edge : (T₁ ∩ T₂).card ≥ 2 := by
          have h_inter_eq : sharesEdgeWith T₁ T₂ := by
            exact two_externals_share_edge G M hM hM_card hν X hX T₁ T₂ hT₁ hT₂ ( by aesop_cat );
          obtain ⟨ u, v, huv, hu, hv, hu', hv' ⟩ := h_inter_eq; exact Finset.one_lt_card.2 ⟨ u, by aesop, v, by aesop ⟩ ;
        refine' le_antisymm _ _;
        · exact le_trans ( Finset.card_le_card fun x hx => by aesop ) h_inter_card.1.le;
        · have h_edge : (T₁ \ X) ∩ (T₂ \ X) = ∅ := by
            have h_edge : (T₁ \ X).card = 1 ∧ (T₂ \ X).card = 1 := by
              have := hT₁.1;
              have := hT₂.1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
              have := Finset.card_sdiff_add_card_inter T₁ X; have := Finset.card_sdiff_add_card_inter T₂ X; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp h_edge.1; obtain ⟨ y, hy ⟩ := Finset.card_eq_one.mp h_edge.2; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
            grind;
          have h_edge : (T₁ ∩ T₂) = (T₁ ∩ T₂ ∩ X) ∪ ((T₁ \ X) ∩ (T₂ \ X)) := by
            grind;
          grind;
      have h_eq : T₁ ∩ X ⊇ T₁ ∩ T₂ ∩ X ∧ T₂ ∩ X ⊇ T₁ ∩ T₂ ∩ X := by
        grind;
      have := Finset.eq_of_subset_of_card_le h_eq.1; have := Finset.eq_of_subset_of_card_le h_eq.2; aesop;

/-
If there exist two external triangles with different outside vertices, then all external triangles share the same edge in X.
-/
lemma externals_all_same_edge_of_exists_diff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (T₁ T₂ : Finset V) (hT₁ : T₁ ∈ externals) (hT₂ : T₂ ∈ externals)
    (h_diff : T₁ \ X ≠ T₂ \ X) :
    ∀ T ∈ externals, T ∩ X = T₁ ∩ X := by
      intro T hT;
      by_cases h_cases : T \ X = T₁ \ X;
      · have h_case2 : T ∩ X = T₂ ∩ X := by
          apply externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T T₂ (h_ext T hT) (h_ext T₂ hT₂);
          aesop;
        have := externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T₁ T₂ ( h_ext T₁ hT₁ ) ( h_ext T₂ hT₂ ) h_diff; aesop;
      · apply externals_disjoint_outside_implies_same_edge G M hM hM_card hν X hX hX_3 T T₁ (h_ext T hT) (h_ext T₁ hT₁) h_cases

end AristotleLemmas

theorem all_externals_share_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (h_nonempty : externals.Nonempty) :
    ∃ v, ∀ T ∈ externals, v ∈ T := by
  -- Consider two cases: all externals share the same outside vertex, or not.
  by_cases h_all_same_outside : ∀ T1 ∈ externals, ∀ T2 ∈ externals, T1 \ X = T2 \ X;
  · obtain ⟨T₀, hT₀⟩ : ∃ T₀ ∈ externals, True := by
      exact ⟨ h_nonempty.choose, h_nonempty.choose_spec, trivial ⟩;
    -- Since T₀ \ X is a singleton set, let's denote its element by v.
    obtain ⟨v, hv⟩ : ∃ v, T₀ \ X = {v} := by
      have hT₀_card : (T₀ \ X).card = 1 := by
        have hT₀_card : T₀.card = 3 := by
          have := h_ext T₀ hT₀.1;
          exact this.1 |> fun h => by simpa using Finset.mem_coe.mp h |> fun h => by simpa using Finset.mem_filter.mp h |>.2.2;
        have hT₀_X_card : (T₀ ∩ X).card = 2 := by
          apply external_inter_X_card G M X hX hX_3 T₀ (h_ext T₀ hT₀.left);
        grind;
      exact Finset.card_eq_one.mp hT₀_card;
    use v;
    intro T hT; specialize h_all_same_outside T hT T₀ hT₀.1; rw [ Finset.ext_iff ] at h_all_same_outside; specialize h_all_same_outside v; aesop;
  · -- By Lemma 2, there is a fixed set S = T1 ∩ X such that ∀ T ∈ externals, T ∩ X = S.
    obtain ⟨S, hS⟩ : ∃ S : Finset V, ∀ T ∈ externals, T ∩ X = S := by
      obtain ⟨T1, hT1, T2, hT2, h_diff⟩ : ∃ T1 ∈ externals, ∃ T2 ∈ externals, T1 \ X ≠ T2 \ X := by
        exact by push_neg at h_all_same_outside; exact h_all_same_outside;
      exact ⟨ T1 ∩ X, fun T hT => by have := externals_all_same_edge_of_exists_diff G M hM hM_card hν X hX hX_3 externals h_ext T1 T2 hT1 hT2 h_diff; aesop ⟩;
    -- By Lemma 1, S has cardinality 2, so it is nonempty. Pick u ∈ S.
    obtain ⟨u, hu⟩ : ∃ u, u ∈ S := by
      have := h_ext _ h_nonempty.choose_spec;
      exact hS _ h_nonempty.choose_spec ▸ ( external_inter_X_card G M X hX hX_3 _ this ) |> fun h => Finset.card_pos.mp ( by linarith );
    exact ⟨ u, fun T hT => Finset.mem_of_mem_inter_left ( hS T hT ▸ hu ) ⟩

/- Corollary: 2 edges incident to the common vertex cover all X-externals -/
noncomputable section AristotleLemmas

/-
If a vertex v in X is common to all X-externals, then the two edges of X incident to v cover X and all externals.
-/
lemma cover_externals_case_inside (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (v : V) (hv : v ∈ X)
    (h_common : ∀ T, isExternalOf G M X T → v ∈ T) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
          -- Let `u` and `w` be the other two vertices in `X`.
          obtain ⟨u, w, hu, hw, hx⟩ : ∃ u w : V, u ≠ w ∧ u ∈ X ∧ w ∈ X ∧ u ≠ v ∧ w ≠ v ∧ X = {v, u, w} := by
            rw [ Finset.card_eq_three ] at hX_3;
            rcases hX_3 with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; by_cases hvx : v = x <;> by_cases hvy : v = y <;> by_cases hvz : v = z <;> simp_all +decide ;
            · exact ⟨ y, z, by tauto, by tauto, by tauto, by tauto, by tauto, by aesop ⟩;
            · exact ⟨ x, z, by tauto, by tauto, by tauto, by tauto, by tauto, by aesop ⟩;
            · exact ⟨ x, y, hxy, by tauto, by tauto, by tauto, by tauto, by aesop ⟩;
          refine' ⟨ Sym2.mk ( v, u ), Sym2.mk ( v, w ), _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.mem_edgeFinset ];
          · have := hX_clique.1; aesop;
          · have := hX_clique.1; aesop;
          · intro T hT hT';
            have := hT.2.2.1; unfold sharesEdgeWith at this; aesop;

/-
If a vertex v outside X is common to all X-externals, then there exist 2 edges covering X and all externals.
-/
lemma cover_externals_case_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (X : Finset V) (hX_clique : X ∈ G.cliqueFinset 3) (hX_3 : X.card = 3)
    (v : V) (hv : v ∉ X)
    (h_common : ∀ T, isExternalOf G M X T → v ∈ T) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
          -- Let $X = \{a, b, c\}$.
          obtain ⟨a, b, c, hac⟩ : ∃ a b c : V, X = {a, b, c} ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
            rw [ Finset.card_eq_three ] at hX_3; tauto;
          -- Since $v$ is common to all externals, each external $T$ must be of the form $\{v, x, y\}$ where $\{x, y\} \subseteq X$.
          have h_ext_form : ∀ T, isExternalOf G M X T → ∃ x y : V, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ T = {v, x, y} := by
            intro T hT
            obtain ⟨hT_clique, hT_not_in_M, hT_sharesEdge, hT_no_sharesEdge⟩ := hT
            have hT_card : T.card = 3 := by
              exact Finset.mem_filter.mp hT_clique |>.2.2
            have hT_inter_X : (T ∩ X).card = 2 := by
              have := external_has_one_outside T X hT_card hX_3 hT_sharesEdge (by
              exact fun h => hv ( h ▸ h_common T ⟨ hT_clique, hT_not_in_M, hT_sharesEdge, hT_no_sharesEdge ⟩ ));
              grind
            have hT_form : ∃ x y : V, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ T = {v, x, y} := by
              obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : V, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ x ∈ T ∧ y ∈ T ∧ v ∈ T := by
                obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.1 ( by linarith : 1 < Finset.card ( T ∩ X ) ) ; use x, y; simp_all +decide [ Finset.inter_comm ] ;
                unfold isExternalOf at *; aesop;
              use x, y;
              rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ hxy.2.2.2, Finset.insert_subset_iff.mpr ⟨ hxy.2.1, Finset.singleton_subset_iff.mpr hxy.2.2.1 ⟩ ⟩ ) ] ; aesop;
              grind
            exact hT_form;
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          by_cases h₁ : G.Adj v c;
          · refine' ⟨ Sym2.mk ( a, b ), _, Sym2.mk ( v, c ), _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
            intro T hT₁ hT₂ hT₃; specialize h_ext_form T hT₁; aesop;
          · use Sym2.mk ( a, b ), ?_, Sym2.mk ( a, c ), ?_ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
            intro T hT hT' hT''; specialize h_ext_form T hT; aesop;

end AristotleLemmas

theorem two_edges_cover_all_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  -- If `E` is empty, then the only triangle to cover is `X`. Since `X` is a triangle, any two edges of `X` cover `X`.
  by_cases hE_empty : ¬∃ T, isExternalOf G M X T;
  · rcases Finset.card_eq_three.mp hX_3 with ⟨ a, b, c, hab, hbc, hac ⟩ ; simp_all +decide [ SimpleGraph.isClique_iff, SimpleGraph.adj_comm ];
    rcases hM with ⟨ hM₁, hM₂ ⟩;
    have := hM₁.1 hX; simp_all +decide [ SimpleGraph.isNClique_iff, Finset.card_eq_three ] ;
    exact ⟨ Sym2.mk ( a, b ), by simp +decide [ this ], Sym2.mk ( b, c ), by simp +decide [ this ], by simp +decide [ this ] ⟩;
  · obtain ⟨T₀, hT₀⟩ : ∃ T₀, isExternalOf G M X T₀ := by
      exact not_not.mp hE_empty;
    -- Apply `all_externals_share_common_vertex` to `E` to find a vertex `v` such that `∀ T ∈ E, v ∈ T`.
    obtain ⟨v, hv⟩ : ∃ v, ∀ T, isExternalOf G M X T → v ∈ T := by
      have := all_externals_share_common_vertex G M hM hM_card hν X hX hX_3 ( Finset.univ.filter fun T => isExternalOf G M X T ) ( by aesop ) ( ⟨ T₀, by aesop ⟩ ) ; aesop;
    by_cases hvX : v ∈ X;
    · -- Apply `cover_externals_case_inside` with `v`.
      apply cover_externals_case_inside G M X (by
      have := hM.1.1 hX; aesop;) (by
      exact hX_3) v hvX (by
      exact hv);
    · apply cover_externals_case_outside G M X (by
      have := hM.1.1 hX; aesop;) (by
      exact hX_3) v hvX hv

end