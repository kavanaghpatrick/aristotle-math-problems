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

lemma two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  -- Proof by contradiction: if they don't share edge, we get 5-packing
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- All X-externals share a common vertex.

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
theorem all_externals_share_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (h_nonempty : externals.Nonempty) :
    ∃ v, ∀ T ∈ externals, v ∈ T := by
  sorry

/-- Corollary: 2 edges incident to the common vertex cover all X-externals -/
theorem two_edges_cover_all_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, (T = X ∨ isExternalOf G M X T) → T ∈ G.cliqueFinset 3 →
        e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2) := by
  sorry

end
