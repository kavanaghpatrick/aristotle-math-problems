/-
Tuza ν=4 Strategy - Slot 371: Fan Apex Exists for X-Externals

DEPENDS ON: slot370 (triangle_helly_vertex_fin6) - PROVEN

THEOREM: If X ∈ M has ≥3 X-externals, they all share a common vertex (fan apex).

PROOF SKETCH:
1. By two_externals_share_edge (slot182), any two X-externals share an edge
2. Pick any three X-externals: T₁, T₂, T₃
3. They pairwise share edges: |T₁ ∩ T₂| ≥ 2, |T₂ ∩ T₃| ≥ 2, |T₁ ∩ T₃| ≥ 2
4. By triangle_helly_vertex_fin6, ∃v ∈ T₁ ∩ T₂ ∩ T₃
5. For any fourth external T₄:
   - T₄ shares edge with T₁ (by two_externals_share_edge)
   - T₄ shares edge with T₂
   - By Triangle Helly on {T₁, T₂, T₄}, they share a vertex w
   - But T₁ ∩ T₂ = {v, x} for some x (exactly 2 elements since distinct)
   - So w ∈ {v, x}
   - Similarly w must be compatible with T₃, forcing w = v
6. Therefore ALL X-externals contain v (the fan apex)

APPLICATION: This means 2 edges through fan apex cover ALL X-externals.

TIER: 2 (Depends on slot370 + two_externals_share_edge)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (standard from slot182)
-- ══════════════════════════════════════════════════════════════════════════════

def isTriangle (T : Finset V) : Prop := T.card = 3

def sharesEdgeWith (T S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ T ∧ v ∈ T ∧ u ∈ S ∧ v ∈ S

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ T ∉ M ∧ sharesEdgeWith T X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith T Y

-- ══════════════════════════════════════════════════════════════════════════════
-- IMPORTED FROM SLOT370 (proven by Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangle Helly: Three pairwise edge-sharing triangles share a common vertex -/
theorem triangle_helly_vertex (T₁ T₂ T₃ : Finset V)
    (hT₁ : T₁.card = 3) (hT₂ : T₂.card = 3) (hT₃ : T₃.card = 3)
    (h_distinct₁₂ : T₁ ≠ T₂) (h_distinct₂₃ : T₂ ≠ T₃) (h_distinct₁₃ : T₁ ≠ T₃)
    (h12 : (T₁ ∩ T₂).card ≥ 2)
    (h23 : (T₂ ∩ T₃).card ≥ 2)
    (h13 : (T₁ ∩ T₃).card ≥ 2) :
    ∃ v, v ∈ T₁ ∧ v ∈ T₂ ∧ v ∈ T₃ := by
  sorry -- Proven in slot370 via native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- IMPORTED FROM SLOT182 (proven by Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Two distinct X-externals share an edge (5-packing contradiction) -/
theorem two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M X T₁) (hT₂ : isExternalOf G M X T₂)
    (h_ne : T₁ ≠ T₂) :
    sharesEdgeWith T₁ T₂ := by
  sorry -- Proven in slot182

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- sharesEdgeWith implies intersection ≥ 2 -/
lemma sharesEdge_implies_inter_ge_two (T S : Finset V)
    (h : sharesEdgeWith T S) : (T ∩ S).card ≥ 2 := by
  obtain ⟨u, v, huv, hu_T, hv_T, hu_S, hv_S⟩ := h
  have hu : u ∈ T ∩ S := mem_inter.mpr ⟨hu_T, hu_S⟩
  have hv : v ∈ T ∩ S := mem_inter.mpr ⟨hv_T, hv_S⟩
  exact one_lt_card.mpr ⟨u, hu, v, hv, huv⟩

/-- External triangles have card 3 -/
lemma external_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X T : Finset V) (hT : isExternalOf G M X T) :
    T.card = 3 := by
  exact SimpleGraph.mem_cliqueFinset_iff.mp hT.1 |>.2

/-- If all pairs in a finite set share a vertex with a fixed pair, they share a common vertex -/
lemma common_vertex_propagation (T₁ T₂ : Finset V) (externals : Finset (Finset V))
    (hT₁_card : T₁.card = 3) (hT₂_card : T₂.card = 3)
    (h_distinct : T₁ ≠ T₂)
    (h_inter : (T₁ ∩ T₂).card = 2)
    (h_all_share : ∀ T ∈ externals, T.card = 3 ∧ (T₁ ∩ T).card ≥ 2 ∧ (T₂ ∩ T).card ≥ 2) :
    ∃ v ∈ T₁ ∩ T₂, ∀ T ∈ externals, v ∈ T := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Fan Apex Exists
-- ══════════════════════════════════════════════════════════════════════════════

/-- If X has ≥3 X-externals, they all share a common vertex (fan apex).

PROOF SKETCH:
1. Take any three externals T₁, T₂, T₃
2. By two_externals_share_edge, each pair shares an edge
3. By triangle_helly_vertex, they share a common vertex v
4. For any other external T, it shares edges with T₁ and T₂
5. Triangle Helly on {T₁, T₂, T} gives common vertex in T₁ ∩ T₂
6. Since T₁ ∩ T₂ has exactly 2 elements including v, and v works for T₃,
   the common vertex must be v
7. Therefore v ∈ T for all externals T
-/
theorem fan_apex_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (h_card : externals.card ≥ 3) :
    ∃ v, ∀ T ∈ externals, v ∈ T := by
  sorry

/-- Corollary: Fan apex is in X (the M-element) -/
theorem fan_apex_in_X (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3)
    (externals : Finset (Finset V))
    (h_ext : ∀ T ∈ externals, isExternalOf G M X T)
    (h_nonempty : externals.Nonempty) :
    ∃ v ∈ X, ∀ T ∈ externals, v ∈ T := by
  -- Fan apex must be in X because externals share edge with X
  sorry

end
