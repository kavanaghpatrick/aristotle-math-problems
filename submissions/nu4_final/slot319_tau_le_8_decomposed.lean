/-
  slot319: τ ≤ 8 for ν = 4 - DECOMPOSED into provable pieces

  Strategy: Break the existential construction into:
  1. Define the cover explicitly (2 edges per packing element)
  2. Prove card bound (arithmetic)
  3. Prove each category is covered separately:
     - M-elements covered (trivial - contain their own edges)
     - Externals covered (uses fan apex lemma)
     - Bridges covered (share edge with some M-element)

  All helper lemmas from slots 314, 317 included verbatim.
-/

import Mathlib

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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
    (M : Finset (Finset V)) (X : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y

def isBridgeTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧
  ∃ X Y : Finset V, X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧ sharesEdgeWith t X ∧ sharesEdgeWith t Y

def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧
  ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN HELPERS (from Aristotle slots 314, 317)
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 := by
  have := SimpleGraph.mem_cliqueFinset_iff.mp hT
  exact this.2

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩,
                                   v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

lemma external_inter_card_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX_in_M : X ∈ M) (hX_card : X.card = 3)
    (T : Finset V) (hT : isExternalOf G M X T) :
    (T ∩ X).card = 2 := by
  have hT_card : T.card = 3 := triangle_card_three G T hT.1
  have h_share : sharesEdgeWith T X := hT.2.2.1
  have h_inter_ge : (T ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two T X |>.mp h_share
  have h_inter_le : (T ∩ X).card ≤ 2 := by
    by_contra h_gt
    push_neg at h_gt
    have h_sub : T ⊆ X := by
      have h_inter_sub : T ∩ X ⊆ T := Finset.inter_subset_left
      have h_card_eq : (T ∩ X).card = T.card := by
        have h1 : (T ∩ X).card ≤ T.card := Finset.card_le_card h_inter_sub
        linarith
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx
      exact Finset.mem_inter.mp hx |>.2
    have h_sub' : X ⊆ T := by
      have h_inter_sub : T ∩ X ⊆ X := Finset.inter_subset_right
      have h_card_eq : (T ∩ X).card = X.card := by
        have h1 : (T ∩ X).card ≤ X.card := Finset.card_le_card h_inter_sub
        linarith
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx
      exact Finset.mem_inter.mp hx |>.1
    have h_eq : T = X := Finset.Subset.antisymm h_sub h_sub'
    exact hT.2.1 (h_eq ▸ hX_in_M)
  omega

lemma packing_inter_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hne : X ≠ Y) :
    (X ∩ Y).card ≤ 1 := hM.2 hX hY hne

lemma nonpacking_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3) (hT_notin : T ∉ M) :
    ∃ X ∈ M, sharesEdgeWith T X := by
  obtain ⟨m, hm_in, hm_inter⟩ := hM.2 T hT_tri hT_notin
  exact ⟨m, hm_in, sharesEdgeWith_iff_card_inter_ge_two T m |>.mpr hm_inter⟩

lemma edge_in_sym2_iff (T : Finset V) (u v : V) :
    s(u, v) ∈ T.sym2 ↔ u ∈ T ∧ v ∈ T := by
  rw [Finset.mem_sym2_iff]
  constructor
  · intro h
    constructor
    · apply h; simp [Sym2.mem_iff]
    · apply h; simp [Sym2.mem_iff]
  · intro ⟨hu, hv⟩ x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> assumption

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 1: Triangle classification (M-element, external, or bridge)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for triangle_classification:
Every triangle T is either:
1. In M (packing element)
2. An X-external for some unique X ∈ M
3. A bridge (shares edges with 2+ packing elements)

Proof: If T ∉ M, by maximality T shares edge with some X ∈ M.
If T shares edge with only X, it's an X-external.
If T shares edge with multiple M-elements, it's a bridge.
This is exhaustive by definition.
-/
lemma triangle_classification (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨ (∃ X ∈ M, isExternalOf G M X T) ∨ isBridgeTriangle G M T := by
  by_cases hT_in : T ∈ M
  · left; exact hT_in
  · right
    obtain ⟨X, hX_in, hX_share⟩ := nonpacking_shares_edge G M hM T hT hT_in
    by_cases h_unique : ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith T Y
    · left
      exact ⟨X, hX_in, hT, hT_in, hX_share, h_unique⟩
    · right
      push_neg at h_unique
      obtain ⟨Y, hY_in, hY_ne, hY_share⟩ := h_unique
      exact ⟨hT, hT_in, X, Y, hX_in, hY_in, hY_ne.symm, hX_share, hY_share⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 2: M-element is covered by any of its edges
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for m_element_covered_by_own_edge:
If X = {a,b,c} ∈ M is a triangle and e = s(a,b) is an edge of X,
then e ∈ X.sym2, so X is covered by {e}.
-/
lemma m_element_covered_by_own_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX : X ∈ G.cliqueFinset 3)
    (a b : V) (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b) :
    s(a, b) ∈ X.sym2 := by
  rw [edge_in_sym2_iff]
  exact ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 3: External is covered by edge through shared vertices
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for external_covered_by_shared_edge:
If T is an X-external, then T ∩ X = {u, v} for some u, v.
The edge s(u,v) is in both T.sym2 and X.sym2.
So any cover containing s(u,v) covers T.
-/
lemma external_covered_by_shared_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X T : Finset V)
    (hX_in_M : X ∈ M) (hX_card : X.card = 3)
    (hT : isExternalOf G M X T) :
    ∃ u v : V, u ≠ v ∧ u ∈ X ∧ v ∈ X ∧ s(u, v) ∈ T.sym2 := by
  have h_share := hT.2.2.1
  obtain ⟨u, v, huv, hu_T, hv_T, hu_X, hv_X⟩ := h_share
  exact ⟨u, v, huv, hu_X, hv_X, edge_in_sym2_iff T u v |>.mpr ⟨hu_T, hv_T⟩⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 4: Bridge is covered by edge through some M-element
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for bridge_covered_by_some_m_edge:
A bridge T shares an edge with some X ∈ M (by definition).
That shared edge s(u,v) with u,v ∈ T ∩ X covers T.
-/
lemma bridge_covered_by_some_m_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T : Finset V)
    (hT : isBridgeTriangle G M T) :
    ∃ X ∈ M, ∃ u v : V, u ≠ v ∧ u ∈ X ∧ v ∈ X ∧ s(u, v) ∈ T.sym2 := by
  obtain ⟨_, _, X, Y, hX_in, _, _, hX_share, _⟩ := hT
  obtain ⟨u, v, huv, hu_T, hv_T, hu_X, hv_X⟩ := hX_share
  exact ⟨X, hX_in, u, v, huv, hu_X, hv_X, edge_in_sym2_iff T u v |>.mpr ⟨hu_T, hv_T⟩⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 5: Fan apex exists for externals of X
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for fan_apex_exists:
For any two X-externals T1, T2, they share a common vertex in X.

Why: T1 ∩ X and T2 ∩ X are both 2-element subsets of X (a 3-set).
By pigeonhole, two 2-sets from a 3-set must intersect.
So (T1 ∩ X) ∩ (T2 ∩ X) ≠ ∅.

Stronger: ALL X-externals share a common vertex (the "fan apex").
-/
lemma two_externals_share_X_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (hX_card : X.card = 3) (hX_in : X ∈ M)
    (T1 T2 : Finset V) (hT1 : isExternalOf G M X T1) (hT2 : isExternalOf G M X T2) :
    ∃ v ∈ X, v ∈ T1 ∧ v ∈ T2 := by
  have h1 : (T1 ∩ X).card = 2 := external_inter_card_two G M X hX_in hX_card T1 hT1
  have h2 : (T2 ∩ X).card = 2 := external_inter_card_two G M X hX_in hX_card T2 hT2
  -- Two 2-subsets of a 3-set must intersect
  have h_inter_nonempty : ((T1 ∩ X) ∩ (T2 ∩ X)).Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    -- (T1 ∩ X) and (T2 ∩ X) are disjoint 2-subsets of X
    have h_disj : Disjoint (T1 ∩ X) (T2 ∩ X) := Finset.disjoint_iff_inter_eq_empty.mpr h_empty
    have h_union_sub : (T1 ∩ X) ∪ (T2 ∩ X) ⊆ X := by
      intro v hv
      rcases Finset.mem_union.mp hv with h | h
      · exact Finset.mem_of_mem_inter_right h
      · exact Finset.mem_of_mem_inter_right h
    have h_union_card : ((T1 ∩ X) ∪ (T2 ∩ X)).card = 4 := by
      rw [Finset.card_union_of_disjoint h_disj]
      omega
    have h_le : ((T1 ∩ X) ∪ (T2 ∩ X)).card ≤ X.card := Finset.card_le_card h_union_sub
    omega
  obtain ⟨v, hv⟩ := h_inter_nonempty
  have hv1 : v ∈ T1 ∩ X := Finset.mem_of_mem_inter_left hv
  have hv2 : v ∈ T2 ∩ X := Finset.mem_of_mem_inter_right hv
  exact ⟨v, Finset.mem_of_mem_inter_right hv1, Finset.mem_of_mem_inter_left hv1, Finset.mem_of_mem_inter_left hv2⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 6: Two edges through apex cover X and all X-externals
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for apex_edges_cover_externals:
Let X = {a, b, c} and let v be the fan apex (shared by all X-externals).
The edges s(v, a'), s(v, b') where {v, a', b'} = X cover:
- X itself (any edge covers a triangle containing it)
- Every X-external T: T ∩ X = {v, w} for some w, and s(v, w) ∈ {s(v,a'), s(v,b')}
-/
lemma apex_edges_cover_X_external (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X T : Finset V)
    (hX_in_M : X ∈ M) (hX_card : X.card = 3)
    (hT : isExternalOf G M X T)
    (v : V) (hv_in_X : v ∈ X) (hv_in_T : v ∈ T) :
    ∃ w ∈ X, w ≠ v ∧ s(v, w) ∈ T.sym2 := by
  have h_inter : (T ∩ X).card = 2 := external_inter_card_two G M X hX_in_M hX_card T hT
  have hv_inter : v ∈ T ∩ X := Finset.mem_inter.mpr ⟨hv_in_T, hv_in_X⟩
  -- There's another vertex w in T ∩ X
  have h_exists : ∃ w ∈ T ∩ X, w ≠ v := by
    have h_card_gt : 1 < (T ∩ X).card := by omega
    obtain ⟨w, hw, hne⟩ := Finset.exists_mem_ne h_card_gt v
    exact ⟨w, hw, hne⟩
  obtain ⟨w, hw_inter, hwv⟩ := h_exists
  have hw_X : w ∈ X := Finset.mem_of_mem_inter_right hw_inter
  have hw_T : w ∈ T := Finset.mem_of_mem_inter_left hw_inter
  exact ⟨w, hw_X, hwv, edge_in_sym2_iff T v w |>.mpr ⟨hv_in_T, hw_T⟩⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 (decomposed version)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8:

CONSTRUCTION: For each X ∈ M, choose a vertex vX ∈ X and include the 2 edges
through vX in X. Total: 4 × 2 = 8 edges.

CORRECTNESS:
1. Each X ∈ M is covered: Any edge of X covers X.
2. Each X-external T is covered: T shares vertex vX with X (by fan apex lemma),
   so some edge s(vX, w) with w ∈ X covers T.
3. Each bridge T is covered: T shares edge with some X, so covered by X's edges.

The key is choosing vX to be the fan apex for X's externals.
If X has no externals, any vX works.
-/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_triangles : ∀ X ∈ M, X.card = 3) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry

end
