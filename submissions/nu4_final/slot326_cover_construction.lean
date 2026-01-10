/-
  slot326: Prove two_edges_cover_X_and_externals (SINGLE TARGET)

  Given universal_apex_exists (assumed proven), construct the 2-edge cover.

  All 14 proven helpers + universal_apex_exists scaffolding included.
-/

import Mathlib

set_option maxHeartbeats 800000
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
-- PROVEN HELPERS (slot319/321 - Aristotle verified)
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

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
    by_contra h_gt; push_neg at h_gt
    have h_sub : T ⊆ X := by
      have h_inter_sub : T ∩ X ⊆ T := Finset.inter_subset_left
      have h_card_eq : (T ∩ X).card = T.card := by linarith [Finset.card_le_card h_inter_sub]
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx; exact (Finset.mem_inter.mp hx).2
    have h_sub' : X ⊆ T := by
      have h_inter_sub : T ∩ X ⊆ X := Finset.inter_subset_right
      have h_card_eq : (T ∩ X).card = X.card := by linarith [Finset.card_le_card h_inter_sub]
      intro x hx
      have h_eq := Finset.eq_of_subset_of_card_le h_inter_sub (le_of_eq h_card_eq.symm)
      rw [← h_eq] at hx; exact (Finset.mem_inter.mp hx).1
    exact hT.2.1 (Finset.Subset.antisymm h_sub h_sub' ▸ hX_in_M)
  omega

lemma edge_in_sym2_iff (T : Finset V) (u v : V) :
    s(u, v) ∈ T.sym2 ↔ u ∈ T ∧ v ∈ T := by
  rw [Finset.mem_sym2_iff]
  constructor
  · intro h
    exact ⟨h u (Sym2.mem_iff.mpr (Or.inl rfl)), h v (Sym2.mem_iff.mpr (Or.inr rfl))⟩
  · intro ⟨hu, hv⟩ x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> assumption

lemma nonpacking_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT_tri : T ∈ G.cliqueFinset 3) (hT_notin : T ∉ M) :
    ∃ X ∈ M, sharesEdgeWith T X := by
  obtain ⟨m, hm_in, hm_inter⟩ := hM.2 T hT_tri hT_notin
  exact ⟨m, hm_in, sharesEdgeWith_iff_card_inter_ge_two T m |>.mpr hm_inter⟩

lemma triangle_classification (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨ (∃ X ∈ M, isExternalOf G M X T) ∨ isBridgeTriangle G M T := by
  by_cases hT_in : T ∈ M
  · left; exact hT_in
  · right
    obtain ⟨X, hX_in, hX_share⟩ := nonpacking_shares_edge G M hM T hT hT_in
    by_cases h_unique : ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith T Y
    · left; exact ⟨X, hX_in, hT, hT_in, hX_share, h_unique⟩
    · right; push_neg at h_unique
      obtain ⟨Y, hY_in, hY_ne, hY_share⟩ := h_unique
      exact ⟨hT, hT_in, X, Y, hX_in, hY_in, hY_ne.symm, hX_share, hY_share⟩

lemma bridge_covered_by_some_m_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T : Finset V) (hT : isBridgeTriangle G M T) :
    ∃ X ∈ M, ∃ u v : V, u ≠ v ∧ u ∈ X ∧ v ∈ X ∧ s(u, v) ∈ T.sym2 := by
  obtain ⟨_, _, X, _, hX_in, _, _, hX_share, _⟩ := hT
  obtain ⟨u, v, huv, hu_T, hv_T, hu_X, hv_X⟩ := hX_share
  exact ⟨X, hX_in, u, v, huv, hu_X, hv_X, edge_in_sym2_iff T u v |>.mpr ⟨hu_T, hv_T⟩⟩

-- Apex edges cover external (proven by slot319)
lemma apex_edges_cover_X_external (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X T : Finset V)
    (hX_in_M : X ∈ M) (hX_card : X.card = 3)
    (hT : isExternalOf G M X T)
    (v : V) (hv_in_X : v ∈ X) (hv_in_T : v ∈ T) :
    ∃ w ∈ X, w ≠ v ∧ s(v, w) ∈ T.sym2 := by
  have h_inter : (T ∩ X).card = 2 := external_inter_card_two G M X hX_in_M hX_card T hT
  have hv_inter : v ∈ T ∩ X := Finset.mem_inter.mpr ⟨hv_in_T, hv_in_X⟩
  have h_exists : ∃ w ∈ T ∩ X, w ≠ v := by
    have h_card_gt : 1 < (T ∩ X).card := by omega
    obtain ⟨w, hw, hne⟩ := Finset.exists_mem_ne h_card_gt v
    exact ⟨w, hw, hne⟩
  obtain ⟨w, hw_inter, hwv⟩ := h_exists
  have hw_X : w ∈ X := Finset.mem_of_mem_inter_right hw_inter
  have hw_T : w ∈ T := Finset.mem_of_mem_inter_left hw_inter
  exact ⟨w, hw_X, hwv, edge_in_sym2_iff T v w |>.mpr ⟨hv_in_T, hw_T⟩⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: universal_apex_exists (target of slot325)
-- ══════════════════════════════════════════════════════════════════════════════

/-
This lemma should be proven by slot325. We include it as scaffolding.
If slot325 succeeds, copy its proof here.
-/
lemma universal_apex_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3) :
    (∀ T, isExternalOf G M X T → False) ∨
    (∃ v ∈ X, ∀ T, isExternalOf G M X T → v ∈ T) ∨
    (∃ t, t ∉ X ∧ ∀ T, isExternalOf G M X T → t ∈ T) := by
  -- TODO: Copy proof from slot325 when available
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Get two other vertices of a 3-set
-- ══════════════════════════════════════════════════════════════════════════════

lemma three_set_decomp (X : Finset V) (hX : X.card = 3) (v : V) (hv : v ∈ X) :
    ∃ a b : V, a ∈ X ∧ b ∈ X ∧ a ≠ v ∧ b ≠ v ∧ a ≠ b ∧ X = {v, a, b} := by
  have h_erase : (X.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv]; omega
  obtain ⟨a, b, hab, h_erase_eq⟩ := Finset.card_eq_two.mp h_erase
  have ha : a ∈ X.erase v := by rw [h_erase_eq]; exact Finset.mem_insert_self a {b}
  have hb : b ∈ X.erase v := by rw [h_erase_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have ha' : a ∈ X := Finset.mem_of_mem_erase ha
  have hb' : b ∈ X := Finset.mem_of_mem_erase hb
  have ha_ne : a ≠ v := Finset.ne_of_mem_erase ha
  have hb_ne : b ≠ v := Finset.ne_of_mem_erase hb
  refine ⟨a, b, ha', hb', ha_ne, hb_ne, hab, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxv : x = v
    · rw [hxv]; exact Finset.mem_insert_self v {a, b}
    · have hx_erase : x ∈ X.erase v := Finset.mem_erase.mpr ⟨hxv, hx⟩
      rw [h_erase_eq] at hx_erase
      rcases Finset.mem_insert.mp hx_erase with rfl | hx_b
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self a {b})
      · rw [Finset.mem_singleton] at hx_b
        rw [hx_b]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hv
    · rcases Finset.mem_insert.mp hx' with rfl | hx''
      · exact ha'
      · rw [Finset.mem_singleton] at hx''; rw [hx'']; exact hb'

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: two_edges_cover_X_and_externals (SINGLE SORRY)
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for two_edges_cover_X_and_externals:

Given X = {v, a, b} ∈ M, use universal_apex_exists to get the apex.

CASE 1: No externals
  - Return {s(v,a), s(v,b)} (any 2 edges of X)
  - X is covered, no externals to worry about

CASE 2: Apex v ∈ X
  - Let X = {v, a, b}
  - Return {s(v,a), s(v,b)}
  - X is covered by s(v,a) (contains v,a)
  - Every external T has v ∈ T and T ∩ X = {v, x} for x ∈ {a,b}
  - So s(v,x) covers T

CASE 3: Apex t ∉ X
  - Let X = {a, b, c}, pick any vertex, say a
  - Return {s(a,t), s(b,c)}
  - X is covered by s(b,c) (contains b,c)
  - Every external T has t ∈ T
  - If T ∩ X contains a: s(a,t) covers T (since a,t ∈ T)
  - If T ∩ X = {b,c}: s(b,c) covers T

Key observation: In case 3, every external contains t and shares edge with X.
An external on edge {b,c} is {b,c,t}, covered by s(b,c).
An external on edge {a,b} is {a,b,t}, covered by s(a,t).
An external on edge {a,c} is {a,c,t}, covered by s(a,t).
-/
lemma two_edges_cover_X_and_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3) (hX_tri : X ∈ G.cliqueFinset 3) :
    ∃ e₁ e₂ : Sym2 V, e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
    (∃ u v, u ∈ X ∧ v ∈ X ∧ (e₁ = s(u,v) ∨ e₂ = s(u,v))) ∧  -- At least one edge from X
    (∀ T, isExternalOf G M X T → (e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2)) := by
  sorry

end
