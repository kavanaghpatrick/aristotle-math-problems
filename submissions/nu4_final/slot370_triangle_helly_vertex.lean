/-
Tuza ν=4 Strategy - Slot 370: Triangle Helly for Common Vertex

MULTI-AGENT DEBATE RESULT (Jan 12, 2026):
  Round 1: All agents agree on "2-edges-suffice" approach
  Round 2: Found base edges necessary, Helly for edges is FALSE
  Round 3: Triangle Helly for VERTEX proposed by Agent A (Claude)
  Round 4: Stress-tested - TRUE for vertex, FALSE for edge
  Round 5: Recommended as Tier 1 submission

THEOREM: Triangle Helly for Edge-Sharing (Common Vertex Version)
  If T₁, T₂, T₃ are three distinct triangles such that every pair
  shares an edge (|Tᵢ ∩ Tⱼ| ≥ 2), then all three share a common vertex.

PROOF SKETCH:
  1. Let T₁ = {a,b,c}. Since T₂ shares edge with T₁, WLOG T₁ ∩ T₂ = {a,b}
     so T₂ = {a,b,d} for some d ≠ c (else T₂ = T₁)
  2. T₃ must share edge with T₁ = {a,b,c}. Options: {a,b}, {a,c}, {b,c}
  3. T₃ must share edge with T₂ = {a,b,d}. Options: {a,b}, {a,d}, {b,d}
  4. Case: T₃ ⊇ {a,b}. Then a,b ∈ T₁ ∩ T₂ ∩ T₃. Done.
  5. Case: T₃ = {a,c,e} (shares {a,c} with T₁). For T₃ to share edge with T₂:
     - {a,e} = {a,d} means e=d, so T₃ = {a,c,d}. Then a ∈ T₁ ∩ T₂ ∩ T₃. Done.
     - {a,c} = {a,b} means c=b, but c ≠ b. Impossible.
     - {c,e} = {a,d} would need c ∈ {a,d}, but c ∉ T₂. Impossible.
  6. Case: T₃ = {b,c,e} (shares {b,c} with T₁). Symmetric to case 5.
     Then b ∈ T₁ ∩ T₂ ∩ T₃. Done.
  All cases yield common vertex. QED.

COUNTEREXAMPLE FOR COMMON EDGE VERSION:
  T₁ = {a,b,x}, T₂ = {b,c,x}, T₃ = {a,c,x}
  Pairwise: T₁∩T₂={b,x}, T₂∩T₃={c,x}, T₁∩T₃={a,x}
  Triple: T₁∩T₂∩T₃ = {x} (only vertex, no common edge)

APPLICATION: For PATH_4, if X ∈ M has ≥3 X-externals, they all share
a common vertex (the "fan apex"). This is because:
  - two_externals_share_edge proves pairwise edge-sharing
  - Triangle Helly gives common vertex
  - Any edge through fan apex covers all X-externals

TIER: 1 (Decidable on Fin 6 via native_decide)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset Classical

-- ══════════════════════════════════════════════════════════════════════════════
-- DECIDABILITY SCAFFOLDING FOR FIN 6
-- ══════════════════════════════════════════════════════════════════════════════

/-- Finset membership is decidable -/
instance : DecidableEq (Finset (Fin 6)) := inferInstance

/-- Card comparison is decidable -/
lemma card_ge_two_decidable (S : Finset (Fin 6)) : Decidable (S.card ≥ 2) := inferInstance

/-- Intersection card is computable -/
lemma inter_card_computable (S T : Finset (Fin 6)) : (S ∩ T).card = (S ∩ T).card := rfl

/-- Common element existence is decidable on Fin 6 -/
lemma common_element_decidable (S T U : Finset (Fin 6)) :
    Decidable (∃ v, v ∈ S ∧ v ∈ T ∧ v ∈ U) := inferInstance

/-- Triple intersection nonempty iff common element exists -/
lemma triple_inter_nonempty_iff (S T U : Finset (Fin 6)) :
    (S ∩ T ∩ U).Nonempty ↔ ∃ v, v ∈ S ∧ v ∈ T ∧ v ∈ U := by
  simp [Finset.Nonempty, Finset.mem_inter]

/-- If triple intersection is nonempty, extract witness -/
lemma triple_inter_witness (S T U : Finset (Fin 6)) (h : (S ∩ T ∩ U).Nonempty) :
    ∃ v, v ∈ S ∧ v ∈ T ∧ v ∈ U := by
  obtain ⟨v, hv⟩ := h
  simp only [Finset.mem_inter] at hv
  exact ⟨v, hv.1.1, hv.1.2, hv.2⟩

/-- Two 3-sets sharing ≥2 elements share exactly 2 (if distinct) -/
lemma share_two_of_card_three (S T : Finset (Fin 6))
    (hS : S.card = 3) (hT : T.card = 3) (hne : S ≠ T) (h : (S ∩ T).card ≥ 2) :
    (S ∩ T).card = 2 := by
  have hle : (S ∩ T).card ≤ S.card := Finset.card_inter_le_left S T
  have hlt : (S ∩ T).card < 3 ∨ (S ∩ T).card = 3 := by omega
  rcases hlt with hlt | heq
  · omega
  · -- If card = 3, then S ∩ T = S, so S ⊆ T, and since both have card 3, S = T
    have hsub : S ⊆ T := by
      have : S ∩ T = S := Finset.eq_of_superset_of_card_ge Finset.inter_subset_left (by omega)
      intro x hx; exact this ▸ Finset.mem_inter.mpr ⟨hx, (this.symm ▸ Finset.mem_inter.mp (this ▸ hx)).2⟩
    have : S = T := Finset.eq_of_subset_of_card_le hsub (by omega)
    exact absurd this hne

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Triangle Helly for Common Vertex (Fin 6 version)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Three pairwise edge-sharing triangles share a common vertex.
    This is the VERTEX version (TRUE), not the EDGE version (FALSE).

    PROOF APPROACH: On Fin 6, this is decidable. The key insight is that
    if |T₁ ∩ T₂| ≥ 2 and |T₁ ∩ T₃| ≥ 2 and |T₂ ∩ T₃| ≥ 2, then the
    constraint propagation forces a common element in all three.

    Case analysis (from proof sketch):
    - T₁ ∩ T₂ = {a,b} (share edge)
    - T₃ shares edge with T₁: must share {a,b}, {a,c}, or {b,c}
    - T₃ shares edge with T₂: must share {a,b}, {a,d}, or {b,d}
    - Cross-checking these constraints forces a ∈ T₃ or b ∈ T₃
-/
theorem triangle_helly_vertex_fin6
    (T₁ T₂ T₃ : Finset (Fin 6))
    (hT₁ : T₁.card = 3) (hT₂ : T₂.card = 3) (hT₃ : T₃.card = 3)
    (h_distinct₁₂ : T₁ ≠ T₂) (h_distinct₂₃ : T₂ ≠ T₃) (h_distinct₁₃ : T₁ ≠ T₃)
    (h12 : (T₁ ∩ T₂).card ≥ 2)
    (h23 : (T₂ ∩ T₃).card ≥ 2)
    (h13 : (T₁ ∩ T₃).card ≥ 2) :
    ∃ v, v ∈ T₁ ∧ v ∈ T₂ ∧ v ∈ T₃ := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: Helper lemmas for case analysis
-- ══════════════════════════════════════════════════════════════════════════════

/-- If intersection has ≥2 elements, we can extract two distinct elements -/
lemma inter_ge_two_has_two_elements {α : Type*} [DecidableEq α]
    (S T : Finset α) (h : (S ∩ T).card ≥ 2) :
    ∃ a b, a ∈ S ∩ T ∧ b ∈ S ∩ T ∧ a ≠ b := by
  exact Finset.one_lt_card.mp h

/-- A triangle (3-element set) has exactly 3 distinct elements -/
lemma triangle_has_three_elements {α : Type*} [DecidableEq α]
    (T : Finset α) (hT : T.card = 3) :
    ∃ a b c, a ∈ T ∧ b ∈ T ∧ c ∈ T ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    T = {a, b, c} := by
  obtain ⟨a, ha, T', hT'_eq, hT'_card⟩ := Finset.card_eq_succ.mp hT
  obtain ⟨b, hb, T'', hT''_eq, hT''_card⟩ := Finset.card_eq_succ.mp hT'_card
  rw [Finset.card_eq_one] at hT''_card
  obtain ⟨c, hc_eq⟩ := hT''_card
  refine ⟨a, b, c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ha
  · rw [hT'_eq]; exact Finset.mem_insert_of_mem hb
  · rw [hT'_eq, hT''_eq, hc_eq]; simp
  · intro hab; rw [hab] at hT'_eq
    have : b ∈ T' := hb
    rw [← hT'_eq] at this
    simp at this
  · intro hbc; rw [hbc, hT''_eq, hc_eq] at hb; simp at hb
  · intro hac; rw [hac, hT'_eq] at ha
    have : c ∈ T' := by rw [hT''_eq, hc_eq]; simp
    simp at ha
  · rw [hT'_eq, hT''_eq, hc_eq]
    ext x; simp [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx; rcases hx with rfl | hx
      · left; rfl
      · rcases hx with rfl | hx
        · right; left; rfl
        · right; right; exact hx
    · intro hx; rcases hx with rfl | rfl | rfl <;> simp

/-- If two distinct triangles share an edge, their intersection is exactly 2 -/
lemma distinct_triangles_share_edge_inter_eq_two {α : Type*} [DecidableEq α]
    (T₁ T₂ : Finset α) (hT₁ : T₁.card = 3) (hT₂ : T₂.card = 3)
    (h_distinct : T₁ ≠ T₂) (h_share : (T₁ ∩ T₂).card ≥ 2) :
    (T₁ ∩ T₂).card = 2 := by
  by_contra h
  push_neg at h
  interval_cases (T₁ ∩ T₂).card
  · omega
  · omega
  · -- card = 3: Then T₁ ⊆ T₂ (since |T₁ ∩ T₂| = 3 = |T₁|)
    have h_sub : T₁ ⊆ T₂ := by
      intro x hx
      have : (T₁ ∩ T₂).card = T₁.card := by omega
      have h_eq : T₁ ∩ T₂ = T₁ := Finset.inter_eq_left.mpr (by
        intro y hy
        by_contra hny
        have : (T₁ ∩ T₂).card < T₁.card := by
          apply Finset.card_lt_card
          constructor
          · exact Finset.inter_subset_left
          · push_neg
            exact ⟨y, hy, fun h => hny (Finset.mem_inter.mp h).2⟩
        omega)
      rw [Finset.mem_inter] at *
      exact (h_eq ▸ hx : x ∈ T₁ ∩ T₂).2
    have h_eq : T₁ = T₂ := Finset.eq_of_subset_of_card_le h_sub (by omega)
    exact h_distinct h_eq
  all_goals omega

-- ══════════════════════════════════════════════════════════════════════════════
-- ALTERNATIVE FORMULATION: Explicit vertex extraction
-- ══════════════════════════════════════════════════════════════════════════════

/-- Given two edge-sharing triangles, extract their shared edge -/
lemma shared_edge_of_triangles {α : Type*} [DecidableEq α]
    (T₁ T₂ : Finset α) (hT₁ : T₁.card = 3) (hT₂ : T₂.card = 3)
    (h_share : (T₁ ∩ T₂).card ≥ 2) :
    ∃ a b, a ∈ T₁ ∧ a ∈ T₂ ∧ b ∈ T₁ ∧ b ∈ T₂ ∧ a ≠ b := by
  obtain ⟨a, b, ha, hb, hab⟩ := inter_ge_two_has_two_elements T₁ T₂ h_share
  exact ⟨a, b, (Finset.mem_inter.mp ha).1, (Finset.mem_inter.mp ha).2,
              (Finset.mem_inter.mp hb).1, (Finset.mem_inter.mp hb).2, hab⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- APPLICATION: Fan apex for X-externals
-- ══════════════════════════════════════════════════════════════════════════════

/-- If three X-externals pairwise share edges, they share a common vertex (fan apex) -/
theorem fan_apex_from_three_externals
    (T₁ T₂ T₃ : Finset (Fin 6))
    (hT₁ : T₁.card = 3) (hT₂ : T₂.card = 3) (hT₃ : T₃.card = 3)
    (h_distinct₁₂ : T₁ ≠ T₂) (h_distinct₂₃ : T₂ ≠ T₃) (h_distinct₁₃ : T₁ ≠ T₃)
    -- Pairwise edge-sharing (from two_externals_share_edge)
    (h12 : (T₁ ∩ T₂).card ≥ 2)
    (h23 : (T₂ ∩ T₃).card ≥ 2)
    (h13 : (T₁ ∩ T₃).card ≥ 2) :
    ∃ v, v ∈ T₁ ∧ v ∈ T₂ ∧ v ∈ T₃ :=
  triangle_helly_vertex_fin6 T₁ T₂ T₃ hT₁ hT₂ hT₃ h_distinct₁₂ h_distinct₂₃ h_distinct₁₃ h12 h23 h13

end
