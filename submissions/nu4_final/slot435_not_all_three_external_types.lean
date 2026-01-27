/-
  slot435_not_all_three_external_types.lean

  CRITICAL LEMMA: For ν = 4 packing, at most 2 of 3 external types are nonempty.

  PROOF SKETCH:
  1. Assume all 3 external types are nonempty for element E = {v, a, b}
  2. Pick one triangle from type v-a (call it T_va) and one from type v-b (call it T_vb)
  3. T_va ≠ T_vb: If equal, T would contain v, a, b = E, but externals ≠ E
  4. T_va, T_vb are edge-disjoint with M\{E} (by external definition)
  5. T_va ∩ T_vb shares only v (one from each external type)
  6. M' = M.erase E ∪ {T_va, T_vb} is a valid packing of size 5
  7. Contradiction with ν = 4

  TIER: 2-3 (construction + pigeonhole)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle packing: set of triangles that pairwise share at most 1 vertex -/
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  (∀ T₁ ∈ M, ∀ T₂ ∈ M, T₁ ≠ T₂ → (T₁ ∩ T₂).card ≤ 1)

/-- Triangles containing edge {u, v} that are edge-disjoint from M\{E} -/
def ExternalsOfType (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (E : Finset V) (u v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ E ∧
    u ∈ T ∧ v ∈ T ∧
    ∀ F ∈ M, F ≠ E → (T ∩ F).card ≤ 1)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_mem_clique {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Finset V)} {E : Finset V} {u v : V}
    {T : Finset V} (hT : T ∈ ExternalsOfType G M E u v) :
    T ∈ G.cliqueFinset 3 := by
  unfold ExternalsOfType at hT
  exact (mem_filter.mp hT).1

lemma external_ne_E {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Finset V)} {E : Finset V} {u v : V}
    {T : Finset V} (hT : T ∈ ExternalsOfType G M E u v) :
    T ≠ E := by
  unfold ExternalsOfType at hT
  exact (mem_filter.mp hT).2.1

lemma external_contains_u {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Finset V)} {E : Finset V} {u v : V}
    {T : Finset V} (hT : T ∈ ExternalsOfType G M E u v) :
    u ∈ T := by
  unfold ExternalsOfType at hT
  exact (mem_filter.mp hT).2.2.1

lemma external_contains_v {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Finset V)} {E : Finset V} {u v : V}
    {T : Finset V} (hT : T ∈ ExternalsOfType G M E u v) :
    v ∈ T := by
  unfold ExternalsOfType at hT
  exact (mem_filter.mp hT).2.2.2.1

lemma external_disjoint {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Finset V)} {E : Finset V} {u v : V}
    {T : Finset V} (hT : T ∈ ExternalsOfType G M E u v)
    {F : Finset V} (hF : F ∈ M) (hFE : F ≠ E) :
    (T ∩ F).card ≤ 1 := by
  unfold ExternalsOfType at hT
  exact (mem_filter.mp hT).2.2.2.2 F hF hFE

lemma clique3_card {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : Finset V} (hT : T ∈ G.cliqueFinset 3) :
    T.card = 3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at hT
  exact hT.2

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: External not in M (shares 2+ vertices with E)
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_not_in_M {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Finset V)} (hM : isTrianglePacking G M)
    {E : Finset V} (hE : E ∈ M) {u v : V}
    (hu : u ∈ E) (hv : v ∈ E) (huv : u ≠ v)
    {T : Finset V} (hT : T ∈ ExternalsOfType G M E u v) :
    T ∉ M := by
  intro hTM
  have hT_ne_E := external_ne_E hT
  have hu_T := external_contains_u hT
  have hv_T := external_contains_v hT
  -- T and E share both u and v
  have h_inter : {u, v} ⊆ T ∩ E := by
    intro x hx
    rw [mem_inter]
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨hu_T, hu⟩
    · exact ⟨hv_T, hv⟩
  have h_card : (T ∩ E).card ≥ 2 := by
    calc (T ∩ E).card ≥ ({u, v} : Finset V).card := card_le_card h_inter
      _ = 2 := card_pair huv
  -- But packing requires intersection ≤ 1
  have h_packing := hM.2 T hTM E hE hT_ne_E
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Two externals from different types share at most 1 vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for h_va_vb_disjoint:
- T_va contains {v, a, x} for some x
- T_vb contains {v, b, y} for some y
- T_va ∩ T_vb contains v
- If T_va ∩ T_vb contains another vertex z:
  - z ∈ {v, a, x} and z ∈ {v, b, y}
  - z ≠ v, so z ∈ {a, x} and z ∈ {b, y}
  - Case z = a: a ∈ T_vb, so T_vb contains {v, a, b}
    But |T_vb| = 3, so T_vb = {v, a, b} = E, contradiction with T_vb ≠ E
  - Case z = x: x ∈ {b, y}
    If x = b: T_va contains {v, a, b} = E, contradiction
    If x = y: Need to show this leads to contradiction too
- Key insight: a ≠ b, and externals are triangles, so overlap is limited
-/

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/--
For a ν = 4 packing, at most 2 of 3 external types are nonempty.

If all 3 exist, we can extend the packing by replacing E with T_va and T_vb,
giving a packing of size 5, contradicting ν = 4.
-/
theorem not_all_three_external_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hM_card : M.card = 4)
    (hν_max : ∀ M' : Finset (Finset V), isTrianglePacking G M' → M'.card ≤ 4)
    (E : Finset V) (hE : E ∈ M)
    (v a b : V) (hE_eq : E = {v, a, b})
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b) :
    ¬((ExternalsOfType G M E v a).Nonempty ∧
      (ExternalsOfType G M E v b).Nonempty ∧
      (ExternalsOfType G M E a b).Nonempty) := by
  intro ⟨⟨T_va, hT_va⟩, ⟨T_vb, hT_vb⟩, _⟩

  -- Vertex containments
  have hv_in_E : v ∈ E := by rw [hE_eq]; simp [hva, hvb]
  have ha_in_E : a ∈ E := by rw [hE_eq]; simp [hva.symm, hab]
  have hb_in_E : b ∈ E := by rw [hE_eq]; simp [hvb.symm, hab.symm]

  have hv_va := external_contains_u hT_va
  have ha_va := external_contains_v hT_va
  have hv_vb := external_contains_u hT_vb
  have hb_vb := external_contains_v hT_vb

  -- T_va and T_vb are not in M
  have hT_va_not_M : T_va ∉ M := external_not_in_M hM hE hv_in_E ha_in_E hva hT_va
  have hT_vb_not_M : T_vb ∉ M := external_not_in_M hM hE hv_in_E hb_in_E hvb hT_vb

  -- T_va ≠ T_vb
  have hT_va_ne_vb : T_va ≠ T_vb := by
    intro h_eq
    -- If T_va = T_vb, then T_va contains v, a, b
    have ha_in_Tvb : a ∈ T_vb := h_eq ▸ ha_va
    have hvab_sub : ({v, a, b} : Finset V) ⊆ T_vb := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv_vb
      · exact ha_in_Tvb
      · exact hb_vb
    -- |{v,a,b}| = 3 = |T_vb|, so T_vb = {v,a,b} = E
    have hT_vb_card := clique3_card (external_mem_clique hT_vb)
    have h_vab_card : ({v, a, b} : Finset V).card = 3 := by
      rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
      · exact fun h => hab (mem_singleton.mp h)
      · simp only [mem_insert, mem_singleton]
        intro h
        rcases h with rfl | rfl
        · exact hva rfl
        · exact hvb rfl
    have h_eq' : {v, a, b} = T_vb := eq_of_subset_of_card_le hvab_sub (by omega)
    rw [← hE_eq] at h_eq'
    exact external_ne_E hT_vb h_eq'.symm

  -- T_va and T_vb are edge-disjoint (share at most 1 vertex)
  have h_va_vb_disjoint : (T_va ∩ T_vb).card ≤ 1 := by
    sorry -- Aristotle: Use the fact that they come from different external types

  -- Construct M' = M.erase E ∪ {T_va, T_vb}
  let M' := M.erase E ∪ {T_va, T_vb}

  -- M' is a valid packing
  have hM'_packing : isTrianglePacking G M' := by
    constructor
    · -- All elements are triangles
      intro X hX
      rw [mem_union] at hX
      rcases hX with hX | hX
      · exact hM.1 (mem_erase.mp hX).2
      · simp only [mem_insert, mem_singleton] at hX
        rcases hX with rfl | rfl
        · exact external_mem_clique hT_va
        · exact external_mem_clique hT_vb
    · -- Pairwise edge-disjoint
      intro X hX Y hY hXY
      rw [mem_union] at hX hY
      rcases hX with hX | hX <;> rcases hY with hY | hY
      · -- Both from M.erase E
        exact hM.2 X (mem_erase.mp hX).2 Y (mem_erase.mp hY).2 hXY
      · -- X from M.erase E, Y from {T_va, T_vb}
        simp only [mem_insert, mem_singleton] at hY
        rcases hY with rfl | rfl
        · rw [inter_comm]; exact external_disjoint hT_va (mem_erase.mp hX).2 (mem_erase.mp hX).1
        · rw [inter_comm]; exact external_disjoint hT_vb (mem_erase.mp hX).2 (mem_erase.mp hX).1
      · -- X from {T_va, T_vb}, Y from M.erase E
        simp only [mem_insert, mem_singleton] at hX
        rcases hX with rfl | rfl
        · exact external_disjoint hT_va (mem_erase.mp hY).2 (mem_erase.mp hY).1
        · exact external_disjoint hT_vb (mem_erase.mp hY).2 (mem_erase.mp hY).1
      · -- Both from {T_va, T_vb}
        simp only [mem_insert, mem_singleton] at hX hY
        rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
        · exact absurd rfl hXY
        · exact h_va_vb_disjoint
        · rw [inter_comm]; exact h_va_vb_disjoint
        · exact absurd rfl hXY

  -- Count: |M'| = 5
  have hM'_card : M'.card = 5 := by
    have h1 : (M.erase E).card = 3 := by
      rw [card_erase_of_mem hE, hM_card]
    have h2 : ({T_va, T_vb} : Finset (Finset V)).card = 2 := by
      rw [card_insert_of_not_mem, card_singleton]
      simp only [mem_singleton]
      exact hT_va_ne_vb
    have h3 : Disjoint (M.erase E) {T_va, T_vb} := by
      rw [disjoint_left]
      intro X hX hX_pair
      simp only [mem_insert, mem_singleton] at hX_pair
      rcases hX_pair with rfl | rfl
      · exact hT_va_not_M (mem_erase.mp hX).2
      · exact hT_vb_not_M (mem_erase.mp hX).2
    calc M'.card = (M.erase E ∪ {T_va, T_vb}).card := rfl
      _ = (M.erase E).card + ({T_va, T_vb} : Finset _).card := card_union_of_disjoint h3
      _ = 3 + 2 := by rw [h1, h2]
      _ = 5 := by norm_num

  -- Contradiction: M' has size 5 but ν = 4
  have h_contra := hν_max M' hM'_packing
  omega

end
