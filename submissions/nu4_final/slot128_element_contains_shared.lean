/-
slot128: Every Edge of a Cycle4 Packing Element Contains a Shared Vertex

GITHUB ISSUE: #29
GOAL: Prove cycle4_element_contains_shared by contradiction (pigeonhole)

AI CONSENSUS (Dec 26-27, 2025):
- Grok: "PROOF IS CORRECT. Pigeonhole-style argument based on set sizes."
- Gemini: "Need |A\S| = 1, |e| = 2 → contradiction"
- Key: Need distinctness axioms from Issue #28

PROOF STRUCTURE:
For X ∈ {A, B, C, D} with edge e ∈ X.sym2:
1. X has 3 vertices = 2 shared (S) + 1 private (P)
2. If e avoids all shared vertices, both endpoints ∈ P
3. But |P| = 1 < 2 = |e| → contradiction
4. Therefore e contains at least one shared vertex ∈ S

EXAMPLE (X = A):
- A = {v_ab, v_da, a_priv}
- Shared vertices in A: S_A = {v_ab, v_da}
- Private vertex: P_A = {a_priv}
- Edge e ∈ A.sym2 has 2 endpoints from A
- If e ⊆ P_A, then |e| ≤ |P_A| = 1, but |e| = 2. Contradiction.

DISTINCTNESS REQUIRED:
v_ab ≠ v_da ensures |S_A| = 2 (not 1 if they coincided)
This follows from B ∩ D = ∅ (diagonal condition)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 STRUCTURE WITH DISTINCTNESS (from slot127)
-- ══════════════════════════════════════════════════════════════════════════════

structure Cycle4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A
  -- Diagonal conditions
  h_diag_AC : (A ∩ C).card ≤ 1
  h_diag_BD : (B ∩ D).card ≤ 1
  -- DISTINCTNESS AXIOMS (crucial for pigeonhole)
  h_vab_ne_vbc : v_ab ≠ v_bc
  h_vbc_ne_vcd : v_bc ≠ v_cd
  h_vcd_ne_vda : v_cd ≠ v_da
  h_vda_ne_vab : v_da ≠ v_ab

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle has exactly 3 vertices -/
lemma triangle_card_eq_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : t.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp ht).2

/-- An edge (as Sym2) has exactly 2 distinct vertices -/
lemma edge_has_two_vertices {a b : V} (hab : a ≠ b) :
    ({a, b} : Finset V).card = 2 := by
  rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
  simp [hab]

/-- Vertices of a Sym2 edge -/
lemma sym2_mem_iff (e : Sym2 V) (x : V) :
    x ∈ e ↔ ∃ y, e = s(x, y) ∨ e = s(y, x) := by
  constructor
  · intro hx
    obtain ⟨a, b, he⟩ := Sym2.exists_mem' e
    cases hx with
    | inl h => exact ⟨b, Or.inl (by simp_all)⟩
    | inr h => exact ⟨a, Or.inr (by simp_all)⟩
  · intro ⟨y, hy⟩
    cases hy with
    | inl h => simp [h]
    | inr h => simp [h]

-- ══════════════════════════════════════════════════════════════════════════════
-- SHARED VERTICES IN EACH ELEMENT
-- ══════════════════════════════════════════════════════════════════════════════

/-- A contains exactly v_ab and v_da as its shared vertices -/
lemma shared_in_A (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) :
    {cfg.v_ab, cfg.v_da} ⊆ cfg.A := by
  simp [cfg.h_vab_A, cfg.h_vda_A]

/-- B contains exactly v_ab and v_bc as its shared vertices -/
lemma shared_in_B (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) :
    {cfg.v_ab, cfg.v_bc} ⊆ cfg.B := by
  simp [cfg.h_vab_B, cfg.h_vbc_B]

/-- C contains exactly v_bc and v_cd as its shared vertices -/
lemma shared_in_C (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) :
    {cfg.v_bc, cfg.v_cd} ⊆ cfg.C := by
  simp [cfg.h_vbc_C, cfg.h_vcd_C]

/-- D contains exactly v_cd and v_da as its shared vertices -/
lemma shared_in_D (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) :
    {cfg.v_cd, cfg.v_da} ⊆ cfg.D := by
  simp [cfg.h_vcd_D, cfg.h_vda_D]

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: ELEMENT CONTAINS SHARED
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every edge of a cycle_4 packing element contains at least one shared vertex -/
theorem cycle4_element_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (X : Finset V) (hX : X ∈ M)
    (e : Sym2 V) (he : e ∈ X.sym2) :
    cfg.v_ab ∈ e ∨ cfg.v_bc ∈ e ∨ cfg.v_cd ∈ e ∨ cfg.v_da ∈ e := by
  -- X is one of A, B, C, D
  rw [cfg.hM_eq] at hX
  simp only [Finset.mem_insert, Finset.mem_singleton] at hX

  -- Get the two endpoints of e from X.sym2
  simp only [Finset.mem_sym2_iff] at he
  obtain ⟨a, b, hab, ha, hb, he_eq⟩ := he

  rcases hX with rfl | rfl | rfl | rfl

  -- Case X = A: shared vertices are v_ab and v_da
  · -- A has 3 vertices, 2 of which are shared (v_ab, v_da)
    -- The edge e = {a, b} has both endpoints in A
    -- If neither a nor b is in {v_ab, v_da}, both must be the private vertex
    -- But a ≠ b, so this is impossible since |private| = 1

    by_contra h_contra
    push_neg at h_contra
    -- h_contra says: v_ab ∉ e ∧ v_bc ∉ e ∧ v_cd ∉ e ∧ v_da ∉ e
    -- We only care about v_ab ∉ e and v_da ∉ e (the shared vertices of A)

    have h_vab_ne : cfg.v_ab ∉ ({a, b} : Finset V) := by
      intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      cases h with
      | inl h => exact h_contra.1 (he_eq ▸ by simp [h])
      | inr h => exact h_contra.1 (he_eq ▸ by simp [h])

    have h_vda_ne : cfg.v_da ∉ ({a, b} : Finset V) := by
      intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      cases h with
      | inl h => exact h_contra.2.2.2 (he_eq ▸ by simp [h])
      | inr h => exact h_contra.2.2.2 (he_eq ▸ by simp [h])

    -- So a ∉ {v_ab, v_da} and b ∉ {v_ab, v_da}
    have ha_not_shared : a ≠ cfg.v_ab ∧ a ≠ cfg.v_da := by
      constructor
      · intro h; exact h_vab_ne (by simp [h])
      · intro h; exact h_vda_ne (by simp [h])

    have hb_not_shared : b ≠ cfg.v_ab ∧ b ≠ cfg.v_da := by
      constructor
      · intro h; exact h_vab_ne (by simp [h])
      · intro h; exact h_vda_ne (by simp [h])

    -- A = {v_ab, v_da, a_priv} for some private vertex a_priv
    -- Since a, b ∈ A and a, b ∉ {v_ab, v_da}, we have a = b = a_priv
    -- But a ≠ b, contradiction!

    have h_A_card : cfg.A.card = 3 := by
      have h_A_triangle : cfg.A ∈ G.cliqueFinset 3 := hM.1.1 cfg.hA
      exact triangle_card_eq_3 G cfg.A h_A_triangle

    -- The shared set in A is {v_ab, v_da} with card = 2 (by distinctness)
    have h_shared_card : ({cfg.v_ab, cfg.v_da} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
      simp [cfg.h_vda_ne_vab]

    have h_shared_subset : ({cfg.v_ab, cfg.v_da} : Finset V) ⊆ cfg.A :=
      shared_in_A G M hM cfg

    -- Private vertices = A \ {v_ab, v_da}, which has card 1
    have h_private_card : (cfg.A \ {cfg.v_ab, cfg.v_da}).card = 1 := by
      rw [Finset.card_sdiff h_shared_subset, h_A_card, h_shared_card]

    -- a ∈ A and a ∉ {v_ab, v_da}, so a ∈ A \ {v_ab, v_da}
    have ha_private : a ∈ cfg.A \ {cfg.v_ab, cfg.v_da} := by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨ha, ha_not_shared.1, ha_not_shared.2⟩

    -- Similarly for b
    have hb_private : b ∈ cfg.A \ {cfg.v_ab, cfg.v_da} := by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hb, hb_not_shared.1, hb_not_shared.2⟩

    -- A \ {v_ab, v_da} has only 1 element, but a ≠ b both belong to it
    have h_contradiction : a = b := by
      have h_singleton := Finset.card_eq_one.mp h_private_card
      obtain ⟨x, hx⟩ := h_singleton
      have ha_eq : a = x := Finset.mem_singleton.mp (hx ▸ ha_private)
      have hb_eq : b = x := Finset.mem_singleton.mp (hx ▸ hb_private)
      rw [ha_eq, hb_eq]

    exact hab h_contradiction

  -- Case X = B: shared vertices are v_ab and v_bc
  · by_contra h_contra
    push_neg at h_contra

    have h_vab_ne : cfg.v_ab ∉ ({a, b} : Finset V) := by
      intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      cases h with
      | inl h => exact h_contra.1 (he_eq ▸ by simp [h])
      | inr h => exact h_contra.1 (he_eq ▸ by simp [h])

    have h_vbc_ne : cfg.v_bc ∉ ({a, b} : Finset V) := by
      intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      cases h with
      | inl h => exact h_contra.2.1 (he_eq ▸ by simp [h])
      | inr h => exact h_contra.2.1 (he_eq ▸ by simp [h])

    have ha_not_shared : a ≠ cfg.v_ab ∧ a ≠ cfg.v_bc := by
      constructor
      · intro h; exact h_vab_ne (by simp [h])
      · intro h; exact h_vbc_ne (by simp [h])

    have hb_not_shared : b ≠ cfg.v_ab ∧ b ≠ cfg.v_bc := by
      constructor
      · intro h; exact h_vab_ne (by simp [h])
      · intro h; exact h_vbc_ne (by simp [h])

    have h_B_card : cfg.B.card = 3 := by
      have h_B_triangle : cfg.B ∈ G.cliqueFinset 3 := hM.1.1 cfg.hB
      exact triangle_card_eq_3 G cfg.B h_B_triangle

    have h_shared_card : ({cfg.v_ab, cfg.v_bc} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
      simp [cfg.h_vab_ne_vbc]

    have h_shared_subset : ({cfg.v_ab, cfg.v_bc} : Finset V) ⊆ cfg.B :=
      shared_in_B G M hM cfg

    have h_private_card : (cfg.B \ {cfg.v_ab, cfg.v_bc}).card = 1 := by
      rw [Finset.card_sdiff h_shared_subset, h_B_card, h_shared_card]

    have ha_private : a ∈ cfg.B \ {cfg.v_ab, cfg.v_bc} := by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨ha, ha_not_shared.1, ha_not_shared.2⟩

    have hb_private : b ∈ cfg.B \ {cfg.v_ab, cfg.v_bc} := by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hb, hb_not_shared.1, hb_not_shared.2⟩

    have h_contradiction : a = b := by
      have h_singleton := Finset.card_eq_one.mp h_private_card
      obtain ⟨x, hx⟩ := h_singleton
      have ha_eq : a = x := Finset.mem_singleton.mp (hx ▸ ha_private)
      have hb_eq : b = x := Finset.mem_singleton.mp (hx ▸ hb_private)
      rw [ha_eq, hb_eq]

    exact hab h_contradiction

  -- Case X = C: shared vertices are v_bc and v_cd
  · by_contra h_contra
    push_neg at h_contra

    have h_vbc_ne : cfg.v_bc ∉ ({a, b} : Finset V) := by
      intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      cases h with
      | inl h => exact h_contra.2.1 (he_eq ▸ by simp [h])
      | inr h => exact h_contra.2.1 (he_eq ▸ by simp [h])

    have h_vcd_ne : cfg.v_cd ∉ ({a, b} : Finset V) := by
      intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      cases h with
      | inl h => exact h_contra.2.2.1 (he_eq ▸ by simp [h])
      | inr h => exact h_contra.2.2.1 (he_eq ▸ by simp [h])

    have ha_not_shared : a ≠ cfg.v_bc ∧ a ≠ cfg.v_cd := by
      constructor
      · intro h; exact h_vbc_ne (by simp [h])
      · intro h; exact h_vcd_ne (by simp [h])

    have hb_not_shared : b ≠ cfg.v_bc ∧ b ≠ cfg.v_cd := by
      constructor
      · intro h; exact h_vbc_ne (by simp [h])
      · intro h; exact h_vcd_ne (by simp [h])

    have h_C_card : cfg.C.card = 3 := by
      have h_C_triangle : cfg.C ∈ G.cliqueFinset 3 := hM.1.1 cfg.hC
      exact triangle_card_eq_3 G cfg.C h_C_triangle

    have h_shared_card : ({cfg.v_bc, cfg.v_cd} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
      simp [cfg.h_vbc_ne_vcd]

    have h_shared_subset : ({cfg.v_bc, cfg.v_cd} : Finset V) ⊆ cfg.C :=
      shared_in_C G M hM cfg

    have h_private_card : (cfg.C \ {cfg.v_bc, cfg.v_cd}).card = 1 := by
      rw [Finset.card_sdiff h_shared_subset, h_C_card, h_shared_card]

    have ha_private : a ∈ cfg.C \ {cfg.v_bc, cfg.v_cd} := by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨ha, ha_not_shared.1, ha_not_shared.2⟩

    have hb_private : b ∈ cfg.C \ {cfg.v_bc, cfg.v_cd} := by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hb, hb_not_shared.1, hb_not_shared.2⟩

    have h_contradiction : a = b := by
      have h_singleton := Finset.card_eq_one.mp h_private_card
      obtain ⟨x, hx⟩ := h_singleton
      have ha_eq : a = x := Finset.mem_singleton.mp (hx ▸ ha_private)
      have hb_eq : b = x := Finset.mem_singleton.mp (hx ▸ hb_private)
      rw [ha_eq, hb_eq]

    exact hab h_contradiction

  -- Case X = D: shared vertices are v_cd and v_da
  · by_contra h_contra
    push_neg at h_contra

    have h_vcd_ne : cfg.v_cd ∉ ({a, b} : Finset V) := by
      intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      cases h with
      | inl h => exact h_contra.2.2.1 (he_eq ▸ by simp [h])
      | inr h => exact h_contra.2.2.1 (he_eq ▸ by simp [h])

    have h_vda_ne : cfg.v_da ∉ ({a, b} : Finset V) := by
      intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      cases h with
      | inl h => exact h_contra.2.2.2 (he_eq ▸ by simp [h])
      | inr h => exact h_contra.2.2.2 (he_eq ▸ by simp [h])

    have ha_not_shared : a ≠ cfg.v_cd ∧ a ≠ cfg.v_da := by
      constructor
      · intro h; exact h_vcd_ne (by simp [h])
      · intro h; exact h_vda_ne (by simp [h])

    have hb_not_shared : b ≠ cfg.v_cd ∧ b ≠ cfg.v_da := by
      constructor
      · intro h; exact h_vcd_ne (by simp [h])
      · intro h; exact h_vda_ne (by simp [h])

    have h_D_card : cfg.D.card = 3 := by
      have h_D_triangle : cfg.D ∈ G.cliqueFinset 3 := hM.1.1 cfg.hD
      exact triangle_card_eq_3 G cfg.D h_D_triangle

    have h_shared_card : ({cfg.v_cd, cfg.v_da} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
      simp [cfg.h_vcd_ne_vda]

    have h_shared_subset : ({cfg.v_cd, cfg.v_da} : Finset V) ⊆ cfg.D :=
      shared_in_D G M hM cfg

    have h_private_card : (cfg.D \ {cfg.v_cd, cfg.v_da}).card = 1 := by
      rw [Finset.card_sdiff h_shared_subset, h_D_card, h_shared_card]

    have ha_private : a ∈ cfg.D \ {cfg.v_cd, cfg.v_da} := by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨ha, ha_not_shared.1, ha_not_shared.2⟩

    have hb_private : b ∈ cfg.D \ {cfg.v_cd, cfg.v_da} := by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hb, hb_not_shared.1, hb_not_shared.2⟩

    have h_contradiction : a = b := by
      have h_singleton := Finset.card_eq_one.mp h_private_card
      obtain ⟨x, hx⟩ := h_singleton
      have ha_eq : a = x := Finset.mem_singleton.mp (hx ▸ ha_private)
      have hb_eq : b = x := Finset.mem_singleton.mp (hx ▸ hb_private)
      rw [ha_eq, hb_eq]

    exact hab h_contradiction

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: ALL TRIANGLES CONTAIN SHARED VERTEX
-- ══════════════════════════════════════════════════════════════════════════════

/-- PROVEN: Every triangle shares an edge with some packing element -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
  by_contra h_contra
  push_neg at h_contra
  have h_packing : isTrianglePacking G (M ∪ {t}) := by
    constructor
    · exact Finset.union_subset hM.1.1 (Finset.singleton_subset_iff.mpr ht)
    · intro t1 ht1 t2 ht2 hne
      simp only [Finset.mem_union, Finset.mem_singleton] at ht1 ht2
      rcases ht1 with ht1 | rfl <;> rcases ht2 with ht2 | rfl
      · exact hM.1.2 ht1 ht2 hne
      · exact hne rfl |>.elim
      · simp only [Finset.inter_comm]
        exact Nat.lt_succ.mp (h_contra _ ht2)
      · exact Nat.lt_succ.mp (h_contra _ ht1)
  have h_card : (M ∪ {t}).card > M.card := by
    have h_not_in : t ∉ M := by
      intro h
      specialize h_contra t h
      simp only [Finset.inter_self, ht.card_eq, Nat.lt_succ_self, not_true] at h_contra
    simp [Finset.card_union_of_disjoint, h_not_in]
  have h_ge : trianglePackingNumber G ≥ (M ∪ {t}).card := by
    unfold trianglePackingNumber
    have h_mem : (M ∪ {t}) ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      simp [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · intro x hx
        simp at hx
        cases hx with
        | inl h => exact hM.1.1 h
        | inr h => exact h ▸ ht
      · exact h_packing
    have := Finset.le_max (Finset.mem_image_of_mem Finset.card h_mem)
    cases h : Finset.max (Finset.image Finset.card ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G))) with
    | none => simp at this
    | some m => simp at this ⊢; exact this
  omega

/-- Every triangle in a cycle_4 graph contains at least one shared vertex -/
theorem cycle4_all_triangles_contain_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    cfg.v_ab ∈ t ∨ cfg.v_bc ∈ t ∨ cfg.v_cd ∈ t ∨ cfg.v_da ∈ t := by
  -- t shares an edge with some X ∈ M
  obtain ⟨X, hX, h_share⟩ := triangle_shares_edge_with_packing G M hM t ht

  -- Extract an edge e from the intersection
  have h_inter_ge_2 : (t ∩ X).card ≥ 2 := h_share
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (Nat.one_lt_iff_ne_one.mpr (by omega))

  -- Construct the edge e = {a, b}
  let e : Sym2 V := s(a, b)

  -- e is in both t.sym2 and X.sym2
  have he_t : e ∈ t.sym2 := by
    simp only [Finset.mem_sym2_iff, Sym2.mem_iff]
    simp only [Finset.mem_inter] at ha hb
    exact ⟨a, b, hab, ha.1, hb.1, rfl⟩

  have he_X : e ∈ X.sym2 := by
    simp only [Finset.mem_sym2_iff, Sym2.mem_iff]
    simp only [Finset.mem_inter] at ha hb
    exact ⟨a, b, hab, ha.2, hb.2, rfl⟩

  -- By cycle4_element_contains_shared, e contains a shared vertex
  have h_shared := cycle4_element_contains_shared G M hM cfg X hX e he_X

  -- If e contains a shared vertex v, and e ⊆ t (since e ∈ t.sym2), then v ∈ t
  simp only [Finset.mem_inter] at ha hb
  rcases h_shared with h_vab | h_vbc | h_vcd | h_vda
  · left
    simp only [Sym2.mem_iff] at h_vab
    cases h_vab with
    | inl h => exact h ▸ ha.1
    | inr h => exact h ▸ hb.1
  · right; left
    simp only [Sym2.mem_iff] at h_vbc
    cases h_vbc with
    | inl h => exact h ▸ ha.1
    | inr h => exact h ▸ hb.1
  · right; right; left
    simp only [Sym2.mem_iff] at h_vcd
    cases h_vcd with
    | inl h => exact h ▸ ha.1
    | inr h => exact h ▸ hb.1
  · right; right; right
    simp only [Sym2.mem_iff] at h_vda
    cases h_vda with
    | inl h => exact h ▸ ha.1
    | inr h => exact h ▸ hb.1

end
