/-
Tuza ν=4 Strategy - Slot 67: CYCLE_4 via All-Middle Property

KEY INSIGHT (Grok + Gemini Consensus):
Cycle_4 is SIMPLER than Path_4 because ALL elements are "middle"!

PATH_4: A—B—C—D (heterogeneous)
- Endpoints A, D have ONE shared vertex → need base edges for "avoiding" triangles
- Middle B, C have TWO shared vertices → no base edges needed

CYCLE_4: A—B—C—D—A (homogeneous)
- EVERY element has TWO shared vertices (e.g., A shares v_ab with B AND v_da with D)
- NO endpoints → NO base edges needed
- Every triangle sharing edge with packing MUST contain a shared vertex

PROOF STRATEGY:
1. Every triangle shares edge with some packing element (maximality)
2. Every packing element X shares vertices on BOTH sides
3. Therefore every triangle in T_X contains v_left OR v_right
4. 8 spokes (2 per shared vertex) cover ALL triangles

8-SPOKE COVER:
- v_ab: 2 spokes
- v_bc: 2 spokes
- v_cd: 2 spokes
- v_da: 2 spokes
Total: 8 spokes, covers everything!

REUSED LEMMAS:
- triangles_containing_v_covered_by_spokes (from slot57)
- path4_no_loose_triangles (maximality - transfers directly)
- path4_T_B_contains_shared (applies to ALL cycle elements!)

TARGET: tau_le_8_cycle4_all_middle
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

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def trianglesContainingVertex (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slot57 c2bcbe2c)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles containing v are covered by edges incident to v (spokes) -/
lemma triangles_containing_v_covered_by_spokes (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hv : (G.neighborFinset v).card ≥ 2) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ (G.neighborFinset v).card ∧ E' ⊆ G.edgeFinset ∧
    ∀ t ∈ trianglesContainingVertex G v, ∃ e ∈ E', e ∈ t.sym2 := by
  use (G.neighborFinset v).image (fun u => s(v, u))
  constructor
  · exact Finset.card_image_le
  constructor
  · intro e he
    simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset] at he
    obtain ⟨u, hu, rfl⟩ := he
    exact SimpleGraph.mem_edgeFinset.mpr hu
  · intro t ht
    simp only [trianglesContainingVertex, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
    have ⟨hclique, hcard⟩ := ht.1
    have hv_in_t := ht.2
    obtain ⟨x, y, z, hxyz⟩ := Finset.card_eq_three.mp hcard
    rw [hxyz.2.2.2] at hv_in_t
    simp at hv_in_t
    rcases hv_in_t with rfl | rfl | rfl
    · use s(x, y)
      constructor
      · simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
        exact ⟨y, hclique (by rw [hxyz.2.2.2]; simp) (by rw [hxyz.2.2.2]; simp) hxyz.1, rfl⟩
      · rw [hxyz.2.2.2]; simp [Sym2.mem_iff]
    · use s(y, x)
      constructor
      · simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
        refine ⟨x, ?_, ?_⟩
        · rw [SimpleGraph.adj_comm]
          exact hclique (by rw [hxyz.2.2.2]; simp) (by rw [hxyz.2.2.2]; simp) hxyz.1
        · rw [Sym2.eq_swap]
      · rw [hxyz.2.2.2]; simp [Sym2.mem_iff]
    · use s(z, x)
      constructor
      · simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
        refine ⟨x, ?_, ?_⟩
        · rw [SimpleGraph.adj_comm]
          exact hclique (by rw [hxyz.2.2.2]; simp) (by rw [hxyz.2.2.2]; simp) hxyz.2.1
        · rw [Sym2.eq_swap]
      · rw [hxyz.2.2.2]; simp [Sym2.mem_iff]

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: All-Middle Property (Cycle-specific)
-- ══════════════════════════════════════════════════════════════════════════════

/-- In cycle_4, every packing element X shares vertices on BOTH sides.
    Therefore, every triangle in T_X contains v_left OR v_right.
    This is the "all-middle" property - no base edges needed! -/
lemma cycle4_element_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (v_left v_right x1 : V)
    (hX_eq : X = {v_left, v_right, x1})
    (h_ne : v_left ≠ v_right ∧ v_left ≠ x1 ∧ v_right ≠ x1)
    (t : Finset V) (ht : t ∈ trianglesSharingEdge G X) :
    v_left ∈ t ∨ v_right ∈ t := by
  simp only [trianglesSharingEdge, Finset.mem_filter] at ht
  have h_share : (t ∩ X).card ≥ 2 := ht.2
  rw [hX_eq] at h_share
  -- t shares ≥2 vertices with {v_left, v_right, x1}
  -- Every pair contains v_left or v_right (since x1 is the only "base" vertex)
  by_contra h_neither
  push_neg at h_neither
  -- t doesn't contain v_left or v_right, so t ∩ {v_left, v_right, x1} ⊆ {x1}
  have hsub : t ∩ {v_left, v_right, x1} ⊆ {x1} := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 h_neither.1
    · exact absurd hx.1 h_neither.2
    · rfl
  have hcard : (t ∩ {v_left, v_right, x1}).card ≤ 1 := by
    calc (t ∩ {v_left, v_right, x1}).card ≤ ({x1} : Finset V).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton x1
  omega

/-- Maximality: Every triangle shares edge with some packing element -/
lemma cycle4_no_loose_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    t ∈ trianglesSharingEdge G A ∨ t ∈ trianglesSharingEdge G B ∨
    t ∈ trianglesSharingEdge G C ∨ t ∈ trianglesSharingEdge G D := by
  -- Same as path4_no_loose_triangles - maximality argument
  by_contra h_none
  push_neg at h_none
  simp only [trianglesSharingEdge, Finset.mem_filter, not_and, not_le] at h_none
  have h_disj_A : (t ∩ A).card ≤ 1 := Nat.lt_succ_iff.mp (h_none.1 ht)
  have h_disj_B : (t ∩ B).card ≤ 1 := Nat.lt_succ_iff.mp (h_none.2.1 ht)
  have h_disj_C : (t ∩ C).card ≤ 1 := Nat.lt_succ_iff.mp (h_none.2.2.1 ht)
  have h_disj_D : (t ∩ D).card ≤ 1 := Nat.lt_succ_iff.mp (h_none.2.2.2 ht)
  -- M ∪ {t} would be a larger packing, contradicting maximality
  have h_packing : isTrianglePacking G (M ∪ {t}) := by
    constructor
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton] at hx
      rcases hx with hxM | rfl
      · exact hM.1.1 hxM
      · exact ht
    · intro x hx y hy hxy
      simp only [Finset.mem_union, Finset.mem_singleton] at hx hy
      rcases hx with hxM | rfl <;> rcases hy with hyM | rfl
      · exact hM.1.2 hxM hyM hxy
      · rw [hcycle.1] at hxM
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxM
        rcases hxM with rfl | rfl | rfl | rfl
        · exact h_disj_A
        · exact h_disj_B
        · exact h_disj_C
        · exact h_disj_D
      · rw [hcycle.1] at hyM
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyM
        rcases hyM with rfl | rfl | rfl | rfl <;> rw [Finset.inter_comm]
        · exact h_disj_A
        · exact h_disj_B
        · exact h_disj_C
        · exact h_disj_D
      · exact absurd rfl hxy
  have ht_not : t ∉ M := by
    intro ht_in
    rw [hcycle.1] at ht_in
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht_in
    rcases ht_in with rfl | rfl | rfl | rfl
    all_goals {
      simp at *
      have := (SimpleGraph.mem_cliqueFinset_iff.mp ht).2
      omega
    }
  have h_card : (M ∪ {t}).card > M.card := by simp [ht_not]
  have h_max := hM.2
  have h_bound : (M ∪ {t}).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    have h_mem : (M ∪ {t}) ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h_packing.1, h_packing⟩
    have h_img : (M ∪ {t}).card ∈ ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card := by
      exact Finset.mem_image_of_mem _ h_mem
    have := Finset.le_max h_img
    cases h : Finset.max (((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card) with
    | none => simp at this
    | some val => simp [h] at this ⊢; exact this
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 8 spokes cover all triangles
-- ══════════════════════════════════════════════════════════════════════════════

/-- All triangles in graph contain at least one shared vertex -/
lemma cycle4_all_triangles_contain_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab v_bc v_cd v_da : V)
    (hAB : A ∩ B = {v_ab}) (hBC : B ∩ C = {v_bc})
    (hCD : C ∩ D = {v_cd}) (hDA : D ∩ A = {v_da})
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    v_ab ∈ t ∨ v_bc ∈ t ∨ v_cd ∈ t ∨ v_da ∈ t := by
  -- Every triangle shares edge with some packing element
  obtain h_case := cycle4_no_loose_triangles G M hM A B C D hcycle t ht
  -- Each packing element X contributes triangles containing v_left OR v_right
  -- where v_left, v_right are the shared vertices adjacent to X
  rcases h_case with hA | hB | hC | hD
  · -- t shares edge with A, so t contains v_ab or v_da
    -- A = {v_ab, v_da, a1} for some a1
    sorry -- Apply cycle4_element_contains_shared
  · -- t shares edge with B, so t contains v_ab or v_bc
    sorry
  · -- t shares edge with C, so t contains v_bc or v_cd
    sorry
  · -- t shares edge with D, so t contains v_cd or v_da
    sorry

/-- Main theorem: τ(G) ≤ 8 for CYCLE_4 via 8 spokes -/
theorem tau_le_8_cycle4_all_middle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  -- Extract shared vertices
  have hAB_card : (A ∩ B).card = 1 := hcycle.2.2.2.2.2.2.2.1
  have hBC_card : (B ∩ C).card = 1 := hcycle.2.2.2.2.2.2.2.2.1
  have hCD_card : (C ∩ D).card = 1 := hcycle.2.2.2.2.2.2.2.2.2.1
  have hDA_card : (D ∩ A).card = 1 := hcycle.2.2.2.2.2.2.2.2.2.2.1

  obtain ⟨v_ab, hv_ab⟩ := Finset.card_eq_one.mp hAB_card
  obtain ⟨v_bc, hv_bc⟩ := Finset.card_eq_one.mp hBC_card
  obtain ⟨v_cd, hv_cd⟩ := Finset.card_eq_one.mp hCD_card
  obtain ⟨v_da, hv_da⟩ := Finset.card_eq_one.mp hDA_card

  -- 8 spokes: 2 from each shared vertex cover all triangles
  -- triangles_containing_v_covered_by_spokes gives us the cover for each vertex
  -- cycle4_all_triangles_contain_shared shows every triangle contains some shared vertex
  -- Therefore union of 4 × 2 = 8 spokes covers everything

  sorry

end
