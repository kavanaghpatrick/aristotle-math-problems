/-
Tuza ν=4 - Slot 57: PATH_4 Case via 8-Edge Cover Construction

PROBLEM: Prove τ(G) ≤ 8 when ν(G) = 4 and packing forms a path A—B—C—D.

KEY INSIGHT (from AI consultation):
Partition triangles by which shared vertices they contain:
- V_ab = triangles containing v_ab
- V_bc = triangles containing v_bc
- V_cd = triangles containing v_cd
- V_none = triangles containing none of v_ab, v_bc, v_cd

Analysis:
- Triangles sharing edge with B: edges are (v_ab, v_bc), (v_ab, b1), (v_bc, b1)
  All contain v_ab OR v_bc. So T_B ⊆ V_ab ∪ V_bc.
- Similarly T_C ⊆ V_bc ∪ V_cd.
- V_none only contains triangles sharing "base edges" (a1,a2) or (d1,d2).

8-EDGE COVER:
1. (a1, a2): 1 edge - covers V_none ∩ T_A
2. (d1, d2): 1 edge - covers V_none ∩ T_D
3. 2 spokes from v_ab: covers V_ab
4. 2 spokes from v_bc: covers V_bc
5. 2 spokes from v_cd: covers V_cd

Total: 1 + 1 + 2 + 2 + 2 = 8 edges

SCAFFOLDING: Proven lemmas from slot49
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

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- TRIANGLES CONTAINING VERTEX v ARE COVERED BY SPOKES
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles containing a specific vertex v -/
def trianglesContainingVertex (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

/--
If G.Adj v u for all neighbors u of v in the graph, then triangles containing v
are covered by edges incident to v.
-/
lemma triangles_containing_v_covered_by_spokes (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hv : (G.neighborFinset v).card ≥ 2) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ (G.neighborFinset v).card ∧ E' ⊆ G.edgeFinset ∧
    ∀ t ∈ trianglesContainingVertex G v, ∃ e ∈ E', e ∈ t.sym2 := by
  -- The spokes are all edges (v, u) for u ∈ G.neighborFinset v
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
    -- t is a triangle containing v
    have ⟨hclique, hcard⟩ := ht.1
    have hv_in_t := ht.2
    -- Since t is a triangle containing v, there's another vertex u in t with G.Adj v u
    obtain ⟨x, y, z, hxyz⟩ := Finset.card_eq_three.mp hcard
    rw [hxyz.2.2.2] at hv_in_t
    simp at hv_in_t
    rcases hv_in_t with rfl | rfl | rfl
    · -- v = x
      use s(x, y)
      constructor
      · simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
        exact ⟨y, hclique (by rw [hxyz.2.2.2]; simp) (by rw [hxyz.2.2.2]; simp) hxyz.1, rfl⟩
      · rw [hxyz.2.2.2]; simp [Sym2.mem_iff]
    · -- v = y
      use s(y, x)
      constructor
      · simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
        refine ⟨x, ?_, ?_⟩
        · rw [SimpleGraph.adj_comm]
          exact hclique (by rw [hxyz.2.2.2]; simp) (by rw [hxyz.2.2.2]; simp) hxyz.1
        · rw [Sym2.eq_swap]
      · rw [hxyz.2.2.2]; simp [Sym2.mem_iff]
    · -- v = z
      use s(z, x)
      constructor
      · simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
        refine ⟨x, ?_, ?_⟩
        · rw [SimpleGraph.adj_comm]
          exact hclique (by rw [hxyz.2.2.2]; simp) (by rw [hxyz.2.2.2]; simp) hxyz.2.1
        · rw [Sym2.eq_swap]
      · rw [hxyz.2.2.2]; simp [Sym2.mem_iff]

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH4 STRUCTURE LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle sharing edge with A either contains v_ab or shares edge (a1,a2) -/
lemma path4_T_A_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    (v_ab a1 a2 : V) (hA_eq : A = {v_ab, a1, a2})
    (hvab : A ∩ B = {v_ab}) (ha_ne : v_ab ≠ a1 ∧ v_ab ≠ a2 ∧ a1 ≠ a2)
    (t : Finset V) (ht : t ∈ trianglesSharingEdge G A) :
    v_ab ∈ t ∨ (a1 ∈ t ∧ a2 ∈ t) := by
  simp only [trianglesSharingEdge, Finset.mem_filter] at ht
  have h_share : (t ∩ A).card ≥ 2 := ht.2
  rw [hA_eq] at h_share
  -- t shares ≥2 vertices with {v_ab, a1, a2}
  -- Either v_ab ∈ t, or {a1, a2} ⊆ t
  by_cases hvab_in : v_ab ∈ t
  · left; exact hvab_in
  · right
    -- t ∩ {v_ab, a1, a2} has ≥2 elements, v_ab ∉ t
    -- So t ∩ {v_ab, a1, a2} ⊆ {a1, a2} and has ≥2 elements
    -- Therefore t ∩ {v_ab, a1, a2} = {a1, a2}
    have hsub : t ∩ {v_ab, a1, a2} ⊆ {a1, a2} := by
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx.2 with rfl | rfl | rfl
      · exact absurd hx.1 hvab_in
      · left; rfl
      · right; rfl
    have hcard_sub : ({a1, a2} : Finset V).card = 2 := by simp [ha_ne.2.2]
    have hcard_eq : (t ∩ {v_ab, a1, a2}).card = 2 := by
      have hle : (t ∩ {v_ab, a1, a2}).card ≤ 2 := by
        calc (t ∩ {v_ab, a1, a2}).card ≤ ({a1, a2} : Finset V).card := Finset.card_le_card hsub
          _ = 2 := hcard_sub
      omega
    have heq : t ∩ {v_ab, a1, a2} = {a1, a2} := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [hcard_sub, hcard_eq]
    constructor
    · have : a1 ∈ t ∩ {v_ab, a1, a2} := by rw [heq]; simp
      exact Finset.mem_inter.mp this |>.1
    · have : a2 ∈ t ∩ {v_ab, a1, a2} := by rw [heq]; simp
      exact Finset.mem_inter.mp this |>.1

/-- Every triangle sharing edge with B contains v_ab or v_bc -/
lemma path4_T_B_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    (v_ab v_bc b1 : V) (hB_eq : B = {v_ab, v_bc, b1})
    (t : Finset V) (ht : t ∈ trianglesSharingEdge G B) :
    v_ab ∈ t ∨ v_bc ∈ t := by
  simp only [trianglesSharingEdge, Finset.mem_filter] at ht
  have h_share : (t ∩ B).card ≥ 2 := ht.2
  rw [hB_eq] at h_share
  -- t shares ≥2 vertices with {v_ab, v_bc, b1}
  -- Every pair from {v_ab, v_bc, b1} contains v_ab or v_bc
  by_contra h_neither
  push_neg at h_neither
  -- t doesn't contain v_ab or v_bc, so t ∩ {v_ab, v_bc, b1} ⊆ {b1}
  have hsub : t ∩ {v_ab, v_bc, b1} ⊆ {b1} := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 h_neither.1
    · exact absurd hx.1 h_neither.2
    · rfl
  have hcard : (t ∩ {v_ab, v_bc, b1}).card ≤ 1 := by
    calc (t ∩ {v_ab, v_bc, b1}).card ≤ ({b1} : Finset V).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton b1
  omega

/-- Similarly for C -/
lemma path4_T_C_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    (v_bc v_cd c1 : V) (hC_eq : C = {v_bc, v_cd, c1})
    (t : Finset V) (ht : t ∈ trianglesSharingEdge G C) :
    v_bc ∈ t ∨ v_cd ∈ t := by
  simp only [trianglesSharingEdge, Finset.mem_filter] at ht
  have h_share : (t ∩ C).card ≥ 2 := ht.2
  rw [hC_eq] at h_share
  by_contra h_neither
  push_neg at h_neither
  have hsub : t ∩ {v_bc, v_cd, c1} ⊆ {c1} := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 h_neither.1
    · exact absurd hx.1 h_neither.2
    · rfl
  have hcard : (t ∩ {v_bc, v_cd, c1}).card ≤ 1 := by
    calc (t ∩ {v_bc, v_cd, c1}).card ≤ ({c1} : Finset V).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton c1
  omega

/-- Similarly for D -/
lemma path4_T_D_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    (v_cd d1 d2 : V) (hD_eq : D = {v_cd, d1, d2})
    (hvcd : C ∩ D = {v_cd}) (hd_ne : v_cd ≠ d1 ∧ v_cd ≠ d2 ∧ d1 ≠ d2)
    (t : Finset V) (ht : t ∈ trianglesSharingEdge G D) :
    v_cd ∈ t ∨ (d1 ∈ t ∧ d2 ∈ t) := by
  simp only [trianglesSharingEdge, Finset.mem_filter] at ht
  have h_share : (t ∩ D).card ≥ 2 := ht.2
  rw [hD_eq] at h_share
  by_cases hvcd_in : v_cd ∈ t
  · left; exact hvcd_in
  · right
    have hsub : t ∩ {v_cd, d1, d2} ⊆ {d1, d2} := by
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx.2 with rfl | rfl | rfl
      · exact absurd hx.1 hvcd_in
      · left; rfl
      · right; rfl
    have hcard_sub : ({d1, d2} : Finset V).card = 2 := by simp [hd_ne.2.2]
    have hcard_eq : (t ∩ {v_cd, d1, d2}).card = 2 := by
      have hle : (t ∩ {v_cd, d1, d2}).card ≤ 2 := by
        calc (t ∩ {v_cd, d1, d2}).card ≤ ({d1, d2} : Finset V).card := Finset.card_le_card hsub
          _ = 2 := hcard_sub
      omega
    have heq : t ∩ {v_cd, d1, d2} = {d1, d2} := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [hcard_sub, hcard_eq]
    constructor
    · have : d1 ∈ t ∩ {v_cd, d1, d2} := by rw [heq]; simp
      exact Finset.mem_inter.mp this |>.1
    · have : d2 ∈ t ∩ {v_cd, d1, d2} := by rw [heq]; simp
      exact Finset.mem_inter.mp this |>.1

-- ══════════════════════════════════════════════════════════════════════════════
-- NO LOOSE TRIANGLES (every triangle shares edge with packing)
-- ══════════════════════════════════════════════════════════════════════════════

lemma path4_no_loose_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    t ∈ trianglesSharingEdge G A ∨ t ∈ trianglesSharingEdge G B ∨
    t ∈ trianglesSharingEdge G C ∨ t ∈ trianglesSharingEdge G D := by
  by_contra h_none
  push_neg at h_none
  -- t doesn't share edge with any packing element
  -- This contradicts maximality: we could add t to M
  simp only [trianglesSharingEdge, Finset.mem_filter, not_and, not_le] at h_none
  have h_disj_A : (t ∩ A).card ≤ 1 := Nat.lt_succ_iff.mp (h_none.1 ht)
  have h_disj_B : (t ∩ B).card ≤ 1 := Nat.lt_succ_iff.mp (h_none.2.1 ht)
  have h_disj_C : (t ∩ C).card ≤ 1 := Nat.lt_succ_iff.mp (h_none.2.2.1 ht)
  have h_disj_D : (t ∩ D).card ≤ 1 := Nat.lt_succ_iff.mp (h_none.2.2.2 ht)
  -- M ∪ {t} would be a larger packing
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
      · rw [hpath.1] at hxM
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxM
        rcases hxM with rfl | rfl | rfl | rfl
        · exact h_disj_A
        · exact h_disj_B
        · exact h_disj_C
        · exact h_disj_D
      · rw [hpath.1] at hyM
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyM
        rcases hyM with rfl | rfl | rfl | rfl <;> rw [Finset.inter_comm]
        · exact h_disj_A
        · exact h_disj_B
        · exact h_disj_C
        · exact h_disj_D
      · exact absurd rfl hxy
  have h_card : (M ∪ {t}).card > M.card := by
    have ht_not : t ∉ M := by
      intro ht_in
      rw [hpath.1] at ht_in
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht_in
      rcases ht_in with rfl | rfl | rfl | rfl
      · have : (A ∩ A).card ≤ 1 := h_disj_A
        simp at this
        have := (SimpleGraph.mem_cliqueFinset_iff.mp ht).2
        omega
      · have : (B ∩ B).card ≤ 1 := h_disj_B
        simp at this
        have := (SimpleGraph.mem_cliqueFinset_iff.mp ht).2
        omega
      · have : (C ∩ C).card ≤ 1 := h_disj_C
        simp at this
        have := (SimpleGraph.mem_cliqueFinset_iff.mp ht).2
        omega
      · have : (D ∩ D).card ≤ 1 := h_disj_D
        simp at this
        have := (SimpleGraph.mem_cliqueFinset_iff.mp ht).2
        omega
    simp [ht_not]
  -- This contradicts maximality of M
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
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/--
Main theorem: τ(G) ≤ 8 for PATH_4 case.

The proof constructs an 8-edge cover based on partitioning triangles by shared vertices.
For Aristotle to complete the explicit cover construction.
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  -- The proof strategy:
  -- 1. Extract vertex structure of A, B, C, D
  -- 2. Partition triangles into V_ab, V_bc, V_cd, V_none
  -- 3. Show V_none is covered by base edges (a1,a2) and (d1,d2)
  -- 4. Show V_ab, V_bc, V_cd are covered by spokes
  -- 5. Total: 1 + 1 + 2 + 2 + 2 = 8 edges

  -- For Aristotle: construct the explicit 8-edge cover and verify coverage
  sorry

end
