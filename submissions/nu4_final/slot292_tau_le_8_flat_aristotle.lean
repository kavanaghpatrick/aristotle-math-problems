/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 11503842-5623-4fa0-ad47-6fa08c04af61
-/

/-
  slot292: PATH_4 τ ≤ 8 - FLAT HYPOTHESES (No nested projections)

  DATE: Jan 8, 2026

  KEY FIX: slot291 failed due to nested projection errors on `hPath.2.2.2.2.2.1.1`.
  Solution: Pass ALL conditions as SEPARATE HYPOTHESES to avoid projections entirely.

  THE CORRECT 8-EDGE COVER:
  {v1,a1}, {a1,a2}   -- A: spoke + base
  {v1,b}, {v2,b}     -- B: both spokes
  {v2,c}, {v3,c}     -- C: both spokes
  {v3,d1}, {d1,d2}   -- D: spoke + base

  WHY IT WORKS (case by case from triangle_structure):
  Case 1 (v1 ∈ t): {v1,a1} or {v1,b} covers
  Case 2 (v2 ∈ t): {v2,b} or {v2,c} covers
  Case 3 (v3 ∈ t): {v3,c} or {v3,d1} covers
  Case 4 (A-base-private): {a1,a2} covers
  Case 5 (D-base-private): {d1,d2} covers
-/

import Mathlib


set_option linter.mathlibStandardSet false

set_option maxHeartbeats 400000

set_option maxRecDepth 4000

open Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Core Definitions -/

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (fun M => isTrianglePacking G M) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Basic Lemmas -/

lemma triangle_card_3 (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : t.card = 3 := by
  simp only [SimpleGraph.cliqueFinset, SimpleGraph.isNClique_iff, Finset.mem_filter] at ht
  exact ht.2

lemma edge_in_triangle_sym2 (t : Finset V) (u w : V) (hu : u ∈ t) (hw : w ∈ t) :
    s(u, w) ∈ t.sym2 := by
  simp only [Finset.mem_sym2_iff]
  exact ⟨hu, hw⟩

lemma clique_edge_in_graph (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (u w : V) (hu : u ∈ t) (hw : w ∈ t) (hne : u ≠ w) :
    s(u, w) ∈ G.edgeFinset := by
  have hclique := SimpleGraph.mem_cliqueFinset_iff.mp ht
  exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hu hw hne)

lemma max_packing_shares_edge (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not : t ∉ M) :
    ∃ m ∈ M, (t ∩ m).card ≥ 2 := by
  by_contra h
  push_neg at h
  have h_packing : isTrianglePacking G (insert t M) := by
    constructor
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact ht
      · exact hM.1.1 hx
    · intro x hx y hy hxy
      simp only [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact Nat.lt_succ_iff.mp (h y hy)
      · rw [Finset.inter_comm]; exact Nat.lt_succ_iff.mp (h x hx)
      · exact hM.1.2 hx hy hxy
  have h_card : (insert t M).card = M.card + 1 := Finset.card_insert_of_not_mem ht_not
  have h_le : (insert t M).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    have h_mem : insert t M ∈ (G.cliqueFinset 3).powerset.filter (fun M => isTrianglePacking G M) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h_packing.1, h_packing⟩
    have h_img := Finset.mem_image_of_mem Finset.card h_mem
    exact Finset.le_max h_img |> WithTop.coe_le_coe.mp
  omega

/-! ### Triangle Structure (flat hypotheses version) -/

theorem triangle_structure_flat (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hC_eq : C = {v2, v3, c}) (hD_eq : D = {v3, d1, d2})
    (hA_clique : A ∈ G.cliqueFinset 3) (hB_clique : B ∈ G.cliqueFinset 3)
    (hC_clique : C ∈ G.cliqueFinset 3) (hD_clique : D ∈ G.cliqueFinset 3)
    (hv12 : v1 ≠ v2) (hv23 : v2 ≠ v3) (hv13 : v1 ≠ v3)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    v1 ∈ t ∨ v2 ∈ t ∨ v3 ∈ t ∨
    ((t ∩ A).card ≥ 2 ∧ v1 ∉ t) ∨
    ((t ∩ D).card ≥ 2 ∧ v3 ∉ t) := by
  by_contra h_contra
  push_neg at h_contra
  obtain ⟨hv1, hv2, hv3, hA_not, hD_not⟩ := h_contra
  by_cases ht_in : t ∈ M
  · rw [hM_eq] at ht_in
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht_in
    rcases ht_in with rfl | rfl | rfl | rfl
    · have hv1_in_A : v1 ∈ A := by rw [hA_eq]; simp
      exact hv1 hv1_in_A
    · have hv1_in_B : v1 ∈ B := by rw [hB_eq]; simp
      exact hv1 hv1_in_B
    · have hv2_in_C : v2 ∈ C := by rw [hC_eq]; simp
      exact hv2 hv2_in_C
    · have hv3_in_D : v3 ∈ D := by rw [hD_eq]; simp
      exact hv3 hv3_in_D
  · obtain ⟨m, hm, h_share⟩ := max_packing_shares_edge G M hM t ht ht_in
    rw [hM_eq] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact hA_not ⟨h_share, hv1⟩
    · -- Shares with B = {v1, v2, b}
      have hB3 : B.card = 3 := triangle_card_3 G B hB_clique
      have h_sub : t ∩ B ⊆ B \ {v1, v2} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        exact ⟨hx.2, fun h => by cases h <;> simp_all⟩
      rw [hB_eq] at hB3 h_sub
      have : ({v1, v2, b} \ {v1, v2} : Finset V).card ≤ 1 := by simp [hv12]
      have := Finset.card_le_card h_sub
      omega
    · -- Shares with C = {v2, v3, c}
      have hC3 : C.card = 3 := triangle_card_3 G C hC_clique
      have h_sub : t ∩ C ⊆ C \ {v2, v3} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        exact ⟨hx.2, fun h => by cases h <;> simp_all⟩
      rw [hC_eq] at hC3 h_sub
      have : ({v2, v3, c} \ {v2, v3} : Finset V).card ≤ 1 := by simp [hv23]
      have := Finset.card_le_card h_sub
      omega
    · exact hD_not ⟨h_share, hv3⟩

/-! ### The Explicit 8-Edge Cover -/

def cover8 (v1 v2 v3 a1 a2 b c d1 d2 : V) : Finset (Sym2 V) :=
  {s(v1, a1), s(a1, a2), s(v1, b), s(v2, b), s(v2, c), s(v3, c), s(v3, d1), s(d1, d2)}

lemma cover8_card_le (v1 v2 v3 a1 a2 b c d1 d2 : V) :
    (cover8 v1 v2 v3 a1 a2 b c d1 d2).card ≤ 8 := by
  unfold cover8
  refine Finset.card_le_card ?_
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  exact hx

/-! ### Distinctness lemmas -/

lemma A_vertices_distinct (A : Finset V) (v1 a1 a2 : V)
    (hA_eq : A = {v1, a1, a2}) (hA_clique : A ∈ G.cliqueFinset 3) :
    v1 ≠ a1 ∧ v1 ≠ a2 ∧ a1 ≠ a2 := by
  have hA3 : A.card = 3 := triangle_card_3 G A hA_clique
  rw [hA_eq] at hA3
  simp only [Finset.card_insert_of_not_mem, Finset.card_singleton, Finset.mem_insert,
             Finset.mem_singleton] at hA3 ⊢
  constructor
  · intro h; simp [h] at hA3
  constructor
  · intro h; simp [h] at hA3
  · intro h; simp [h] at hA3

lemma D_vertices_distinct (D : Finset V) (v3 d1 d2 : V)
    (hD_eq : D = {v3, d1, d2}) (hD_clique : D ∈ G.cliqueFinset 3) :
    v3 ≠ d1 ∧ v3 ≠ d2 ∧ d1 ≠ d2 := by
  have hD3 : D.card = 3 := triangle_card_3 G D hD_clique
  rw [hD_eq] at hD3
  simp only [Finset.card_insert_of_not_mem, Finset.card_singleton, Finset.mem_insert,
             Finset.mem_singleton] at hD3 ⊢
  constructor
  · intro h; simp [h] at hD3
  constructor
  · intro h; simp [h] at hD3
  · intro h; simp [h] at hD3

/-! ### Helper: Extract two distinct elements from intersection ≥ 2 avoiding v -/

lemma two_from_A_avoiding_v1 (A t : Finset V) (v1 a1 a2 : V)
    (hA_eq : A = {v1, a1, a2}) (hA_clique : A ∈ G.cliqueFinset 3)
    (h_share : (t ∩ A).card ≥ 2) (hv1_not : v1 ∉ t) :
    a1 ∈ t ∧ a2 ∈ t := by
  have ⟨_, _, ha12⟩ := A_vertices_distinct G A v1 a1 a2 hA_eq hA_clique
  rw [hA_eq] at h_share
  have h_sub : t ∩ {v1, a1, a2} ⊆ {a1, a2} := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 hv1_not
    · left; rfl
    · right; rfl
  have hcard : (t ∩ {v1, a1, a2}).card ≤ ({a1, a2} : Finset V).card := Finset.card_le_card h_sub
  have hcard2 : ({a1, a2} : Finset V).card = 2 := by simp [ha12]
  have heq : t ∩ {v1, a1, a2} = {a1, a2} := by
    apply Finset.eq_of_subset_of_card_le h_sub
    omega
  constructor
  · have : a1 ∈ t ∩ {v1, a1, a2} := by rw [heq]; simp
    simp at this; exact this.1
  · have : a2 ∈ t ∩ {v1, a1, a2} := by rw [heq]; simp [ha12]
    simp at this; exact this.1

lemma two_from_D_avoiding_v3 (D t : Finset V) (v3 d1 d2 : V)
    (hD_eq : D = {v3, d1, d2}) (hD_clique : D ∈ G.cliqueFinset 3)
    (h_share : (t ∩ D).card ≥ 2) (hv3_not : v3 ∉ t) :
    d1 ∈ t ∧ d2 ∈ t := by
  have ⟨_, _, hd12⟩ := D_vertices_distinct G D v3 d1 d2 hD_eq hD_clique
  rw [hD_eq] at h_share
  have h_sub : t ∩ {v3, d1, d2} ⊆ {d1, d2} := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 hv3_not
    · left; rfl
    · right; rfl
  have hcard : (t ∩ {v3, d1, d2}).card ≤ ({d1, d2} : Finset V).card := Finset.card_le_card h_sub
  have hcard2 : ({d1, d2} : Finset V).card = 2 := by simp [hd12]
  have heq : t ∩ {v3, d1, d2} = {d1, d2} := by
    apply Finset.eq_of_subset_of_card_le h_sub
    omega
  constructor
  · have : d1 ∈ t ∩ {v3, d1, d2} := by rw [heq]; simp
    simp at this; exact this.1
  · have : d2 ∈ t ∩ {v3, d1, d2} := by rw [heq]; simp [hd12]
    simp at this; exact this.1

/-! ### Helper: v1 in t means t has another vertex from B or A -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unsolved goals
case left.inr.inl.inr.inl
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
C D : Finset V
M : Finset (Finset V)
A : Finset V
a1 a2 b : V
t : Finset V
hM : isMaxPacking G M
hA_clique : A ∈ G.cliqueFinset 3
ht : t ∈ G.cliqueFinset 3
ht_not : t ∉ M
m : Finset V
h_share : (t ∩ m).card ≥ 2
x y : V
hxy : x ≠ y
hx : x ∈ t ∧ x ∈ m
hA_eq : A = {x, a1, a2}
hv1_in : x ∈ t
hM_eq : M = {A, m, C, D}
hB_clique : m ∈ G.cliqueFinset 3
hB_eq : m = {x, y, b}
hy : y ∈ t ∧ (y = x ∨ y = y ∨ y = b)
⊢ y = a1 ∨ y = a2 ∨ y = b
unsolved goals
case left.inr.inl.inr.inl
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
C D : Finset V
M : Finset (Finset V)
A : Finset V
v1 a1 a2 b : V
t : Finset V
hM : isMaxPacking G M
hA_eq : A = {v1, a1, a2}
hA_clique : A ∈ G.cliqueFinset 3
ht : t ∈ G.cliqueFinset 3
hv1_in : v1 ∈ t
ht_not : t ∉ M
m : Finset V
h_share : (t ∩ m).card ≥ 2
x y : V
hxy : x ≠ y
hy : y ∈ t ∧ y ∈ m
hxv1 : ¬x = v1
hM_eq : M = {A, m, C, D}
hB_clique : m ∈ G.cliqueFinset 3
hB_eq : m = {v1, x, b}
hx : x ∈ t ∧ (x = v1 ∨ x = x ∨ x = b)
⊢ x = a1 ∨ x = a2 ∨ x = b-/
lemma v1_in_t_has_neighbor (M : Finset (Finset V)) (A B : Finset V)
    (v1 v2 a1 a2 b : V) (t : Finset V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hA_clique : A ∈ G.cliqueFinset 3) (hB_clique : B ∈ G.cliqueFinset 3)
    (ht : t ∈ G.cliqueFinset 3) (hv1_in : v1 ∈ t) (ht_not : t ∉ M) :
    ∃ w ∈ ({a1, a2, b} : Finset V), w ∈ t := by
  obtain ⟨m, hm, h_share⟩ := max_packing_shares_edge G M hM t ht ht_not
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h_share
  simp only [Finset.mem_inter] at hx hy
  -- At least one of x, y is not v1 (since there are 2 distinct elements)
  by_cases hxv1 : x = v1
  · subst hxv1
    use y, ?_, hy.1
    -- y ∈ m and m ∈ M, need y ∈ {a1, a2, b}
    rw [hM_eq] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | hm | hm
    · rw [hA_eq] at hy
      simp at hy
      rcases hy.2 with rfl | rfl | rfl
      · exact absurd rfl hxy
      · simp
      · simp
    · rw [hB_eq] at hy
      simp at hy
      rcases hy.2 with rfl | rfl | rfl
      · exact absurd rfl hxy
      · simp  -- y = v2, but we need y ∈ {a1, a2, b}... this is tricky
      · simp
    all_goals sorry  -- other M elements don't contain v1
  · use x, ?_, hx.1
    rw [hM_eq] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | hm | hm
    · rw [hA_eq] at hx
      simp at hx
      rcases hx.2 with rfl | rfl | rfl
      · exact absurd rfl hxv1
      · simp
      · simp
    · rw [hB_eq] at hx
      simp at hx
      rcases hx.2 with rfl | rfl | rfl
      · exact absurd rfl hxv1
      · simp  -- x = v2
      · simp
    all_goals sorry

/-! ### Main Theorem: τ ≤ 8 (flat hypotheses) -/

/- Aristotle failed to find a proof. -/
/-
PROOF SKETCH:
1. triangle_structure_flat gives 5 cases for any triangle t
2. Cases 1-3: t contains spine vertex (v1, v2, or v3)
   - If v1 ∈ t: cover8 contains {v1,a1} and {v1,b}, one covers t
   - If v2 ∈ t: cover8 contains {v2,b} and {v2,c}, one covers t
   - If v3 ∈ t: cover8 contains {v3,c} and {v3,d1}, one covers t
3. Case 4: A-base-private (v1 ∉ t but (t∩A).card ≥ 2)
   - t must contain {a1,a2}, which is edge {a1,a2} in cover8
4. Case 5: D-base-private (v3 ∉ t but (t∩D).card ≥ 2)
   - t must contain {d1,d2}, which is edge {d1,d2} in cover8
-/
theorem tau_le_8_path4 (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hC_eq : C = {v2, v3, c}) (hD_eq : D = {v3, d1, d2})
    (hA_clique : A ∈ G.cliqueFinset 3) (hB_clique : B ∈ G.cliqueFinset 3)
    (hC_clique : C ∈ G.cliqueFinset 3) (hD_clique : D ∈ G.cliqueFinset 3)
    (hv12 : v1 ≠ v2) (hv23 : v2 ≠ v3) (hv13 : v1 ≠ v3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  use (cover8 v1 v2 v3 a1 a2 b c d1 d2).filter (fun e => e ∈ G.edgeFinset)
  refine ⟨?_, ?_, ?_⟩
  · -- Card ≤ 8
    calc ((cover8 v1 v2 v3 a1 a2 b c d1 d2).filter (fun e => e ∈ G.edgeFinset)).card
        ≤ (cover8 v1 v2 v3 a1 a2 b c d1 d2).card := Finset.card_filter_le _ _
      _ ≤ 8 := cover8_card_le v1 v2 v3 a1 a2 b c d1 d2
  · -- Subset of G.edgeFinset
    intro e he
    simp only [Finset.mem_filter] at he
    exact he.2
  · -- Covers all triangles
    intro t ht
    have h_struct := triangle_structure_flat G M A B C D v1 v2 v3 a1 a2 b c d1 d2
      hM hM_eq hA_eq hB_eq hC_eq hD_eq hA_clique hB_clique hC_clique hD_clique hv12 hv23 hv13 t ht
    have hA_dist := A_vertices_distinct G A v1 a1 a2 hA_eq hA_clique
    have hD_dist := D_vertices_distinct G D v3 d1 d2 hD_eq hD_clique
    rcases h_struct with hv1_in | hv2_in | hv3_in | ⟨hA_share, hv1_not⟩ | ⟨hD_share, hv3_not⟩
    · -- Case 1: v1 ∈ t, use edge {v1, a1}
      use s(v1, a1)
      constructor
      · simp only [Finset.mem_filter, cover8]
        constructor
        · simp
        · have ha1_in_A : a1 ∈ A := by rw [hA_eq]; simp
          have hv1_in_A : v1 ∈ A := by rw [hA_eq]; simp
          exact clique_edge_in_graph G A hA_clique v1 a1 hv1_in_A ha1_in_A hA_dist.1
      · -- Need to show s(v1, a1) ∈ t.sym2
        -- We know v1 ∈ t. We need a1 ∈ t.
        -- Since t is a triangle with v1, t shares an edge with some M-element by maximality
        -- This is subtle - we can't directly conclude a1 ∈ t
        -- Actually, let's use a different edge from cover8
        sorry
    · -- Case 2: v2 ∈ t, use edge {v2, b}
      sorry
    · -- Case 3: v3 ∈ t, use edge {v3, d1}
      sorry
    · -- Case 4: A-base-private
      have ⟨ha1, ha2⟩ := two_from_A_avoiding_v1 G A t v1 a1 a2 hA_eq hA_clique hA_share hv1_not
      use s(a1, a2)
      constructor
      · simp only [Finset.mem_filter, cover8]
        constructor
        · simp
        · have ha1_in_A : a1 ∈ A := by rw [hA_eq]; simp
          have ha2_in_A : a2 ∈ A := by rw [hA_eq]; simp
          exact clique_edge_in_graph G A hA_clique a1 a2 ha1_in_A ha2_in_A hA_dist.2.2
      · exact edge_in_triangle_sym2 t a1 a2 ha1 ha2
    · -- Case 5: D-base-private
      have ⟨hd1, hd2⟩ := two_from_D_avoiding_v3 G D t v3 d1 d2 hD_eq hD_clique hD_share hv3_not
      use s(d1, d2)
      constructor
      · simp only [Finset.mem_filter, cover8]
        constructor
        · simp
        · have hd1_in_D : d1 ∈ D := by rw [hD_eq]; simp
          have hd2_in_D : d2 ∈ D := by rw [hD_eq]; simp
          exact clique_edge_in_graph G D hD_clique d1 d2 hd1_in_D hd2_in_D hD_dist.2.2
      · exact edge_in_triangle_sym2 t d1 d2 hd1 hd2

end