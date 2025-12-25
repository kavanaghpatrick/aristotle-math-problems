/-
Tuza ν=4 Strategy - Slot 58: PATH_4 via Unified Approach

FIXES FROM AI DEBATE (Dec 25, 2025):
1. Port proven `triangle_shares_edge_with_packing` from slot127 (scattered_case)
2. Add `triangleCoveringNumberOn_subset` monotonicity lemma
3. Use tau_pair_le_4 (from slot35) for adjacent pairs sharing exactly one vertex

STRATEGY:
For PATH_4 (A—B—C—D with shared vertices v_ab, v_bc, v_cd):
1. Every triangle shares edge with some packing element (maximality)
2. T_left = T_pair(A,B), T_right = T_pair(C,D)
3. All triangles ⊆ T_left ∪ T_right (path covers all)
4. τ(T_left) ≤ 4 (tau_pair_le_4 with shared v_ab)
5. τ(T_right) ≤ 4 (tau_pair_le_4 with shared v_cd)
6. τ(all) ≤ 8

KEY INSIGHT (from Gemini): Non-adjacent pairs (A,C) and (A,D) are vertex-disjoint,
so no triangle can share edges with both A and C (or A and D).
Thus every triangle is in T_A ∪ T_B OR T_C ∪ T_D.
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

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧
  (B ∩ C).card = 1 ∧
  (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧
  (A ∩ D).card = 0 ∧
  (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

-- τ(A ∪ B) ≤ τ(A) + τ(B) (PROVEN in slot16, uuid b4f73fa3)
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- SCAFFOLDING: Proven by Aristotle in slot16

-- NEW: Monotonicity for covering number (standard result)
lemma triangleCoveringNumberOn_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset (Finset V)) (hST : S ⊆ T) :
    triangleCoveringNumberOn G S ≤ triangleCoveringNumberOn G T := by
  -- Any cover for T is also a cover for S (since S ⊆ T)
  -- So min over covers of S ≤ min over covers of T
  sorry -- TARGET: Standard subset argument

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Every triangle shares edge with packing (PROVEN in slot127)
-- ══════════════════════════════════════════════════════════════════════════════

/-- If a triangle t shares no edge with any packing element (≤1 vertex with each),
    then t could be added to M, contradicting maximality.

    Proof adapted from slot127 (scattered_case.lean, lines 194-255). -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_in_M : t ∉ M) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  by_contra h
  push_neg at h
  -- Then M ∪ {t} is a valid packing (t shares ≤1 with each element)
  have h_can_add : isTrianglePacking G (M ∪ {t}) := by
    constructor
    · -- M ∪ {t} ⊆ triangles
      intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton] at hx
      rcases hx with hxM | rfl
      · exact hM.1.1 hxM
      · exact ht
    · -- Pairwise edge-disjoint
      intro x hx y hy hxy
      simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff] at hx hy
      rcases hx with hx_in_M | hx_eq_t
      · rcases hy with hy_in_M | hy_eq_t
        · exact hM.1.2 hx_in_M hy_in_M hxy
        · subst hy_eq_t
          have h_lt := h x hx_in_M
          rw [Finset.inter_comm] at h_lt
          omega
      · subst hx_eq_t
        rcases hy with hy_in_M | hy_eq_t
        · have h_lt := h y hy_in_M
          omega
        · subst hy_eq_t; exact absurd rfl hxy
  -- But |M ∪ {t}| = M.card + 1 > ν(G) = M.card
  have h_card : (M ∪ {t}).card = M.card + 1 := by
    rw [Finset.card_union_of_disjoint]
    · simp
    · simp [ht_not_in_M]
  have h_exceeds : (M ∪ {t}).card > trianglePackingNumber G := by
    rw [h_card, hM.2]
    omega
  -- Contradiction: M ∪ {t} is a valid packing larger than ν(G)
  have h_le : (M ∪ {t}).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    have h_mem : M ∪ {t} ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h_can_add.1, h_can_add⟩
    have h_in_image : (M ∪ {t}).card ∈ ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card :=
      Finset.mem_image_of_mem Finset.card h_mem
    have h_le_max := Finset.le_max h_in_image
    cases hmax : ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card |>.max with
    | bot =>
      exfalso
      have : (M ∪ {t}).card ∈ ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card := h_in_image
      rw [Finset.max_eq_bot] at hmax
      exact Finset.eq_empty_iff_forall_not_mem.mp hmax _ this
    | coe n =>
      simp only [Option.getD]
      rw [hmax] at h_le_max
      exact WithBot.coe_le_coe.mp h_le_max
  linarith

/-- Version that handles both t ∈ M and t ∉ M -/
lemma triangle_shares_edge_with_packing' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  by_cases ht_M : t ∈ M
  · -- t ∈ M → t shares all 3 vertices with itself
    use t, ht_M
    simp only [Finset.inter_self]
    have h_t_card : t.card = 3 := by
      simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht
      exact ht.2
    omega
  · exact triangle_shares_edge_with_packing G M hM t ht ht_M

-- ══════════════════════════════════════════════════════════════════════════════
-- tau_pair_le_4 (from slot35, uuid da605278)
-- ══════════════════════════════════════════════════════════════════════════════

/-- When e ∩ f = {v} (exactly one shared vertex), τ(T_pair(e,f)) ≤ 4 -/
theorem tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  sorry -- SCAFFOLDING: Proven by Aristotle in slot35 (uuid da605278)

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 COVERAGE LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- In PATH_4, every triangle is in T_pair(A,B) ∪ T_pair(C,D).

    Key insight: If t shares edge with A or B → t ∈ T_pair(A,B).
    If t shares edge with C or D → t ∈ T_pair(C,D).
    No triangle can share edges with both A and C (they're vertex-disjoint). -/
lemma path4_triangle_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    ∀ t ∈ G.cliqueFinset 3, t ∈ T_pair G A B ∪ T_pair G C D := by
  intro t ht
  -- Every triangle shares edge with some packing element
  obtain ⟨e, heM, h_share⟩ := triangle_shares_edge_with_packing' G M hM t ht
  -- M = {A, B, C, D}, so e is one of A, B, C, D
  have hM_eq : M = {A, B, C, D} := hpath.1
  rw [hM_eq] at heM
  simp only [Finset.mem_insert, Finset.mem_singleton] at heM
  -- t shares edge with e means t ∈ trianglesSharingEdge G e
  have h_t_in_Te : t ∈ trianglesSharingEdge G e := by
    simp only [trianglesSharingEdge, Finset.mem_filter]
    exact ⟨ht, h_share⟩
  -- Case analysis: e ∈ {A, B} or e ∈ {C, D}
  rcases heM with rfl | rfl | rfl | rfl
  · -- e = A
    left
    simp only [T_pair, Finset.mem_union]
    left
    exact h_t_in_Te
  · -- e = B
    left
    simp only [T_pair, Finset.mem_union]
    right
    exact h_t_in_Te
  · -- e = C
    right
    simp only [T_pair, Finset.mem_union]
    left
    exact h_t_in_Te
  · -- e = D
    right
    simp only [T_pair, Finset.mem_union]
    right
    exact h_t_in_Te

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Extract shared vertices
-- ══════════════════════════════════════════════════════════════════════════════

lemma shared_vertex_exists (e f : Finset V) (h : (e ∩ f).card = 1) :
    ∃ v, e ∩ f = {v} := by
  have h_nonempty : (e ∩ f).Nonempty := by
    rw [Finset.card_pos] at h
    exact h
  obtain ⟨v, hv⟩ := h_nonempty
  use v
  ext x
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · intro hx
    have : (e ∩ f) = {v} ∨ (e ∩ f).card > 1 := by
      by_cases heq : e ∩ f = {v}
      · left; exact heq
      · right
        have : {v} ⊂ e ∩ f := by
          rw [Finset.ssubset_iff_of_subset]
          · use x
            exact ⟨hx, fun hxv => heq (Finset.eq_singleton_iff_unique_mem.mpr ⟨hv, fun y hy => by
              rcases Finset.mem_singleton.mp hxv with rfl
              exact Finset.mem_singleton.mpr (Finset.eq_of_mem_singleton (Finset.mem_inter.mp hy).1).symm⟩)⟩
          · exact Finset.singleton_subset_iff.mpr hv
        exact Finset.card_lt_card this
    rcases this with heq | hgt
    · rw [heq] at hx
      exact Finset.mem_singleton.mp hx
    · omega
  · intro hxv
    subst hxv
    exact hv

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: PATH_4 CASE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: If ν = 4 with PATH_4 structure, then τ ≤ 8 -/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  -- Step 1: Get shared vertices
  have hAB_card : (A ∩ B).card = 1 := hpath.2.2.2.2.2.2.1
  have hCD_card : (C ∩ D).card = 1 := hpath.2.2.2.2.2.2.2.2.1
  obtain ⟨v_ab, hv_ab⟩ := shared_vertex_exists A B hAB_card
  obtain ⟨v_cd, hv_cd⟩ := shared_vertex_exists C D hCD_card
  -- Step 2: M membership
  have hM_eq : M = {A, B, C, D} := hpath.1
  have hA_in : A ∈ M := by rw [hM_eq]; simp
  have hB_in : B ∈ M := by rw [hM_eq]; simp
  have hC_in : C ∈ M := by rw [hM_eq]; simp
  have hD_in : D ∈ M := by rw [hM_eq]; simp
  have hAB_ne : A ≠ B := hpath.2.1
  have hCD_ne : C ≠ D := hpath.2.2.2.1
  -- Step 3: Bounds on T_pair
  have h_left : triangleCoveringNumberOn G (T_pair G A B) ≤ 4 :=
    tau_pair_le_4 G M hM A B hA_in hB_in hAB_ne v_ab hv_ab
  have h_right : triangleCoveringNumberOn G (T_pair G C D) ≤ 4 :=
    tau_pair_le_4 G M hM C D hC_in hD_in hCD_ne v_cd hv_cd
  -- Step 4: All triangles are in T_pair(A,B) ∪ T_pair(C,D)
  have h_all : ∀ t ∈ G.cliqueFinset 3, t ∈ T_pair G A B ∪ T_pair G C D :=
    path4_triangle_cover G M hM A B C D hpath
  -- Step 5: τ(all triangles) ≤ τ(union) ≤ τ(left) + τ(right) ≤ 4 + 4 = 8
  have h_subset : G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D := fun t ht => h_all t ht
  have h_mono : triangleCoveringNumberOn G (G.cliqueFinset 3) ≤
      triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) :=
    triangleCoveringNumberOn_mono G (G.cliqueFinset 3) (T_pair G A B ∪ T_pair G C D) h_subset
  have h_union : triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) ≤
      triangleCoveringNumberOn G (T_pair G A B) + triangleCoveringNumberOn G (T_pair G C D) :=
    tau_union_le_sum G (T_pair G A B) (T_pair G C D)
  -- Step 6: Connect to global covering number
  have h_global : triangleCoveringNumber G ≤ triangleCoveringNumberOn G (G.cliqueFinset 3) := by
    sorry -- TARGET: Global ≤ On(all triangles)
  linarith

end
