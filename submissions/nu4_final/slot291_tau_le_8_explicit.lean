/-
  slot291: PATH_4 τ ≤ 8 - EXPLICIT 8-Edge Cover

  DATE: Jan 8, 2026

  KEY LEARNINGS FROM FAILED SLOTS:
  - Do NOT use Path4Config structure (field accessor errors)
  - Do NOT use .toList.head! (needs Inhabited V)
  - Do NOT use let bindings for cover (projection errors)
  - DO use `open Classical` (DecidablePred fix)
  - DO use explicit vertex parameters

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

/-! ### PATH_4 Definition (as predicate with explicit vertices) -/

/-- PATH_4 configuration with all vertices explicit -/
def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) (v1 v2 v3 a1 a2 b c d1 d2 : V) : Prop :=
  M = {A, B, C, D} ∧
  A = {v1, a1, a2} ∧ B = {v1, v2, b} ∧ C = {v2, v3, c} ∧ D = {v3, d1, d2} ∧
  A ∈ G.cliqueFinset 3 ∧ B ∈ G.cliqueFinset 3 ∧ C ∈ G.cliqueFinset 3 ∧ D ∈ G.cliqueFinset 3 ∧
  A ∩ B = {v1} ∧ B ∩ C = {v2} ∧ C ∩ D = {v3} ∧
  A ∩ C = ∅ ∧ A ∩ D = ∅ ∧ B ∩ D = ∅ ∧
  v1 ≠ v2 ∧ v2 ≠ v3 ∧ v1 ≠ v3

/-! ### Triangle Structure (PROVEN in slot285) -/

theorem triangle_structure (M : Finset (Finset V)) (A B C D : Finset V) (v1 v2 v3 a1 a2 b c d1 d2 : V)
    (hM : isMaxPacking G M)
    (hPath : isPath4 G M A B C D v1 v2 v3 a1 a2 b c d1 d2)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    v1 ∈ t ∨ v2 ∈ t ∨ v3 ∈ t ∨
    ((t ∩ A).card ≥ 2 ∧ v1 ∉ t) ∨
    ((t ∩ D).card ≥ 2 ∧ v3 ∉ t) := by
  by_contra h_contra
  push_neg at h_contra
  obtain ⟨hv1, hv2, hv3, hA_not, hD_not⟩ := h_contra
  by_cases ht_in : t ∈ M
  · rw [hPath.1] at ht_in
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht_in
    rcases ht_in with rfl | rfl | rfl | rfl
    · -- t = A, but v1 ∈ A
      have hv1_in_A : v1 ∈ A := by rw [hPath.2.1]; simp
      exact hv1 hv1_in_A
    · -- t = B, contains v1
      have hv1_in_B : v1 ∈ B := by rw [hPath.2.2.1]; simp
      exact hv1 hv1_in_B
    · -- t = C, contains v2
      have hv2_in_C : v2 ∈ C := by rw [hPath.2.2.2.1]; simp
      exact hv2 hv2_in_C
    · -- t = D, contains v3
      have hv3_in_D : v3 ∈ D := by rw [hPath.2.2.2.2.1]; simp
      exact hv3 hv3_in_D
  · obtain ⟨m, hm, h_share⟩ := max_packing_shares_edge G M hM t ht ht_in
    rw [hPath.1] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact hA_not ⟨h_share, hv1⟩
    · -- Shares with B = {v1, v2, b}
      have hB3 : B.card = 3 := triangle_card_3 G B hPath.2.2.2.2.2.1.2.1
      have h_sub : t ∩ B ⊆ B \ {v1, v2} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        exact ⟨hx.2, fun h => by cases h <;> simp_all⟩
      rw [hPath.2.2.1] at hB3 h_sub
      have : (B \ {v1, v2}).card ≤ 1 := by
        simp only [hPath.2.2.1]
        simp [hPath.2.2.2.2.2.2.2.2.1]
      have := Finset.card_le_card h_sub
      omega
    · -- Shares with C = {v2, v3, c}
      have hC3 : C.card = 3 := triangle_card_3 G C hPath.2.2.2.2.2.1.2.2.1
      have h_sub : t ∩ C ⊆ C \ {v2, v3} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        exact ⟨hx.2, fun h => by cases h <;> simp_all⟩
      rw [hPath.2.2.2.1] at hC3 h_sub
      have : (C \ {v2, v3}).card ≤ 1 := by
        simp only [hPath.2.2.2.1]
        simp [hPath.2.2.2.2.2.2.2.2.2.1]
      have := Finset.card_le_card h_sub
      omega
    · exact hD_not ⟨h_share, hv3⟩

/-! ### The Explicit 8-Edge Cover -/

/-- The 8-edge cover: explicit construction -/
def cover8 (v1 v2 v3 a1 a2 b c d1 d2 : V) : Finset (Sym2 V) :=
  {s(v1, a1), s(a1, a2), s(v1, b), s(v2, b), s(v2, c), s(v3, c), s(v3, d1), s(d1, d2)}

/-- Cover has at most 8 edges -/
lemma cover8_card_le (v1 v2 v3 a1 a2 b c d1 d2 : V) :
    (cover8 v1 v2 v3 a1 a2 b c d1 d2).card ≤ 8 := by
  unfold cover8
  refine Finset.card_le_card ?_
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  exact hx

/-! ### Main Theorem: τ ≤ 8 -/

theorem tau_le_8_path4 (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V)
    (hM : isMaxPacking G M)
    (hPath : isPath4 G M A B C D v1 v2 v3 a1 a2 b c d1 d2) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  -- Use the filtered 8-edge cover
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
    have h_struct := triangle_structure G M A B C D v1 v2 v3 a1 a2 b c d1 d2 hM hPath t ht
    rcases h_struct with hv1_in | hv2_in | hv3_in | ⟨hA_share, hv1_not⟩ | ⟨hD_share, hv3_not⟩
    · -- Case 1: v1 ∈ t
      -- v1 ∈ A and v1 ∈ B. t shares edge with some M-element.
      -- If v1 ∈ t, then t contains at least one of: a1, a2 (from A) or b (from B) along with v1
      sorry
    · -- Case 2: v2 ∈ t
      -- v2 ∈ B and v2 ∈ C. covered by {v2,b} or {v2,c}
      sorry
    · -- Case 3: v3 ∈ t
      -- v3 ∈ C and v3 ∈ D. covered by {v3,c} or {v3,d1}
      sorry
    · -- Case 4: A-base-private (v1 ∉ t, shares edge {a1,a2} with A)
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hA_share
      simp only [Finset.mem_inter] at hx hy
      -- Since v1 ∉ t and A = {v1, a1, a2}, we have x, y ∈ {a1, a2}
      -- So {x, y} = {a1, a2}
      use s(a1, a2)
      constructor
      · simp only [Finset.mem_filter, cover8]
        constructor
        · simp
        · -- {a1, a2} is an edge in G because A is a triangle
          have hA_clique := hPath.2.2.2.2.2.1.1
          rw [hPath.2.1] at hA_clique
          have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hA_clique
          have ha1_in : a1 ∈ ({v1, a1, a2} : Finset V) := by simp
          have ha2_in : a2 ∈ ({v1, a1, a2} : Finset V) := by simp
          -- Need a1 ≠ a2
          sorry
      · -- s(a1, a2) ∈ t.sym2
        -- x, y are in {a1, a2} ∩ t, so a1, a2 ∈ t
        sorry
    · -- Case 5: D-base-private (v3 ∉ t, shares edge {d1,d2} with D)
      use s(d1, d2)
      constructor
      · simp only [Finset.mem_filter, cover8]
        constructor
        · simp
        · -- {d1, d2} is an edge in G because D is a triangle
          have hD_clique := hPath.2.2.2.2.2.1.2.2.2
          rw [hPath.2.2.2.2.1] at hD_clique
          sorry
      · sorry

end
