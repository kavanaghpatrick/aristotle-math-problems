/-
Tuza ν=4 Strategy - Slot 63: CYCLE_4 via T_pair Decomposition

This is the FINAL CASE needed for Tuza ν=4!

STRATEGY: Same as PATH_4 (slot51) - use proven tau_pair_le_4 theorem.

For CYCLE_4 (A—B—C—D—A with shared vertices v_ab, v_bc, v_cd, v_da):
1. T_left = T_pair(A,B) = triangles sharing edge with A or B
2. T_right = T_pair(C,D) = triangles sharing edge with C or D
3. All triangles ⊆ T_left ∪ T_right (same as path_4)
4. τ(T_left) ≤ 4 (by tau_pair_le_4 since A ∩ B = {v_ab})
5. τ(T_right) ≤ 4 (by tau_pair_le_4 since C ∩ D = {v_cd})
6. τ(all) ≤ τ(T_left) + τ(T_right) ≤ 8

KEY INSIGHT: Cycle has 4 adjacencies (A-B, B-C, C-D, D-A) vs path's 3,
but T_pair(A,B) ∪ T_pair(C,D) still covers ALL triangles!
The extra D-A adjacency doesn't change the union coverage.

PROVEN LEMMAS USED (from slot35 uuid da605278):
- tau_pair_le_4: τ(T_pair) ≤ 4 when e ∩ f = {v}
- tau_union_le_sum: τ(A∪B) ≤ τ(A) + τ(B)
- tau_containing_v_in_pair_le_4: Spokes cover containing triangles
- tau_avoiding_v_in_pair_le_2: Base edges cover avoiding triangles

TARGET: tau_le_8_cycle4
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (same as path_4)
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

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  -- Adjacent pairs share exactly 1 vertex
  (A ∩ B).card = 1 ∧
  (B ∩ C).card = 1 ∧
  (C ∩ D).card = 1 ∧
  (D ∩ A).card = 1 ∧
  -- Opposite pairs are disjoint (no shared vertex)
  (A ∩ C).card = 0 ∧
  (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slot35/slot51)
-- ══════════════════════════════════════════════════════════════════════════════

-- Union bound (PROVEN in slot61)
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- PROVEN in slot61 (uuid 16fa79da) - copy full proof

-- Pair bound (PROVEN in slot35)
lemma tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  sorry -- PROVEN in slot35 (uuid da605278) - copy full proof

-- Every triangle shares edge with max packing (PROVEN in slot61)
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  sorry -- PROVEN in slot61 - copy full proof

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: T_pair union covers all triangles (same as path_4)
-- ══════════════════════════════════════════════════════════════════════════════

lemma cycle4_tpair_union_covers_all (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D := by
  intro t ht
  -- Every triangle shares an edge with some packing element
  obtain ⟨e, he_in_M, h_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  -- M = {A, B, C, D}
  have hM_eq : M = {A, B, C, D} := hcycle.1
  rw [hM_eq] at he_in_M
  simp only [Finset.mem_insert, Finset.mem_singleton] at he_in_M
  -- t shares edge with A, B, C, or D
  rcases he_in_M with rfl | rfl | rfl | rfl
  · -- t shares edge with A → t ∈ T_pair(A,B)
    left
    simp only [T_pair, Finset.mem_union, trianglesSharingEdge, Finset.mem_filter]
    left
    exact ⟨ht, h_share⟩
  · -- t shares edge with B → t ∈ T_pair(A,B)
    left
    simp only [T_pair, Finset.mem_union, trianglesSharingEdge, Finset.mem_filter]
    right
    exact ⟨ht, h_share⟩
  · -- t shares edge with C → t ∈ T_pair(C,D)
    right
    simp only [T_pair, Finset.mem_union, trianglesSharingEdge, Finset.mem_filter]
    left
    exact ⟨ht, h_share⟩
  · -- t shares edge with D → t ∈ T_pair(C,D)
    right
    simp only [T_pair, Finset.mem_union, trianglesSharingEdge, Finset.mem_filter]
    right
    exact ⟨ht, h_share⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for CYCLE_4
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  -- Extract cycle structure
  have hAB_card : (A ∩ B).card = 1 := hcycle.2.2.2.2.2.2.2.1
  have hCD_card : (C ∩ D).card = 1 := hcycle.2.2.2.2.2.2.2.2.2.1
  have hM_eq : M = {A, B, C, D} := hcycle.1

  -- Get shared vertices
  have h_vab : ∃ v, A ∩ B = {v} := Finset.card_eq_one.mp hAB_card
  have h_vcd : ∃ v, C ∩ D = {v} := Finset.card_eq_one.mp hCD_card
  obtain ⟨v_ab, hv_ab⟩ := h_vab
  obtain ⟨v_cd, hv_cd⟩ := h_vcd

  -- A, B, C, D are in M
  have hA : A ∈ M := by rw [hM_eq]; simp
  have hB : B ∈ M := by rw [hM_eq]; simp
  have hC : C ∈ M := by rw [hM_eq]; simp
  have hD : D ∈ M := by rw [hM_eq]; simp

  -- Distinctness
  have hAB : A ≠ B := hcycle.2.1
  have hCD : C ≠ D := hcycle.2.2.2.1

  -- All triangles covered by T_pair(A,B) ∪ T_pair(C,D)
  have h_cover : G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D :=
    cycle4_tpair_union_covers_all G M hM A B C D hcycle

  -- τ(all) ≤ τ(T_pair(A,B) ∪ T_pair(C,D))
  have h1 : triangleCoveringNumberOn G (G.cliqueFinset 3) ≤
            triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) := by
    -- Covering a subset is easier
    sorry -- monotonicity lemma

  -- τ(T_pair(A,B) ∪ T_pair(C,D)) ≤ τ(T_pair(A,B)) + τ(T_pair(C,D))
  have h2 : triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) ≤
            triangleCoveringNumberOn G (T_pair G A B) +
            triangleCoveringNumberOn G (T_pair G C D) :=
    tau_union_le_sum G (T_pair G A B) (T_pair G C D)

  -- τ(T_pair(A,B)) ≤ 4 and τ(T_pair(C,D)) ≤ 4
  have h_left : triangleCoveringNumberOn G (T_pair G A B) ≤ 4 :=
    tau_pair_le_4 G M hM A B hA hB hAB v_ab hv_ab
  have h_right : triangleCoveringNumberOn G (T_pair G C D) ≤ 4 :=
    tau_pair_le_4 G M hM C D hC hD hCD v_cd hv_cd

  -- Combine: τ ≤ 4 + 4 = 8
  calc triangleCoveringNumber G
      = triangleCoveringNumberOn G (G.cliqueFinset 3) := by sorry -- definition
    _ ≤ triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) := h1
    _ ≤ triangleCoveringNumberOn G (T_pair G A B) +
        triangleCoveringNumberOn G (T_pair G C D) := h2
    _ ≤ 4 + 4 := Nat.add_le_add h_left h_right
    _ = 8 := by norm_num

end
