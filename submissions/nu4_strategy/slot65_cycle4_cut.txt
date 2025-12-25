/-
Tuza ν=4 Strategy - Slot 65: CYCLE_4 via Cyclic Cut (Reduce to Path)

STRATEGY: "Cut" the cycle by ignoring one adjacency, reducing to a path.

For CYCLE_4 (A—B—C—D—A):
- Ignore the D—A edge, treating it as PATH_4: A—B—C—D
- The D—A adjacency only adds bridges X_DA, which we handle separately
- All non-bridge triangles are covered by path_4 approach
- X_DA bridges are covered by the shared vertex v_da

MATH:
1. Path P = A—B—C—D has τ ≤ 8 (proven in slot51)
2. Cycle adds X_DA bridges
3. X_DA ⊆ triangles containing v_da (the shared vertex)
4. These are already counted in T_pair(A,B) or T_pair(C,D)
5. So cycle has same bound as path: τ ≤ 8

KEY INSIGHT: The "extra" edge D—A doesn't add new triangles to cover -
it just creates more overlap between T_pair sets.

PROVEN LEMMAS USED:
- tau_pair_le_4: τ(T_pair) ≤ 4 when adjacent pairs share vertex
- tau_union_le_sum: τ(A∪B) ≤ τ(A) + τ(B)
- bridges_contain_shared_vertex: All X_ef bridges contain e ∩ f

TARGET: tau_le_8_cycle4_cut
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

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

-- X_ef: bridges between e and f
def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- PROVEN in slot61

lemma tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  sorry -- PROVEN in slot35

lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  sorry -- PROVEN in slot61

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Bridges are subset of T_pair
-- ══════════════════════════════════════════════════════════════════════════════

-- X_DA ⊆ T_pair(A,B) because any bridge sharing edge with D and A
-- also shares edge with A, hence is in trianglesSharingEdge(A) ⊆ T_pair(A,B)
lemma bridges_subset_tpair (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : Finset V) :
    X_ef G D A ⊆ T_pair G A B := by
  intro t ht
  simp only [X_ef, Finset.mem_filter] at ht
  simp only [T_pair, Finset.mem_union, trianglesSharingEdge, Finset.mem_filter]
  -- t shares edge with A (from bridge definition)
  left
  exact ⟨ht.1, ht.2.2⟩

-- Similarly for other bridges
lemma bridges_BC_subset_tpair_CD (G : SimpleGraph V) [DecidableRel G.Adj]
    (B C D : Finset V) :
    X_ef G B C ⊆ T_pair G C D := by
  intro t ht
  simp only [X_ef, Finset.mem_filter] at ht
  simp only [T_pair, Finset.mem_union, trianglesSharingEdge, Finset.mem_filter]
  left
  exact ⟨ht.1, ht.2.2⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN: Cycle reduction to path
-- ══════════════════════════════════════════════════════════════════════════════

-- The cycle A—B—C—D—A can be "cut" to path A—B—C—D
-- The extra D—A adjacency only adds X_DA bridges
-- But X_DA ⊆ T_pair(A,B), so the union is unchanged!
lemma cycle4_same_as_path4_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) :
    T_pair G A B ∪ T_pair G C D = T_pair G A B ∪ T_pair G C D ∪ X_ef G D A := by
  -- X_DA ⊆ T_pair(A,B), so adding it doesn't change the union
  have h_sub : X_ef G D A ⊆ T_pair G A B := bridges_subset_tpair G A B D
  ext t
  simp only [Finset.mem_union]
  constructor
  · intro h; left; exact h
  · intro h
    rcases h with h | ht_DA
    · exact h
    · left; left; exact h_sub ht_DA

theorem tau_le_8_cycle4_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  -- Extract structure
  have hM_eq : M = {A, B, C, D} := hcycle.1
  have hA : A ∈ M := by rw [hM_eq]; simp
  have hB : B ∈ M := by rw [hM_eq]; simp
  have hC : C ∈ M := by rw [hM_eq]; simp
  have hD : D ∈ M := by rw [hM_eq]; simp

  -- Distinctness and sharing
  have hAB : A ≠ B := hcycle.2.1
  have hCD : C ≠ D := hcycle.2.2.2.1
  have hAB_card : (A ∩ B).card = 1 := hcycle.2.2.2.2.2.2.2.1
  have hCD_card : (C ∩ D).card = 1 := hcycle.2.2.2.2.2.2.2.2.2.1

  -- Get shared vertices
  have h_vab : ∃ v, A ∩ B = {v} := Finset.card_eq_one.mp hAB_card
  have h_vcd : ∃ v, C ∩ D = {v} := Finset.card_eq_one.mp hCD_card
  obtain ⟨v_ab, hv_ab⟩ := h_vab
  obtain ⟨v_cd, hv_cd⟩ := h_vcd

  -- All triangles covered by T_pair(A,B) ∪ T_pair(C,D)
  have h_cover : G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D := by
    intro t ht
    obtain ⟨e, he_in_M, h_share⟩ := triangle_shares_edge_with_packing G M hM t ht
    rw [hM_eq] at he_in_M
    simp only [Finset.mem_insert, Finset.mem_singleton] at he_in_M
    simp only [T_pair, Finset.mem_union, trianglesSharingEdge, Finset.mem_filter]
    rcases he_in_M with rfl | rfl | rfl | rfl
    · left; left; exact ⟨ht, h_share⟩
    · left; right; exact ⟨ht, h_share⟩
    · right; left; exact ⟨ht, h_share⟩
    · right; right; exact ⟨ht, h_share⟩

  -- τ(T_pair(A,B)) ≤ 4, τ(T_pair(C,D)) ≤ 4
  have h_left : triangleCoveringNumberOn G (T_pair G A B) ≤ 4 :=
    tau_pair_le_4 G M hM A B hA hB hAB v_ab hv_ab
  have h_right : triangleCoveringNumberOn G (T_pair G C D) ≤ 4 :=
    tau_pair_le_4 G M hM C D hC hD hCD v_cd hv_cd

  -- τ(union) ≤ 4 + 4 = 8
  have h_union : triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) ≤ 8 := by
    calc triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D)
        ≤ triangleCoveringNumberOn G (T_pair G A B) +
          triangleCoveringNumberOn G (T_pair G C D) := tau_union_le_sum G _ _
      _ ≤ 4 + 4 := Nat.add_le_add h_left h_right
      _ = 8 := by norm_num

  -- Monotonicity: covering superset is at least as easy
  have h_mono : triangleCoveringNumber G ≤ triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) := by
    -- triangleCoveringNumber covers ALL triangles
    -- triangleCoveringNumberOn covers the union
    -- Since all triangles ⊆ union, any cover of union covers all triangles
    sorry -- monotonicity lemma

  calc triangleCoveringNumber G
      ≤ triangleCoveringNumberOn G (T_pair G A B ∪ T_pair G C D) := h_mono
    _ ≤ 8 := h_union

end
