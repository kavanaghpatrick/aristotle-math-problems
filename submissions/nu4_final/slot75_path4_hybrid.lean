/-
TUZA ν=4: PATH_4 HYBRID APPROACH
Goal: Prove τ ≤ 8 for graphs with path_4 packing structure A—B—C—D

Key difference from cycle_4:
- Endpoints A, D have only 1 shared vertex each (not 2)
- Middles B, C have 2 shared vertices each (All-Middle applies)

Strategy:
- Middles B, C: Use All-Middle approach (2 edges per shared vertex = 4 edges)
- Endpoints A, D: Use base edges for avoiding set + spokes for containing set
- Total: 4 (middles) + 2 (endpoint A) + 2 (endpoint D) = 8

Cover construction:
- From A: base edge {a1, a2} covers avoiding(v_ab), 1 spoke covers containing(v_ab)
- From v_ab: 1-2 spokes cover triangles at this shared vertex
- From v_bc: 2 spokes cover triangles at this shared vertex
- From v_cd: 1-2 spokes cover triangles at this shared vertex
- From D: base edge {d1, d2} covers avoiding(v_cd), 1 spoke covers containing(v_cd)
-/

import Mathlib

set_option linter.mathlibStandardSet false
open scoped BigOperators Real Nat Classical Pointwise
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

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

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  -- Adjacent pairs share exactly 1 vertex
  (A ∩ B).card = 1 ∧
  (B ∩ C).card = 1 ∧
  (C ∩ D).card = 1 ∧
  -- Non-adjacent pairs are disjoint
  (A ∩ C).card = 0 ∧
  (A ∩ D).card = 0 ∧
  (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN INFRASTRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- PROVEN in slot69

-- τ(containing v in T_pair) ≤ 4 (4 spokes from v)
lemma tau_containing_v_in_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv_e : v ∈ e) (hv_f : v ∈ f) :
    triangleCoveringNumberOn G (trianglesContaining (T_pair G e f) v) ≤ 4 := by
  sorry -- PROVEN in slot69

-- τ(avoiding v in T_pair) ≤ 2 (2 base edges)
lemma tau_avoiding_v_in_pair_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) :
    triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) ≤ 2 := by
  sorry -- PROVEN in slot69

-- Maximality: every triangle shares edge with some packing element
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  sorry -- PROVEN in slot69

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 SPECIFIC LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

-- For path_4, all triangles are in T_pair(A,B) ∪ T_pair(C,D)
lemma path4_tpair_covers_all (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D := by
  intro t ht
  obtain ⟨X, hX_mem, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  rw [hpath.1] at hX_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hX_mem
  unfold T_pair trianglesSharingEdge
  simp only [Finset.mem_union, Finset.mem_filter]
  rcases hX_mem with rfl | rfl | rfl | rfl
  · left; left; exact ⟨ht, hX_share⟩
  · left; right; exact ⟨ht, hX_share⟩
  · right; left; exact ⟨ht, hX_share⟩
  · right; right; exact ⟨ht, hX_share⟩

-- Middles B, C have All-Middle property (each edge incident to a shared vertex)
-- This is because B = {v_ab, v_bc, b1} and C = {v_bc, v_cd, c1}

lemma middle_all_middle (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (v_left v_right b1 : V)
    (hB_eq : B = {v_left, v_right, b1})
    (h_ne : v_left ≠ v_right ∧ v_left ≠ b1 ∧ v_right ≠ b1)
    (t : Finset V) (ht : t ∈ trianglesSharingEdge G B) :
    v_left ∈ t ∨ v_right ∈ t := by
  -- Same proof as cycle4_element_contains_shared
  simp only [trianglesSharingEdge, Finset.mem_filter] at ht
  have h_share : (t ∩ B).card ≥ 2 := ht.2
  rw [hB_eq] at h_share
  by_contra h_neither
  push_neg at h_neither
  have hsub : t ∩ {v_left, v_right, b1} ⊆ {b1} := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 h_neither.1
    · exact absurd hx.1 h_neither.2
    · rfl
  have hcard : (t ∩ {v_left, v_right, b1}).card ≤ 1 := by
    calc (t ∩ {v_left, v_right, b1}).card ≤ ({b1} : Finset V).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton b1
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

theorem path4_tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    (v_ab v_bc v_cd : V)
    (hAB : A ∩ B = {v_ab}) (hBC : B ∩ C = {v_bc}) (hCD : C ∩ D = {v_cd}) :
    triangleCoveringNumber G ≤ 8 := by
  -- Strategy:
  -- All triangles ⊆ T_pair(A,B) ∪ T_pair(C,D)
  -- τ(T_pair(A,B)) ≤ τ(containing v_ab) + τ(avoiding v_ab) ≤ 4 + 2 = 6
  -- τ(T_pair(C,D)) ≤ τ(containing v_cd) + τ(avoiding v_cd) ≤ 4 + 2 = 6
  -- But this gives 12, not 8!
  --
  -- Refined approach using path structure:
  -- T_pair(A,B) ∩ T_pair(C,D) includes triangles sharing with B and C
  -- The overlap saves edges
  --
  -- Alternative: Use direct 8-edge construction
  -- - 2 edges from A's base and spokes
  -- - 2 edges covering v_ab region
  -- - 2 edges covering v_bc region
  -- - 2 edges covering v_cd region
  -- - 2 edges from D's base and spokes
  -- Total: Careful counting gives 8

  -- Using proven infrastructure with overlap exploitation
  have h_covers : G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D :=
    path4_tpair_covers_all G M hM A B C D hpath

  -- The key insight: triangles at v_bc are in BOTH T_pair(A,B) and T_pair(C,D)
  -- because v_bc ∈ B and v_bc ∈ C
  -- So we can use a smarter decomposition

  have h_v_ab_in_A : v_ab ∈ A := by
    have := Finset.mem_singleton.mpr rfl
    rw [← hAB] at this
    exact Finset.mem_inter.mp this |>.1
  have h_v_ab_in_B : v_ab ∈ B := by
    have := Finset.mem_singleton.mpr rfl
    rw [← hAB] at this
    exact Finset.mem_inter.mp this |>.2

  have h_v_bc_in_B : v_bc ∈ B := by
    have := Finset.mem_singleton.mpr rfl
    rw [← hBC] at this
    exact Finset.mem_inter.mp this |>.1
  have h_v_bc_in_C : v_bc ∈ C := by
    have := Finset.mem_singleton.mpr rfl
    rw [← hBC] at this
    exact Finset.mem_inter.mp this |>.2

  have h_v_cd_in_C : v_cd ∈ C := by
    have := Finset.mem_singleton.mpr rfl
    rw [← hCD] at this
    exact Finset.mem_inter.mp this |>.1
  have h_v_cd_in_D : v_cd ∈ D := by
    have := Finset.mem_singleton.mpr rfl
    rw [← hCD] at this
    exact Finset.mem_inter.mp this |>.2

  -- Use V-decomposition on both T_pairs with overlap accounting
  sorry

end
