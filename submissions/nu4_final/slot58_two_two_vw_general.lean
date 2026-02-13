/-
Tuza ν=4: TWO_TWO_VW General Theorem
Slot 58

GOAL: Prove τ ≤ 8 for ANY two_two_vw configuration with ν = 4.

STRUCTURE:
  M = {A, B, C, D} where:
  - A and B share vertex v (A ∩ B = {v})
  - C and D share vertex w (C ∩ D = {w})
  - Pairs are vertex-disjoint: (A ∪ B) ∩ (C ∪ D) = ∅

KEY INSIGHT (from scattered proof slot56):
  1. No inter-pair bridges (pairs vertex-disjoint → pigeonhole on card 3)
  2. 5-packing argument: externals at shared vertex share common apex
  3. τ_pair ≤ 4 (2 edges through apex + 2 base edges)
  4. Total: 2 pairs × 4 = 8 edges

TIER: 2 (Subadditivity + 5-packing argument)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) : Prop :=
  T.card = 3 ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → G.Adj x y

def edgeDisjoint (T1 T2 : Finset V) : Prop :=
  (T1 ∩ T2).card ≤ 1

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  (∀ T ∈ M, isTriangle G T) ∧
  (∀ T1 ∈ M, ∀ T2 ∈ M, T1 ≠ T2 → edgeDisjoint T1 T2)

def isMaximumPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ ∀ M', isTrianglePacking G M' → M'.card ≤ M.card

def sharesEdge (T A : Finset V) : Prop :=
  (T ∩ A).card ≥ 2

def trianglesAt (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter (fun T => isTriangle G T ∧ sharesEdge T A)

def edgeInTriangle (e : Finset V) (T : Finset V) : Prop :=
  e.card = 2 ∧ e ⊆ T

def isCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Finset V)) (S : Finset (Finset V)) : Prop :=
  (∀ e ∈ E, e.card = 2) ∧
  (∀ T ∈ S, ∃ e ∈ E, edgeInTriangle e T)

-- ══════════════════════════════════════════════════════════════════════════════
-- TWO_TWO_VW CONFIGURATION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Two_two_vw configuration: two pairs of triangles sharing vertices -/
structure TwoTwoVWConfig (V : Type*) [DecidableEq V] where
  A B C D : Finset V
  v w : V
  hA_card : A.card = 3
  hB_card : B.card = 3
  hC_card : C.card = 3
  hD_card : D.card = 3
  hAB : A ∩ B = {v}
  hCD : C ∩ D = {w}
  hPairs_disjoint : Disjoint (A ∪ B : Finset V) (C ∪ D)
  hv_in_A : v ∈ A
  hv_in_B : v ∈ B
  hw_in_C : w ∈ C
  hw_in_D : w ∈ D

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 1: No inter-pair bridges
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for no_inter_pair_bridges:
1. If T shares edge with A (or B), then |T ∩ (A ∪ B)| ≥ 2
2. If T also shares edge with C (or D), then |T ∩ (C ∪ D)| ≥ 2
3. But T.card = 3 and (A ∪ B) ∩ (C ∪ D) = ∅
4. So |T ∩ (A ∪ B)| + |T ∩ (C ∪ D)| ≤ 3
5. This contradicts 2 + 2 = 4 > 3
-/

/-- Helper: A set of size 3 cannot share 2+ vertices with each of two disjoint sets -/
lemma disjoint_sets_intersection_card
    (T X Y : Finset V)
    (hT : T.card = 3)
    (hDisjoint : Disjoint X Y)
    (hTX : (T ∩ X).card ≥ 2)
    (hTY : (T ∩ Y).card ≥ 2) :
    False := by
  have h_card : (T ∩ X).card + (T ∩ Y).card ≤ T.card := by
    rw [← Finset.card_union_of_disjoint]
    · exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
    · exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hDisjoint
  omega

/-- No triangle can share edges with elements from BOTH pairs -/
theorem no_inter_pair_bridges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : TwoTwoVWConfig V)
    (T : Finset V) (hT : isTriangle G T)
    (h_AB : sharesEdge T cfg.A ∨ sharesEdge T cfg.B) :
    ¬(sharesEdge T cfg.C ∨ sharesEdge T cfg.D) := by
  intro h_CD
  -- T shares edge with A or B → |T ∩ (A ∪ B)| ≥ 2
  have h_TAB : (T ∩ (cfg.A ∪ cfg.B)).card ≥ 2 := by
    rcases h_AB with hA | hB
    · calc (T ∩ (cfg.A ∪ cfg.B)).card ≥ (T ∩ cfg.A).card := by
        apply Finset.card_le_card
        exact Finset.inter_subset_inter_right T (Finset.subset_union_left)
      _ ≥ 2 := hA
    · calc (T ∩ (cfg.A ∪ cfg.B)).card ≥ (T ∩ cfg.B).card := by
        apply Finset.card_le_card
        exact Finset.inter_subset_inter_right T (Finset.subset_union_right)
      _ ≥ 2 := hB
  -- T shares edge with C or D → |T ∩ (C ∪ D)| ≥ 2
  have h_TCD : (T ∩ (cfg.C ∪ cfg.D)).card ≥ 2 := by
    rcases h_CD with hC | hD
    · calc (T ∩ (cfg.C ∪ cfg.D)).card ≥ (T ∩ cfg.C).card := by
        apply Finset.card_le_card
        exact Finset.inter_subset_inter_right T (Finset.subset_union_left)
      _ ≥ 2 := hC
    · calc (T ∩ (cfg.C ∪ cfg.D)).card ≥ (T ∩ cfg.D).card := by
        apply Finset.card_le_card
        exact Finset.inter_subset_inter_right T (Finset.subset_union_right)
      _ ≥ 2 := hD
  -- Apply disjoint_sets_intersection_card
  exact disjoint_sets_intersection_card T (cfg.A ∪ cfg.B) (cfg.C ∪ cfg.D) hT.1 cfg.hPairs_disjoint h_TAB h_TCD

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 2: Bridge at shared vertex contains that vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for bridge_contains_shared_vertex:
1. T shares edge with A: |T ∩ A| ≥ 2
2. T shares edge with B: |T ∩ B| ≥ 2
3. A ∩ B = {v}
4. If v ∉ T, then T ∩ A and T ∩ B are disjoint
5. So |T ∩ A| + |T ∩ B| ≤ |T| = 3
6. But 2 + 2 = 4 > 3, contradiction
7. Therefore v ∈ T
-/

/-- A bridge between A and B must contain the shared vertex v -/
lemma bridge_contains_shared_vertex
    (A B : Finset V) (v : V)
    (hAB : A ∩ B = {v})
    (T : Finset V) (hT_card : T.card = 3)
    (hTA : (T ∩ A).card ≥ 2) (hTB : (T ∩ B).card ≥ 2) :
    v ∈ T := by
  by_contra hv
  -- If v ∉ T, then T ∩ A and T ∩ B are disjoint
  have h_disj : Disjoint (T ∩ A) (T ∩ B) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hx_A : x ∈ A := Finset.mem_inter.mp hxA |>.2
    have hx_B : x ∈ B := Finset.mem_inter.mp hxB |>.2
    have hx_AB : x ∈ A ∩ B := Finset.mem_inter.mpr ⟨hx_A, hx_B⟩
    rw [hAB, Finset.mem_singleton] at hx_AB
    have hx_T : x ∈ T := Finset.mem_inter.mp hxA |>.1
    rw [hx_AB] at hx_T
    exact hv hx_T
  -- Then |T ∩ A| + |T ∩ B| ≤ |T| = 3
  have h_sum : (T ∩ A).card + (T ∩ B).card ≤ T.card := by
    rw [← Finset.card_union_of_disjoint h_disj]
    exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
  -- But 2 + 2 = 4 > 3
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 3: 5-packing argument for pairs
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for externals_share_external_vertex:
1. T1 and T2 are externals at v (share edge with A or B, not in M)
2. If T1 and T2 are edge-disjoint, could replace A or B with them
3. This gives packing of size 5, contradicting ν = 4
4. So T1 and T2 share an edge: |T1 ∩ T2| ≥ 2
5. Since both contain v (bridges) or share v's edges, they share external apex x
-/

/-- Two externals at a pair cannot be edge-disjoint (5-packing argument) -/
lemma no_disjoint_externals_at_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximumPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB_ne : A ≠ B)
    (T1 T2 : Finset V)
    (hT1_tri : isTriangle G T1) (hT2_tri : isTriangle G T2)
    (hT1_shares : sharesEdge T1 A ∨ sharesEdge T1 B)
    (hT2_shares : sharesEdge T2 A ∨ sharesEdge T2 B)
    (hT1_not_M : T1 ∉ M) (hT2_not_M : T2 ∉ M)
    (hT1_T2_ne : T1 ≠ T2) :
    ¬edgeDisjoint T1 T2 := by
  -- If edge-disjoint, we could form a larger packing
  intro h_disj
  -- This would give M' = (M \ {A, B}) ∪ {T1, T2, ...} with more elements
  -- Contradicting maximality
  sorry  -- Aristotle will prove via 5-packing construction

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA 4: τ_pair ≤ 4
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_pair_le_4:
1. By no_disjoint_externals_at_pair, externals share edges
2. Since externals contain v (bridge case) or share v's spoke edges,
   all externals share a common external vertex x (or v itself)
3. Cover construction:
   - 2 edges through apex (covers all externals + containing-v triangles)
   - 1 base edge for A (covers avoiding-v triangles of A)
   - 1 base edge for B (covers avoiding-v triangles of B)
4. Total: 4 edges
-/

/-- τ(T_pair) ≤ 4 for a pair {A, B} sharing vertex v -/
theorem tau_pair_le_4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximumPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB_ne : A ≠ B)
    (v : V) (hv : A ∩ B = {v}) :
    ∃ E : Finset (Finset V), E.card ≤ 4 ∧
      isCover G E (trianglesAt G A ∪ trianglesAt G B) := by
  sorry  -- Aristotle will prove using the 5-packing argument

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for tau_le_8_two_two_vw_general:
1. By no_inter_pair_bridges, all triangles partition into:
   - T_pair1 = triangles sharing edge with A or B
   - T_pair2 = triangles sharing edge with C or D
2. By tau_pair_le_4:
   - τ(T_pair1) ≤ 4
   - τ(T_pair2) ≤ 4
3. By subadditivity: τ ≤ τ(T_pair1) + τ(T_pair2) ≤ 8
-/

/-- Every triangle shares edge with some M-element (maximality) -/
lemma every_triangle_shares_edge_with_M
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximumPacking G M)
    (T : Finset V) (hT : isTriangle G T) (hT_not_M : T ∉ M) :
    ∃ A ∈ M, sharesEdge T A := by
  by_contra h
  push_neg at h
  -- T is edge-disjoint from all of M
  have h_disj : ∀ A ∈ M, edgeDisjoint T A := by
    intro A hA
    have := h A hA
    unfold sharesEdge edgeDisjoint at *
    omega
  -- M ∪ {T} is a valid packing
  have h_packing : isTrianglePacking G (M ∪ {T}) := by
    constructor
    · intro X hX
      simp only [Finset.mem_union, Finset.mem_singleton] at hX
      rcases hX with hXM | rfl
      · exact hM.1.1 X hXM
      · exact hT
    · intro X hX Y hY hXY
      simp only [Finset.mem_union, Finset.mem_singleton] at hX hY
      rcases hX with hXM | rfl <;> rcases hY with hYM | rfl
      · exact hM.1.2 X hXM Y hYM hXY
      · exact h_disj X hXM
      · rw [Finset.inter_comm]; exact h_disj Y hYM
      · exact absurd rfl hXY
  -- But |M ∪ {T}| > |M|, contradicting maximality
  have h_card : (M ∪ {T}).card = M.card + 1 := by
    rw [Finset.card_union_of_disjoint]
    simp
    simp [hT_not_M]
  have h_le := hM.2 (M ∪ {T}) h_packing
  omega

/-- Main theorem: τ ≤ 8 for two_two_vw configuration -/
theorem tau_le_8_two_two_vw_general
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximumPacking G M) (hMcard : M.card = 4)
    (cfg : TwoTwoVWConfig V)
    (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D}) :
    ∃ E : Finset (Finset V), E.card ≤ 8 ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ T, isTriangle G T → ∃ e ∈ E, edgeInTriangle e T) := by
  -- Get covers for each pair
  have hA : cfg.A ∈ M := by rw [hM_eq]; simp
  have hB : cfg.B ∈ M := by rw [hM_eq]; simp
  have hC : cfg.C ∈ M := by rw [hM_eq]; simp
  have hD : cfg.D ∈ M := by rw [hM_eq]; simp
  have hAB_ne : cfg.A ≠ cfg.B := by
    intro h
    have : (cfg.A ∩ cfg.B).card = cfg.A.card := by simp [h]
    rw [cfg.hAB, Finset.card_singleton, cfg.hA_card] at this
    omega
  have hCD_ne : cfg.C ≠ cfg.D := by
    intro h
    have : (cfg.C ∩ cfg.D).card = cfg.C.card := by simp [h]
    rw [cfg.hCD, Finset.card_singleton, cfg.hC_card] at this
    omega
  -- Pair 1 cover
  obtain ⟨E1, hE1_card, hE1_cover⟩ := tau_pair_le_4 G M hM cfg.A cfg.B hA hB hAB_ne cfg.v cfg.hAB
  -- Pair 2 cover
  obtain ⟨E2, hE2_card, hE2_cover⟩ := tau_pair_le_4 G M hM cfg.C cfg.D hC hD hCD_ne cfg.w cfg.hCD
  -- Combined cover
  use E1 ∪ E2
  refine ⟨?_, ?_, ?_⟩
  · -- |E1 ∪ E2| ≤ 8
    calc (E1 ∪ E2).card ≤ E1.card + E2.card := Finset.card_union_le E1 E2
      _ ≤ 4 + 4 := by omega
      _ = 8 := rfl
  · -- All edges have size 2
    intro e he
    simp only [Finset.mem_union] at he
    rcases he with he1 | he2
    · exact hE1_cover.1 e he1
    · exact hE2_cover.1 e he2
  · -- Covers all triangles
    intro T hT
    by_cases hT_M : T ∈ M
    · -- T is in M, so T is A, B, C, or D
      rw [hM_eq] at hT_M
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT_M
      rcases hT_M with rfl | rfl | rfl | rfl
      · -- T = A, covered by E1
        have h_A_in : cfg.A ∈ trianglesAt G cfg.A := by
          simp only [trianglesAt, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · exact ⟨cfg.hA_card, sorry⟩  -- A is a triangle in G
          · unfold sharesEdge; simp [cfg.hA_card]
        obtain ⟨e, he, hedge⟩ := hE1_cover.2 cfg.A (Finset.mem_union_left _ h_A_in)
        exact ⟨e, Finset.mem_union_left E2 he, hedge⟩
      · sorry  -- Similar for B, C, D
      · sorry
      · sorry
    · -- T not in M, shares edge with some M-element
      obtain ⟨X, hXM, hTX⟩ := every_triangle_shares_edge_with_M G M hM T hT hT_M
      rw [hM_eq] at hXM
      simp only [Finset.mem_insert, Finset.mem_singleton] at hXM
      rcases hXM with rfl | rfl | rfl | rfl
      · -- Shares edge with A, covered by E1
        have h_T_in : T ∈ trianglesAt G cfg.A := by
          simp only [trianglesAt, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hT, hTX⟩
        obtain ⟨e, he, hedge⟩ := hE1_cover.2 T (Finset.mem_union_left _ h_T_in)
        exact ⟨e, Finset.mem_union_left E2 he, hedge⟩
      · sorry  -- Similar for B, C, D
      · sorry
      · sorry

/-- Corollary: Tuza's conjecture holds for two_two_vw with ν = 4 -/
theorem tuza_two_two_vw_nu4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximumPacking G M) (hMcard : M.card = 4)
    (cfg : TwoTwoVWConfig V)
    (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D}) :
    ∃ E : Finset (Finset V), E.card ≤ 2 * M.card ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ T, isTriangle G T → ∃ e ∈ E, edgeInTriangle e T) := by
  obtain ⟨E, hEcard, hEedge, hEcover⟩ := tau_le_8_two_two_vw_general G M hM hMcard cfg hM_eq
  exact ⟨E, by omega, hEedge, hEcover⟩

end
