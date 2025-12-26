/-
TUZA ν=4: TWO_TWO_VW (Two Independent Pairs)
Goal: Prove τ ≤ 8 for graphs with two_two_vw packing structure

Structure:
- Pair 1: A—B sharing v (v ∈ A ∩ B)
- Pair 2: C—D sharing w (w ∈ C ∩ D)
- No edges between pairs: A, B disjoint from C, D

This is EASIER than path_4/cycle_4 because:
- The pairs are completely independent
- No bridges between pairs
- Each pair can be handled separately

Strategy:
- τ(T_pair(A,B)) ≤ 6 (4 containing v + 2 avoiding v)
- τ(T_pair(C,D)) ≤ 6 (4 containing w + 2 avoiding w)
- But pairs are independent, so we can use S_e decomposition:
  - τ(S_A) ≤ 2, τ(S_B) ≤ 2, τ(S_C) ≤ 2, τ(S_D) ≤ 2
  - Bridges X_AB ⊆ triangles at v (absorbed by spokes)
  - Bridges X_CD ⊆ triangles at w (absorbed by spokes)
  - Total: 4 × 2 = 8
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

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t =>
    (t ∩ e).card ≥ 2 ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def isTwoTwoVW (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  -- Pair 1: A—B share exactly 1 vertex
  (A ∩ B).card = 1 ∧
  -- Pair 2: C—D share exactly 1 vertex
  (C ∩ D).card = 1 ∧
  -- No inter-pair sharing
  (A ∩ C).card = 0 ∧
  (A ∩ D).card = 0 ∧
  (B ∩ C).card = 0 ∧
  (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN INFRASTRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- PROVEN in slot69

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry -- PROVEN in slot71

lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  sorry -- PROVEN in slot69

-- ══════════════════════════════════════════════════════════════════════════════
-- TWO_TWO_VW SPECIFIC LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

-- Key insight: pairs are completely independent
-- No triangle can share edge with elements from BOTH pairs

lemma no_inter_pair_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (h_disjoint : (A ∩ C).card = 0) :
    X_ef G A C = ∅ := by
  ext t
  simp only [X_ef, Finset.mem_filter, Finset.not_mem_empty, iff_false]
  intro ⟨ht_tri, ht_A, ht_C⟩
  -- A triangle can't share ≥2 vertices with BOTH A and C if A ∩ C = ∅
  -- |t ∩ A| ≥ 2 and |t ∩ C| ≥ 2 but |t| = 3 and A ∩ C = ∅
  -- So |t ∩ A| + |t ∩ C| ≥ 4 but |t| = 3, contradiction
  have h_card : t.card = 3 := ht_tri.card_eq
  have h_sum : (t ∩ A).card + (t ∩ C).card ≤ t.card := by
    have h1 : t ∩ A ⊆ t := Finset.inter_subset_left
    have h2 : t ∩ C ⊆ t := Finset.inter_subset_left
    have h3 : t ∩ A ∩ (t ∩ C) = t ∩ (A ∩ C) := by
      ext x; simp only [Finset.mem_inter]; tauto
    have h4 : (t ∩ (A ∩ C)).card = 0 := by
      have : t ∩ (A ∩ C) ⊆ A ∩ C := Finset.inter_subset_right
      calc (t ∩ (A ∩ C)).card ≤ (A ∩ C).card := Finset.card_le_card this
        _ = 0 := h_disjoint
    sorry -- Set arithmetic
  omega

-- All triangles decompose cleanly into pair-local sets
lemma two_two_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (h22 : isTwoTwoVW M A B C D) :
    G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D := by
  intro t ht
  obtain ⟨X, hX_mem, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  rw [h22.1] at hX_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hX_mem
  unfold T_pair trianglesSharingEdge
  simp only [Finset.mem_union, Finset.mem_filter]
  rcases hX_mem with rfl | rfl | rfl | rfl
  · left; left; exact ⟨ht, hX_share⟩
  · left; right; exact ⟨ht, hX_share⟩
  · right; left; exact ⟨ht, hX_share⟩
  · right; right; exact ⟨ht, hX_share⟩

-- S_e sets are disjoint for elements from different pairs
lemma Se_disjoint_across_pairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (A C : Finset V) (hA : A ∈ M) (hC : C ∈ M)
    (h_disjoint : (A ∩ C).card = 0) :
    S_e G M A ∩ S_e G M C = ∅ := by
  ext t
  simp only [Finset.mem_inter, Finset.not_mem_empty, iff_false]
  intro ⟨htA, htC⟩
  unfold S_e at htA htC
  simp only [Finset.mem_filter] at htA htC
  -- t shares edge with A and with C, but A ∩ C = ∅
  -- This contradicts the pigeonhole argument
  have h_share_A : (t ∩ A).card ≥ 2 := htA.2.1
  have h_share_C : (t ∩ C).card ≥ 2 := htC.2.1
  have h_t_card : t.card = 3 := htA.1.card_eq
  -- Same contradiction as no_inter_pair_bridges
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

theorem two_two_vw_tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (h22 : isTwoTwoVW M A B C D)
    (v w : V) (hAB : A ∩ B = {v}) (hCD : C ∩ D = {w}) :
    triangleCoveringNumber G ≤ 8 := by
  -- Strategy using S_e decomposition:
  -- 1. All triangles ⊆ S_A ∪ S_B ∪ S_C ∪ S_D ∪ X_AB ∪ X_CD
  -- 2. X_AC, X_AD, X_BC, X_BD are all empty (no inter-pair bridges)
  -- 3. τ(S_e) ≤ 2 for each e
  -- 4. X_AB ⊆ triangles at v, covered by S_A ∪ S_B covers
  -- 5. X_CD ⊆ triangles at w, covered by S_C ∪ S_D covers
  -- 6. Total: 4 × 2 = 8

  have hA : A ∈ M := by rw [h22.1]; simp
  have hB : B ∈ M := by rw [h22.1]; simp
  have hC : C ∈ M := by rw [h22.1]; simp
  have hD : D ∈ M := by rw [h22.1]; simp

  -- Inter-pair bridges are empty
  have h_AC : X_ef G A C = ∅ := no_inter_pair_bridges G A C h22.2.2.2.2.2.2.2.2.1
  have h_AD : X_ef G A D = ∅ := no_inter_pair_bridges G A D h22.2.2.2.2.2.2.2.2.2.1
  have h_BC : X_ef G B C = ∅ := no_inter_pair_bridges G B C h22.2.2.2.2.2.2.2.2.2.2.1
  have h_BD : X_ef G B D = ∅ := no_inter_pair_bridges G B D h22.2.2.2.2.2.2.2.2.2.2.2

  -- Each S_e covered by 2 edges
  have h_SA : triangleCoveringNumberOn G (S_e G M A) ≤ 2 := tau_S_le_2 G M hM A hA
  have h_SB : triangleCoveringNumberOn G (S_e G M B) ≤ 2 := tau_S_le_2 G M hM B hB
  have h_SC : triangleCoveringNumberOn G (S_e G M C) ≤ 2 := tau_S_le_2 G M hM C hC
  have h_SD : triangleCoveringNumberOn G (S_e G M D) ≤ 2 := tau_S_le_2 G M hM D hD

  -- The pairs are independent, so we can sum:
  -- τ(Pair 1) ≤ τ(S_A) + τ(S_B) + τ(X_AB absorption) ≤ 2 + 2 = 4
  -- τ(Pair 2) ≤ τ(S_C) + τ(S_D) + τ(X_CD absorption) ≤ 2 + 2 = 4
  -- Total: 4 + 4 = 8

  -- Key: X_AB triangles share vertex v with BOTH A and B
  -- So X_AB triangles contain v
  -- The 2 edges covering S_A and 2 edges covering S_B include spokes from v
  -- These spokes also cover X_AB for free!

  sorry

end
