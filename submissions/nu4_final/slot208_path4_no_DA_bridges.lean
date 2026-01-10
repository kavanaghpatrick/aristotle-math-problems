/-
Tuza ν=4: Path_4 Has No D-A Bridges (Slot 208)

GOAL: In Path_4 configuration, there are no bridges between D and A.

PATH_4 vs CYCLE_4:
  - Cycle_4: A-B-C-D-A (4 adjacencies, 4 shared vertices)
  - Path_4:  A-B-C-D   (3 adjacencies, D and A are disjoint)

LEMMA: X(D,A) = ∅ in Path_4
  - D ∩ A = ∅ (definition of Path_4)
  - A bridge between D and A would need to share edge with BOTH
  - If t shares edge with D: t ∩ D ≥ 2
  - If t shares edge with A: t ∩ A ≥ 2
  - Since D ∩ A = ∅, t would need ≥ 4 vertices (impossible for triangle)

IMPLICATION: Path_4 is easier than Cycle_4!
  - No D-A bridges to handle
  - The "open ends" D and A are effectively independent
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isBridgeBetween (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧ sharesEdgeWith t B

def bridgesBetween (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (isBridgeBetween G M A B)

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 CONFIGURATION
-- ══════════════════════════════════════════════════════════════════════════════

structure Path4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  v_ab : V
  v_bc : V
  v_cd : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  -- KEY DIFFERENCE: D and A are DISJOINT (no v_da)
  hDA : D ∩ A = ∅
  -- Non-adjacencies
  hAC : A ∩ C = ∅
  hBD : B ∩ D = ∅

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA: No D-A Bridges in Path_4
-- ══════════════════════════════════════════════════════════════════════════════

/-- If D ∩ A = ∅, no triangle can share edge with both D and A -/
theorem no_DA_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (D A : Finset V) (hDA : D ∩ A = ∅)
    (t : Finset V) (ht : t.card = 3) :
    ¬(sharesEdgeWith t D ∧ sharesEdgeWith t A) := by
  intro ⟨h_tD, h_tA⟩
  -- t shares edge with D: t ∩ D ≥ 2
  obtain ⟨u₁, v₁, huv₁, hu₁_t, hv₁_t, hu₁_D, hv₁_D⟩ := h_tD
  -- t shares edge with A: t ∩ A ≥ 2
  obtain ⟨u₂, v₂, huv₂, hu₂_t, hv₂_t, hu₂_A, hv₂_A⟩ := h_tA
  -- {u₁, v₁} ⊆ t ∩ D and {u₂, v₂} ⊆ t ∩ A
  -- Since D ∩ A = ∅, (t ∩ D) ∩ (t ∩ A) = ∅
  have h_disj : Disjoint (t ∩ D) (t ∩ A) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    calc (t ∩ D) ∩ (t ∩ A) = t ∩ D ∩ A := by ext x; simp [Finset.mem_inter]; tauto
       _ = t ∩ (D ∩ A) := by ext x; simp [Finset.mem_inter]; tauto
       _ = t ∩ ∅ := by rw [hDA]
       _ = ∅ := Finset.inter_empty t
  -- |t| ≥ |(t ∩ D) ∪ (t ∩ A)| = |t ∩ D| + |t ∩ A| ≥ 2 + 2 = 4
  have h_card_ge_4 : t.card ≥ 4 := by
    have h_tD_card : (t ∩ D).card ≥ 2 := by
      calc (t ∩ D).card ≥ ({u₁, v₁} : Finset V).card := Finset.card_le_card (by
             intro x hx; simp at hx; rcases hx with rfl | rfl
             · exact Finset.mem_inter.mpr ⟨hu₁_t, hu₁_D⟩
             · exact Finset.mem_inter.mpr ⟨hv₁_t, hv₁_D⟩)
         _ = 2 := by simp [huv₁]
    have h_tA_card : (t ∩ A).card ≥ 2 := by
      calc (t ∩ A).card ≥ ({u₂, v₂} : Finset V).card := Finset.card_le_card (by
             intro x hx; simp at hx; rcases hx with rfl | rfl
             · exact Finset.mem_inter.mpr ⟨hu₂_t, hu₂_A⟩
             · exact Finset.mem_inter.mpr ⟨hv₂_t, hv₂_A⟩)
         _ = 2 := by simp [huv₂]
    calc t.card ≥ ((t ∩ D) ∪ (t ∩ A)).card := Finset.card_le_card (by
           intro x hx; simp at hx; rcases hx with ⟨hxT, _⟩ | ⟨hxT, _⟩ <;> exact hxT)
       _ = (t ∩ D).card + (t ∩ A).card := Finset.card_union_of_disjoint h_disj
       _ ≥ 2 + 2 := by omega
       _ = 4 := by norm_num
  omega

/-- Bridges between D and A are empty in Path_4 -/
theorem path4_no_DA_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M) :
    bridgesBetween G M cfg.D cfg.A = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro t ht
  simp only [bridgesBetween, Finset.mem_filter] at ht
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht.1).2
  exact no_DA_bridges G cfg.D cfg.A cfg.hDA t ht_card ⟨ht.2.2.2.1, ht.2.2.2.2⟩

/-- Also no A-C or B-D bridges -/
theorem path4_no_AC_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M) :
    bridgesBetween G M cfg.A cfg.C = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro t ht
  simp only [bridgesBetween, Finset.mem_filter] at ht
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht.1).2
  exact no_DA_bridges G cfg.A cfg.C cfg.hAC t ht_card ⟨ht.2.2.2.1, ht.2.2.2.2⟩

theorem path4_no_BD_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M) :
    bridgesBetween G M cfg.B cfg.D = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro t ht
  simp only [bridgesBetween, Finset.mem_filter] at ht
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht.1).2
  exact no_DA_bridges G cfg.B cfg.D cfg.hBD t ht_card ⟨ht.2.2.2.1, ht.2.2.2.2⟩

end
