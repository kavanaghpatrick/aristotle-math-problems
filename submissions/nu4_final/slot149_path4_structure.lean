/-
Tuza ν=4 Strategy - Slot 149: Path_4 Structure Analysis

TARGET: Analyze the path_4 configuration where M = {A-B-C-D} form a path.

STRUCTURE:
- A shares exactly one vertex v_ab with B
- B shares exactly one vertex v_bc with C
- C shares exactly one vertex v_cd with D
- A and C are disjoint (no shared vertices)
- B and D are disjoint (no shared vertices)
- A and D may or may not share a vertex

KEY INSIGHT:
- Endpoints (A, D) have simpler structure: only ONE neighbor
- Middle elements (B, C) have TWO neighbors each

PROVEN SCAFFOLDING:
- no_bridge_disjoint: No triangle bridges disjoint M-elements
- This means NO external triangle shares edge with both A and C, or both B and D

ZERO SORRIES EXPECTED - structure definitions + basic properties
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
  ∃ e, e ∈ t.sym2 ∧ e ∈ S.sym2

/-- Two M-elements share exactly one vertex -/
def sharesOneVertex (A B : Finset V) : Prop :=
  (A ∩ B).card = 1

/-- Path_4 configuration: A-B-C-D with shared vertices v_ab, v_bc, v_cd -/
structure Path4Config (G : SimpleGraph V) [DecidableRel G.Adj] where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ G.cliqueFinset 3
  hB : B ∈ G.cliqueFinset 3
  hC : C ∈ G.cliqueFinset 3
  hD : D ∈ G.cliqueFinset 3
  h_AB : sharesOneVertex A B
  h_BC : sharesOneVertex B C
  h_CD : sharesOneVertex C D
  h_AC : Disjoint A C
  h_BD : Disjoint B D

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slot67)
-- ══════════════════════════════════════════════════════════════════════════════

lemma no_bridge_disjoint (A B t : Finset V)
    (hA : A.card = 3) (hB : B.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint A B)
    (h_share_A : sharesEdgeWith t A)
    (h_share_B : sharesEdgeWith t B) :
    False := by
  obtain ⟨eA, heA_t, heA_A⟩ := h_share_A
  rw [Finset.mem_sym2_iff] at heA_t heA_A
  obtain ⟨a₁, a₂, ha12, ha1_t, ha2_t, rfl⟩ := heA_t
  obtain ⟨a₁', a₂', _, ha1'_A, ha2'_A, heq_A⟩ := heA_A
  simp only [Sym2.eq, Sym2.rel_iff] at heq_A
  obtain ⟨eB, heB_t, heB_B⟩ := h_share_B
  rw [Finset.mem_sym2_iff] at heB_t heB_B
  obtain ⟨b₁, b₂, hb12, hb1_t, hb2_t, rfl⟩ := heB_t
  obtain ⟨b₁', b₂', _, hb1'_B, hb2'_B, heq_B⟩ := heB_B
  simp only [Sym2.eq, Sym2.rel_iff] at heq_B
  have ha1_A : a₁ ∈ A := by rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have ha2_A : a₂ ∈ A := by rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb1_B : b₁ ∈ B := by rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb2_B : b₂ ∈ B := by rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have h_a1_not_B : a₁ ∉ B := Finset.disjoint_left.mp h_disj ha1_A
  have h_a2_not_B : a₂ ∉ B := Finset.disjoint_left.mp h_disj ha2_A
  have h_a1_ne_b1 : a₁ ≠ b₁ := fun h => h_a1_not_B (h ▸ hb1_B)
  have h_a1_ne_b2 : a₁ ≠ b₂ := fun h => h_a1_not_B (h ▸ hb2_B)
  have h_a2_ne_b1 : a₂ ≠ b₁ := fun h => h_a2_not_B (h ▸ hb1_B)
  have h_a2_ne_b2 : a₂ ≠ b₂ := fun h => h_a2_not_B (h ▸ hb2_B)
  have h4 : ({a₁, a₂, b₁, b₂} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_insert_of_not_mem, Finset.card_singleton]
    · simp [h_a2_ne_b2, h_a2_ne_b1]
    · simp [h_a1_ne_b2, h_a1_ne_b1]
    · simp [ha12]
  have h_sub : ({a₁, a₂, b₁, b₂} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card h_sub
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 STRUCTURAL PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

/-- In Path_4, no external triangle bridges A and C -/
lemma path4_no_AC_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(sharesEdgeWith t cfg.A ∧ sharesEdgeWith t cfg.C) := by
  intro ⟨h_share_A, h_share_C⟩
  have hA_card : cfg.A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hA).card_eq
  have hC_card : cfg.C.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hC).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint cfg.A cfg.C t hA_card hC_card ht_card cfg.h_AC h_share_A h_share_C

/-- In Path_4, no external triangle bridges B and D -/
lemma path4_no_BD_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(sharesEdgeWith t cfg.B ∧ sharesEdgeWith t cfg.D) := by
  intro ⟨h_share_B, h_share_D⟩
  have hB_card : cfg.B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hB).card_eq
  have hD_card : cfg.D.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hD).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint cfg.B cfg.D t hB_card hD_card ht_card cfg.h_BD h_share_B h_share_D

/-- Extract the shared vertex from A ∩ B -/
lemma path4_shared_vertex_AB (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4Config G) :
    ∃ v, cfg.A ∩ cfg.B = {v} := by
  have h := cfg.h_AB
  unfold sharesOneVertex at h
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h
  exact ⟨v, hv⟩

/-- Extract the shared vertex from B ∩ C -/
lemma path4_shared_vertex_BC (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4Config G) :
    ∃ v, cfg.B ∩ cfg.C = {v} := by
  have h := cfg.h_BC
  unfold sharesOneVertex at h
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h
  exact ⟨v, hv⟩

/-- Extract the shared vertex from C ∩ D -/
lemma path4_shared_vertex_CD (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4Config G) :
    ∃ v, cfg.C ∩ cfg.D = {v} := by
  have h := cfg.h_CD
  unfold sharesOneVertex at h
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h
  exact ⟨v, hv⟩

end
