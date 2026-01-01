/-
Tuza ν=4 Strategy - Slot 150: Matching_2 Structure Analysis

TARGET: Analyze the matching_2 configuration where M = {(A-B), (C-D)}.

STRUCTURE:
- A shares exactly one vertex with B (pair 1)
- C shares exactly one vertex with D (pair 2)
- No shared vertices between pairs: A,B disjoint from C,D

KEY INSIGHT:
- This is essentially TWO independent T_pair problems!
- By no_bridge_disjoint: no external bridges the two pairs
- Each pair's triangles are independent of the other pair

PROVEN SCAFFOLDING:
- no_bridge_disjoint: No triangle bridges disjoint M-elements

ZERO SORRIES EXPECTED
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

def sharesOneVertex (A B : Finset V) : Prop :=
  (A ∩ B).card = 1

/-- Matching_2 configuration: (A-B) and (C-D) are two independent pairs -/
structure Matching2Config (G : SimpleGraph V) [DecidableRel G.Adj] where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ G.cliqueFinset 3
  hB : B ∈ G.cliqueFinset 3
  hC : C ∈ G.cliqueFinset 3
  hD : D ∈ G.cliqueFinset 3
  h_AB : sharesOneVertex A B
  h_CD : sharesOneVertex C D
  h_AC : Disjoint A C
  h_AD : Disjoint A D
  h_BC : Disjoint B C
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
-- MATCHING_2 STRUCTURAL PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

/-- In Matching_2, no external triangle bridges A and C -/
lemma matching2_no_AC_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Matching2Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(sharesEdgeWith t cfg.A ∧ sharesEdgeWith t cfg.C) := by
  intro ⟨h_share_A, h_share_C⟩
  have hA_card : cfg.A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hA).card_eq
  have hC_card : cfg.C.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hC).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint cfg.A cfg.C t hA_card hC_card ht_card cfg.h_AC h_share_A h_share_C

/-- In Matching_2, no external triangle bridges A and D -/
lemma matching2_no_AD_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Matching2Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(sharesEdgeWith t cfg.A ∧ sharesEdgeWith t cfg.D) := by
  intro ⟨h_share_A, h_share_D⟩
  have hA_card : cfg.A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hA).card_eq
  have hD_card : cfg.D.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hD).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint cfg.A cfg.D t hA_card hD_card ht_card cfg.h_AD h_share_A h_share_D

/-- In Matching_2, no external triangle bridges B and C -/
lemma matching2_no_BC_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Matching2Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(sharesEdgeWith t cfg.B ∧ sharesEdgeWith t cfg.C) := by
  intro ⟨h_share_B, h_share_C⟩
  have hB_card : cfg.B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hB).card_eq
  have hC_card : cfg.C.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hC).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint cfg.B cfg.C t hB_card hC_card ht_card cfg.h_BC h_share_B h_share_C

/-- In Matching_2, no external triangle bridges B and D -/
lemma matching2_no_BD_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Matching2Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(sharesEdgeWith t cfg.B ∧ sharesEdgeWith t cfg.D) := by
  intro ⟨h_share_B, h_share_D⟩
  have hB_card : cfg.B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hB).card_eq
  have hD_card : cfg.D.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hD).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint cfg.B cfg.D t hB_card hD_card ht_card cfg.h_BD h_share_B h_share_D

/-- KEY THEOREM: External triangles touch at most one pair.
    An external triangle shares edge with at most one of {A,B} or at most one of {C,D}. -/
theorem matching2_independent_pairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Matching2Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    (sharesEdgeWith t cfg.A ∨ sharesEdgeWith t cfg.B) →
    (sharesEdgeWith t cfg.C ∨ sharesEdgeWith t cfg.D) →
    False := by
  intro h_pair1 h_pair2
  rcases h_pair1 with h_A | h_B
  · rcases h_pair2 with h_C | h_D
    · exact matching2_no_AC_bridge G cfg t ht ⟨h_A, h_C⟩
    · exact matching2_no_AD_bridge G cfg t ht ⟨h_A, h_D⟩
  · rcases h_pair2 with h_C | h_D
    · exact matching2_no_BC_bridge G cfg t ht ⟨h_B, h_C⟩
    · exact matching2_no_BD_bridge G cfg t ht ⟨h_B, h_D⟩

/-- COROLLARY: Triangles partition into pair-1 triangles and pair-2 triangles -/
theorem matching2_triangle_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Matching2Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (h_touches_AB : sharesEdgeWith t cfg.A ∨ sharesEdgeWith t cfg.B)
    (h_touches_CD : sharesEdgeWith t cfg.C ∨ sharesEdgeWith t cfg.D) :
    False :=
  matching2_independent_pairs G cfg t ht h_touches_AB h_touches_CD

end
