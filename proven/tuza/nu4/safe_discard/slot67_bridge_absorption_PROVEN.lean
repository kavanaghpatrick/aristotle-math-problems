/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c522a35a-27ef-4d6a-820d-764bfc403092
-/

/-
Tuza ν=4 Strategy - Slot 67: Bridge Absorption

TARGET: Triangles bridging disjoint M-elements are "free" (don't add to τ)

THEOREM (bridge_absorption):
  If A, B ∈ M are vertex-disjoint (Disjoint A B),
  and triangle T shares an edge with both A and B,
  then T is automatically covered by any cover of A's or B's edges.

INTUITION:
  - T shares edge with A means T contains an edge {a₁, a₂} ⊆ A
  - T shares edge with B means T contains an edge {b₁, b₂} ⊆ B
  - But |T| = 3, and {a₁,a₂} ∩ {b₁,b₂} = ∅ (since A ∩ B = ∅)
  - So T has 4 distinct vertices? Contradiction! T can only have 3.
  - Therefore: no triangle can share edges with BOTH of two disjoint M-elements

This means triangles "bridging" disjoint pairs don't exist, so they don't add to τ.

STATUS: Key structural lemma - Aristotle should prove this
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA: No triangle shares edge with two disjoint M-elements
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle shares an edge with a set if some edge is in both sym2s -/
def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ e, e ∈ t.sym2 ∧ e ∈ S.sym2

/-- CORE LEMMA: No triangle can share an edge with each of two disjoint triangles.
    This is a pure combinatorial fact about 3-sets. -/
lemma no_bridge_disjoint (A B t : Finset V)
    (hA : A.card = 3) (hB : B.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint A B)
    (h_share_A : sharesEdgeWith t A)
    (h_share_B : sharesEdgeWith t B) :
    False := by
  -- t shares edge {a₁, a₂} with A
  obtain ⟨eA, heA_t, heA_A⟩ := h_share_A
  rw [Finset.mem_sym2_iff] at heA_t heA_A
  obtain ⟨a₁, a₂, ha12, ha1_t, ha2_t, rfl⟩ := heA_t
  obtain ⟨a₁', a₂', _, ha1'_A, ha2'_A, heq_A⟩ := heA_A
  simp only [Sym2.eq, Sym2.rel_iff] at heq_A
  -- t shares edge {b₁, b₂} with B
  obtain ⟨eB, heB_t, heB_B⟩ := h_share_B
  rw [Finset.mem_sym2_iff] at heB_t heB_B
  obtain ⟨b₁, b₂, hb12, hb1_t, hb2_t, rfl⟩ := heB_t
  obtain ⟨b₁', b₂', _, hb1'_B, hb2'_B, heq_B⟩ := heB_B
  simp only [Sym2.eq, Sym2.rel_iff] at heq_B
  -- a₁, a₂ ∈ A and b₁, b₂ ∈ B
  have ha1_A : a₁ ∈ A := by
    rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have ha2_A : a₂ ∈ A := by
    rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb1_B : b₁ ∈ B := by
    rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb2_B : b₂ ∈ B := by
    rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  -- {a₁, a₂} ∩ {b₁, b₂} = ∅ (since A ∩ B = ∅)
  have h_a1_not_B : a₁ ∉ B := Finset.disjoint_left.mp h_disj ha1_A
  have h_a2_not_B : a₂ ∉ B := Finset.disjoint_left.mp h_disj ha2_A
  have h_a1_ne_b1 : a₁ ≠ b₁ := fun h => h_a1_not_B (h ▸ hb1_B)
  have h_a1_ne_b2 : a₁ ≠ b₂ := fun h => h_a1_not_B (h ▸ hb2_B)
  have h_a2_ne_b1 : a₂ ≠ b₁ := fun h => h_a2_not_B (h ▸ hb1_B)
  have h_a2_ne_b2 : a₂ ≠ b₂ := fun h => h_a2_not_B (h ▸ hb2_B)
  -- All of a₁, a₂, b₁, b₂ ∈ t, and they're 4 distinct vertices
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
-- BRIDGE ABSORPTION THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- Bridge triangles don't exist for disjoint M-elements.
    This means: for disjoint A, B ∈ M, no external triangle T can share edges with both. -/
theorem bridge_nonexistence (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (h_disj : Disjoint A B)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(sharesEdgeWith t A ∧ sharesEdgeWith t B) := by
  intro ⟨h_share_A, h_share_B⟩
  have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hA)).card_eq
  have hB_card : B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hB)).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint A B t hA_card hB_card ht_card h_disj h_share_A h_share_B

/-- Corollary: For disjoint M-elements, external triangles share edge with at most one. -/
theorem external_unique_disjoint_parent (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_M : t ∉ M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (h_disj : Disjoint A B)
    (h_share_A : sharesEdgeWith t A) :
    ¬sharesEdgeWith t B := by
  intro h_share_B
  exact bridge_nonexistence G M hM A B hA hB hAB h_disj t ht ⟨h_share_A, h_share_B⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- APPLICATION: Scattered Case (All M-elements pairwise disjoint)
-- ══════════════════════════════════════════════════════════════════════════════

/-- In the scattered case (all M-elements disjoint), each external triangle
    shares edge with exactly one M-element. -/
theorem scattered_unique_parent (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (h_scattered : ∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_M : t ∉ M)
    (A : Finset V) (hA : A ∈ M) (h_share_A : sharesEdgeWith t A) :
    ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B := by
  intro B hB hBA
  exact external_unique_disjoint_parent G M hM t ht ht_not_M A B hA hB hBA.symm (h_scattered A B hA hB hBA.symm) h_share_A

/-- In the scattered case, there are no interactions between M-edges from
    different M-elements. This means the Interaction Graph is empty! -/
theorem scattered_ig_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (h_scattered : ∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B)
    (e₁ e₂ : Sym2 V)
    (he₁ : ∃ A ∈ M, e₁ ∈ A.sym2)
    (he₂ : ∃ B ∈ M, e₂ ∈ B.sym2)
    (h_diff_parent : ∀ X ∈ M, ¬(e₁ ∈ X.sym2 ∧ e₂ ∈ X.sym2)) :
    ∀ t ∈ G.cliqueFinset 3, t ∉ M → ¬(e₁ ∈ t.sym2 ∧ e₂ ∈ t.sym2) := by
  intro t ht ht_not_M ⟨he₁_t, he₂_t⟩
  obtain ⟨A, hA, he₁_A⟩ := he₁
  obtain ⟨B, hB, he₂_B⟩ := he₂
  -- e₁ ∈ A.sym2, e₂ ∈ B.sym2, and e₁ ≠ e₂ from different parents
  have hAB : A ≠ B := by
    intro heq
    exact h_diff_parent A hA ⟨he₁_A, heq ▸ he₂_B⟩
  -- t shares edge with both A (via e₁) and B (via e₂)
  have h_share_A : sharesEdgeWith t A := ⟨e₁, he₁_t, he₁_A⟩
  have h_share_B : sharesEdgeWith t B := ⟨e₂, he₂_t, he₂_B⟩
  -- Contradiction from bridge_nonexistence
  exact bridge_nonexistence G M hM A B hA hB hAB (h_scattered A B hA hB hAB) t ht ⟨h_share_A, h_share_B⟩

end