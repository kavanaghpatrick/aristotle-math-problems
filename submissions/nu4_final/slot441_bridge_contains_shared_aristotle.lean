/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 67c528b3-7c3d-49f0-ae40-6d0212d2e66f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot441_bridge_contains_shared_fixed.lean

  FIXES from slot440:
  1. Line 66: Simplified rcases pattern
  2. Line 86: Changed `corollary` to `theorem` (not valid Lean4 keyword)
  3. Line 102: Removed omega_nat (not a valid tactic)

  SIMPLE TARGET: Prove the bridge containment lemma via cardinality bounds.

  If T is a bridge between E and F (sharing only vertex v), then v ∈ T.

  PROOF: Pure inclusion-exclusion on cardinalities.
  1. |T ∩ E| ≥ 2, |T ∩ F| ≥ 2
  2. E ∩ F = {v}
  3. |T| = 3
  4. (T ∩ E) ∩ (T ∩ F) = T ∩ (E ∩ F) = T ∩ {v}
  5. By inclusion-exclusion: |T ∩ E| + |T ∩ F| - |T ∩ {v}| ≤ 3
  6. So: 4 - |T ∩ {v}| ≤ 3, meaning |T ∩ {v}| ≥ 1
  7. Therefore v ∈ T

  TIER: 1 (simple cardinality/set theory)
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

lemma inter_inter_eq_inter_inter' (T E F : Finset V) :
    (T ∩ E) ∩ (T ∩ F) = T ∩ (E ∩ F) := by
  ext x
  simp only [mem_inter]
  tauto

lemma union_subset_of_inter_subset (T E F : Finset V) :
    (T ∩ E) ∪ (T ∩ F) ⊆ T := by
  intro x hx
  simp only [mem_union, mem_inter] at hx
  cases hx with
  | inl h => exact h.1
  | inr h => exact h.1

lemma nonempty_inter_singleton_iff (A : Finset V) (v : V) :
    (A ∩ {v}).Nonempty ↔ v ∈ A := by
  constructor
  · intro ⟨x, hx⟩
    simp only [mem_inter, mem_singleton] at hx
    exact hx.2 ▸ hx.1
  · intro hv
    exact ⟨v, mem_inter.mpr ⟨hv, mem_singleton_self v⟩⟩

lemma card_inter_singleton_pos_iff (A : Finset V) (v : V) :
    0 < (A ∩ {v}).card ↔ v ∈ A := by
  rw [card_pos, nonempty_inter_singleton_iff]

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

theorem bridge_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v : V) (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : 2 ≤ (T ∩ E).card) (hTF : 2 ≤ (T ∩ F).card) :
    v ∈ T := by
  -- T has exactly 3 elements
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT
    exact hT.2
  -- Key set-theoretic identity
  have h_inter : (T ∩ E) ∩ (T ∩ F) = T ∩ {v} := by
    rw [inter_inter_eq_inter_inter', hEF]
  -- Union is subset of T
  have h_sub : (T ∩ E) ∪ (T ∩ F) ⊆ T := union_subset_of_inter_subset T E F
  -- Union has at most 3 elements
  have h_union_le : ((T ∩ E) ∪ (T ∩ F)).card ≤ 3 := by
    calc ((T ∩ E) ∪ (T ∩ F)).card ≤ T.card := card_le_card h_sub
      _ = 3 := hT_card
  -- Inclusion-exclusion identity
  have h_ie := card_union_add_card_inter (T ∩ E) (T ∩ F)
  -- Derive bound on intersection
  have h_pos : 0 < (T ∩ {v}).card := by
    rw [← h_inter]
    -- h_ie: |(T∩E) ∪ (T∩F)| + |(T∩E) ∩ (T∩F)| = |T∩E| + |T∩F|
    -- |T∩E| + |T∩F| ≥ 4
    -- |(T∩E) ∪ (T∩F)| ≤ 3
    -- So |(T∩E) ∩ (T∩F)| ≥ 1
    have h_sum : (T ∩ E).card + (T ∩ F).card ≥ 4 := by omega
    omega
  -- Conclude v ∈ T
  rwa [card_inter_singleton_pos_iff] at h_pos

-- ══════════════════════════════════════════════════════════════════════════════
-- IMMEDIATE COROLLARIES
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every bridge between adjacent elements E and F contains their shared vertex -/
theorem bridge_shares_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (E F T : Finset V) (v : V)
    (hE : E ∈ M) (hF : F ∈ M) (hEF_ne : E ≠ F)
    (hEF_inter : E ∩ F = {v})
    (hT : T ∈ G.cliqueFinset 3)
    (hTE : 2 ≤ (T ∩ E).card) (hTF : 2 ≤ (T ∩ F).card) :
    v ∈ T :=
  bridge_contains_shared G E F v hEF_inter T hT hTE hTF

/-- The shared vertex is in both the bridge and the parent elements -/
lemma shared_vertex_membership (E F : Finset V) (v : V) (hEF : E ∩ F = {v}) :
    v ∈ E ∧ v ∈ F := by
  have hv : v ∈ E ∩ F := by rw [hEF]; exact mem_singleton_self v
  exact mem_inter.mp hv

/-- Any edge from v in E covers bridges to F -/
lemma edge_from_v_covers_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v u : V)
    (hEF : E ∩ F = {v})
    (hv : v ∈ E) (hu : u ∈ E)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : 2 ≤ (T ∩ E).card) (hTF : 2 ≤ (T ∩ F).card)
    (huT : u ∈ T) :
    s(v, u) ∈ T.sym2 := by
  have hv_T := bridge_contains_shared G E F v hEF T hT hTE hTF
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨hv_T, huT⟩

end