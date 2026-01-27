/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b00ae710-4674-4050-88f8-a2dffacef8f7
-/

/-
  slot393_endpoint_external_edge.lean

  Tuza ν=4 PATH_4: Endpoint External Edge Theorem

  3-AGENT DEBATE CONSENSUS (Round 3):
  This proves that any external triangle sharing an edge with endpoint A
  must contain at least 2 vertices of A (forming an edge of A).

  KEY INSIGHT: This is SIMPLER than interior (slot390, slot392) because:
  - Interior: Must identify SPECIFIC shared vertices (v₁ or v₂)
  - Endpoint: ANY 2 vertices of A form an edge (trivial pigeonhole)

  PROOF: By definition of S_e, any T ∈ S_A satisfies (T ∩ A).card ≥ 2.
  Therefore T contains at least 2 vertices of A, which form an edge.

  WHY THIS MATTERS:
  - S_A is covered by the 3 edges of A (at most 3 edges needed)
  - Combined with slot390/slot392: Interior contributes 0 edges
  - Total: 3(A) + 2(spine) + 3(D) = 8 edges → τ ≤ 8

  TIER: 1 (Even simpler than slot390 which succeeded with 0 sorry)
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (same as slot390/392)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Endpoint externals contain an edge of A
-- ══════════════════════════════════════════════════════════════════════════════

/-- Any triangle in S_A contains at least 2 vertices of A (which form an edge of A) -/
theorem endpoint_external_contains_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V)
    (hA_tri : A ∈ G.cliqueFinset 3)
    (T : Finset V)
    (hT_in_SA : T ∈ S_e G M A) :
    ∃ u v : V, u ∈ A ∧ v ∈ A ∧ u ≠ v ∧ u ∈ T ∧ v ∈ T := by
  have hT_share : (T ∩ A).card ≥ 2 := by
    simp only [S_e, trianglesSharingEdge, mem_filter] at hT_in_SA
    exact hT_in_SA.1.2
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hT_share
  use u, v
  exact ⟨mem_of_mem_inter_right hu, mem_of_mem_inter_right hv, huv,
         mem_of_mem_inter_left hu, mem_of_mem_inter_left hv⟩

/-- The edge {u, v} from T ∩ A is actually an edge of the graph -/
theorem endpoint_external_edge_in_graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V)
    (hA_tri : A ∈ G.cliqueFinset 3)
    (T : Finset V)
    (hT_in_SA : T ∈ S_e G M A)
    (u v : V) (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v) :
    G.Adj u v := by
  have hA_clique := G.mem_cliqueFinset_iff.mp hA_tri
  exact hA_clique.1 hu hv huv

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: S_A is covered by edges of A (at most 3 edges)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle in S_A is hit by some edge of A -/
theorem endpoint_S_covered_by_A_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V)
    (hA_tri : A ∈ G.cliqueFinset 3) :
    ∀ T ∈ S_e G M A, ∃ u v : V, u ∈ A ∧ v ∈ A ∧ u ≠ v ∧ u ∈ T ∧ v ∈ T :=
  fun T hT => endpoint_external_contains_edge G M A hA_tri T hT

/-- A triangle has exactly 3 edges, so S_A needs at most 3 edges to cover -/
theorem endpoint_cover_size_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V)
    (hA_tri : A ∈ G.cliqueFinset 3) :
    ∃ (cover : Finset (Sym2 V)), cover.card ≤ 3 ∧
      ∀ T ∈ S_e G M A, ∃ e ∈ cover, ∃ u v : V, e = s(u, v) ∧ u ∈ T ∧ v ∈ T := by
  -- The 3 edges of A form the cover
  have hA_card : A.card = 3 := (G.mem_cliqueFinset_iff.mp hA_tri).2
  obtain ⟨a, b, c, hab, hac, hbc, hA_eq⟩ : ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ A = {a, b, c} := by
    have h3 := hA_card
    obtain ⟨a, ha⟩ := card_pos.mp (by omega : 0 < A.card)
    have hrest : (A.erase a).card = 2 := by simp [card_erase_of_mem ha, h3]
    obtain ⟨b, hb⟩ := card_pos.mp (by omega : 0 < (A.erase a).card)
    have hb' := mem_erase.mp hb
    have hrest2 : ((A.erase a).erase b).card = 1 := by
      simp [card_erase_of_mem hb, hrest]
    obtain ⟨c, hc⟩ := card_eq_one.mp hrest2
    have hc' := mem_erase.mp (mem_of_eq_singleton hc)
    have hc'' := mem_erase.mp hc'.1
    use a, b, c
    refine ⟨hb'.1.symm, hc''.1.symm, hc'.1.symm, ?_⟩
    ext x
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hx
      by_cases hxa : x = a
      · left; exact hxa
      · by_cases hxb : x = b
        · right; left; exact hxb
        · right; right
          have : x ∈ (A.erase a).erase b := mem_erase.mpr ⟨hxb, mem_erase.mpr ⟨hxa, hx⟩⟩
          rw [hc] at this
          exact mem_singleton.mp this
    · intro hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact mem_of_mem_erase hb
      · exact mem_of_mem_erase (mem_of_mem_erase (mem_of_eq_singleton hc))
  -- Define the cover as the 3 edges of A
  let cover : Finset (Sym2 V) := {s(a, b), s(a, c), s(b, c)}
  use cover
  constructor
  · -- cover.card ≤ 3
    have h1 : s(a, b) ≠ s(a, c) := by
      simp only [Sym2.eq, Sym2.rel_iff']
      push_neg
      constructor
      · intro h; exact hbc (h.2.symm)
      · intro h; exact hab h.1
    have h2 : s(a, b) ≠ s(b, c) := by
      simp only [Sym2.eq, Sym2.rel_iff']
      push_neg
      constructor
      · intro h; exact hac h.2
      · intro h; exact hab h.2.symm
    have h3 : s(a, c) ≠ s(b, c) := by
      simp only [Sym2.eq, Sym2.rel_iff']
      push_neg
      constructor
      · intro h; exact hab h.1.symm
      · intro h; exact hac h.1
    simp only [cover, card_insert_of_not_mem, card_singleton, mem_insert, mem_singleton]
    simp [h1, h2, h3]
  · -- Every T in S_A contains one of these edges
    intro T hT
    obtain ⟨u, v, hu_in_A, hv_in_A, huv, hu_in_T, hv_in_T⟩ :=
      endpoint_external_contains_edge G M A hA_tri T hT
    rw [hA_eq] at hu_in_A hv_in_A
    simp only [mem_insert, mem_singleton] at hu_in_A hv_in_A
    -- Case analysis on which vertices u, v are
    rcases hu_in_A with rfl | rfl | rfl <;> rcases hv_in_A with rfl | rfl | rfl
    · exact absurd rfl huv
    · exact ⟨s(a, b), by simp [cover], a, b, rfl, hu_in_T, hv_in_T⟩
    · exact ⟨s(a, c), by simp [cover], a, c, rfl, hu_in_T, hv_in_T⟩
    · exact ⟨s(a, b), by simp [cover], a, b, Sym2.eq_swap.mpr rfl, hv_in_T, hu_in_T⟩
    · exact absurd rfl huv
    · exact ⟨s(b, c), by simp [cover], b, c, rfl, hu_in_T, hv_in_T⟩
    · exact ⟨s(a, c), by simp [cover], a, c, Sym2.eq_swap.mpr rfl, hv_in_T, hu_in_T⟩
    · exact ⟨s(b, c), by simp [cover], b, c, Sym2.eq_swap.mpr rfl, hv_in_T, hu_in_T⟩
    · exact absurd rfl huv

end