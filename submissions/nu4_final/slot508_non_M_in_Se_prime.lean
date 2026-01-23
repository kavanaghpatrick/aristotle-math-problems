/-
  slot508_non_M_in_Se_prime.lean

  SINGLE TARGET: non_M_triangle_in_some_Se'

  Every non-M triangle is assigned to exactly one S_e' via min-index.
  This is the KEY lemma that fixes the bridge partition problem.

  TIER: 2 (min-index selection on finite set)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot506)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaximalPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ e ∈ M, (T ∩ e).card ≥ 2

def sharesEdgeWith (M : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  M.filter (fun e => 2 ≤ (T ∩ e).card)

def S_e' (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V)
    (idx : Finset V → ℕ) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧
    2 ≤ (T ∩ e).card ∧
    (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 1: sharesEdgeWith is nonempty for non-M triangles
-- ══════════════════════════════════════════════════════════════════════════════

lemma sharesEdgeWith_nonempty_of_maximal (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) (hT_notM : T ∉ M) :
    (sharesEdgeWith M T).Nonempty := by
  obtain ⟨e, he, he_inter⟩ := hM.2 T hT hT_notM
  exact ⟨e, mem_filter.mpr ⟨he, he_inter⟩⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 2: Nonempty finset has minimum under any function
-- ══════════════════════════════════════════════════════════════════════════════

lemma exists_min_of_nonempty (S : Finset (Finset V)) (hS : S.Nonempty) (f : Finset V → ℕ) :
    ∃ e ∈ S, ∀ x ∈ S, f e ≤ f x := by
  have : (S.image f).Nonempty := Nonempty.image hS f
  obtain ⟨m, hm⟩ := Finset.min'_mem (S.image f) this
  obtain ⟨e, he_S, he_f⟩ := mem_image.mp hm
  use e, he_S
  intro x hx
  have : f x ∈ S.image f := mem_image.mpr ⟨x, hx, rfl⟩
  rw [← he_f]
  exact Finset.min'_le (S.image f) (f x) this

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 3: Minimum element satisfies filter condition
-- ══════════════════════════════════════════════════════════════════════════════

lemma min_satisfies_filter (S : Finset (Finset V)) (e : Finset V) (he : e ∈ S)
    (f : Finset V → ℕ) (h_min : ∀ x ∈ S, f e ≤ f x) :
    S.filter (fun x => f x < f e) = ∅ := by
  ext x
  simp only [mem_filter, not_mem_empty, iff_false, not_and]
  intro hx
  have := h_min x hx
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 4: T ≠ e when T ∉ M and e ∈ M
-- ══════════════════════════════════════════════════════════════════════════════

lemma ne_of_not_mem_of_mem (T e : Finset V) (M : Finset (Finset V))
    (hT : T ∉ M) (he : e ∈ M) : T ≠ e := by
  intro h
  rw [h] at hT
  exact hT he

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 5: sharesEdgeWith subset of M
-- ══════════════════════════════════════════════════════════════════════════════

lemma sharesEdgeWith_subset_M (M : Finset (Finset V)) (T : Finset V) :
    sharesEdgeWith M T ⊆ M := filter_subset _ M

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 6: Element of sharesEdgeWith has ≥2 intersection
-- ══════════════════════════════════════════════════════════════════════════════

lemma mem_sharesEdgeWith_iff (M : Finset (Finset V)) (T e : Finset V) :
    e ∈ sharesEdgeWith M T ↔ e ∈ M ∧ 2 ≤ (T ∩ e).card := mem_filter

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 7: Min element is in M
-- ══════════════════════════════════════════════════════════════════════════════

lemma min_in_M (M : Finset (Finset V)) (T : Finset V) (e : Finset V)
    (he : e ∈ sharesEdgeWith M T) : e ∈ M :=
  (mem_sharesEdgeWith_iff M T e).mp he |>.1

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 8: Min element has ≥2 intersection with T
-- ══════════════════════════════════════════════════════════════════════════════

lemma min_has_intersection (M : Finset (Finset V)) (T : Finset V) (e : Finset V)
    (he : e ∈ sharesEdgeWith M T) : 2 ≤ (T ∩ e).card :=
  (mem_sharesEdgeWith_iff M T e).mp he |>.2

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 9: T is a triangle (in cliqueFinset 3)
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_mem_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T ∈ G.cliqueFinset 3 := hT

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 10: Membership in S_e' unpacked
-- ══════════════════════════════════════════════════════════════════════════════

lemma mem_S_e'_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e T : Finset V) (idx : Finset V → ℕ) :
    T ∈ S_e' G M e idx ↔
      T ∈ G.cliqueFinset 3 ∧
      T ≠ e ∧
      2 ≤ (T ∩ e).card ∧
      (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅ := by
  simp only [S_e', mem_filter]
  constructor
  · intro ⟨hT_clique, hT_ne, hT_inter, hT_min⟩
    exact ⟨hT_clique, hT_ne, hT_inter, hT_min⟩
  · intro ⟨hT_clique, hT_ne, hT_inter, hT_min⟩
    exact ⟨hT_clique, hT_ne, hT_inter, hT_min⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Every non-M triangle is in some S_e'
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. By maximality, T shares edge with some M-element, so sharesEdgeWith M T ≠ ∅
2. By exists_min_of_nonempty, get e_min with minimum idx among sharesEdgeWith M T
3. By min_satisfies_filter, the filter condition is satisfied
4. e_min ∈ M by min_in_M
5. 2 ≤ (T ∩ e_min).card by min_has_intersection
6. T ≠ e_min since T ∉ M and e_min ∈ M
7. Therefore T ∈ S_e_min' by mem_S_e'_iff
-/
theorem non_M_triangle_in_some_Se' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) (hT_notM : T ∉ M) :
    ∃ e ∈ M, T ∈ S_e' G M e idx := by
  -- Step 1: sharesEdgeWith M T is nonempty
  have h_nonempty := sharesEdgeWith_nonempty_of_maximal G M hM T hT hT_notM
  -- Step 2: Get minimum element
  obtain ⟨e_min, he_min_shares, he_min_le⟩ := exists_min_of_nonempty _ h_nonempty idx
  -- Step 3: e_min ∈ M
  have he_min_M := min_in_M M T e_min he_min_shares
  use e_min, he_min_M
  -- Step 4: Show T ∈ S_e_min'
  rw [mem_S_e'_iff]
  refine ⟨hT, ?_, ?_, ?_⟩
  -- T ≠ e_min
  · exact ne_of_not_mem_of_mem T e_min M hT_notM he_min_M
  -- 2 ≤ (T ∩ e_min).card
  · exact min_has_intersection M T e_min he_min_shares
  -- Filter is empty
  · exact min_satisfies_filter (sharesEdgeWith M T) e_min he_min_shares idx he_min_le

end
