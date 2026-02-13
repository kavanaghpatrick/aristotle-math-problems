/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f0581631-f983-4a98-a059-d6a2dbfc93bb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot509_Se_prime_disjoint.lean

  SINGLE TARGET: S_e' sets are pairwise disjoint

  Key insight: If T ∈ S_e' ∩ S_f', then T shares edge with both e and f.
  But min-index forces T to be in exactly one - the one with smaller idx.

  TIER: 2 (set disjointness with injectivity)
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def sharesEdgeWith (M : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  M.filter (fun e => 2 ≤ (T ∩ e).card)

def S_e' (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V)
    (idx : Finset V → ℕ) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧
    2 ≤ (T ∩ e).card ∧
    (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 1: Membership unpacking
-- ══════════════════════════════════════════════════════════════════════════════

lemma mem_S_e'_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e T : Finset V) (idx : Finset V → ℕ) :
    T ∈ S_e' G M e idx ↔
      T ∈ G.cliqueFinset 3 ∧ T ≠ e ∧ 2 ≤ (T ∩ e).card ∧
      (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅ := by
  simp only [S_e', mem_filter, and_assoc]

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 2: T ∈ S_e' implies T shares edge with e
-- ══════════════════════════════════════════════════════════════════════════════

lemma S_e'_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e T : Finset V) (idx : Finset V → ℕ)
    (hT : T ∈ S_e' G M e idx) : 2 ≤ (T ∩ e).card := by
  rw [mem_S_e'_iff] at hT
  exact hT.2.2.1

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 3: T ∈ S_e' implies e has min index among shared
-- ══════════════════════════════════════════════════════════════════════════════

lemma S_e'_min_idx (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e T : Finset V) (idx : Finset V → ℕ)
    (hT : T ∈ S_e' G M e idx) :
    (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅ := by
  rw [mem_S_e'_iff] at hT
  exact hT.2.2.2

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 4: If e shares edge with T and e ∈ M, then e ∈ sharesEdgeWith
-- ══════════════════════════════════════════════════════════════════════════════

lemma mem_sharesEdgeWith_of_inter (M : Finset (Finset V)) (T e : Finset V)
    (he_M : e ∈ M) (h_inter : 2 ≤ (T ∩ e).card) :
    e ∈ sharesEdgeWith M T := by
  simp only [sharesEdgeWith, mem_filter]
  exact ⟨he_M, h_inter⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 5: Contradiction from both having min index
-- ══════════════════════════════════════════════════════════════════════════════

lemma no_two_min_indices (e f : Finset V) (idx : Finset V → ℕ)
    (S : Finset (Finset V)) (he : e ∈ S) (hf : f ∈ S) (hef : e ≠ f)
    (he_min : S.filter (fun g => idx g < idx e) = ∅)
    (hf_min : S.filter (fun g => idx g < idx f) = ∅)
    (h_inj : Function.Injective idx) : False := by
  by_cases h : idx e < idx f
  · -- e has smaller index, so e ∈ filter for f
    have : e ∈ S.filter (fun g => idx g < idx f) := by
      simp only [mem_filter]
      exact ⟨he, h⟩
    rw [hf_min] at this
    exact not_mem_empty e this
  · push_neg at h
    cases' Nat.lt_or_eq_of_le h with h_lt h_eq
    · -- f has smaller index, so f ∈ filter for e
      have : f ∈ S.filter (fun g => idx g < idx e) := by
        simp only [mem_filter]
        exact ⟨hf, h_lt⟩
      rw [he_min] at this
      exact not_mem_empty f this
    · -- idx e = idx f, contradicts injectivity
      exact hef (h_inj h_eq)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 6: If T shares edge with e and f, both are in sharesEdgeWith
-- ══════════════════════════════════════════════════════════════════════════════

lemma both_in_sharesEdgeWith (M : Finset (Finset V)) (T e f : Finset V)
    (he : e ∈ M) (hf : f ∈ M)
    (he_inter : 2 ≤ (T ∩ e).card) (hf_inter : 2 ≤ (T ∩ f).card) :
    e ∈ sharesEdgeWith M T ∧ f ∈ sharesEdgeWith M T := by
  constructor
  · exact mem_sharesEdgeWith_of_inter M T e he he_inter
  · exact mem_sharesEdgeWith_of_inter M T f hf hf_inter

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 7: disjoint_iff_ne for Finset
-- ══════════════════════════════════════════════════════════════════════════════

lemma disjoint_iff_forall_ne (A B : Finset (Finset V)) :
    Disjoint A B ↔ ∀ x ∈ A, ∀ y ∈ B, x ≠ y := Finset.disjoint_iff_ne

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: S_e' sets are disjoint
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Suppose T ∈ S_e' ∩ S_f' for e ≠ f
2. Then T shares edge with e (2 ≤ (T ∩ e).card) and with f (2 ≤ (T ∩ f).card)
3. Both e and f are in sharesEdgeWith M T
4. T ∈ S_e' means no g with idx g < idx e in sharesEdgeWith
5. T ∈ S_f' means no g with idx g < idx f in sharesEdgeWith
6. By no_two_min_indices, this is impossible when e ≠ f and idx is injective
7. Contradiction, so S_e' and S_f' are disjoint
-/
theorem S_e'_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx) :
    Disjoint (S_e' G M e idx) (S_e' G M f idx) := by
  rw [Finset.disjoint_iff_ne]
  intro T hT_e T' hT_f hTT'
  subst hTT'
  -- T shares edge with both e and f
  have he_inter := S_e'_shares_edge G M e T idx hT_e
  have hf_inter := S_e'_shares_edge G M f T idx hT_f
  -- Both e and f are in sharesEdgeWith M T
  have ⟨he_shares, hf_shares⟩ := both_in_sharesEdgeWith M T e f he hf he_inter hf_inter
  -- Both have "min index" property
  have he_min := S_e'_min_idx G M e T idx hT_e
  have hf_min := S_e'_min_idx G M f T idx hT_f
  -- Contradiction
  exact no_two_min_indices e f idx (sharesEdgeWith M T) he_shares hf_shares hef he_min hf_min h_inj

end