/-
Tuza's Conjecture for ν ≤ 3: Final Assembly

PROVEN by Aristotle:
- ν=0: τ=0 (tuza_case_nu_0)
- ν=1: τ≤2 (nu_eq_1_implies_tau_le_2)
- ν=2: τ≤4 (tuza_nu2)
- Parker's lemmas: S_e pairwise share edges, τ(S_e)≤2

Goal: Combine into τ ≤ 2ν for ν ≤ 3
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Core definitions
def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ (M : Set (Finset V)).PairwiseDisjoint
    (fun t => t.offDiag.image (fun x => Sym2.mk (x.1, x.2)))

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}

def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2}

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ m ∈ M, m ≠ e → (t ∩ m).card ≤ 1)

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

-- Proven by Aristotle (2b21c426)
lemma tau_0_of_nu_0 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G = 0) : coveringNumber G = 0 := by
  sorry

-- Proven by Aristotle (2b21c426)
lemma tau_le_2_of_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G = 1) : coveringNumber G ≤ 2 := by
  sorry

-- Proven by Aristotle (0764be78)
lemma tau_le_4_of_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G = 2) : coveringNumber G ≤ 4 := by
  sorry

-- Proven by Aristotle (181fa406): S_e triangles pairwise share edges
lemma S_e_pairwise_share_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∀ t₁ t₂, t₁ ∈ S_e G e M → t₂ ∈ S_e G e M → (t₁ ∩ t₂).card ≥ 2 := by
  sorry

-- Proven by Aristotle: τ(S_e) ≤ 2 (triangles sharing edges can be covered by 2 edges)
lemma tau_S_e_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ ∀ t ∈ S_e G e M, ∃ edge ∈ E, edge ∈ t.sym2 := by
  sorry

-- Key: For ν=3, can find e such that T_e = S_e (i.e., no cross-overlaps)
lemma nu_3_exists_clean_packing_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3) :
    ∃ e ∈ M, T_e G e = S_e G e M := by
  sorry

-- Main theorem for ν=3
lemma tau_le_6_of_nu_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G = 3) : coveringNumber G ≤ 6 := by
  sorry

-- Final theorem: τ ≤ 2ν for ν ≤ 3
theorem tuza_conjecture_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G ≤ 3) : coveringNumber G ≤ 2 * packingNumber G := by
  rcases Nat.lt_or_eq_of_le h with h' | h'
  · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h') with h'' | h''
    · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h'') with h''' | h'''
      · -- ν = 0
        have hnu : packingNumber G = 0 := Nat.lt_one_iff.mp h'''
        simp [tau_0_of_nu_0 G hnu]
      · -- ν = 1
        have := tau_le_2_of_nu_1 G h'''
        linarith
    · -- ν = 2
      have := tau_le_4_of_nu_2 G h''
      linarith
  · -- ν = 3
    have := tau_le_6_of_nu_3 G h'
    linarith

end
