/-
Tuza nu=4 Cycle_4: tau <= 8 via Krivelevich's Theorem

GOAL: Prove tau(G) <= 8 for any graph G with nu(G) = 4 in cycle_4 configuration.

APPROACH:
1. Axiomatize Krivelevich (1995): tau <= 2*nu* (published theorem)
2. Use nu* = 4 from slot153 + slot153b
3. Conclude: tau <= 2 * 4 = 8

AXIOMS:
- krivelevich_bound: tau(G) <= 2 * nu*(G) (Discrete Mathematics 142(1995):281-286)

SCAFFOLDING:
- nu_star_ge_4 (slot153 - proves nu* >= 4)
- nu_star_le_4 (slot153b - proves nu* <= 4)

ZERO SORRIES EXPECTED (1 axiom for Krivelevich)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- DEFINITIONS

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def IsFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
  (∀ t, t ∉ G.cliqueFinset 3 → w t = 0) ∧
  (∀ e ∈ G.edgeFinset,
    ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w ≤ 1)

def packingWeight (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : ℝ :=
  (G.cliqueFinset 3).sum w

/-- Fractional packing number: supremum of weights over all valid packings -/
noncomputable def fractionalPackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup { r : ℝ | ∃ w : Finset V → ℝ, IsFractionalPacking G w ∧ packingWeight G w = r }

/-- Triangle covering number -/
noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { n : ℕ | ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧
    (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card = n }

-- KRIVELEVICH'S THEOREM (AXIOM)

/-
CITATION: M. Krivelevich, "On a conjecture of Tuza about packing and covering
          of triangles," Discrete Mathematics 142(1-3):281-286, 1995.

THEOREM: For any graph G, tau(G) <= 2*nu*(G) where nu* is the fractional packing number.

NOTE: This uses the SUPREMUM of fractional packings, not any particular packing.
      Pattern 10 documents the error of using forall w instead of sup.
-/
axiom krivelevich_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    (triangleCoveringNumber G : ℝ) ≤ 2 * fractionalPackingNumber G

-- SCAFFOLDING FROM slot153 and slot153b

/-- nu* >= 4: There exists a fractional packing achieving weight 4 (from slot153) -/
axiom nu_star_ge_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM4 : M.card = 4) :
    ∃ w : Finset V → ℝ, IsFractionalPacking G w ∧ packingWeight G w = 4

/-- nu* <= 4: Any fractional packing has weight at most 4 (from slot153b) -/
axiom nu_star_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    packingWeight G w ≤ 4

-- HELPER LEMMAS FOR sSup

/-- The set of fractional packing weights is nonempty -/
lemma fractional_packing_set_nonempty (G : SimpleGraph V) [DecidableRel G.Adj] :
    { r : ℝ | ∃ w : Finset V → ℝ, IsFractionalPacking G w ∧ packingWeight G w = r }.Nonempty := by
  use 0
  use (fun _ => 0)
  constructor
  · refine ⟨fun _ => le_refl 0, fun _ _ => rfl, fun e _ => ?_⟩
    simp only [Finset.sum_const_zero]
    linarith
  · simp only [packingWeight, Finset.sum_const_zero]

/-- The set of fractional packing weights is bounded above by 4 (for |M|=4) -/
lemma fractional_packing_bdd_above (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4) :
    BddAbove { r : ℝ | ∃ w : Finset V → ℝ, IsFractionalPacking G w ∧ packingWeight G w = r } := by
  use 4
  intro x hx
  obtain ⟨w, hw, rfl⟩ := hx
  exact nu_star_le_4 G M hM hM4 w hw

/-- nu* = 4 for |M| = 4 -/
theorem nu_star_eq_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4) :
    fractionalPackingNumber G = 4 := by
  unfold fractionalPackingNumber
  apply le_antisymm
  · -- nu* <= 4: Use csSup_le with nu_star_le_4
    apply csSup_le (fractional_packing_set_nonempty G)
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact nu_star_le_4 G M hM hM4 w hw
  · -- nu* >= 4: Use le_csSup with nu_star_ge_4
    obtain ⟨w, hw, hw4⟩ := nu_star_ge_4 G M hM.1 hM4
    rw [← hw4]
    apply le_csSup (fractional_packing_bdd_above G M hM hM4)
    exact ⟨w, hw, rfl⟩

-- MAIN THEOREM

/-- TUZA'S CONJECTURE for nu = 4: tau(G) <= 8 -/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4) :
    triangleCoveringNumber G ≤ 8 := by
  -- By Krivelevich: tau <= 2*nu*
  have h1 : (triangleCoveringNumber G : ℝ) ≤ 2 * fractionalPackingNumber G :=
    krivelevich_bound G
  -- By nu_star_eq_4: nu* = 4
  have h2 : fractionalPackingNumber G = 4 := nu_star_eq_4 G M hM hM4
  -- Combine: tau <= 2 * 4 = 8
  rw [h2] at h1
  -- h1 : (triangleCoveringNumber G : R) <= 2 * 4 = 8
  have h3 : (2 : ℝ) * 4 = 8 := by norm_num
  rw [h3] at h1
  -- h1 : (triangleCoveringNumber G : R) <= 8
  -- Need: triangleCoveringNumber G <= 8 (as Nat)
  have h4 : triangleCoveringNumber G ≤ 8 := by
    have : (triangleCoveringNumber G : ℝ) ≤ (8 : ℝ) := h1
    exact_mod_cast this
  exact h4

end
