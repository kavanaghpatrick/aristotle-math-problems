/-
slot56: LP Approach - Corrected Formulation

BUG IN slot55: Krivelevich bound was stated incorrectly!
- WRONG: ∀ w, isFractionalPacking w → τ ≤ 2 * packingWeight(w)
- CORRECT: τ ≤ 2 * ν* where ν* = sup{packingWeight(w) : isFractionalPacking(w)}

Aristotle found counterexample: K₃ with w=0 gives τ=1 > 0=2*0.

CORRECTED APPROACH:
1. Define ν* (fractional packing number) as supremum
2. Show M_char achieves packingWeight = 4
3. Therefore ν* ≥ 4
4. State Krivelevich: τ ≤ 2 * ν*
5. Conclude: τ ≤ 2 * ν* ≤ 2 * (some bound) → but we need ν* ≤ 4 too!

Actually, simpler approach: Just prove τ ≤ 8 directly for Cycle_4
without formalizing the full LP theory.
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

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- FRACTIONAL PACKING NUMBER (LP Optimum)
-- ══════════════════════════════════════════════════════════════════════════════

def isFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) : Prop :=
  (∀ t, w t ≥ 0) ∧
  (∀ t, t ∉ G.cliqueFinset 3 → w t = 0) ∧
  (∀ e ∈ G.edgeFinset, ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2), w t ≤ 1)

def packingWeight (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : ℝ :=
  ∑ t ∈ G.cliqueFinset 3, w t

/-- Fractional packing number: supremum of packing weights over all valid fractional packings -/
noncomputable def nu_star (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup {x : ℝ | ∃ w, isFractionalPacking G w ∧ packingWeight G w = x}

def M_char (M : Finset (Finset V)) : Finset V → ℝ :=
  fun t => if t ∈ M then 1 else 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMAS (from slot54/55)
-- ══════════════════════════════════════════════════════════════════════════════

lemma M_char_nonneg (M : Finset (Finset V)) (t : Finset V) :
    M_char M t ≥ 0 := by
  unfold M_char; split_ifs <;> linarith

lemma M_char_zero_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (t : Finset V) (ht : t ∉ G.cliqueFinset 3) :
    M_char M t = 0 := by
  unfold M_char; split_ifs with h; · exfalso; exact ht (hM.1 h); · rfl

lemma M_char_edge_sum_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2), M_char M t ≤ 1 := by
  unfold M_char
  have h_edge_bound : (Finset.card (Finset.filter (fun t => e ∈ t.sym2) M)) ≤ 1 := by
    have h_edge_in_M : ∀ t1 t2 : Finset V, t1 ∈ M → t2 ∈ M → t1 ≠ t2 → ¬(e ∈ t1.sym2 ∧ e ∈ t2.sym2) := by
      intros t1 t2 ht1 ht2 hne h_edge
      have h_inter : (t1 ∩ t2).card ≤ 1 := hM.2 ht1 ht2 hne |> fun h => by simpa using h
      rcases e with ⟨ u, v ⟩ ; simp_all +decide [ Finset.ext_iff ]
      exact h_inter.not_lt ( Finset.one_lt_card.2 ⟨ u, by aesop, v, by aesop ⟩ )
    exact Finset.card_le_one.mpr fun t1 ht1 t2 ht2 => Classical.not_not.1 fun h =>
      h_edge_in_M t1 t2 ( Finset.filter_subset _ _ ht1 ) ( Finset.filter_subset _ _ ht2 ) h
      ⟨ Finset.mem_filter.mp ht1 |>.2, Finset.mem_filter.mp ht2 |>.2 ⟩
  simp_all +decide [ Finset.sum_ite ]
  exact le_trans ( Finset.card_le_card fun x hx => by aesop ) h_edge_bound

lemma M_char_is_fractional (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    isFractionalPacking G (M_char M) :=
  ⟨M_char_nonneg M, M_char_zero_outside G M hM, fun e he => M_char_edge_sum_le_1 G M hM e he⟩

lemma M_char_weight_eq_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    packingWeight G (M_char M) = M.card := by
  unfold packingWeight M_char
  have h_split : ∑ t ∈ G.cliqueFinset 3, (if t ∈ M then (1 : ℝ) else 0) = ∑ t ∈ M, (1 : ℝ) := by
    rw [← Finset.sum_filter]; congr 1; ext t; simp only [Finset.mem_filter]
    exact ⟨fun ⟨_, ht⟩ => ht, fun ht => ⟨hM.1 ht, ht⟩⟩
  rw [h_split]; simp

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: ν* ≥ 4 for Cycle_4
-- ══════════════════════════════════════════════════════════════════════════════

lemma nu_star_ge_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    nu_star G ≥ 4 := by
  -- M_char gives a fractional packing with weight 4
  have hw : isFractionalPacking G (M_char M) := M_char_is_fractional G M hM.1
  have hw_weight : packingWeight G (M_char M) = 4 := by
    rw [M_char_weight_eq_card G M hM.1]
    have hM_eq : M = {A, B, C, D} := hcycle.1
    rw [hM_eq]
    have hAB : A ≠ B := hcycle.2.1
    have hAC : A ≠ C := hcycle.2.2.2.2.1
    have hAD : A ≠ D := hcycle.2.2.2.2.2.1
    have hBC : B ≠ C := hcycle.2.2.1
    have hBD : B ≠ D := hcycle.2.2.2.2.2.2.1
    have hCD : C ≠ D := hcycle.2.2.2.1
    simp only [Finset.card_insert_of_not_mem, Finset.card_singleton,
               Finset.mem_insert, Finset.mem_singleton, not_or]
    simp_all
  -- nu_star is the supremum, so it's at least 4
  unfold nu_star
  apply le_csSup
  · -- Show the set is bounded above (by number of triangles)
    sorry
  · -- Show 4 is in the set
    exact ⟨M_char M, hw, hw_weight⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KRIVELEVICH'S THEOREM (Corrected Statement)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Krivelevich (1995): τ(G) ≤ 2·ν*(G)
    where ν* is the fractional packing number (LP optimum).

    Source: "On a conjecture of Tuza about packing and covering of triangles"
    Discrete Mathematics 142(1-3):281-286 -/
theorem krivelevich_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    (triangleCoveringNumber G : ℝ) ≤ 2 * nu_star G := by
  sorry -- Literature result

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- For Cycle_4, we need to show τ ≤ 8.

    The LP approach gives:
    - ν* ≥ 4 (by M_char achieving weight 4)
    - τ ≤ 2ν* (by Krivelevich)

    But this only gives τ ≤ 2ν*, not τ ≤ 8, unless we also bound ν* ≤ 4.

    Actually, for the Krivelevich bound to give τ ≤ 8, we need:
    - Either prove ν* = 4 exactly
    - Or use a different approach

    The issue: 2ν* could be > 8 if ν* > 4.
    But for Cycle_4, the M-edges are fully utilized, so ν* = 4.
-/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  -- We need ν* ≤ 4 to get τ ≤ 2*4 = 8
  -- Key insight: Each M-edge is saturated, so ν* = 4
  sorry
  -- Alternative: Prove directly without LP

end
