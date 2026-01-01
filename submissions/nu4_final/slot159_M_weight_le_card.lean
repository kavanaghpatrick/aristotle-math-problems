/-
Tuza ν=4: M_weight_le_card - Sum of M-element weights ≤ |M|

GOAL: Prove M.sum w ≤ M.card for any fractional packing w.

SCAFFOLDING (from previous proven slots):
- M_edges_card (slot157): |M_edges| = 3|M|

APPROACH (Edge-Counting):
1. Sum edge constraints over M-edges: sum ≤ |M_edges| = 3|M|
2. Each M-element contributes w(m) to exactly 3 terms
3. Rearranging: 3 × M.sum(w) ≤ 3|M|
4. Therefore: M.sum(w) ≤ |M|

1 SORRY: The double-counting rearrangement (Fubini-type sum swap).
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def IsFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
  (∀ t, t ∉ G.cliqueFinset 3 → w t = 0) ∧
  (∀ e ∈ G.edgeFinset, ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w ≤ 1)

def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

-- SCAFFOLDING: Proven in slot157
axiom M_edges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    (M_edges G M).card = 3 * M.card

-- Helper: M-edges are in G.edgeFinset
lemma M_edge_in_G (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Sym2 V) (he : e ∈ M_edges G M) : e ∈ G.edgeFinset := by
  simp only [M_edges, mem_biUnion, mem_filter] at he
  obtain ⟨_, _, _, he_G⟩ := he
  exact he_G

/-- Sum of M-element weights ≤ |M|. -/
theorem M_weight_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    M.sum w ≤ M.card := by
  by_contra h_neg
  push_neg at h_neg
  -- Step 1: Sum constraints over M-edges
  have h_edge_sum : (M_edges G M).sum (fun e =>
      ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w) ≤ (M_edges G M).card := by
    have h_each : ∀ e ∈ M_edges G M,
        ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w ≤ 1 :=
      fun e he => hw.2.2 e (M_edge_in_G G M e he)
    calc (M_edges G M).sum (fun e => ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w)
        ≤ (M_edges G M).sum (fun _ => (1 : ℝ)) := Finset.sum_le_sum h_each
      _ = (M_edges G M).card := by simp
  -- Step 2: Rearrange to get 3 × M.sum(w)
  have h_M_contribution : 3 * M.sum w ≤
      (M_edges G M).sum (fun e => ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w) := by
    -- Double-counting: each m ∈ M contributes w(m) to exactly 3 edge sums
    -- Σ_e Σ_{t:e∈t} w(t) ≥ Σ_{m∈M} 3·w(m) = 3·M.sum(w)
    sorry
  -- Step 3: Combine
  have h_card : (M_edges G M).card = 3 * M.card := M_edges_card G M hM
  have h1 : 3 * M.sum w ≤ 3 * (M.card : ℝ) := by
    calc 3 * M.sum w ≤ _ := h_M_contribution
      _ ≤ (M_edges G M).card := h_edge_sum
      _ = ((3 * M.card : ℕ) : ℝ) := by rw [h_card]
      _ = 3 * (M.card : ℝ) := by push_cast; ring
  linarith
