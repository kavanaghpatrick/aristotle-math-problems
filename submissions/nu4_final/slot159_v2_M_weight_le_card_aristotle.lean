/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 64eb2512-5e95-4d79-b641-0838f3568122
-/

/-
Tuza ν=4: M_weight_le_card - Sum of M-element weights ≤ |M|

GOAL: Prove M.sum w ≤ M.card for any fractional packing w.

SCAFFOLDING: M_edges_card proven in slot162.

1 SORRY: The double-counting rearrangement - Fubini-type sum swap showing
  Σ_{e ∈ M_edges} Σ_{t : e ∈ t} w(t) ≥ 3 * M.sum(w)

KEY INSIGHT: For each m ∈ M, m has exactly 3 edges in M_edges.
For each such edge e, m is in cliqueFinset 3 (since M ⊆ cliqueFinset 3)
and e ∈ m.sym2, so m is in the filter. Thus m contributes w(m) to 3 edge-sums.
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry34747', 'M_edges_card']-/
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

-- SCAFFOLDING: Proven in slot162 by Aristotle
axiom M_edges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    (M_edges G M).card = 3 * M.card

-- Helper: M-edges are in G.edgeFinset
lemma M_edge_in_G (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Sym2 V) (he : e ∈ M_edges G M) : e ∈ G.edgeFinset := by
  simp only [M_edges, mem_biUnion, mem_filter] at he
  obtain ⟨_, _, _, he_G⟩ := he
  exact he_G

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isTrianglePacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  IsFractionalPacking
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Unknown identifier `M_edges`
Unknown identifier `M_edges`
unsolved goals
V : Type u_1
x✝¹ : Sort u_2
isTrianglePacking : x✝¹
x✝ : Sort u_3
IsFractionalPacking : x✝
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
hM : sorry
w : Finset V → ℝ
hw : sorry
h_neg : (↑M.card : ℝ) < M.sum w
⊢ False-/
/-- Sum of M-element weights ≤ |M|. -/
theorem M_weight_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    M.sum w ≤ M.card := by
  by_contra h_neg
  push_neg at h_neg
  -- Step 1: Sum constraints over M-edges gives sum ≤ |M_edges|
  have h_edge_sum : (M_edges G M).sum (fun e =>
      ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w) ≤ (M_edges G M).card := by
    have h_each : ∀ e ∈ M_edges G M,
        ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w ≤ 1 :=
      fun e he => hw.2.2 e (M_edge_in_G G M e he)
    calc (M_edges G M).sum (fun e => ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w)
        ≤ (M_edges G M).sum (fun _ => (1 : ℝ)) := Finset.sum_le_sum h_each
      _ = (M_edges G M).card := by simp
  -- Step 2: Double-counting shows edge-sum ≥ 3 × M.sum(w)
  -- Each m ∈ M has 3 edges in M_edges, and for each such edge e, m is in the filter
  have h_M_contribution : 3 * M.sum w ≤
      (M_edges G M).sum (fun e => ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w) := by
    -- Key: rewrite as double sum and apply Fubini
    -- LHS = Σ_{m∈M} 3·w(m) = Σ_{m∈M} Σ_{e∈M_edges_of(m)} w(m)
    -- RHS = Σ_{e∈M_edges} Σ_{t:e∈t} w(t) ≥ Σ_{e∈M_edges} Σ_{m∈M:e∈m} w(m)
    --     = Σ_{m∈M} Σ_{e∈M_edges:e∈m} w(m) = Σ_{m∈M} |M_edges_of(m)|·w(m) = Σ_{m∈M} 3·w(m)
    sorry
  -- Step 3: Combine to get contradiction
  have h_card : (M_edges G M).card = 3 * M.card := M_edges_card G M hM
  have h1 : 3 * M.sum w ≤ 3 * (M.card : ℝ) := by
    calc 3 * M.sum w ≤ _ := h_M_contribution
      _ ≤ (M_edges G M).card := h_edge_sum
      _ = ((3 * M.card : ℕ) : ℝ) := by rw [h_card]
      _ = 3 * (M.card : ℝ) := by push_cast; ring
  linarith