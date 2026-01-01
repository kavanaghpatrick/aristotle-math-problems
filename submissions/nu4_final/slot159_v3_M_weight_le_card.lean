/-
Tuza ν=4: M_weight_le_card - Sum of M-element weights ≤ |M|

GOAL: Prove M.sum w ≤ M.card for any fractional packing w.

SCAFFOLDING: M_element_has_3_M_edges and M_edges_card proven in slot162 (inlined below).

1 SORRY: The double-counting rearrangement - Fubini-type sum swap showing
  Σ_{e ∈ M_edges} Σ_{t : e ∈ t} w(t) ≥ 3 * M.sum(w)
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

-- PROVEN in slot162 by Aristotle
lemma M_element_has_3_M_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (m : Finset V) (hm : m ∈ M) :
    (m.sym2.filter (fun e => e ∈ G.edgeFinset)).card = 3 := by
  have h_triangle_edges : ∀ t ∈ G.cliqueFinset 3, Finset.card (t.sym2.filter (fun e => e ∈ G.edgeFinset)) = 3 := by
    simp +decide [SimpleGraph.cliqueFinset]
    intro t ht
    have h_triangle_edges : Finset.card (t.sym2.filter (fun e => e ∈ G.edgeSet)) = Finset.card (Finset.powersetCard 2 t) := by
      refine' Finset.card_bij _ _ _ _
      use fun e he => e.toFinset
      · simp +decide [Finset.mem_powersetCard, Finset.subset_iff]
        rintro ⟨a, b⟩ hab h; cases eq_or_ne a b <;> simp_all +decide [SimpleGraph.adj_comm]
        simp +decide [*, Sym2.toFinset]
        simp +decide [*, Sym2.toMultiset]
      · simp +contextual [Finset.ext_iff, Sym2.ext_iff]
      · simp +decide [Finset.mem_powersetCard, SimpleGraph.isNClique_iff] at ht ⊢
        intro b hb hb'; obtain ⟨x, y, hxy⟩ := Finset.card_eq_two.mp hb'; use Sym2.mk (x, y); aesop
    simp_all +decide [SimpleGraph.isNClique_iff]
  exact h_triangle_edges m (hM.1 hm)

-- PROVEN in slot162 by Aristotle
lemma M_edges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    (M_edges G M).card = 3 * M.card := by
  have h_card_add : ∀ m1 m2 : Finset V, m1 ∈ M → m2 ∈ M → m1 ≠ m2 →
      Disjoint (m1.sym2.filter (fun e => e ∈ G.edgeFinset)) (m2.sym2.filter (fun e => e ∈ G.edgeFinset)) := by
    have := hM.2
    intro m1 m2 hm1 hm2 hne; specialize this hm1 hm2 hne; rw [Finset.disjoint_left]; simp_all +decide [Finset.ext_iff]
    contrapose! this
    obtain ⟨a, ha1, ha2, ha3⟩ := this; rcases a with ⟨x, y⟩; simp_all +decide [Finset.ext_iff]
    exact Finset.one_lt_card.2 ⟨x, by aesop, y, by aesop⟩
  rw [M_edges, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl fun x hx => M_element_has_3_M_edges G M hM x hx]; simp +decide [mul_comm]
  · exact fun x hx y hy hxy => h_card_add x y hx hy hxy

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
  have h_M_contribution : 3 * M.sum w ≤
      (M_edges G M).sum (fun e => ((G.cliqueFinset 3).filter (fun t => e ∈ t.sym2)).sum w) := by
    -- Key: For each m ∈ M, m contributes w(m) to exactly 3 edge-sums
    -- LHS = Σ_{m∈M} 3·w(m)
    -- RHS ≥ Σ_{m∈M} Σ_{e∈m's edges} w(m) = Σ_{m∈M} 3·w(m)
    sorry
  -- Step 3: Combine to get contradiction
  have h_card : (M_edges G M).card = 3 * M.card := M_edges_card G M hM
  have h1 : 3 * M.sum w ≤ 3 * (M.card : ℝ) := by
    calc 3 * M.sum w ≤ _ := h_M_contribution
      _ ≤ (M_edges G M).card := h_edge_sum
      _ = ((3 * M.card : ℕ) : ℝ) := by rw [h_card]
      _ = 3 * (M.card : ℝ) := by push_cast; ring
  linarith
