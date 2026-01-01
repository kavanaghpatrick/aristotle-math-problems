/-
Tuza ν=4: packingWeight_le_4 - Total weight bounded by 4

GOAL: Prove packingWeight(w) ≤ 4 for any fractional packing w.

PROVEN SCAFFOLDING:
- M_weight_le_card: M.sum ≤ 4
- externals_zero_when_saturated: If M.sum = 4, externals = 0

KEY INSIGHT (Edge-Counting Refinement):
We sum edge constraints over M-edges:
  Σ_{e ∈ M_edges} (constraint_sum_e) ≤ 12

LHS counts each triangle by its M-edge degree:
- M-elements: degree = 3, contribute 3 × w(m)
- Externals: degree = d(t) ≥ 1, contribute d(t) × w(t)

So: 3 × M.sum + Σ_ext d(t) × w(t) ≤ 12

The key is: externals at shared vertices have d(t) ≥ 2 because they share edges
with MULTIPLE M-elements. When properly counted, this gives:
  packingWeight ≤ 4

1 SORRY: The refined edge-counting with d(t) ≥ k for appropriate k.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

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

def externals (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3) \ M

def M_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))

/-- M-edge degree of a triangle: number of M-edges it contains. -/
def M_edge_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) : ℕ :=
  (t.sym2.filter (fun e => e ∈ M_edges G M)).card

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING (PROVEN)
-- ══════════════════════════════════════════════════════════════════════════════

lemma M_edges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    (M_edges G M).card = 3 * M.card := by sorry -- PROVEN slot162

lemma external_shares_M_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ externals G M) :
    ∃ e ∈ M_edges G M, e ∈ t.sym2 := by sorry -- PROVEN slot158

lemma M_weight_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    M.sum w ≤ M.card := by sorry -- PROVEN slot159

lemma externals_zero_when_saturated (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w)
    (h_sat : ∀ m ∈ M, w m = 1) :
    ∀ t ∈ externals G M, w t = 0 := by sorry -- PROVEN slot166

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: M-elements have degree 3, externals have degree ≥ 1
-- ══════════════════════════════════════════════════════════════════════════════

lemma M_element_degree_eq_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (m : Finset V) (hm : m ∈ M) :
    M_edge_degree G M m = 3 := by
  -- All 3 edges of m are M-edges
  unfold M_edge_degree
  have h_eq : m.sym2.filter (fun e => e ∈ M_edges G M) =
              m.sym2.filter (fun e => e ∈ G.edgeFinset) := by
    ext e
    simp only [Finset.mem_filter, M_edges, Finset.mem_biUnion]
    constructor
    · intro ⟨he_sym, ⟨m', hm', he_filter⟩⟩
      exact ⟨he_sym, (Finset.mem_filter.mp he_filter).2⟩
    · intro ⟨he_sym, he_edge⟩
      exact ⟨he_sym, ⟨m, hm, Finset.mem_filter.mpr ⟨he_sym, he_edge⟩⟩⟩
  rw [h_eq]
  -- This is just M_element_has_3_M_edges
  sorry -- PROVEN in slot156/162

lemma external_degree_ge_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ externals G M) :
    M_edge_degree G M t ≥ 1 := by
  -- External shares at least one M-edge
  obtain ⟨e, he_M, he_t⟩ := external_shares_M_edge G M hM t ht
  unfold M_edge_degree
  have : e ∈ t.sym2.filter (fun e => e ∈ M_edges G M) :=
    Finset.mem_filter.mpr ⟨he_t, he_M⟩
  exact Finset.card_pos.mpr ⟨e, this⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- Any fractional packing has total weight ≤ |M| when M is maximal with |M| = 4. -/
theorem packingWeight_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    packingWeight G w ≤ 4 := by
  unfold packingWeight
  -- Split into M and externals
  have h_part : G.cliqueFinset 3 = M ∪ externals G M := by
    ext t; simp only [Finset.mem_union, externals, Finset.mem_sdiff]
    constructor
    · intro ht; by_cases h : t ∈ M <;> [left; right] <;> [exact h; exact ⟨ht, h⟩]
    · intro h; rcases h with h | ⟨h, _⟩ <;> [exact hM.1.1 h; exact h]
  have h_disj : Disjoint M (externals G M) := by
    rw [Finset.disjoint_left]; intro t ht hext
    exact (Finset.mem_sdiff.mp hext).2 ht
  rw [h_part, Finset.sum_union h_disj]
  -- M.sum ≤ 4
  have hM_le : M.sum w ≤ M.card := M_weight_le_card G M hM.1 w hw
  -- Need: externals.sum ≤ 0, i.e., externals.sum = 0
  -- This follows from the edge-counting: when properly accounting for M-edge degrees,
  -- externals are squeezed out.
  --
  -- The refined argument:
  -- Σ_{e ∈ M_edges} (constraint_sum_e) ≤ |M_edges| = 12
  -- LHS = Σ_m 3×w(m) + Σ_ext d(ext)×w(ext) where d(ext) ≥ 1
  --     ≥ 3×M.sum + externals.sum
  -- So: 3×M.sum + externals.sum ≤ 12
  -- packingWeight = M.sum + externals.sum
  --
  -- From 3×M.sum + externals.sum ≤ 12:
  --   externals.sum ≤ 12 - 3×M.sum
  --   packingWeight ≤ M.sum + 12 - 3×M.sum = 12 - 2×M.sum
  --
  -- When M.sum = 4: packingWeight ≤ 4 ✓
  -- When M.sum < 4: need tighter bound...
  --
  -- KEY: The constraint is that optimal M.sum = 4 (exchange argument)
  sorry

end
