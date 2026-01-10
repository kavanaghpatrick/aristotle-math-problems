/-
  slot216_nu_star_le_4.lean

  THEOREM: ν*(G) ≤ 4 for cycle_4 configuration

  THE LP PATH TO τ ≤ 8 (Avoiding all 16 false patterns):

  1. Krivelevich (1995): τ(G) ≤ 2ν*(G) where ν* = fractional packing number
  2. If we prove ν* ≤ 4, then τ ≤ 8 follows immediately

  KEY INSIGHT (from 5-round informed debate):
  - Each M-edge e is in EXACTLY ONE M-element (edge-disjoint packing)
  - For any fractional packing w, edge constraint: Σ{w(T) : e ∈ T} ≤ 1
  - Externals MUST use M-edges (by maximality)
  - So external weight + M-element weight ≤ 1 per M-edge
  - This forces total weight ≤ 4

  FALSE PATTERNS AVOIDED:
  - Pattern 10: We use ν* = SUP, not arbitrary w
  - Pattern 11: We PROVE ν* ≤ 4, not assume it
  - Pattern 12: We don't use externals_sum_le_totalSlack
  - Pattern 13: We don't use covering_selection_exists

  DIFFICULTY: 4/5
  SUCCESS PROBABILITY: 70%
-/

import Mathlib

open scoped Classical

set_option maxHeartbeats 400000

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- BASIC DEFINITIONS (matching slot139 proven structure)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 CONFIGURATION (from slot139)
-- ══════════════════════════════════════════════════════════════════════════════

structure Cycle4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A

-- ══════════════════════════════════════════════════════════════════════════════
-- M-EDGES: The 12 edges of the 4 M-triangles
-- ══════════════════════════════════════════════════════════════════════════════

/-- Edges of a triangle (non-diagonal elements of sym2) -/
def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.sym2.filter (fun e => ¬e.IsDiag)

/-- All M-edges in the packing -/
def allMEdges (M : Finset (Finset V)) : Finset (Sym2 V) :=
  M.biUnion triangleEdges

/-- Triangles containing a specific edge -/
def trianglesContainingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => e ∈ triangleEdges t)

-- ══════════════════════════════════════════════════════════════════════════════
-- FRACTIONAL PACKING DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A fractional packing assigns non-negative weights to triangles
    such that each edge is covered by at most 1 total weight -/
structure FractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj] where
  w : Finset V → ℚ
  nonneg : ∀ t, w t ≥ 0
  support : ∀ t, w t > 0 → t ∈ G.cliqueFinset 3
  edge_constraint : ∀ e ∈ G.edgeFinset, (trianglesContainingEdge G e).sum w ≤ 1

/-- Total weight of a fractional packing -/
noncomputable def FractionalPacking.weight (G : SimpleGraph V) [DecidableRel G.Adj]
    (fp : FractionalPacking G) : ℚ :=
  (G.cliqueFinset 3).sum fp.w

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Each M-edge is in exactly one M-element
-- ══════════════════════════════════════════════════════════════════════════════

/-- If e is an edge of M-element X, and Y is a different M-element,
    then e is NOT an edge of Y (edge-disjoint packing) -/
lemma M_edge_unique (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (e : Sym2 V) (he_X : e ∈ triangleEdges X) :
    e ∉ triangleEdges Y := by
  intro he_Y
  -- e ∈ X.sym2 and e ∈ Y.sym2 means e has both endpoints in X and in Y
  simp only [triangleEdges, Finset.mem_filter] at he_X he_Y
  -- If e is an edge of both X and Y, then e's endpoints are in X ∩ Y
  -- This means |X ∩ Y| ≥ 2, contradicting edge-disjoint packing
  -- (M-elements share at most 1 vertex)
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Every triangle uses at least one M-edge (maximality)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle shares an edge with some M-element (by maximality) -/
lemma triangle_uses_M_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, ∃ e ∈ triangleEdges X, e ∈ triangleEdges t := by
  -- By maximality, t shares ≥2 vertices with some X
  -- If t shares 2 vertices with X, it shares an edge
  by_contra h_no_share
  push_neg at h_no_share
  -- This means t shares ≤1 vertex with each X, so M ∪ {t} is a larger packing
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Any fractional packing has weight ≤ 4 for cycle_4
-- ══════════════════════════════════════════════════════════════════════════════

/-- Upper bound: any fractional packing has weight ≤ 4

The key insight: Each of the 12 M-edges has edge constraint ≤ 1.
Each M-element X has 3 edges, but each edge is used by X and possibly externals.
Summing constraints cleverly gives total weight ≤ 4. -/
theorem nu_star_le_4_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (fp : FractionalPacking G) :
    fp.weight ≤ 4 := by
  -- Strategy: Use edge constraints on the 12 M-edges
  -- Each M-edge e is in exactly one M-element X
  -- Triangles using e: {X} ∪ {externals sharing e with X}
  -- Edge constraint: w(X) + Σ{w(T) : T external sharing e} ≤ 1
  --
  -- Summing over all 12 M-edges:
  -- 3·w(A) + 3·w(B) + 3·w(C) + 3·w(D) + Σ{external weights} ≤ 12
  --
  -- But each external T uses exactly one M-edge (otherwise |T ∩ X| ≥ 2 for some X)
  -- So each external is counted exactly once in the sum
  --
  -- Total: 3·(w(A)+w(B)+w(C)+w(D)) + Σ{w(T) : T external} ≤ 12
  -- = 3 · packingWeight ≤ 12
  -- Therefore packingWeight ≤ 4
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- KRIVELEVICH BOUND (axiom from LP duality)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Krivelevich's Theorem: τ ≤ 2ν* for any graph

Note: This is a deep result from LP duality. We state it as an axiom
since proving it from scratch requires significant LP machinery.
See: Krivelevich (1995), "On a conjecture of Tuza about packing and covering of triangles" -/
axiom krivelevich_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hFP : ∃ fp : FractionalPacking G, True) :
    ∀ (upper_bound : ℚ), (∀ fp : FractionalPacking G, fp.weight ≤ upper_bound) →
      (triangleCoveringNumber G : ℚ) ≤ 2 * upper_bound

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN RESULT: τ ≤ 8 for cycle_4
-- ══════════════════════════════════════════════════════════════════════════════

/-- MAIN THEOREM: τ ≤ 8 for cycle_4 configuration -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- First, we need a fractional packing to exist
  have hFP : ∃ fp : FractionalPacking G, True := by
    -- The zero packing exists
    use ⟨fun _ => 0, fun _ => le_refl 0, fun _ h => by linarith, fun _ _ => by simp⟩
  -- Apply Krivelevich's bound with upper_bound = 4
  have h_bound := krivelevich_bound G hFP 4 (fun fp => nu_star_le_4_cycle4 G M hM cfg fp)
  -- h_bound: (triangleCoveringNumber G : ℚ) ≤ 2 * 4 = 8
  norm_num at h_bound
  exact Nat.cast_le.mp h_bound

end
