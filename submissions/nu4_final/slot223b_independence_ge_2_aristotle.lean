/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e2d1d210-f9f7-4554-8894-34389dabdd07
-/

/-
  slot223b_independence_ge_2.lean

  LEMMA: The link graph at shared vertex v has independence number ≥ 2.

  FROM 3-ROUND DEBATE (Jan 3, 2026):
  This is the KEY lemma for τ ≤ 8. It uses the ν = 4 constraint.

  PROOF IDEA (5-packing contradiction):
  1. Suppose α(L_v) = 1, meaning L_v is a complete graph on 4 vertices (K₄)
  2. K₄ has 6 edges, so there are 6 triangles through v
  3. At most 2 are M-elements (A and B at v_ab)
  4. So at least 4 are externals
  5. By slot182, externals of same M-element share edge
  6. But 4 externals from 2 M-elements creates a 5-packing structure
  7. Contradiction with ν = 4

  1 SORRY: The 5-packing contradiction argument
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['two_externals_share_edge', 'harmonicSorry850592']-/
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

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

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
  hM_card : M.card = 4
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  hAC : A ∩ C = ∅
  hBD : B ∩ D = ∅

/-- M-neighbors of v: vertices in M-elements containing v, excluding v itself -/
def M_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset V :=
  M.biUnion (fun X => if v ∈ X then X.erase v else ∅)

/-- Link graph adjacency: two M-neighbors form a triangle with v -/
def linkGraphAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) (u w : V) : Prop :=
  u ∈ M_neighbors G M v ∧ w ∈ M_neighbors G M v ∧ u ≠ w ∧
  {v, u, w} ∈ G.cliqueFinset 3

-- ══════════════════════════════════════════════════════════════════════════════
-- SLOT182 AXIOM (PROVEN)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Two externals of the same M-element share an edge -/
axiom two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M)
    (T₁ T₂ : Finset V)
    (hT₁ : T₁ ∈ G.cliqueFinset 3 ∧ T₁ ∉ M ∧ (T₁ ∩ X).card ≥ 2)
    (hT₂ : T₂ ∈ G.cliqueFinset 3 ∧ T₂ ∉ M ∧ (T₂ ∩ X).card ≥ 2)
    (h_ne : T₁ ≠ T₂) :
    ∃ u v, u ≠ v ∧ u ∈ T₁ ∧ v ∈ T₁ ∧ u ∈ T₂ ∧ v ∈ T₂

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

overloaded, errors 
  failed to synthesize
    Insert ?m.30 (Finset V)
  
  Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
  
  86:43 `cfg` is not a field of structure `Finset`
Function expected at
  isMaxPacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isTrianglePacking
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  Cycle4
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  M_neighbors
but this term has type
  ?m.5

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  M_neighbors
but this term has type
  ?m.5

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  linkGraphAdj
but this term has type
  ?m.6

Note: Expected a function because this term is being applied to the argument
  G-/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- The link graph has independent set of size ≥ 2.

    KEY INSIGHT: If L_v were K₄ (α = 1), there would be 6 triangles through v.
    At most 2 are M-elements. The remaining 4+ externals, combined with slot182,
    enable constructing a 5-packing, contradicting ν = 4.

    The independence ≥ 2 means: there exist two M-neighbors u, w such that
    {v, u, w} is NOT a triangle. This "missing" triangle is crucial. -/
theorem link_graph_independence_ge_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V)) :
    ∃ u w, u ∈ M_neighbors G M v ∧ w ∈ M_neighbors G M v ∧ u ≠ w ∧
           ¬linkGraphAdj G M v u w := by
  -- Proof by contradiction: suppose every pair of M-neighbors forms triangle with v
  -- At v_ab, M-neighbors = {v_da, a_priv, v_bc, b_priv} (4 vertices)
  -- If all C(4,2) = 6 pairs form triangles with v_ab:
  --   - {v_ab, v_da, a_priv} = A (M-element)
  --   - {v_ab, v_bc, b_priv} = B (M-element)
  --   - {v_ab, v_da, v_bc}, {v_ab, v_da, b_priv}, {v_ab, a_priv, v_bc}, {v_ab, a_priv, b_priv}
  --     are 4 external triangles
  -- Externals of A: {v_ab, v_da, v_bc}, {v_ab, v_da, b_priv}, {v_ab, a_priv, v_bc}, {v_ab, a_priv, b_priv}
  -- Wait - which ones share edge with A? Need (T ∩ A).card ≥ 2
  -- A = {v_ab, v_da, a_priv}
  -- T1 = {v_ab, v_da, v_bc}: T1 ∩ A = {v_ab, v_da} ✓ (external of A)
  -- T2 = {v_ab, v_da, b_priv}: T2 ∩ A = {v_ab, v_da} ✓ (external of A)
  -- T3 = {v_ab, a_priv, v_bc}: T3 ∩ A = {v_ab, a_priv} ✓ (external of A)
  -- T4 = {v_ab, a_priv, b_priv}: T4 ∩ A = {v_ab, a_priv} ✓ (external of A)
  -- So A has 4 externals! But slot182 says any 2 externals of A share an edge.
  -- T1 ∩ T2 = {v_ab, v_da} ✓
  -- T1 ∩ T3 = {v_ab} - only 1 vertex! No shared edge!
  -- This contradicts slot182 if both T1 and T3 are externals of A.
  -- Therefore, not all 6 pairs can form triangles. QED.
  sorry

end