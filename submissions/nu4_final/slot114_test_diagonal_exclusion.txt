/-- Submission timestamp: 20251226_164343 --/
/-
Tuza ν=4: CYCLE_4 Case - TEST: Diagonal Exclusion
Slot 114

PURPOSE: Determine if diagonal_exclusion is TRUE or FALSE.
This is a DISCOVERY submission - we want Aristotle to tell us the answer.

HYPOTHESIS TO TEST:
"A triangle in a cycle_4 configuration cannot contain both v_ab and v_cd"

If TRUE: Enables the diagonal partition approach (τ ≤ 8)
If FALSE: We need a different strategy (provides counterexample structure)

MINIMAL DEPENDENCIES:
Only uses basic definitions, no scaffolding lemmas.
This gives Aristotle maximum freedom to find proofs or counterexamples.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 CONFIGURATION (Minimal)
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
  -- Triangles are 3-cliques
  hA_tri : A ∈ G.cliqueFinset 3
  hB_tri : B ∈ G.cliqueFinset 3
  hC_tri : C ∈ G.cliqueFinset 3
  hD_tri : D ∈ G.cliqueFinset 3
  -- Shared vertices
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  -- Intersection structure (cycle adjacencies)
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  -- Membership
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A

-- ══════════════════════════════════════════════════════════════════════════════
-- THE HYPOTHESIS TO TEST
-- ══════════════════════════════════════════════════════════════════════════════

/--
## HYPOTHESIS: Diagonal Exclusion for v_ab and v_cd

A triangle t in G cannot contain both v_ab and v_cd.

ANALYSIS:
- v_ab ∈ A ∩ B (shared by adjacent elements A, B)
- v_cd ∈ C ∩ D (shared by adjacent elements C, D)
- A and C are NON-adjacent in the cycle (opposite corners)
- B and D are NON-adjacent in the cycle (opposite corners)

GEOMETRIC INTUITION:
- v_ab and v_cd are "far apart" in the cycle structure
- For t = {v_ab, v_cd, w} to be a triangle, we need:
  * v_ab adjacent to v_cd in G
  * v_ab adjacent to w in G
  * v_cd adjacent to w in G

POTENTIAL PROOF:
- If t = {v_ab, v_cd, w} exists, by maximality t shares edge with some X ∈ M
- Case analysis on X ∈ {A, B, C, D}
- Show each case leads to contradiction or special structure

POTENTIAL COUNTEREXAMPLE:
- If v_ab ~ v_cd in G (they're adjacent)
- Then t = {v_ab, v_cd, v_da} might be a triangle (if v_da ~ v_cd)
- Check: v_da ∈ D, v_cd ∈ D, so {v_da, v_cd} is an edge of D
- Check: v_ab ∈ A, v_da ∈ A, so {v_ab, v_da} is an edge of A
- So if v_ab ~ v_cd, then {v_ab, v_cd, v_da} is a triangle!

QUESTION FOR ARISTOTLE:
Does the cycle_4 structure force v_ab and v_cd to be NON-adjacent?
-/
lemma diagonal_exclusion_test (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (h_diag_AC : (cfg.A ∩ cfg.C).card ≤ 1)
    (h_diag_BD : (cfg.B ∩ cfg.D).card ≤ 1)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(cfg.v_ab ∈ t ∧ cfg.v_cd ∈ t) := by
  sorry

/-- Alternative: Test if v_ab and v_cd can even be adjacent -/
lemma diagonal_non_adjacency_test (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (h_diag_AC : (cfg.A ∩ cfg.C).card ≤ 1)
    (h_diag_BD : (cfg.B ∩ cfg.D).card ≤ 1) :
    ¬G.Adj cfg.v_ab cfg.v_cd := by
  /-
  If v_ab ~ v_cd in G, then edge {v_ab, v_cd} is in G.edgeFinset.
  This edge is NOT in any packing element:
  - {v_ab, v_cd} ⊈ A = {v_ab, v_da, a_priv} since v_cd ∉ A
  - {v_ab, v_cd} ⊈ B = {v_ab, v_bc, b_priv} since v_cd ∉ B
  - {v_ab, v_cd} ⊈ C = {v_bc, v_cd, c_priv} since v_ab ∉ C
  - {v_ab, v_cd} ⊈ D = {v_cd, v_da, d_priv} since v_ab ∉ D

  So {v_ab, v_cd} is an "external" edge.

  Does this violate maximality?
  Consider triangle t = {v_ab, v_cd, v_da}:
  - {v_ab, v_da} ⊆ A (edge of A)
  - {v_cd, v_da} ⊆ D (edge of D)
  - {v_ab, v_cd} external

  So t shares edge with A ({v_ab, v_da}) and with D ({v_cd, v_da}).
  This is consistent with maximality (t shares edge with M).

  CONCLUSION: v_ab ~ v_cd does NOT violate maximality!
  So this lemma might be FALSE.
  -/
  sorry

/-- Test the weaker claim: all 4 shared vertices are distinct -/
lemma shared_vertices_distinct (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (h_diag_AC : (cfg.A ∩ cfg.C).card ≤ 1)
    (h_diag_BD : (cfg.B ∩ cfg.D).card ≤ 1) :
    cfg.v_ab ≠ cfg.v_bc ∧ cfg.v_ab ≠ cfg.v_cd ∧ cfg.v_ab ≠ cfg.v_da ∧
    cfg.v_bc ≠ cfg.v_cd ∧ cfg.v_bc ≠ cfg.v_da ∧
    cfg.v_cd ≠ cfg.v_da := by
  /-
  This should be true from the cycle structure:
  - v_ab ∈ A ∩ B, v_bc ∈ B ∩ C
  - If v_ab = v_bc, then v_ab ∈ A ∩ B ∩ C
  - But A ∩ C has at most 1 element by h_diag_AC
  - And B ∩ C = {v_bc}, so v_ab = v_bc implies v_ab ∈ A ∩ C
  - This would mean A ∩ C = {v_ab}, violating... wait, that's allowed.

  Need more careful analysis.
  -/
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- ALTERNATIVE: Test what CAN be proven
-- ══════════════════════════════════════════════════════════════════════════════

/-- Definitely true: A triangle containing v_ab must share edge with A or B -/
lemma triangle_at_vab_shares_AB (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (h_vab : cfg.v_ab ∈ t) :
    (t ∩ cfg.A).card ≥ 2 ∨ (t ∩ cfg.B).card ≥ 2 := by
  /-
  Since t contains v_ab, and v_ab ∈ A ∩ B:
  - t ∩ A contains v_ab
  - t ∩ B contains v_ab

  t = {v_ab, x, y} for some x, y.
  If x ∈ A, then t ∩ A ⊇ {v_ab, x}, so |t ∩ A| ≥ 2. Done.
  If x ∉ A and y ∈ A, similar.
  If x ∉ A and y ∉ A:
    - t ∩ A = {v_ab}, so |t ∩ A| = 1
    - By maximality, t shares edge with SOME X ∈ M
    - If X = A, contradiction (we just showed |t ∩ A| = 1)
    - If X = B, then |t ∩ B| ≥ 2. Done.
    - If X = C or D... need to show this forces |t ∩ B| ≥ 2

  Hmm, this needs the "All-Middle" property.
  -/
  sorry

end
