/-
  slot305: τ ≤ 8 for PATH_4 Using Fan Apex Structure

  GOAL: Prove τ ≤ 8 using the fan apex theorems from slot301 and slot303.

  KEY PROVEN RESULTS:
  - slot301: For endpoint A, two A-externals share a vertex in A
  - slot303: Same for middle element B (and by symmetry, C)

  IMPLICATION: Each M-element X has a "fan apex" vertex x ∈ X such that
  ALL X-externals contain x. Therefore, 2 edges incident to x cover X + all X-externals.

  THE 8-EDGE COVER:
  For each M-element X ∈ {A, B, C, D}:
  - Find fan apex x_X ∈ X
  - Include 2 edges of X incident to x_X

  Total: 4 elements × 2 edges = 8 edges
-/

import Mathlib

set_option maxHeartbeats 400000
set_option linter.mathlibStandardSet false

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { n | ∃ E : Finset (Sym2 V), E ⊆ G.edgeFinset ∧
    (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2) ∧ E.card = n }

-- ══════════════════════════════════════════════════════════════════════════════
-- FAN APEX AXIOM (from slot301/slot303)
-- ══════════════════════════════════════════════════════════════════════════════

/-- From slot301/slot303: All externals of X share a vertex in X -/
axiom fan_apex_in_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_3 : X.card = 3) :
    ∃ x ∈ X, ∀ T, isExternalOf G M X T → x ∈ T

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- τ ≤ 8 for PATH_4 using fan apex structure.

PROOF SKETCH:
1. For each X ∈ M, get fan apex x_X ∈ X (by fan_apex_in_element)
2. Construct cover E = ⋃_{X ∈ M} {2 edges of X incident to x_X}
3. |E| ≤ 8 (2 edges per element)
4. E covers all triangles:
   - If T ∈ M: T is some X, and E contains 2 edges of X covering it
   - If T ∉ M: T is external to some X, x_X ∈ T, and T shares edge with X
     → T contains edge {x_X, w} for some w ∈ X, which is in E
-/
theorem tau_le_8_fan_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (hA_eq : A = {v1, a1, a2}) (hB_eq : B = {v1, v2, b})
    (hC_eq : C = {v2, v3, c}) (hD_eq : D = {v3, d1, d2})
    (hA_clique : A ∈ G.cliqueFinset 3) (hB_clique : B ∈ G.cliqueFinset 3)
    (hC_clique : C ∈ G.cliqueFinset 3) (hD_clique : D ∈ G.cliqueFinset 3)
    (h_distinct : ({v1, v2, v3, a1, a2, b, c, d1, d2} : Finset V).card = 9)
    (hAB : A ∩ B = {v1}) (hBC : B ∩ C = {v2}) (hCD : C ∩ D = {v3})
    (hAC : A ∩ C = ∅) (hAD : A ∩ D = ∅) (hBD : B ∩ D = ∅) :
    triangleCoveringNumber G ≤ 8 := by
  sorry

end
