/-
  slot302: τ ≤ 8 for PATH_4 - 8-edge Cover Attempt

  Based on proven slot300 (τ ≤ 10), this attempts τ ≤ 8.

  THE 8-EDGE COVER:
  {a1,a2}, {v1,a1}, {v1,v2}, {v2,b}, {v2,v3}, {v3,c}, {d1,d2}, {v3,d1}

  KEY GAP: Missing {v1,a2} and {v3,d2} - externals through these edges
  may not be covered.

  1 sorry for Aristotle (main theorem).
-/

import Mathlib

set_option maxHeartbeats 400000
set_option linter.mathlibStandardSet false

open Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E =>
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- 8-edge cover for PATH_4 -/
def cover8 (v1 v2 v3 a1 a2 b c d1 d2 : V) : Finset (Sym2 V) :=
  {s(a1, a2), s(v1, a1), s(v1, v2), s(v2, b), s(v2, v3), s(v3, c), s(d1, d2), s(v3, d1)}

/-
PROOF SKETCH for tau_le_8_path4:

1. Define E = cover8 filtered to actual graph edges
2. Show |E| ≤ 8 (it's a subset of 8-element set)
3. For t ∈ M = {A, B, C, D}:
   - A covered by {a1,a2}
   - B covered by {v1,v2}
   - C covered by {v2,v3}
   - D covered by {d1,d2}
4. For t ∉ M (external):
   - t shares edge with some M-element
   - Need to show that shared edge is in cover8
   - KEY CHALLENGE: {v1,a2} and {v3,d2} NOT in cover!
     - If t shares {v1,a2} with A: need {v1,a1} or {a1,a2} to also hit t
     - This works if t contains a1 (which externals through {v1,a2} might not!)
5. Conclude using min definition of triangleCoveringNumber
-/
theorem tau_le_8_path4 (M : Finset (Finset V)) (A B C D : Finset V)
    (v1 v2 v3 a1 a2 b c d1 d2 : V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {A, B, C, D})
    (hM_card : M.card = 4)
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
