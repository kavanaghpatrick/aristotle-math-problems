/-
Tuza ν=4 Portfolio - Slot 16: Missing tau_union_le_sum Lemma

INSIGHT FROM GROK-4 + GEMINI CONSULTATION:
Both agents identified this as THE missing intermediate lemma.

GOAL: Prove τ(A ∪ B) ≤ τ(A) + τ(B) for triangle sets A, B

This lemma would immediately enable:
  τ(T_e ∪ T_f) ≤ τ(Y_v) + τ(Z) ≤ 2 + 2 = 4

Once proven, it closes tau_union_le_4 which unlocks nu4_case_pairwise.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧
  ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: The missing union bound lemma
-- ══════════════════════════════════════════════════════════════════════════════

/--
The key missing intermediate lemma identified by Grok-4 and Gemini.
If we have covers C_A for A and C_B for B, then C_A ∪ C_B covers A ∪ B.
-/
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  -- Let C_A be a minimal cover for A, C_B be a minimal cover for B
  -- Then C_A ∪ C_B is a cover for A ∪ B
  -- |C_A ∪ C_B| ≤ |C_A| + |C_B|
  -- Therefore τ(A ∪ B) ≤ τ(A) + τ(B)
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: Direct application to V-decomposition
-- ══════════════════════════════════════════════════════════════════════════════

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

/-- V-decomposition is disjoint -/
lemma v_decomposition_disjoint (triangles : Finset (Finset V)) (v : V) :
    Disjoint (trianglesContaining triangles v) (trianglesAvoiding triangles v) := by
  simp [trianglesContaining, trianglesAvoiding, Finset.disjoint_filter]
  intro t _ hv hnv
  exact hnv hv

/-- V-decomposition covers the whole set -/
lemma v_decomposition_union (triangles : Finset (Finset V)) (v : V) :
    triangles = trianglesContaining triangles v ∪ trianglesAvoiding triangles v := by
  ext t
  simp [trianglesContaining, trianglesAvoiding]
  tauto

/-- Key corollary for tau_union_le_4 -/
corollary tau_v_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (v : V) :
    triangleCoveringNumberOn G triangles ≤
    triangleCoveringNumberOn G (trianglesContaining triangles v) +
    triangleCoveringNumberOn G (trianglesAvoiding triangles v) := by
  rw [v_decomposition_union triangles v]
  exact tau_union_le_sum G _ _

end
