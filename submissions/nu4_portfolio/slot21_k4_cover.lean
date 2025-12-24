/-
Tuza ν=4 Portfolio - Slot 21: K4 Cover Lemma

GOAL: Prove that any set of triangles on at most 4 vertices has τ ≤ 2.

KEY FACTS:
- K4 has exactly 4 triangles
- Any edge in K4 covers exactly 2 triangles
- Two disjoint edges cover all 4 triangles
- For fewer vertices, bound is even tighter
-/

import Mathlib

set_option maxHeartbeats 800000

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E ⊆ G.edgeFinset ∧
    (∀ t ∈ T, ∃ e ∈ E, e ∈ t.sym2) ∧ E.card = n}

theorem k4_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (U : Finset V)
    (hT : T ⊆ G.cliqueFinset 3)
    (hU : U.card ≤ 4)
    (h_support : ∀ t ∈ T, t ⊆ U) :
    triangleCoveringNumberOn G T ≤ 2 := by
  sorry
