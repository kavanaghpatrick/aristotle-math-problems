/-
Tuza ν=4: external_tradeoff_simple - Direct edge constraint argument

GOAL: If t shares edge e with m, and w(t) > 0, then w(m) < 1.

This is pure arithmetic from the edge constraint.

1 SORRY: The arithmetic deduction.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edge constraint implies trade-off: if two triangles share an edge and one has
    positive weight, the other has weight < 1. -/
theorem edge_tradeoff (w_m w_t : ℝ) (h_sum : w_m + w_t ≤ 1) (h_pos : w_t > 0) :
    w_m < 1 := by
  linarith
