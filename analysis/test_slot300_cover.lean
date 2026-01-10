/-
Test if slot300's cover10 actually covers all external triangles

Key question: Does the proof work even when external shares {v1,b} or {v2,c}?
-/

import Mathlib

set_option linter.mathlibStandardSet false

open Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Reproduce cover10 definition
def cover10 (v1 v2 v3 a1 a2 b c d1 d2 : V) : Finset (Sym2 V) :=
  {s(v1, a1), s(v1, a2), s(a1, a2),   -- A's 3 edges
   s(v1, v2), s(v2, b),               -- B's 2 edges (missing {v1,b})
   s(v2, v3), s(v3, c),               -- C's 2 edges (missing {v2,c})
   s(v3, d1), s(v3, d2), s(d1, d2)}   -- D's 3 edges

-- Check: is {v1,b} in cover10?
example (v1 v2 v3 a1 a2 b c d1 d2 : V)
    (h_distinct : ({v1, v2, v3, a1, a2, b, c, d1, d2} : Finset V).card = 9) :
    s(v1, b) ∉ cover10 v1 v2 v3 a1 a2 b c d1 d2 := by
  intro h
  unfold cover10 at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  -- h says s(v1,b) equals one of the 10 edges
  -- But none of them equal s(v1,b) when all 9 vertices are distinct
  sorry  -- This should be provable by distinctness

-- Check: is {v2,c} in cover10?
example (v1 v2 v3 a1 a2 b c d1 d2 : V)
    (h_distinct : ({v1, v2, v3, a1, a2, b, c, d1, d2} : Finset V).card = 9) :
    s(v2, c) ∉ cover10 v1 v2 v3 a1 a2 b c d1 d2 := by
  intro h
  unfold cover10 at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  sorry  -- This should be provable by distinctness

/-
QUESTION: If an external triangle shares ONLY edge {v1,b} with B,
then cover10 does NOT cover it!

The proof in slot300 seems to assume this case doesn't happen.

WHY might this be true?
1. Graph structure prevents it (no such external exists)
2. The proof has a bug
3. The maximality property prevents it

Let's check the maximality lemma...
-/
