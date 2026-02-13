/-
SLOT 531: K4-free version of not_all_three_types
==================================================

HYPOTHESIS (from multi-agent debate):
When G is K4-free, the lemma "not_all_three_types" should hold because:
- Without K4, external triangles cannot share a common apex vertex
- Externals must spread out to different vertices
- This forces 5th disjoint triangle (contradiction with ν=4)

TEST: Submit to Aristotle to verify no counterexample exists.

PROOF SKETCH:
1. Assume all three edge-types {a,b}, {b,c}, {a,c} of triangle e={a,b,c} have externals
2. Let T_ab = {a,b,x}, T_bc = {b,c,y}, T_ac = {a,c,z} be these externals
3. In K4-free graph, x, y, z cannot all equal the same vertex (that would create K4 on {a,b,c,x})
4. If x ≠ y ≠ z, then T_ab, T_bc, T_ac are vertex-disjoint from each other outside {a,b,c}
5. Combined with the 4-packing M, we get 5+ triangles pairwise edge-disjoint → contradiction

The key insight: K4-free forces externals to have DIFFERENT third vertices.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Sym.Sym2

open Finset

-- Concrete type for decidability
abbrev V12 := Fin 12

-- Triangle definition
def isTriangle12 (G : SimpleGraph V12) [DecidableRel G.Adj] (T : Finset V12) : Prop :=
  T.card = 3 ∧ ∀ u ∈ T, ∀ v ∈ T, u ≠ v → G.Adj u v

-- Edge-disjoint triangles
def edgeDisjoint12 (T1 T2 : Finset V12) : Prop :=
  ∀ a b : V12, a ∈ T1 → b ∈ T1 → a ≠ b → a ∈ T2 → b ∈ T2 → False

-- Triangle packing
def isTrianglePacking12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) : Prop :=
  (∀ T ∈ M, isTriangle12 G T) ∧
  (∀ T1 ∈ M, ∀ T2 ∈ M, T1 ≠ T2 → edgeDisjoint12 T1 T2)

-- K4-free: no 4-clique exists
def isK4Free (G : SimpleGraph V12) [DecidableRel G.Adj] : Prop :=
  ∀ s : Finset V12, s.card = 4 → ¬(∀ u ∈ s, ∀ v ∈ s, u ≠ v → G.Adj u v)

-- External triangle for edge {u,v} of packing element e
-- An external shares edge {u,v} with e but is not in packing M
def isExternalFor12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12) (u v : V12) (T : Finset V12) : Prop :=
  isTriangle12 G T ∧
  u ∈ T ∧ v ∈ T ∧
  T ∉ M ∧
  T ≠ e

-- Has external for edge type
def hasExternalForEdge12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12) (u v : V12) : Prop :=
  ∃ T : Finset V12, isExternalFor12 G M e u v T

/-
MAIN THEOREM (K4-FREE VERSION):

In a K4-free graph with maximal 4-packing, not all three edge-types of
a packing element can have externals simultaneously.
-/
theorem not_all_three_types_K4free (G : SimpleGraph V12) [DecidableRel G.Adj]
    (hK4free : isK4Free G)
    (M : Finset (Finset V12))
    (hPacking : isTrianglePacking12 G M)
    (hM4 : M.card = 4)
    (hMaximal : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M) (he3 : e.card = 3)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    -- Assume all three edge-types have externals
    (hExtAB : hasExternalForEdge12 G M e a b)
    (hExtBC : hasExternalForEdge12 G M e b c)
    (hExtAC : hasExternalForEdge12 G M e a c) :
    False := by
  sorry

/-
HELPER LEMMA 1: If K4-free and three externals exist, their third vertices are distinct

When T_ab = {a,b,x}, T_bc = {b,c,y}, T_ac = {a,c,z} and G is K4-free:
- x ≠ y (else {a,b,c,x} forms K4 via edges ab, bc, ac, ax, bx, cx)
- Similarly y ≠ z and x ≠ z
-/
lemma K4free_externals_distinct_thirds (G : SimpleGraph V12) [DecidableRel G.Adj]
    (hK4free : isK4Free G)
    (a b c x y z : V12)
    (habc_distinct : a ≠ b ∧ b ≠ c ∧ a ≠ c)
    (hx_not_abc : x ∉ ({a, b, c} : Finset V12))
    (hy_not_abc : y ∉ ({a, b, c} : Finset V12))
    (hz_not_abc : z ∉ ({a, b, c} : Finset V12))
    -- T_ab = {a,b,x} is triangle
    (hTab : G.Adj a x ∧ G.Adj b x)
    -- T_bc = {b,c,y} is triangle
    (hTbc : G.Adj b y ∧ G.Adj c y)
    -- T_ac = {a,c,z} is triangle
    (hTac : G.Adj a z ∧ G.Adj c z)
    -- Original triangle edges
    (hedge_ab : G.Adj a b) (hedge_bc : G.Adj b c) (hedge_ac : G.Adj a c)
    -- Common external vertex creates K4
    (hxy : x = y) :
    False := by
  -- If x = y, then {a,b,c,x} has all edges:
  -- ab (given), bc (given), ac (given), ax (from T_ab), bx (from T_ab), cx = cy (from T_bc)
  -- This is a K4, contradicting hK4free
  sorry

/-
HELPER LEMMA 2: With distinct third vertices, externals form 5-packing

If T_ab, T_bc, T_ac have distinct third vertices x, y, z (all outside {a,b,c}),
and M is the original 4-packing, then M ∪ {T_ab} has 5 edge-disjoint triangles.
-/
lemma distinct_thirds_give_5packing (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12))
    (hPacking : isTrianglePacking12 G M)
    (hM4 : M.card = 4)
    (e : Finset V12) (he : e ∈ M)
    (a b c x : V12)
    (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hx_not_e : x ∉ e)
    (T_ab : Finset V12) (hTab_def : T_ab = {a, b, x})
    (hTab_tri : isTriangle12 G T_ab)
    (hTab_not_M : T_ab ∉ M)
    -- T_ab is edge-disjoint from all M elements except sharing edge {a,b} with e
    (hTab_disjoint : ∀ f ∈ M, f ≠ e → edgeDisjoint12 T_ab f) :
    -- Then M' = (M.erase e) ∪ {e, T_ab} witnesses 5-packing... wait, that's not right
    -- Actually: M ∪ {T_ab} minus e gives us new structure
    -- Key: T_ab shares edge with e, so not edge-disjoint from e
    -- But T_ab IS edge-disjoint from other 3 elements of M
    -- Combined with those 3 + T_ab + one of the other externals...
    False := by
  -- This needs more careful construction
  sorry

/-
COMBINED: K4-free forces contradiction via 5-packing

In K4-free graph:
1. If all three types have externals T_ab, T_bc, T_ac
2. By K4free_externals_distinct_thirds, their third vertices x,y,z are pairwise distinct
3. Each external shares only ONE edge with e (its defining edge)
4. Externals are edge-disjoint from each other (different edges of e, distinct thirds)
5. At least one external is edge-disjoint from all other M-elements
6. M.erase(e) ∪ {that external} has 4 edge-disjoint triangles, none sharing edge with e
7. Add e back: now we have 5 edge-disjoint triangles → contradiction with ν=4
-/
lemma K4free_forces_5packing (G : SimpleGraph V12) [DecidableRel G.Adj]
    (hK4free : isK4Free G)
    (M : Finset (Finset V12))
    (hPacking : isTrianglePacking12 G M)
    (hM4 : M.card = 4)
    (hMaximal : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (T_ab T_bc T_ac : Finset V12)
    (hExtAB : isExternalFor12 G M e a b T_ab)
    (hExtBC : isExternalFor12 G M e b c T_bc)
    (hExtAC : isExternalFor12 G M e a c T_ac) :
    False := by
  sorry
