/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: aeaf3480-88bd-4ed3-bc72-6b8bb77e8a81

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Aristotle encountered an error processing this file.
Lean errors:
At line 102, column 2:
  unexpected token '/--'; expected 'lemma'

At line 110, column 2:
  unexpected token '/--'; expected 'lemma'

At line 166, column 2:
  unexpected token '/--'; expected 'lemma'

At line 179, column 2:
  unexpected token '/--'; expected 'lemma'

At line 266, column 0:
  Invalid `end`: There is no current scope to end

Note: Scopes are introduced using `namespace` and `section`
-/

/-
  slot494_tetrahedron_case.lean

  HANDLES THE GAP: When all 3 edges of m have externals that share a common apex.

  KEY INSIGHT (from analysis):
  - not_all_three_ext proves: no pairwise-disjoint triple of externals
  - This does NOT imply: some edge has no external

  THE TETRAHEDRON CASE:
  - m = {a,b,c}
  - All 3 edges have externals using common apex x:
    - T_ab = {a,b,x}
    - T_ac = {a,c,x}
    - T_bc = {b,c,x}
  - These share edges: (a,x), (b,x), (c,x)
  - No pairwise-disjoint triple exists

  WHY THIS CASE STILL GIVES τ ≤ 8:
  - The apex x must be in some triangle (possibly M-element)
  - If x ∈ some m' ∈ M, then apex edges (a,x), (b,x), (c,x) might be M-edges
  - These apex edges cover multiple externals simultaneously!

  TIER: 2 (structural analysis with finite verification)
-/

import Mathlib

set_option maxHeartbeats 800000

open Finset

abbrev V9 := Fin 9

def mkE (x y : V9) : V9 × V9 := if x ≤ y then (x, y) else (y, x)

structure Tri where
  a : V9
  b : V9
  c : V9
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  deriving DecidableEq

def Tri.vertices (t : Tri) : Finset V9 := {t.a, t.b, t.c}
def Tri.e1 (t : Tri) : V9 × V9 := mkE t.a t.b
def Tri.e2 (t : Tri) : V9 × V9 := mkE t.a t.c
def Tri.e3 (t : Tri) : V9 × V9 := mkE t.b t.c
def Tri.edges (t : Tri) : Finset (V9 × V9) := {t.e1, t.e2, t.e3}

def edgeDisj (t1 t2 : Tri) : Prop := Disjoint t1.edges t2.edges

instance (t1 t2 : Tri) : Decidable (edgeDisj t1 t2) :=
  inferInstanceAs (Decidable (Disjoint _ _))

def pack4 (m0 m1 m2 m3 : Tri) : Prop :=
  edgeDisj m0 m1 ∧ edgeDisj m0 m2 ∧ edgeDisj m0 m3 ∧
  edgeDisj m1 m2 ∧ edgeDisj m1 m3 ∧ edgeDisj m2 m3

instance (m0 m1 m2 m3 : Tri) : Decidable (pack4 m0 m1 m2 m3) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

-- ══════════════════════════════════════════════════════════════════════════════
-- TETRAHEDRON DETECTION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Vertex x forms a tetrahedron with triangle m -/
def formsTetrahedron (m : Tri) (x : V9) : Prop :=
  x ≠ m.a ∧ x ≠ m.b ∧ x ≠ m.c

instance (m : Tri) (x : V9) : Decidable (formsTetrahedron m x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The 3 "apex edges" from m's vertices to apex x -/
def apexEdges (m : Tri) (x : V9) : Finset (V9 × V9) :=
  {mkE m.a x, mkE m.b x, mkE m.c x}

/-- The 3 "apex triangles" (tetrahedron faces other than m) -/
def apexTriangles (m : Tri) (x : V9) (hx : formsTetrahedron m x) :
    Finset (V9 × V9 × V9) :=
  {(m.a, m.b, x), (m.a, m.c, x), (m.b, m.c, x)}

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY: Apex vertex must be "reachable" by M-edges
-- ══════════════════════════════════════════════════════════════════════════════

/--
If all 3 edges of m have externals with common apex x, then:
1. x ∉ m (by definition)
2. The apex triangles {a,b,x}, {a,c,x}, {b,c,x} are edge-disjoint from m1,m2,m3
3. Therefore, apex edges (a,x), (b,x), (c,x) are NOT in m1, m2, m3

But by ν=4 maximality, every triangle shares edge with some M-element.
Consider triangle {a,x,y} for any y ∈ V adjacent to both a and x.
This triangle must share edge with some M-element.

If it shares edge (a,y) or (x,y) with some m' ∈ M (m' ≠ m), then:
- Either y ∈ {b,c} (back to m)
- Or we get structural constraint on x's neighborhood
-/
/-
ERROR 1:
unexpected token '/--'; expected 'lemma'
-/

/--
CLAIM: In the tetrahedron case, either:
1. Some apex edge (a,x), (b,x), or (c,x) is in some m' ∈ M
   → That edge covers 2 apex triangles, reducing cover to 2 M-edges from m
2. x is "isolated" from M (no M-element contains x)
   → Strong constraint on graph structure
-/
/-
ERROR 1:
unexpected token '/--'; expected 'lemma'
-/

/-- x is in some M-element -/
def xInM (x : V9) (m0 m1 m2 m3 : Tri) : Prop :=
  x ∈ m0.vertices ∨ x ∈ m1.vertices ∨ x ∈ m2.vertices ∨ x ∈ m3.vertices

instance (x : V9) (m0 m1 m2 m3 : Tri) : Decidable (xInM x m0 m1 m2 m3) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

-- ══════════════════════════════════════════════════════════════════════════════
-- CASE 1: Apex x is in some M-element
-- ══════════════════════════════════════════════════════════════════════════════

/--
If x ∈ m' (some M-element other than m), then some apex edge is in m'.

For example, if x ∈ m1 = {x, y, z}, then edges (x,y) and (x,z) are in m1.
If y = a, then (a,x) ∈ m1.edges, covering apex triangles {a,b,x} and {a,c,x}.
-/
lemma apex_edge_in_M_element (m0 m1 : Tri) (x : V9)
    (hx_not_m0 : x ∉ m0.vertices) (hx_in_m1 : x ∈ m1.vertices)
    (hshare : (m0.vertices ∩ m1.vertices).Nonempty) :
    ∃ v ∈ m0.vertices, mkE v x ∈ m1.edges := by
  obtain ⟨v, hv⟩ := hshare
  simp only [mem_inter] at hv
  use v, hv.1
  -- v ∈ m0 and v ∈ m1, and x ∈ m1
  -- So edge (v, x) is in m1
  unfold Tri.edges Tri.e1 Tri.e2 Tri.e3
  simp only [mem_insert, mem_singleton]
  -- Need to show mkE v x is one of m1's edges
  -- m1 = {m1.a, m1.b, m1.c} contains v and x
  -- So (v,x) is an edge of m1 iff v ≠ x
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- CASE 2: Apex x is not in any M-element
-- ══════════════════════════════════════════════════════════════════════════════

/--
If x ∉ any M-element, the tetrahedron faces {a,b,x}, {a,c,x}, {b,c,x}
are triangles that don't share edges with m1, m2, m3.
By ν=4 maximality, they must share edges with m.
Since they already share edges (a,b), (a,c), (b,c) with m, this is consistent.

But the APEX TRIANGLES {a,x,?}, {b,x,?}, {c,x,?} for some other vertex ?
must also share edges with M.

If x has degree > 3 (edges to more than just a,b,c), consider another neighbor y of x.
Triangle {a,x,y} must share edge with some M-element:
- (a,x) not in any M (since x ∉ M)
- (a,y) must be in some M (otherwise {a,x,y} is edge-disjoint from M)
- So y is adjacent to a in some M-element

This constrains x's neighborhood: every neighbor of x (other than a,b,c)
must form an edge with a,b,c that's in some M-element.
-/
/-
ERROR 1:
unexpected token '/--'; expected 'lemma'
-/

/--
CONCLUSION: The "isolated apex" case (x ∉ any M) forces strong constraints
on the graph that make the tetrahedron structure rare.

In practice, we claim: for any 4-packing, we can select ≤2 edges per element
such that the 8 edges cover all triangles.

The selection rule:
- For m ∈ M, let E_m = set of externals for m
- If E_m shares common apex x with another M-element m', use apex edges from m'
- Otherwise, use the 2 edges of m that have externals (by 6-packing constraint)
-/
/-
ERROR 1:
unexpected token '/--'; expected 'lemma'
-/

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN: τ ≤ 8 Construction
-- ══════════════════════════════════════════════════════════════════════════════

/--
For each m ∈ M, define "active edges" as edges with externals.
By 6-packing constraint + tetrahedron analysis:
- Either ≤2 edges have externals → select those
- Or 3 edges have externals (tetrahedron) → apex edge in another M covers 2

In both cases, ≤2 edges from m needed in cover.
-/
def selectEdges (m0 m1 m2 m3 m : Tri) : Finset (V9 × V9) :=
  -- Simplified: just take first 2 edges
  -- In real proof, this is the smart selection based on external structure
  {m.e1, m.e2}

lemma selectEdges_card (m0 m1 m2 m3 m : Tri) :
    (selectEdges m0 m1 m2 m3 m).card ≤ 2 := by
  unfold selectEdges
  simp only [card_insert_of_not_mem, card_singleton]
  · omega
  · simp [Tri.e1, Tri.e2, mkE]
    intro h
    -- e1 ≠ e2 since they involve different vertex pairs
    sorry

lemma selectEdges_subset (m0 m1 m2 m3 m : Tri) :
    selectEdges m0 m1 m2 m3 m ⊆ m.edges := by
  unfold selectEdges Tri.edges
  intro e he
  simp only [mem_insert, mem_singleton] at he ⊢
  rcases he with rfl | rfl <;> tauto

/--
MAIN THEOREM: τ ≤ 8 for ν = 4.
-/
theorem tau_le_8 (m0 m1 m2 m3 : Tri) (hpack : pack4 m0 m1 m2 m3) :
    ∃ E : Finset (V9 × V9), E.card ≤ 8 ∧
      ∀ t : Tri, (¬edgeDisj t m0 ∨ ¬edgeDisj t m1 ∨ ¬edgeDisj t m2 ∨ ¬edgeDisj t m3) →
        ∃ e ∈ E, e ∈ t.edges := by
  -- Construct E as union of selected edges
  let E0 := selectEdges m0 m1 m2 m3 m0
  let E1 := selectEdges m0 m1 m2 m3 m1
  let E2 := selectEdges m0 m1 m2 m3 m2
  let E3 := selectEdges m0 m1 m2 m3 m3
  use E0 ∪ E1 ∪ E2 ∪ E3
  constructor
  · -- Card bound
    calc (E0 ∪ E1 ∪ E2 ∪ E3).card
        ≤ E0.card + E1.card + E2.card + E3.card := by
          calc (E0 ∪ E1 ∪ E2 ∪ E3).card
              ≤ (E0 ∪ E1 ∪ E2).card + E3.card := card_union_le _ _
            _ ≤ (E0 ∪ E1).card + E2.card + E3.card := by linarith [card_union_le (E0 ∪ E1) E2]
            _ ≤ E0.card + E1.card + E2.card + E3.card := by linarith [card_union_le E0 E1]
      _ ≤ 2 + 2 + 2 + 2 := by
          have h0 := selectEdges_card m0 m1 m2 m3 m0
          have h1 := selectEdges_card m0 m1 m2 m3 m1
          have h2 := selectEdges_card m0 m1 m2 m3 m2
          have h3 := selectEdges_card m0 m1 m2 m3 m3
          omega
      _ = 8 := by norm_num
  · -- Coverage
    intro t ht
    -- t shares edge with some M-element
    -- The selected edges cover the shared edge
    rcases ht with h0 | h1 | h2 | h3
    · -- t shares edge with m0
      -- The shared edge is in m0.edges
      -- If it's in E0, we're done
      -- If not, the tetrahedron argument shows another M's edge covers t
      unfold edgeDisj at h0
      simp only [Set.not_disjoint_iff] at h0
      obtain ⟨e, he_t, he_m0⟩ := h0
      -- Check if e ∈ E0
      by_cases he_E0 : e ∈ E0
      · exact ⟨e, mem_union_left _ (mem_union_left _ (mem_union_left _ he_E0)), he_t⟩
      · -- e is the "third edge" of m0 (not selected)
        -- Either t is a bridge (covered by another M's edge)
        -- Or t is external, covered by tetrahedron argument
        sorry
    · sorry -- Similar for m1
    · sorry -- Similar for m2
    · sorry -- Similar for m3

end
/-
ERROR 1:
Invalid `end`: There is no current scope to end

Note: Scopes are introduced using `namespace` and `section`
-/
