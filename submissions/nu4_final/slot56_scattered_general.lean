/-
Tuza ν=4: SCATTERED General Theorem
Slot 56

GOAL: Prove τ ≤ 8 for ANY scattered graph with ν = 4.

DEFINITION (Scattered):
  A graph G has "scattered" structure for packing M iff:
  - M is a maximum edge-disjoint triangle packing with |M| = 4
  - All elements of M are pairwise VERTEX-disjoint

KEY THEOREM:
  For scattered configurations, τ ≤ 2|M| = 8.

PROOF STRATEGY:
  1. Each M-element A contributes triangles T_A = {triangles sharing edge with A}
  2. Since M-elements are vertex-disjoint, T_A sets are disjoint
  3. τ(T_A) ≤ 2 for each A (2 edges of A cover all triangles in T_A)
  4. By subadditivity: τ ≤ Σ τ(T_A) ≤ 4 × 2 = 8

CRITICAL LEMMA (tau_local_le_2):
  For any triangle A and set S of triangles all sharing an edge with A,
  there exist 2 edges of A that cover all of S.

PROOF OF tau_local_le_2:
  - A has 3 edges: e1, e2, e3
  - Each triangle in S shares at least one edge with A
  - Case analysis on which edges are used:
    * If all S use only {e1, e2}: cover = {e1, e2}
    * If all S use only {e1, e3}: cover = {e1, e3}
    * If all S use only {e2, e3}: cover = {e2, e3}
    * If S uses all 3 edges: any 2 edges miss at most triangles using the 3rd
      But triangles using e3 also use a vertex of e3, which is in e1 or e2
      Actually this needs more care...

REVISED APPROACH:
  The issue is that 2 edges may NOT suffice if externals exist on all 3 edges.

  BETTER LEMMA: τ(T_A) ≤ 3 (use all 3 edges of A)
  Then: τ ≤ 4 × 3 = 12 (which matches known bounds)

  For τ ≤ 8, we need a tighter argument using the MAXIMUM packing property.

MAXIMUM PACKING ARGUMENT:
  If M is MAXIMUM and scattered, then for each M-element A:
  - Externals at A are triangles sharing edge with A but not in M
  - Since M is maximum, no external can be added to M
  - Each external shares edge with A, so can't extend M
  - Key: externals at A are "constrained" by maximality

  Claim: At most 2 edges of A have externals using them.

  Why? If all 3 edges of A have externals:
  - Let e1, e2, e3 be A's edges
  - External T1 uses e1, T2 uses e2, T3 uses e3
  - Are T1, T2, T3 pairwise edge-disjoint?
  - If yes, we could add them to M, contradicting maximality!

  So: At most 2 of A's edges have externals → 2 edges suffice → τ(T_A) ≤ 2

TIER: 2 (Needs careful maximality argument)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

namespace ScatteredGeneral

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: Basic Definitions
-- ══════════════════════════════════════════════════════════════════════════════

/-- A triangle is a 3-clique in G -/
def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) : Prop :=
  T.card = 3 ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → G.Adj x y

/-- Two triangles are edge-disjoint if they share at most 1 vertex -/
def edgeDisjoint (T1 T2 : Finset V) : Prop :=
  (T1 ∩ T2).card ≤ 1

/-- M is an edge-disjoint triangle packing -/
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  (∀ T ∈ M, isTriangle G T) ∧
  (∀ T1 ∈ M, ∀ T2 ∈ M, T1 ≠ T2 → edgeDisjoint T1 T2)

/-- M is a MAXIMUM triangle packing -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ T, isTriangle G T → (∀ A ∈ M, edgeDisjoint T A) → T ∈ M

/-- Scattered: M-elements are pairwise vertex-disjoint -/
def isScattered (M : Finset (Finset V)) : Prop :=
  ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B

/-- Triangle T shares an edge with triangle A -/
def sharesEdge (T A : Finset V) : Prop :=
  (T ∩ A).card ≥ 2

/-- Triangles at A: triangles sharing an edge with A -/
def trianglesAt (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Finset (Finset V) :=
  (univ : Finset V).powerset.filter (fun T => isTriangle G T ∧ sharesEdge T A)

/-- An edge (pair of vertices) is contained in triangle T -/
def edgeInTriangle (e : Finset V) (T : Finset V) : Prop :=
  e.card = 2 ∧ e ⊆ T

/-- Cover: set of edges that hit all triangles -/
def isCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Finset V)) (S : Finset (Finset V)) : Prop :=
  (∀ e ∈ E, e.card = 2) ∧
  (∀ T ∈ S, ∃ e ∈ E, edgeInTriangle e T)

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: Key Lemmas
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for at_most_two_edges_have_externals:
1. Suppose all 3 edges of A have externals: T1 on e1, T2 on e2, T3 on e3
2. T1, T2, T3 are not in M (they are externals)
3. Check if T1, T2, T3 are pairwise edge-disjoint:
   - T1 uses e1 = {a,b}, T2 uses e2 = {b,c}, T3 uses e3 = {a,c}
   - T1 ∩ T2: both contain b, but T1 has e1, T2 has e2, different edges
   - Actually T1, T2 could share vertex b but not edge
   - Similarly for other pairs
4. If T1, T2, T3 are edge-disjoint with each other AND with all of M,
   then M ∪ {T1, T2, T3} is a larger packing, contradicting maximality
5. So at least one pair shares an edge, meaning not all 3 edges have externals
-/

/-- If M is maximum scattered and A ∈ M, at most 2 edges of A have externals -/
lemma at_most_two_edges_have_externals
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hS : isScattered M)
    (A : Finset V) (hA : A ∈ M) (hAcard : A.card = 3) :
    ∃ e1 e2 : Finset V, e1.card = 2 ∧ e2.card = 2 ∧ e1 ⊆ A ∧ e2 ⊆ A ∧
      ∀ T, isTriangle G T → T ∉ M → sharesEdge T A →
        edgeInTriangle e1 T ∨ edgeInTriangle e2 T := by
  sorry

/-
PROOF SKETCH for tau_at_A_le_2:
1. By at_most_two_edges_have_externals, get edges e1, e2 of A
2. Every triangle sharing edge with A either:
   - Is A itself (covered by e1 or e2 since e1, e2 ⊆ A)
   - Is an external using e1 or e2 (covered by definition)
3. So {e1, e2} covers all triangles at A
-/

/-- τ(triangles at A) ≤ 2 for any A in maximum scattered packing -/
lemma tau_at_A_le_2
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hS : isScattered M)
    (A : Finset V) (hA : A ∈ M) :
    ∃ E : Finset (Finset V), E.card ≤ 2 ∧ isCover G E (trianglesAt G A) := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: Main Theorem
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for scattered_tau_le_8:
1. M = {A, B, C, D} with |M| = 4, all pairwise vertex-disjoint
2. Every triangle T shares edge with some M-element (by maximality)
3. Since M-elements are vertex-disjoint, each T shares edge with exactly one
4. So triangles partition into trianglesAt(A), trianglesAt(B), trianglesAt(C), trianglesAt(D)
5. By tau_at_A_le_2, each set needs ≤ 2 edges to cover
6. Total: τ ≤ 2 + 2 + 2 + 2 = 8
-/

/-- Main theorem: τ ≤ 8 for scattered ν = 4 -/
theorem scattered_tau_le_8
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hMcard : M.card = 4)
    (hS : isScattered M) :
    ∃ E : Finset (Finset V), E.card ≤ 8 ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ T, isTriangle G T → ∃ e ∈ E, edgeInTriangle e T) := by
  sorry

/-- Corollary: Tuza's conjecture holds for scattered ν = 4 -/
theorem tuza_scattered_nu4
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hMcard : M.card = 4)
    (hS : isScattered M) :
    ∃ E : Finset (Finset V), E.card ≤ 2 * M.card ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ T, isTriangle G T → ∃ e ∈ E, edgeInTriangle e T) := by
  obtain ⟨E, hEcard, hEedge, hEcover⟩ := scattered_tau_le_8 G M hM hMcard hS
  exact ⟨E, by omega, hEedge, hEcover⟩

end ScatteredGeneral
