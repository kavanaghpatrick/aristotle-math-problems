/-
  slot558_both_endpoints_allsix.lean

  EXPLORATION: A PATH_4 graph where BOTH endpoints have the all-six pattern.
  This is the worst case: τ(T_e(A))=3 AND τ(T_e(D))=3.
  Question: Does τ(remaining) ≤ 2 so that 3+3+2 = 8?

  Graph on Fin 11:
    A = {0,1,2}, B = {0,3,4}, C = {3,5,6}, D = {5,7,8}
    PATH_4: A—[0]—B—[3]—C—[5]—D

    For A's all-six: w1=3, w2=4 ∈ B, adjacent to a1=1, a2=2
      Extra edges: 1-3, 1-4, 2-3, 2-4

    For D's all-six: w3=9, w4=10, adjacent to d1=7, d2=8
      BUT we need w3,w4 ∈ C. Let's use w3=3, w4=6 ∈ C.
      Wait, w3 needs to be adjacent to both d1=7 and d2=8.
      3 is NOT adjacent to 7 or 8 in the base graph.
      So add: 3-7, 3-8 (making vertex 3 adjacent to all of D minus v3=5)
      Hmm but 3 is already used. Let me use 6 and new vertex 9.
      6 is adjacent to 3 and 5 (in C). Need 6-7 and 6-8.
      9 is new, need 9-5 (for C adjacency? No, 9 ∈ C would change C).

  Actually, for D's all-six with extras in C={3,5,6}:
    D = {5,7,8}. We need w ∈ C adjacent to both 7 and 8.
    C = {3,5,6}. v3=5 is already in D. So extras from C would be 3 or 6.
    Need: 3-7, 3-8 (making 3 ∈ C adjacent to d1=7, d2=8)
    Need: 6-7, 6-8 (making 6 ∈ C adjacent to d1=7, d2=8)

  Graph on Fin 9 (same vertex set, more edges):
    Base PATH_4: A—[0]—B—[3]—C—[5]—D
    A's extras: 1-3, 1-4, 2-3, 2-4 (w1=3, w2=4 ∈ B)
    D's extras: 3-7, 3-8, 6-7, 6-8 (w3=3, w4=6 ∈ C)

  T_e(A) all-six: {0,1,3},{0,1,4},{0,2,3},{0,2,4},{1,2,3},{1,2,4} + A
  T_e(D) all-six: {5,7,3},{5,7,6},{5,8,3},{5,8,6},{7,8,3},{7,8,6} + D

  But wait: {7,8,3} — is 3-7 an edge? Yes. Is 3-8? Yes. Is 7-8? Yes (D). ✓
  {7,8,6} — 6-7? Yes. 6-8? Yes. 7-8? Yes. ✓

  Question: ν = 4 still? Need to check no 5-packing.
-/

import Mathlib

open Finset SimpleGraph

private def g9bothMat : Fin 9 → Fin 9 → Bool
  -- A = {0,1,2}
  | 0, 1 | 1, 0 | 0, 2 | 2, 0 | 1, 2 | 2, 1 => true
  -- B = {0,3,4}
  | 0, 3 | 3, 0 | 0, 4 | 4, 0 | 3, 4 | 4, 3 => true
  -- C = {3,5,6}
  | 3, 5 | 5, 3 | 3, 6 | 6, 3 | 5, 6 | 6, 5 => true
  -- D = {5,7,8}
  | 5, 7 | 7, 5 | 5, 8 | 8, 5 | 7, 8 | 8, 7 => true
  -- A's all-six: 1-3, 1-4, 2-3, 2-4
  | 1, 3 | 3, 1 | 1, 4 | 4, 1 | 2, 3 | 3, 2 | 2, 4 | 4, 2 => true
  -- D's all-six: 3-7, 3-8, 6-7, 6-8
  | 3, 7 | 7, 3 | 3, 8 | 8, 3 | 6, 7 | 7, 6 | 6, 8 | 8, 6 => true
  | _, _ => false

def G9both : SimpleGraph (Fin 9) where
  Adj x y := g9bothMat x y = true
  symm x y h := by revert h; revert x y; native_decide
  loopless x h := by revert h; revert x; native_decide

instance : DecidableRel G9both.Adj := fun x y =>
  inferInstanceAs (Decidable (g9bothMat x y = true))

def Ab : Finset (Fin 9) := {0, 1, 2}
def Bb : Finset (Fin 9) := {0, 3, 4}
def Cb : Finset (Fin 9) := {3, 5, 6}
def Db : Finset (Fin 9) := {5, 7, 8}
def Mb : Finset (Finset (Fin 9)) := {Ab, Bb, Cb, Db}

-- Helper for T_e
def Te_b (X : Finset (Fin 9)) : Finset (Finset (Fin 9)) :=
  (G9both.cliqueFinset 3).filter (fun T => 2 ≤ (T ∩ X).card)

-- Helper for remaining
def remaining_b : Finset (Finset (Fin 9)) :=
  (G9both.cliqueFinset 3).filter (fun T => (T ∩ Ab).card ≤ 1 ∧ (T ∩ Db).card ≤ 1)

-- ═══════════════════════════════════════════════════════════════════════
-- BASIC TESTS
-- ═══════════════════════════════════════════════════════════════════════

-- Is ν still 4?
theorem both_nu_le_4 :
    ∀ P ⊆ G9both.cliqueFinset 3,
      Set.Pairwise (P : Set (Finset (Fin 9))) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) →
      P.card ≤ 4 := by native_decide

-- Packing is valid
theorem both_packing_valid : Mb ⊆ G9both.cliqueFinset 3 ∧
    Set.Pairwise (Mb : Set (Finset (Fin 9))) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
  native_decide

-- T_e sizes for both endpoints
theorem both_Te_A_card : (Te_b Ab).card = 7 := by native_decide
theorem both_Te_D_card : (Te_b Db).card = 7 := by native_decide

-- τ(T_e(A)) ≥ 3 (all-six on A side)
theorem both_tau_Te_A_ge_3 :
    ∀ e1 ∈ G9both.edgeFinset, ∀ e2 ∈ G9both.edgeFinset,
    ∃ T ∈ Te_b Ab, e1 ∉ T.sym2 ∧ e2 ∉ T.sym2 := by native_decide

-- τ(T_e(D)) ≥ 3 (all-six on D side)
theorem both_tau_Te_D_ge_3 :
    ∀ e1 ∈ G9both.edgeFinset, ∀ e2 ∈ G9both.edgeFinset,
    ∃ T ∈ Te_b Db, e1 ∉ T.sym2 ∧ e2 ∉ T.sym2 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- COMPENSATING DECOMPOSITION: 3 + 3 + ? ≤ 8 ?
-- ═══════════════════════════════════════════════════════════════════════

-- How many remaining triangles?
theorem both_remaining_card : remaining_b.card = 4 := by native_decide

-- ν(remaining) ≤ 2
theorem both_nu_remaining_le_2 :
    ∀ P ⊆ remaining_b,
      Set.Pairwise (P : Set (Finset (Fin 9))) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) →
      P.card ≤ 2 := by native_decide

-- τ(remaining) ≤ 2? Test with specific cover
-- First, what are the remaining triangles?
-- They should be triangles with ≤1 vertex in A and ≤1 in D
-- B, C, and perhaps bridges between B-C

-- Test: can 1 edge cover remaining? (probably not)
-- Test: can 2 edges cover remaining?
theorem both_remaining_cover_2 :
    ∃ e1 ∈ G9both.edgeFinset, ∃ e2 ∈ G9both.edgeFinset,
    ∀ T ∈ remaining_b, e1 ∈ T.sym2 ∨ e2 ∈ T.sym2 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- OVERALL τ(G) ≤ 8
-- ═══════════════════════════════════════════════════════════════════════

-- Can we cover all triangles with 8 edges?
theorem both_tau_le_8 :
    ∃ E ⊆ G9both.edgeFinset,
    E.card ≤ 8 ∧ ∀ T ∈ G9both.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2 := by native_decide

-- STRONGER: Can we cover all with 6 edges? (checking if τ is even smaller)
-- theorem both_tau_le_6 :
--     ∃ E ⊆ G9both.edgeFinset,
--     E.card ≤ 6 ∧ ∀ T ∈ G9both.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- KEY QUESTION: Is 3 + 3 + 2 = 8 achievable? We need:
-- 1. 3-edge cover of T_e(A)
-- 2. 3-edge cover of T_e(D)
-- 3. 2-edge cover of remaining
-- 4. These 8 edges might overlap, so total ≤ 8
-- ═══════════════════════════════════════════════════════════════════════

-- In fact, T_e(A) ∩ T_e(D) = ∅ (since A∩D=∅, card 3)
-- So the 3+3+2 covers are for DISJOINT sets
-- But edges CAN be shared between covers

end
