/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 46a8d88e-dac3-4a6f-9eb9-39697d0ab50e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot556_allsix_falsification.lean

  FALSIFICATION TEST: Can all-six T_e(A) pattern coexist with ν=4?

  Graph on Fin 9:
    A = {0,1,2}, B = {0,3,4}, C = {3,5,6}, D = {5,7,8}
    PATH_4: A—[0]—B—[3]—C—[5]—D
    Extra edges: 1-3, 1-4, 2-3, 2-4 (making w1=3,w2=4 adjacent to all of A)
    Note: w1=3 ∈ B, w2=4 ∈ B

  All-six T_e(A) triangles:
    Fan(a1,a2): {1,2,3}, {1,2,4}
    Fan(v1,a2): {0,2,3}, {0,2,4}
    Fan(v1,a1): {0,1,3}, {0,1,4}

  TEST 1: ν = 4 (no 5-packing exists)
  TEST 2: τ(T_e(A)) = 3 (no 2-edge cover of T_e(A))
  TEST 3: τ(G) ≤ 8 (overall Tuza bound still holds)

  If TEST 1 + TEST 2 pass: τ(T_e(A)) ≤ 2 is FALSE and the
  decomposition T_e(A)+T_e(D)+remaining can't prove τ ≤ 8.
-/

import Mathlib


open Finset SimpleGraph

-- Define the graph on Fin 9
def allSixGraph : SimpleGraph (Fin 9) where
  Adj x y :=
    -- A = {0,1,2}
    (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨
    (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) ∨
    (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨
    -- B = {0,3,4}
    (x = 0 ∧ y = 3) ∨ (x = 3 ∧ y = 0) ∨
    (x = 0 ∧ y = 4) ∨ (x = 4 ∧ y = 0) ∨
    (x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 3) ∨
    -- C = {3,5,6}
    (x = 3 ∧ y = 5) ∨ (x = 5 ∧ y = 3) ∨
    (x = 3 ∧ y = 6) ∨ (x = 6 ∧ y = 3) ∨
    (x = 5 ∧ y = 6) ∨ (x = 6 ∧ y = 5) ∨
    -- D = {5,7,8}
    (x = 5 ∧ y = 7) ∨ (x = 7 ∧ y = 5) ∨
    (x = 5 ∧ y = 8) ∨ (x = 8 ∧ y = 5) ∨
    (x = 7 ∧ y = 8) ∨ (x = 8 ∧ y = 7) ∨
    -- Extra: w1=3, w2=4 adjacent to a1=1, a2=2
    (x = 1 ∧ y = 3) ∨ (x = 3 ∧ y = 1) ∨
    (x = 1 ∧ y = 4) ∨ (x = 4 ∧ y = 1) ∨
    (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) ∨
    (x = 2 ∧ y = 4) ∨ (x = 4 ∧ y = 2)
  symm x y h := by rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> simp_all
  loopless x h := by rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> simp_all

instance : DecidableRel allSixGraph.Adj := fun x y => by
  unfold allSixGraph; simp only; infer_instance

-- Define the packing elements
def A : Finset (Fin 9) := {0, 1, 2}

def B : Finset (Fin 9) := {0, 3, 4}

def C : Finset (Fin 9) := {3, 5, 6}

def D : Finset (Fin 9) := {5, 7, 8}

-- T_e(A) = triangles sharing ≥2 vertices with A
def T_e_A : Finset (Finset (Fin 9)) :=
  (allSixGraph.cliqueFinset 3).filter (fun T => 2 ≤ (T ∩ A).card)

-- TEST 1: The packing M = {A, B, C, D} is valid
def M : Finset (Finset (Fin 9)) := {A, B, C, D}

-- Verify all elements are triangles
theorem A_is_triangle : A ∈ allSixGraph.cliqueFinset 3 := by native_decide

theorem B_is_triangle : B ∈ allSixGraph.cliqueFinset 3 := by native_decide

theorem C_is_triangle : C ∈ allSixGraph.cliqueFinset 3 := by native_decide

theorem D_is_triangle : D ∈ allSixGraph.cliqueFinset 3 := by native_decide

-- Verify packing condition (pairwise ≤1 shared vertex)
theorem M_is_packing : M ⊆ allSixGraph.cliqueFinset 3 ∧
    Set.Pairwise (M : Set (Finset (Fin 9))) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
  native_decide

-- Verify M has 4 elements
theorem M_card : M.card = 4 := by native_decide

-- TEST 1: ν = 4 (no 5-packing exists)
theorem nu_eq_4 : ∀ P ⊆ allSixGraph.cliqueFinset 3,
    Set.Pairwise (P : Set (Finset (Fin 9))) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) →
    P.card ≤ 4 := by
  native_decide

-- TEST 2a: T_e(A) has 7 elements (A + 6 non-M triangles)
theorem T_e_A_card : T_e_A.card = 7 := by native_decide

-- TEST 2b: No 2-element edge set covers all of T_e(A)
-- i.e., τ(T_e(A)) ≥ 3
-- We check: for every pair of edges e1, e2 from G.edgeFinset,
-- there exists a triangle in T_e_A not hit by {e1, e2}
theorem tau_Te_A_ge_3 :
    ∀ e1 ∈ allSixGraph.edgeFinset, ∀ e2 ∈ allSixGraph.edgeFinset,
    ∃ T ∈ T_e_A, e1 ∉ T.sym2 ∨ e2 ∉ T.sym2 := by
  native_decide

-- Actually, the above is wrong. We need: for every {e1, e2},
-- there exists T ∈ T_e_A such that e1 ∉ T.sym2 AND e2 ∉ T.sym2
-- i.e., T is not hit by either edge
theorem tau_Te_A_ge_3' :
    ∀ e1 ∈ allSixGraph.edgeFinset, ∀ e2 ∈ allSixGraph.edgeFinset,
    ∃ T ∈ T_e_A, e1 ∉ T.sym2 ∧ e2 ∉ T.sym2 := by
  native_decide

-- TEST 3: τ(G) ≤ 8 (the overall Tuza bound still holds)
-- Witness: {0-1, 3-4, 5-6, 7-8, 2-3, 2-4} covers all triangles (6 edges)
-- This shows τ ≤ 6 ≤ 8

end