/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c7b118db-ecca-436f-a975-fbae7253f562

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot557_partition_test.lean

  EXPLORATION: Test various decomposition strategies on the Fin 9 all-six graph.

  Graph on Fin 9:
    A = {0,1,2}, B = {0,3,4}, C = {3,5,6}, D = {5,7,8}
    PATH_4: A—[0]—B—[3]—C—[5]—D
    Extra edges: 1-3, 1-4, 2-3, 2-4 (w1=3,w2=4 ∈ B)

  Tests:
  1. S_A∪S_B partition: τ(S_A∪S_B) and τ(complement)
  2. Compensating decomposition: when τ(T_e(A))=3, is τ(remaining)≤2?
  3. Overall τ(G) ≤ 8 (sanity check)
  4. Various specific 8-edge cover candidates
-/

import Mathlib


open Finset SimpleGraph

-- Reuse the graph definition from slot556
def G9 : SimpleGraph (Fin 9) where
  Adj x y :=
    (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨
    (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) ∨
    (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨
    (x = 0 ∧ y = 3) ∨ (x = 3 ∧ y = 0) ∨
    (x = 0 ∧ y = 4) ∨ (x = 4 ∧ y = 0) ∨
    (x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 3) ∨
    (x = 3 ∧ y = 5) ∨ (x = 5 ∧ y = 3) ∨
    (x = 3 ∧ y = 6) ∨ (x = 6 ∧ y = 3) ∨
    (x = 5 ∧ y = 6) ∨ (x = 6 ∧ y = 5) ∨
    (x = 5 ∧ y = 7) ∨ (x = 7 ∧ y = 5) ∨
    (x = 5 ∧ y = 8) ∨ (x = 8 ∧ y = 5) ∨
    (x = 7 ∧ y = 8) ∨ (x = 8 ∧ y = 7) ∨
    (x = 1 ∧ y = 3) ∨ (x = 3 ∧ y = 1) ∨
    (x = 1 ∧ y = 4) ∨ (x = 4 ∧ y = 1) ∨
    (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) ∨
    (x = 2 ∧ y = 4) ∨ (x = 4 ∧ y = 2)
  symm x y h := by rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> simp_all
  loopless x h := by rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> simp_all

instance : DecidableRel G9.Adj := fun x y => by
  unfold G9; simp only; infer_instance

def A9 : Finset (Fin 9) := {0, 1, 2}

def B9 : Finset (Fin 9) := {0, 3, 4}

def C9 : Finset (Fin 9) := {3, 5, 6}

def D9 : Finset (Fin 9) := {5, 7, 8}

-- T_e(X) = triangles sharing ≥2 vertices with X
def Te (X : Finset (Fin 9)) : Finset (Finset (Fin 9)) :=
  (G9.cliqueFinset 3).filter (fun T => 2 ≤ (T ∩ X).card)

-- S_A ∪ S_B = triangles sharing ≥2 with A or ≥2 with B
def S_AB : Finset (Finset (Fin 9)) :=
  (G9.cliqueFinset 3).filter (fun T => 2 ≤ (T ∩ A9).card ∨ 2 ≤ (T ∩ B9).card)

-- Complement: triangles sharing ≤1 with both A and B
def S_rest : Finset (Finset (Fin 9)) :=
  (G9.cliqueFinset 3).filter (fun T => (T ∩ A9).card ≤ 1 ∧ (T ∩ B9).card ≤ 1)

-- Remaining after T_e(A) ∪ T_e(D) (the old decomposition)
def remaining_old : Finset (Finset (Fin 9)) :=
  (G9.cliqueFinset 3).filter (fun T => (T ∩ A9).card ≤ 1 ∧ (T ∩ D9).card ≤ 1)

-- ═══════════════════════════════════════════════════════════════════════
-- COUNTING TESTS
-- ═══════════════════════════════════════════════════════════════════════

-- Total triangles in G9
theorem total_triangles : (G9.cliqueFinset 3).card = 12 := by native_decide

-- S_A∪S_B partition sizes
theorem S_AB_card : S_AB.card = 10 := by native_decide

theorem S_rest_card : S_rest.card = 2 := by native_decide

-- T_e sizes
theorem Te_A_card : (Te A9).card = 7 := by native_decide

theorem Te_B_card : (Te B9).card = 7 := by native_decide

theorem Te_C_card : (Te C9).card = 1 := by native_decide

theorem Te_D_card : (Te D9).card = 1 := by native_decide

-- Old decomposition remaining
theorem remaining_old_card : remaining_old.card = 4 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- PARTITION COMPLETENESS: every triangle is in S_AB or S_rest
-- ═══════════════════════════════════════════════════════════════════════

theorem partition_complete :
    ∀ T ∈ G9.cliqueFinset 3, T ∈ S_AB ∨ T ∈ S_rest := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- COVER TESTS: Can we cover S_AB with specific edges?
-- ═══════════════════════════════════════════════════════════════════════

-- S_AB cover with 4 edges: {s(1,3), s(2,4), s(0,1), s(0,3)}
theorem S_AB_cover_4 :
    ∀ T ∈ S_AB,
      s((1:Fin 9), 3) ∈ T.sym2 ∨ s((2:Fin 9), 4) ∈ T.sym2 ∨
      s((0:Fin 9), 1) ∈ T.sym2 ∨ s((0:Fin 9), 3) ∈ T.sym2 := by native_decide

-- S_rest cover with 2 edges: {s(3,5), s(7,8)} covers C and D
theorem S_rest_cover_2 :
    ∀ T ∈ S_rest,
      s((3:Fin 9), 5) ∈ T.sym2 ∨ s((7:Fin 9), 8) ∈ T.sym2 := by native_decide

-- Full graph cover with 6 edges (τ ≤ 6)
theorem full_cover_6 :
    ∀ T ∈ G9.cliqueFinset 3,
      s((1:Fin 9), 3) ∈ T.sym2 ∨ s((2:Fin 9), 4) ∈ T.sym2 ∨
      s((0:Fin 9), 1) ∈ T.sym2 ∨ s((0:Fin 9), 3) ∈ T.sym2 ∨
      s((3:Fin 9), 5) ∈ T.sym2 ∨ s((7:Fin 9), 8) ∈ T.sym2 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- COMPENSATING DECOMPOSITION TEST
-- Old decomposition: T_e(A) ∪ T_e(D) ∪ remaining
-- τ(T_e(A)) = 3, τ(T_e(D)) = 1, τ(remaining) = ?
-- ═══════════════════════════════════════════════════════════════════════

-- remaining_old cover with 2 edges: {s(3,4), s(5,6)}
-- remaining = {B={0,3,4}, C={3,5,6}, {1,3,4}, {2,3,4}}
theorem remaining_old_cover_2 :
    ∀ T ∈ remaining_old,
      s((3:Fin 9), 4) ∈ T.sym2 ∨ s((5:Fin 9), 6) ∈ T.sym2 := by native_decide

-- Verify τ(remaining) ≥ 2 (1 edge can't cover all 4 remaining triangles)
theorem remaining_old_tau_ge_2 :
    ∀ e ∈ G9.edgeFinset,
      ∃ T ∈ remaining_old, e ∉ T.sym2 := by native_decide

-- So τ(remaining_old) = 2 exactly

-- τ(T_e(D)) = 1 (just one triangle, one edge suffices)
theorem Te_D_tau_eq_1 :
    ∃ e ∈ G9.edgeFinset, ∀ T ∈ Te D9, e ∈ T.sym2 := by native_decide

-- COMPENSATING TOTAL: τ(T_e(A)) + τ(T_e(D)) + τ(remaining)
-- = 3 + 1 + 2 = 6 ≤ 8 ✓
-- The decomposition STILL gives ≤ 8 on this graph!
-- The issue is proving τ(remaining) ≤ 2 in GENERAL when τ(T_e(A)) = 3.

-- ═══════════════════════════════════════════════════════════════════════
-- ν TESTS FOR PARTITIONS
-- ═══════════════════════════════════════════════════════════════════════

-- ν(S_AB) ≤ 3 (no 4-packing within S_AB)
theorem nu_S_AB_le_3 :
    ∀ P ⊆ S_AB,
      Set.Pairwise (P : Set (Finset (Fin 9))) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) →
      P.card ≤ 3 := by native_decide

-- ν(S_rest) ≤ 2
theorem nu_S_rest_le_2 :
    ∀ P ⊆ S_rest,
      Set.Pairwise (P : Set (Finset (Fin 9))) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) →
      P.card ≤ 2 := by native_decide

-- ν(remaining_old) ≤ 2
theorem nu_remaining_old_le_2 :
    ∀ P ⊆ remaining_old,
      Set.Pairwise (P : Set (Finset (Fin 9))) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) →
      P.card ≤ 2 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- KEY TEST: When τ(T_e(A))=3, does ν(remaining) actually drop?
-- On this graph: ν(remaining_old) = 2, τ(remaining_old) = 2
-- If generally: τ(T_e(A))=3 ⟹ τ(remaining)≤2, then 3+3+2=8 ✓
-- ═══════════════════════════════════════════════════════════════════════

-- Verify the "compensating" bound: total ≤ 8
-- Using: T_e(A) needs 3 edges, T_e(D) needs 1, remaining needs 2
-- 3 + 1 + 2 = 6 ≤ 8
-- Even if symmetric: 3 + 3 + 2 = 8 ≤ 8

end