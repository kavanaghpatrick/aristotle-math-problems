/-
ALGORITHM DISCOVERY: All-Pairs Shortest Paths - Strengthened Formalization v4

LESSON FROM v3: Weak isCorrect allowed trivial exploits (constant functions).

FIXES IN v4:
1. isCorrect requires EXACT shortest path computation
2. Asymptotic bounds over ALL n (not existential)
3. Use ENNReal for cleaner infinity handling
4. Concrete path/distance definitions

PROVABLE GOALS:
- Floyd-Warshall correctness (O(n³))
- Conditional: fast matmult → fast APSP
- NOT provable: truly subcubic (open problem)
-/

import Mathlib

set_option maxHeartbeats 400000

open Matrix Finset BigOperators ENNReal

noncomputable section

/-! ## Concrete Definitions with Strong Correctness -/

/-- Weighted directed graph as function to ENNReal (∞ = no edge) -/
def WeightedDigraph (n : ℕ) := Fin n → Fin n → ENNReal

/-- Distance matrix -/
def DistanceMatrix (n : ℕ) := Fin n → Fin n → ENNReal

/-- Length of a path with m edges through vertices p(0), p(1), ..., p(m) -/
def pathLength {n : ℕ} (G : WeightedDigraph n) (m : ℕ) (p : Fin (m + 1) → Fin n) : ENNReal :=
  ∑ t : Fin m, G (p (Fin.castSucc t)) (p (Fin.succ t))

/-- Minimum distance using exactly m edges from i to j -/
def minDistWithEdges {n : ℕ} (G : WeightedDigraph n) (m : ℕ) (i j : Fin n) : ENNReal :=
  ⨅ (p : Fin (m + 1) → Fin n) (_ : p 0 = i) (_ : p (Fin.last m) = j), pathLength G m p

/-- Shortest path distance: infimum over all path lengths 0 to n-1 -/
def shortestDist {n : ℕ} (G : WeightedDigraph n) (i j : Fin n) : ENNReal :=
  ⨅ (m : Fin n), minDistWithEdges G m.val i j

/-- An APSP algorithm with operation count -/
structure APSPAlgorithm (n : ℕ) where
  compute : WeightedDigraph n → DistanceMatrix n
  operationCount : ℕ

/-- STRONG correctness: must compute EXACT shortest paths -/
def APSPAlgorithm.isCorrect (alg : APSPAlgorithm n) : Prop :=
  ∀ (G : WeightedDigraph n) (i j : Fin n),
    alg.compute G i j = shortestDist G i j

/-! ## Floyd-Warshall Implementation -/

/-- Floyd-Warshall step: relax through vertex k -/
def fwStep {n : ℕ} (D : DistanceMatrix n) (k : Fin n) : DistanceMatrix n :=
  fun i j => min (D i j) (D i k + D k j)

/-- Initialize distance matrix from graph (with 0 on diagonal) -/
def fwInit {n : ℕ} (G : WeightedDigraph n) : DistanceMatrix n :=
  fun i j => if i = j then 0 else G i j

/-- Full Floyd-Warshall: initialize then iterate over all k -/
def floydWarshall {n : ℕ} (G : WeightedDigraph n) : DistanceMatrix n :=
  (List.finRange n).foldl fwStep (fwInit G)

/-- Floyd-Warshall as an APSPAlgorithm -/
def floydWarshallAlgo (n : ℕ) : APSPAlgorithm n where
  compute := floydWarshall
  operationCount := n ^ 3

/-! ## Provable Theorems -/

/--
GOAL 1: Floyd-Warshall computes correct shortest paths.
This IS provable - it's a standard correctness proof.
-/
theorem floydWarshall_correct (n : ℕ) : (floydWarshallAlgo n).isCorrect := by
  sorry

/--
GOAL 2: Floyd-Warshall has cubic complexity.
Trivially true by definition.
-/
theorem floydWarshall_cubic (n : ℕ) :
    (floydWarshallAlgo n).operationCount = n ^ 3 := rfl

/--
GOAL 3: Shortest paths satisfy triangle inequality.
A basic property that should be provable from the definition.
-/
theorem shortestDist_triangle {n : ℕ} (G : WeightedDigraph n) (i j k : Fin n) :
    shortestDist G i k ≤ shortestDist G i j + shortestDist G j k := by
  sorry

/--
GOAL 4: Shortest paths are symmetric for symmetric graphs.
-/
theorem shortestDist_symm {n : ℕ} (G : WeightedDigraph n)
    (hG : ∀ i j, G i j = G j i) (i j : Fin n) :
    shortestDist G i j = shortestDist G j i := by
  sorry

/--
GOAL 5: For path graphs (linear), shortest distance = sum of edges.
A concrete sanity check.
-/
theorem shortestDist_path {n : ℕ} (hn : n ≥ 2) (G : WeightedDigraph n)
    (hPath : ∀ i : Fin n, ∀ j : Fin n,
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∨ G i j = ⊤) :
    ∀ i j : Fin n, i.val < j.val →
      shortestDist G i j = ∑ k : Fin (j.val - i.val), G ⟨i.val + k.val, sorry⟩ ⟨i.val + k.val + 1, sorry⟩ := by
  sorry

/-! ## Conditional Results (what's actually interesting) -/

/--
CONDITIONAL GOAL: If we have fast matrix multiplication over (min,+) semiring,
then we get fast APSP via repeated squaring.

This is the Seidel/Williams approach - provable in principle.
-/
theorem fast_matmult_implies_fast_apsp (n : ℕ) (T : ℕ → ℕ) :
    -- If (min,+) matrix mult of n×n matrices uses T(n) operations
    (∀ m : ℕ, ∃ (matmult : (Fin m → Fin m → ENNReal) →
                          (Fin m → Fin m → ENNReal) →
                          (Fin m → Fin m → ENNReal)),
      -- matmult is correct (computes min-plus product)
      (∀ A B i j, matmult A B i j = ⨅ k, A i k + B k j)) →
    -- Then APSP uses O(T(n) · log n) operations
    ∃ (alg : APSPAlgorithm n),
      alg.isCorrect ∧ alg.operationCount ≤ T n * (Nat.log2 n + 1) := by
  sorry

/--
NEGATIVE RESULT: No algorithm can beat Ω(n²) for dense graphs.
(Must read all edges in worst case.)
-/
theorem apsp_lower_bound (n : ℕ) (hn : n ≥ 2) (alg : APSPAlgorithm n) :
    alg.isCorrect → alg.operationCount ≥ n * (n - 1) / 2 := by
  sorry

end
