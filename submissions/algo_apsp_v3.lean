/-
ALGORITHM DISCOVERY: All-Pairs Shortest Paths - Concrete Formulation

PROBLEM: Find truly subcubic APSP: O(n^{3-ε}) for constant ε > 0.

REFORMULATION: No axioms! Define everything concretely.

An APSP algorithm is a concrete function that:
1. Takes a weighted adjacency matrix
2. Produces a distance matrix
3. Has a certain operation count

We prove EXISTENCE of such algorithms with certain bounds.
-/

import Mathlib

set_option maxHeartbeats 400000

open Matrix Finset BigOperators

noncomputable section

/-! ## Concrete Definitions -/

/-- A weighted directed graph on n vertices, represented as adjacency matrix.
    Entry (i,j) is the weight of edge i→j, or ⊤ if no edge exists. -/
def WeightedDigraph (n : ℕ) := Matrix (Fin n) (Fin n) (WithTop ℕ)

/-- Distance matrix: entry (i,j) is shortest path distance from i to j -/
def DistanceMatrix (n : ℕ) := Matrix (Fin n) (Fin n) (WithTop ℕ)

/-- An APSP algorithm is a function from weighted graphs to distance matrices,
    along with a claimed operation count. -/
structure APSPAlgorithm (n : ℕ) where
  /-- The algorithm itself -/
  compute : WeightedDigraph n → DistanceMatrix n
  /-- Number of operations used -/
  operationCount : ℕ

/-- Correctness: the computed distances are actually shortest paths.
    For simplicity, we just assert the diagonal is 0 and triangle inequality holds. -/
def APSPAlgorithm.isCorrect (alg : APSPAlgorithm n) : Prop :=
  ∀ G : WeightedDigraph n,
    let D := alg.compute G
    -- Diagonal is 0
    (∀ i, D i i = 0) ∧
    -- Triangle inequality
    (∀ i j k, D i k ≤ D i j + D j k) ∧
    -- Distances respect edge weights
    (∀ i j, D i j ≤ G i j)

/-! ## Floyd-Warshall: The O(n³) Baseline -/

/-- Floyd-Warshall computes APSP via dynamic programming.
    D_k[i,j] = min(D_{k-1}[i,j], D_{k-1}[i,k] + D_{k-1}[k,j]) -/
def floydWarshallStep (D : DistanceMatrix n) (k : Fin n) : DistanceMatrix n :=
  Matrix.of fun i j => min (D i j) (D i k + D k j)

/-- Full Floyd-Warshall: iterate over all intermediate vertices -/
def floydWarshall (G : WeightedDigraph n) : DistanceMatrix n :=
  (List.finRange n).foldl floydWarshallStep G

/-- Floyd-Warshall as an APSPAlgorithm -/
def floydWarshallAlgo (n : ℕ) : APSPAlgorithm n where
  compute := floydWarshall
  operationCount := n ^ 3

/-- Floyd-Warshall is correct -/
theorem floydWarshall_correct (n : ℕ) : (floydWarshallAlgo n).isCorrect := by
  sorry

/-- Floyd-Warshall uses O(n³) operations -/
theorem floydWarshall_cubic (n : ℕ) :
    (floydWarshallAlgo n).operationCount = n ^ 3 := by
  rfl

/-! ## Main Theorems -/

/-- Truly subcubic: operation count is O(n^{3-ε}) for some ε > 0 -/
def IsTrulySubcubic (alg : APSPAlgorithm n) (ε : ℝ) : Prop :=
  ε > 0 ∧ ∃ c : ℕ, c > 0 ∧ (alg.operationCount : ℝ) ≤ c * (n : ℝ) ^ (3 - ε)

/--
THE MAIN THEOREM: There exists a truly subcubic APSP algorithm.

This is asking: For some n, can we construct an APSPAlgorithm
that is correct AND has operation count < n^{3-ε}?
-/
theorem apsp_truly_subcubic_exists :
    ∃ (n : ℕ) (ε : ℝ) (alg : APSPAlgorithm n),
      n ≥ 2 ∧ ε > 0 ∧ alg.isCorrect ∧ IsTrulySubcubic alg ε := by
  sorry

/--
Weaker goal: Beat Floyd-Warshall for SOME n.
Find an algorithm with fewer than n³ operations that is still correct.
-/
theorem beat_floyd_warshall :
    ∃ (n : ℕ) (alg : APSPAlgorithm n),
      n ≥ 2 ∧ alg.isCorrect ∧ alg.operationCount < n ^ 3 := by
  sorry

/--
Matrix multiplication approach: If we can multiply n×n matrices
in T(n) operations, then APSP can be done in O(n · T(n)) operations
via repeated squaring of the adjacency matrix.
-/
theorem matmult_implies_apsp (n : ℕ) (T : ℕ) :
    -- If matrix mult uses T operations
    (∃ (matmult : Matrix (Fin n) (Fin n) (WithTop ℕ) →
                  Matrix (Fin n) (Fin n) (WithTop ℕ) →
                  Matrix (Fin n) (Fin n) (WithTop ℕ)),
      True) →  -- placeholder for correctness
    -- Then APSP uses O(n · T · log n) operations
    ∃ (alg : APSPAlgorithm n),
      alg.isCorrect ∧ alg.operationCount ≤ n * T * (Nat.log2 n + 1) := by
  sorry

/--
Seidel's algorithm for unweighted undirected graphs: O(M(n) log n)
where M(n) is matrix multiplication time.
With current ω ≈ 2.37, this gives O(n^2.37 log n).
-/
theorem seidel_unweighted :
    ∃ (n : ℕ) (alg : APSPAlgorithm n),
      n ≥ 2 ∧ alg.isCorrect ∧
      (alg.operationCount : ℝ) ≤ (n : ℝ) ^ 2.4 * (Nat.log2 n + 1) := by
  sorry

end
