/-
APSP v6: FIXED Discovery Mode - Building on v4 Proven Results

v5 FAILED because of undefined `pathCost` and type errors.
This version is SIMPLER and CORRECT.

=== AXIOMS FROM v4 (Your own proven results) ===
1. floydWarshall_correct - O(n³) Floyd-Warshall is correct
2. shortestDist_triangle - Triangle inequality
3. shortestDist_symm - Symmetry for undirected graphs
4. fast_matmult_implies_fast_apsp - Conditional speedup

=== FOCUSED GOALS ===
Build on these axioms to discover:
1. Properties of the distance matrix
2. Special graph classes with faster algorithms
3. Connections between APSP variants
-/

import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Core Definitions -/

/-- Weighted directed graph as adjacency function -/
def WeightedDigraph (n : ℕ) := Fin n → Fin n → ENNReal

/-- Distance matrix -/
def DistanceMatrix (n : ℕ) := Fin n → Fin n → ENNReal

/-- Path of length m: sequence of m+1 vertices -/
def IsPath {n : ℕ} (G : WeightedDigraph n) (m : ℕ) (p : Fin (m + 1) → Fin n) : Prop :=
  ∀ t : Fin m, G (p (Fin.castSucc t)) (p (Fin.succ t)) < ⊤

/-- Cost of a path -/
def pathCost {n : ℕ} (G : WeightedDigraph n) (m : ℕ) (p : Fin (m + 1) → Fin n) : ENNReal :=
  ∑ t : Fin m, G (p (Fin.castSucc t)) (p (Fin.succ t))

/-- Minimum distance using at most m edges -/
def minDistBounded {n : ℕ} (G : WeightedDigraph n) (m : ℕ) (i j : Fin n) : ENNReal :=
  ⨅ (p : Fin (m + 1) → Fin n) (_ : p 0 = i) (_ : p (Fin.last m) = j), pathCost G m p

/-- Shortest path distance -/
def shortestDist {n : ℕ} (G : WeightedDigraph n) (i j : Fin n) : ENNReal :=
  ⨅ (m : Fin n), minDistBounded G m.val i j

/-- APSP algorithm structure -/
structure APSPAlgorithm (n : ℕ) where
  compute : WeightedDigraph n → DistanceMatrix n
  operations : ℕ

def APSPAlgorithm.isCorrect (alg : APSPAlgorithm n) : Prop :=
  ∀ G i j, alg.compute G i j = shortestDist G i j

/-! ## Floyd-Warshall Definition -/

def fwStep {n : ℕ} (D : DistanceMatrix n) (k : Fin n) : DistanceMatrix n :=
  fun i j => min (D i j) (D i k + D k j)

def fwInit {n : ℕ} (G : WeightedDigraph n) : DistanceMatrix n :=
  fun i j => if i = j then 0 else G i j

def floydWarshall {n : ℕ} (G : WeightedDigraph n) : DistanceMatrix n :=
  (List.finRange n).foldl fwStep (fwInit G)

def floydWarshallAlgo (n : ℕ) : APSPAlgorithm n where
  compute := floydWarshall
  operations := n ^ 3

/-! ## AXIOMS: Your Own Proven Results -/

axiom floydWarshall_correct (n : ℕ) : (floydWarshallAlgo n).isCorrect

axiom shortestDist_triangle {n : ℕ} (G : WeightedDigraph n) (i j k : Fin n) :
    shortestDist G i k ≤ shortestDist G i j + shortestDist G j k

axiom shortestDist_symm {n : ℕ} (G : WeightedDigraph n)
    (hG : ∀ i j, G i j = G j i) (i j : Fin n) :
    shortestDist G i j = shortestDist G j i

/-! ## DISCOVERY THEOREMS -/

/-- Distance matrix is a metric on connected graphs -/
theorem distance_is_pseudometric {n : ℕ} (G : WeightedDigraph n) :
    -- Zero on diagonal
    (∀ i : Fin n, shortestDist G i i = 0) ∧
    -- Triangle inequality (from axiom)
    (∀ i j k : Fin n, shortestDist G i k ≤ shortestDist G i j + shortestDist G j k) := by
  constructor
  · intro i
    -- d(i,i) = 0 via empty path
    sorry
  · exact shortestDist_triangle G

/-- Monotonicity: Adding edges can only decrease distances -/
theorem more_edges_shorter_paths {n : ℕ} (G H : WeightedDigraph n)
    (hGH : ∀ i j, H i j ≤ G i j) :
    ∀ i j, shortestDist H i j ≤ shortestDist G i j := by
  sorry

/-- For unweighted graphs (0/1/∞), distance = BFS level -/
def isUnweighted {n : ℕ} (G : WeightedDigraph n) : Prop :=
  ∀ i j, G i j = 0 ∨ G i j = 1 ∨ G i j = ⊤

theorem unweighted_distance_is_hop_count {n : ℕ} (G : WeightedDigraph n)
    (hG : isUnweighted G) (i j : Fin n) :
    -- Distance equals minimum number of edges
    ∃ m : ℕ, shortestDist G i j = m ∨ shortestDist G i j = ⊤ := by
  sorry

/-! ## Special Graph Classes -/

/-- A graph is sparse (at most m edges) -/
def isSparse {n : ℕ} (G : WeightedDigraph n) (m : ℕ) : Prop :=
  (univ.filter (fun p : Fin n × Fin n => G p.1 p.2 < ⊤ ∧ p.1 ≠ p.2)).card ≤ m

/-- A graph is a tree -/
def isTree {n : ℕ} (G : WeightedDigraph n) : Prop :=
  isSparse G (n - 1) ∧
  (∀ i j : Fin n, shortestDist G i j < ⊤)  -- Connected

/-- Trees have O(n²) APSP via DFS from each vertex -/
theorem tree_apsp_quadratic {n : ℕ} (G : WeightedDigraph n) (hTree : isTree G) :
    ∃ (alg : APSPAlgorithm n),
      alg.isCorrect ∧ alg.operations ≤ n * n := by
  sorry

/-- Sparse graphs: O(nm) via Bellman-Ford from each vertex -/
theorem sparse_apsp {n : ℕ} (G : WeightedDigraph n) (m : ℕ)
    (hSparse : isSparse G m) :
    ∃ (alg : APSPAlgorithm n),
      alg.isCorrect ∧ alg.operations ≤ n * m := by
  sorry

/-! ## The Discovery Question -/

/-- Main theorem: Characterize when subcubic APSP is possible -/
theorem apsp_complexity_dichotomy {n : ℕ} :
    -- Either: There's a graph class with subcubic APSP
    (∃ (P : WeightedDigraph n → Prop) (alg : APSPAlgorithm n),
      (∀ G, P G → alg.isCorrect) ∧
      alg.operations < n ^ 3 ∧
      ∃ G, P G) ∨  -- The class is non-empty
    -- Or: All correct algorithms need Ω(n³) in worst case
    (∀ alg : APSPAlgorithm n, alg.isCorrect → alg.operations ≥ n ^ 3) := by
  -- The first disjunct is true: trees give subcubic
  left
  use isTree
  obtain ⟨alg, hCorrect, hOps⟩ := tree_apsp_quadratic (n := n)
  sorry  -- Need a specific tree to show class is non-empty

/-! ## Bonus: Distance Matrix Properties -/

/-- The distance matrix after k iterations of Floyd-Warshall -/
def fwAfterK {n : ℕ} (G : WeightedDigraph n) (k : ℕ) : DistanceMatrix n :=
  ((List.finRange n).take k).foldl fwStep (fwInit G)

/-- Floyd-Warshall invariant: after k steps, D[i][j] = shortest path using only {0,...,k-1} as intermediates -/
theorem fw_invariant {n : ℕ} (G : WeightedDigraph n) (k : ℕ) (hk : k ≤ n) :
    ∀ i j : Fin n,
      fwAfterK G k i j = ⨅ (m : ℕ) (hm : m ≤ k)
        (p : Fin (m + 1) → Fin n)
        (_ : p 0 = i) (_ : p (Fin.last m) = j)
        (_ : ∀ t : Fin m, (p (Fin.succ t)).val < k),  -- Intermediates < k
        pathCost G m p := by
  sorry

/-- After n iterations, we have all shortest paths -/
theorem fw_complete {n : ℕ} (G : WeightedDigraph n) :
    ∀ i j, fwAfterK G n i j = shortestDist G i j := by
  sorry

end
