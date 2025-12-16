# MASTER LIST: Interdisciplinary Unsolved Problems for Aristotle

**Generated:** December 11, 2025
**Sources:** 7 Claude agents + Gemini + Grok
**Total Problems Identified:** ~70+ unique problems

---

## Executive Summary

This document consolidates findings from:
- 7 specialized Claude research agents (Statistical Physics, Algorithm Optimality, Information Theory, Topological Quantum Computing, Expander Graphs, SAT/CSP, Algebraic Coding Theory)
- Gemini comprehensive analysis
- Grok quantum complexity focus

**Problem Distribution:**
- **Statistical Physics:** 7 problems (10-35% success)
- **Algorithm Optimality:** 7 problems (10-35% success)
- **Information Theory:** 7 problems (5-35% success)
- **Topological Quantum Computing:** 5 problems (5-40% success)
- **Expander Graphs & Spectral Theory:** 5 problems (15-45% success)
- **SAT/Constraint Satisfaction:** 5 problems (10-35% success)
- **Algebraic Coding Theory:** 5 problems (5-28% success)
- **Gemini Pure Math:** ~15 problems (varies)
- **Grok Quantum Complexity:** 18 problems (mostly 5-15% success)

---

## TOP TIER PROBLEMS (30-45% Success Probability)

### 1. **Spectral Gap Bounds for Odd-Diameter Graphs** ⭐ HIGHEST
- **Category:** Expander Graphs
- **Success:** 30-45%
- **Why:** Recent 2024 progress by Exoo; tighter bounds proven for odd diameters
- **CS Impact:** Random walk mixing, gossip protocols, algorithm performance
- **Formalizability:** MEDIUM
- **Source:** Expander Graphs agent

### 2. **Sorting Network Size Optimality (n=18)**
- **Category:** Algorithm Optimality
- **Success:** 35%
- **Why:** n=17 just solved in 2024; natural next target
- **CS Impact:** Hardware sorting circuits, parallel algorithms
- **Formalizability:** MEDIUM
- **Source:** Algorithm Optimality agent

### 3. **Jones Polynomial Certifiable Cases**
- **Category:** Topological Quantum Computing
- **Success:** 30-40%
- **Why:** Explicit Fibonacci anyon braid matrices published 2024
- **Physics Impact:** Topological quantum computing verification
- **Formalizability:** MEDIUM
- **Source:** Topological Quantum agent

### 4. **Polar Codes Finite Blocklength Scaling**
- **Category:** Information Theory
- **Success:** 30-35%
- **Why:** March 2025 paper with new bounds for 5G applications
- **CS Impact:** 5G/6G communication systems
- **Formalizability:** MEDIUM-HARD
- **Source:** Information Theory agent

### 5. **Resolution Complexity for Specific SAT Formulas**
- **Category:** SAT/CSP
- **Success:** 35%
- **Why:** Resolution well-formalized; can verify LRAT proofs
- **CS Impact:** SAT solver performance, automated reasoning
- **Formalizability:** MEDIUM
- **Source:** SAT/CSP agent

### 6. **Quantum Query Complexity of Collision Problem**
- **Category:** Quantum Complexity
- **Success:** 30%
- **Why:** Discrete query complexity with known techniques
- **CS Impact:** Quantum algorithm design, cryptography
- **Formalizability:** MEDIUM
- **Source:** Grok

### 7. **Quantum Communication Complexity of Disjointness**
- **Category:** Quantum Complexity
- **Success:** 30%
- **Why:** Discrete communication protocol analysis
- **CS Impact:** Distributed quantum computing, cryptography
- **Formalizability:** MEDIUM
- **Source:** Grok

---

## HIGH-VALUE PROBLEMS (20-30% Success Probability)

### 8. **Two-Sided Vertex Expansion Beyond 60%**
- **Category:** Expander Graphs
- **Success:** 25-40%
- **Why:** Nov 2024 breakthrough achieved 59.5%; optimal constant remains
- **CS Impact:** LDPC codes, quantum error correction
- **Formalizability:** MEDIUM
- **Source:** Expander Graphs agent

### 9. **Antiferromagnetic Potts Model - Partition Function Bounds**
- **Category:** Statistical Physics
- **Success:** 25-35%
- **Why:** 2023-2024 progress on Galvin-Tetali conjecture
- **Physics Impact:** Phase transitions, statistical mechanics
- **Formalizability:** HARD
- **Source:** Statistical Physics agent

### 10. **F-Matrix Solvability for Fusion Rules**
- **Category:** Topological Quantum Computing
- **Success:** 25-35%
- **Why:** Pentagon equation solvers exist (SageMath)
- **Physics Impact:** Anyonic systems, topological quantum computing
- **Formalizability:** MEDIUM
- **Source:** Topological Quantum agent

### 11. **Type I [56,28,12] Self-Dual Code Existence**
- **Category:** Algebraic Coding Theory
- **Success:** 25-30%
- **Why:** Concrete finite problem; new necessary conditions 2021-2024
- **CS Impact:** Quantum error correction, lattice theory
- **Formalizability:** MEDIUM-HARD
- **Source:** Information Theory agent

### 12. **Online Bipartite Matching (degree d=3)**
- **Category:** Algorithm Optimality
- **Success:** 25%
- **Why:** d=2 just solved Nov 2024; incremental step
- **CS Impact:** Ad allocation, ride-sharing algorithms
- **Formalizability:** MEDIUM-HARD
- **Source:** Algorithm Optimality agent

### 13. **LIS Streaming Lower Bound**
- **Category:** Algorithm Optimality
- **Success:** 25%
- **Why:** Ω(√n) bound proven Dec 2024 (brand new!)
- **CS Impact:** Streaming algorithms, data structures
- **Formalizability:** HARD
- **Source:** Algorithm Optimality agent

### 14. **Polynomial Calculus Resolution (PCR) Space Lower Bounds**
- **Category:** SAT/CSP
- **Success:** 25%
- **Why:** Can verify for pebbling principles (n ≤ 15)
- **CS Impact:** Memory requirements for automated reasoning
- **Formalizability:** HARD
- **Source:** SAT/CSP agent

### 15. **Lossless Bipartite Expanders in Unbalanced Settings**
- **Category:** Expander Graphs
- **Success:** 20-35%
- **Why:** Golowich (SODA 2024) solved balanced case
- **CS Impact:** Error-correcting codes, derandomization
- **Formalizability:** HARD
- **Source:** Expander Graphs agent

### 16. **TEE Lower Bound Characterization**
- **Category:** Topological Quantum Computing
- **Success:** 20-30%
- **Why:** Universal lower bound proven 2023; characterization open
- **Physics Impact:** Topological entanglement entropy
- **Formalizability:** MEDIUM-HARD
- **Source:** Topological Quantum agent

### 17. **Ingleton Inequality Maximum Violation**
- **Category:** Information Theory
- **Success:** 20-25%
- **Why:** Previous conjecture disproven; current best: 0.0925000777
- **CS Impact:** Information theory bounds, network coding
- **Formalizability:** MEDIUM
- **Source:** Information Theory agent

### 18. **Boolean Promise CSP Dichotomy**
- **Category:** SAT/CSP
- **Success:** 20%
- **Why:** CSP dichotomy solved 2017; PCSP remains open
- **CS Impact:** Hardness of approximation, learning theory
- **Formalizability:** MEDIUM-HARD
- **Source:** SAT/CSP agent

### 19. **Linear Programming Bound Improvement (Small Cases)**
- **Category:** Algebraic Coding Theory
- **Success:** 18-28%
- **Why:** Computationally verified for n ≤ 100; best success/difficulty ratio
- **CS Impact:** Code bounds, approximation algorithms
- **Formalizability:** MEDIUM
- **Source:** Coding Theory agent

### 20. **QAOA Depth-2 Optimality Conjecture**
- **Category:** Quantum Complexity
- **Success:** 20%
- **Why:** MaxCut on 3-regular graphs; discrete optimization
- **CS Impact:** Quantum optimization algorithms
- **Formalizability:** MEDIUM
- **Source:** Grok

---

## MEDIUM-VALUE PROBLEMS (15-20% Success Probability)

### 21. **k-Server Conjecture for Small k**
- **Success:** 20%
- **Why:** 40-year-old conjecture; bounded metric spaces tractable
- **Source:** Algorithm Optimality agent

### 22. **Bilu-Linial Conjecture for Signed Graphs**
- **Success:** 15-25%
- **Why:** Upper bound proven 2015; lower bound open
- **Source:** Expander Graphs agent

### 23. **Integral Cayley Graphs Characterization**
- **Success:** 15-25%
- **Why:** Known for cyclic, abelian, dihedral groups
- **Source:** Expander Graphs agent

### 24. **Weak Integrality ⟹ Finite Braid Representation**
- **Success:** 15-25%
- **Why:** Known solution techniques; discrete structure
- **Source:** Topological Quantum agent

### 25. **Chromatic Polynomial Zeros for Series-Parallel Graphs**
- **Success:** 15-25%
- **Why:** 2023 disproved Sokal's conjecture; zero-free regions open
- **Source:** Statistical Physics agent

### 26. **Matrix Discrepancy - Kómlos Conjecture Lower Bound**
- **Success:** 15-25%
- **Why:** 2024 improved bound to K ≥ 1+√2
- **Source:** Statistical Physics agent

### 27. **Metric TSP Inapproximability Gap**
- **Success:** 15%
- **Why:** Huge gap between 1.008 hardness and 1.5 algorithm
- **Source:** Algorithm Optimality agent

### 28. **Non-Existence of MDS Cyclic Codes at Boundary Parameters**
- **Success:** 12-18%
- **Why:** 2024 enumeration identified gaps; non-existence proofs easier
- **Source:** Coding Theory agent

### 29. **Gilbert-Varshamov Bound Asymptotic Exactness**
- **Success:** 10-15%
- **Why:** Logarithmic improvements established recently
- **Source:** Information Theory agent

### 30. **Site Percolation Threshold on Square Lattice**
- **Success:** 10-15%
- **Why:** No exact analytical value (13 decimal numerical precision)
- **Source:** Statistical Physics agent

### 31. **Additive MDS Codes Over F_{2^m}**
- **Success:** 10-20%
- **Why:** Linear case solved Feb 2024; additive remains
- **Source:** Coding Theory agent

---

## LOWER-PRIORITY PROBLEMS (5-15% Success)

### 32-41: Quantum Complexity Problems (Grok)
Most of these are "prove quantum advantage for X algorithm" problems with 5-15% success:
- Entanglement Distillation Threshold (10%)
- Bounded-Depth NAND Circuit Complexity (5%)
- QMA vs QCMA Separation (5%)
- Random Circuit Sampling (10%)
- Quantum Error Correction Threshold (10%)
- Boson Sampling Advantage (10%)
- IQP Circuits (10%)
- Randomized Benchmarking (10%)
- Shor's Algorithm variants (10%)
- Grover's Algorithm variants (10%)
- Quantum Walks (10%)
- Quantum Annealing (10%)
- Quantum Machine Learning (10%)
- Quantum Simulation (10%)
- Quantum Metrology (10%)

**Issue:** These are mostly similar in structure and formalizability is HARD/VERY HARD.

### 42. **Random 3-SAT Satisfiability Threshold (Exact)**
- **Success:** 15%
- **Why:** Statistical mechanics formalization challenging
- **Source:** SAT/CSP agent

### 43. **Algorithmic Gap for Low-Degree Polynomial Algorithms**
- **Success:** 10%
- **Why:** Requires spectral methods
- **Source:** SAT/CSP agent

### 44. **Frequency Moments F₃, F₄ Space Lower Bounds**
- **Success:** 10%
- **Why:** Fundamental streaming complexity
- **Source:** Algorithm Optimality agent

### 45. **Circuit Complexity Lower Bounds (Monotone CLIQUE)**
- **Success:** 12%
- **Why:** Bounded depth/size creates finite verification
- **Source:** Algorithm Optimality agent

### 46. **Kac-Ward Determinant Extension to Higher Genus**
- **Success:** 10-20%
- **Why:** 2024 extends planar formula; genus g≥2 open
- **Source:** Statistical Physics agent

### 47. **Lévy Spin Glass Model - Enriched Free Energy**
- **Success:** 8-15%
- **Why:** 2025 paper establishes partial results
- **Source:** Statistical Physics agent

### 48. **Quantum MDS Conjecture**
- **Success:** 5-10%
- **Why:** Only proven for q=2,3 and distance-3
- **Source:** Information Theory agent

### 49. **Shannon Capacity of C₇**
- **Success:** 5-8%
- **Why:** Famous since Lovász solved C₅ in 1979
- **Source:** Information Theory agent

### 50. **Rank ≤ 4 Modular Tensor Category Classification**
- **Success:** 5-15%
- **Why:** VERY HARD formalizability; 5000+ LOC
- **Source:** Topological Quantum agent

### 51. **Li-Li Conjecture (Network Coding)**
- **Success:** 15-20%
- **Why:** 2023-2024 progress on special cases
- **Source:** Information Theory agent

### 52. **Achievability of Drinfeld-Vladut Bound**
- **Success:** 5-12%
- **Why:** Asymptotic solutions exist; finite-length unclear
- **Source:** Coding Theory agent

### 53. **Non-uniqueness of Ising Phase Transitions on Tree-like Graphs**
- **Success:** 20-30%
- **Why:** 2024 breakthrough showing non-monotonicity
- **Source:** Statistical Physics agent

---

## GEMINI-SPECIFIC ADDITIONS (Classic Pure Math)

These complement the interdisciplinary focus but are more traditional:

### 54. **1/3–2/3 Conjecture (Posets)**
- **Success:** ~25%?
- **Why:** Clean finite discrete structure
- **Category:** Combinatorics

### 55. **Lonely Runner Conjecture**
- **Success:** ~20%?
- **Why:** Diophantine approximation
- **Category:** Number Theory/Combinatorics

### 56. **Odd Perfect Numbers**
- **Success:** ~10%?
- **Why:** Massive computational bounds + formal modular arithmetic
- **Category:** Number Theory

### 57. **Erdős-Szemerédi Sum-Product Problem**
- **Success:** ~15%?
- **Why:** Managing many inequalities
- **Category:** Number Theory/Combinatorics

### 58. **Kaplansky's Unit Conjecture (Variations)**
- **Success:** ~20%?
- **Why:** Computational algebra; matrix finding
- **Category:** Algebra

### 59. **Inscribed Square Problem**
- **Success:** ~15%?
- **Why:** Smooth case solved; continuous open
- **Category:** Topology/Geometry

### 60. **Invariant Subspace Problem (Hilbert)**
- **Success:** ~5%?
- **Why:** "Holy Grail" of functional analysis
- **Category:** Analysis

### 61. **Smooth Poincaré in 4D**
- **Success:** ~5%?
- **Why:** Gap between topological and smooth manifolds
- **Category:** Topology

### 62. **PFR Constant Optimization**
- **Success:** ~25%?
- **Why:** Recent Lean proof; optimizing constant
- **Category:** Combinatorics/Additive Combinatorics

### 63. **Hat Guessing Number of a Graph**
- **Success:** ~20%?
- **Why:** Combinatorial game theory
- **Category:** Combinatorics/Graph Theory

### 64. **Infinite Skolem Sequences**
- **Success:** ~15%?
- **Why:** Constructive or non-existence proof
- **Category:** Combinatorics

### 65. **Equational Theories (Tao's Project)**
- **Success:** ~30%?
- **Why:** Purely mechanical logic at massive scale
- **Category:** Algebra/Logic

---

## OVERLAP WITH ORIGINAL 14 PROBLEMS

From our original verified unsolved problems:

1. ✅ **R(5,5)** - Already in original list (Gemini also mentioned)
2. ✅ **Frankl's Conjecture** - Already in original list (Gemini also mentioned)
3. ✅ **W(3,5)** - Already in original list (Van der Waerden)
4. ✅ **S(4)** - Already in original list (Boolean Schur)
5. ✅ **Twin Prime bounds** - Already in original list
6. ✅ **McKay Conjecture** - Already in original list
7. ✅ **ζ(5) Irrationality** - Already in original list
8. ✅ **Burnside B(2,5)** - Already in original list
9. ✅ **Inverse Galois M₂₃** - Already in original list
10. ✅ **Hadwiger-Nelson** - Already in original list
11. ✅ **Collatz** - Already in original list

**Conclusion:** The new interdisciplinary research has found **~54 NEW problems** beyond our original 14!

---

## NEXT STEPS

1. ✅ Consolidate all problems (DONE - this document)
2. ⏳ Verify top 30 problems are genuinely unsolved (web search)
3. ⏳ Filter to 20-25 highest-quality for GitHub issues
4. ⏳ Create detailed GitHub issues with all metadata
5. ⏳ Update project documentation

**Recommended Priority Order for Verification:**
1. Top Tier (7 problems with 30-45% success)
2. High-Value (14 problems with 20-30% success)
3. Medium-Value (11 problems with 15-20% success)
4. Select best from Lower-Priority and Gemini additions

---

## Document History

- **2025-12-11:** Initial consolidation from 7 Claude agents + Gemini + Grok
