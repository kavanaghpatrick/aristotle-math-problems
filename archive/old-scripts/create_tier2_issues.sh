#!/bin/bash
# Create Tier 2 (20-30%) High-Value Issues

cd /Users/patrickkavanagh/math

echo "Creating 12 high-value tier-2 issues..."

# Issue #30: Antiferromagnetic Potts Model
gh issue create \
  --repo kavanaghpatrick/aristotle-math-problems \
  --title "[STATISTICAL PHYSICS] Antiferromagnetic Potts Model - Partition Function Bounds (Success: 25-35%)" \
  --label "tier-2-high,statistical-physics,verified-unsolved" \
  --body "## Problem Statement

For q ≥ 5 colors and 4-regular graphs G, prove that the number of proper q-colorings is maximized by a disjoint union of complete bipartite graphs K_{4,4}.

## Current Status (2024)
- March 2024 paper by Perkins, Jenssen, and Roberts proves first case
- \"Almost proves\" d=4 case of Galvin-Tetali conjecture
- General case for all regular graphs remains open

## Why Unsolved
Requires understanding extremal structure of partition function over all graph topologies with bounded degree.

## Inter disciplinary Connection
- Computer Science: Approximation algorithms for counting problems
- Constraint Satisfaction: Hard instances of graph coloring
- Quantum Annealing: Optimization landscapes

## Formalizability: HARD

## Success Probability: 25-35%

## References
- https://math-mprf.org/journal/articles/id884/
- https://ar5iv.labs.arxiv.org/html/1801.07547" && echo "✅ #30 created"

# Issue #31: F-Matrix Solvability
gh issue create \
  --repo kavanaghpatrick/aristotle-math-problems \
  --title "[TOPOLOGICAL QUANTUM] F-Matrix Solvability for Fusion Rules (Success: 25-35%)" \
  --label "tier-2-high,topological-quantum,verified-unsolved" \
  --body "## Problem Statement

Given fusion rules F = {N_ab^c}, determine which finite sets of fusion multiplicities admit unique F-matrix solutions satisfying the pentagon equation.

For n ≤ 5 anyon types, decide whether solutions exist and count them up to SU(2) gauge equivalence.

## Current Status (2024-2025)
- SageMath pentagon equation solver exists but doesn't solve inverse problem
- 2024: Braiding Fibonacci anyons solved explicitly for n ≤ 8
- No general algorithm for determining solvability of arbitrary fusion rules

## Why Unsolved
Systematic procedure not fully characterized. Computational barriers from nested quantifiers and multi-variable polynomial equations under gauge constraints.

## Interdisciplinary Connection
- **Physics**: Determines which topological phases can exist
- **Quantum Computing**: F-matrices encode fusion algebra gates in topological quantum computers

## Formalizability: MEDIUM

## Success Probability: 25-35%

## References
- arXiv:2307.01892 (2023)
- JHEP Braiding Fibonacci anyons (2024)
- arXiv:2212.00831 (2022)" && echo "✅ #31 created"

# Issue #32: Type I Self-Dual Code
gh issue create \
  --repo kavanaghpatrick/aristotle-math-problems \
  --title "[CODING THEORY] Type I [56,28,12] Self-Dual Code Existence (Success: 25-30%)" \
  --label "tier-2-high,coding-theory,verified-unsolved" \
  --body "## Problem Statement

Does there exist a Type I binary self-dual code with parameters [56, 28, 12]?

**Type I codes**: Binary self-dual codes that are singly-even (all codewords have even weight, but not all divisible by 4).

A [56, 28, 12] code would have:
- Length: 56 bits
- Dimension: 28 (2²⁸ codewords)
- Minimum distance: 12 (can correct up to 5 errors)

## Current Status (2021-2024)
New necessary conditions established through:
- Neighborhood analysis of binary self-dual codes
- Weight enumerator constraints
- Reduced search space but no proof of existence/non-existence

## Why Unsolved
Finite but enormous search space (2²⁸ possible codes to check with constraints).

## Interdisciplinary Connection
- **Quantum Error Correction**: Self-dual codes relate to CSS quantum codes
- **Lattice Theory**: Connects to unimodular lattices via Construction A
- **Cryptography**: Applications in code-based cryptography

## Formalizability: MEDIUM-HARD

## Success Probability: 25-30%

## References
- arXiv:2110.09244 - The search for Type I codes
- arXiv:2206.05588 - Neighborhoods of binary self-dual codes
- ScienceDirect 2021 - New binary self-dual codes" && echo "✅ #32 created"

# Issue #33: Online Bipartite Matching
gh issue create \
  --repo kavanaghpatrick/aristotle-math-problems \
  --title "[ALGORITHMS] Online Bipartite Matching for d=3 Graphs (Success: 25%)" \
  --label "tier-2-high,algorithm-optimality,verified-unsolved" \
  --body "## Problem Statement

Determine the optimal competitive ratio for online bipartite matching on d-regular graphs when d=3.

**Background**: In online bipartite matching, one side of a bipartite graph is revealed vertex-by-vertex, and edges must be matched irrevocably as vertices arrive.

## Current Status (November 2024)
- d=2 just solved in November 2024
- Natural next incremental step
- General d remains open

## Why Unsolved
Requires new adversarial analysis techniques for d=3 case.

## Interdisciplinary Connection
- **Ad Allocation**: Real-time bidding systems
- **Ride-Sharing**: Driver-passenger matching algorithms
- **Resource Allocation**: Online matching markets

## Formalizability: MEDIUM-HARD

## Success Probability: 25%

## References
- November 2024 breakthrough for d=2
- Mehta et al. FOCS 2007 (original problem)" && echo "✅ #33 created"

# Issue #34: LIS Streaming Lower Bound
gh issue create \
  --repo kavanaghpatrick/aristotle-math-problems \
  --title "[ALGORITHMS] Longest Increasing Subsequence Streaming Lower Bound (Success: 25%)" \
  --label "tier-2-high,algorithm-optimality,verified-unsolved" \
  --body "## Problem Statement

Prove tight space lower bounds for computing the length of the longest increasing subsequence (LIS) in the streaming model.

**Known**: Ω(√n) lower bound proven December 2024 (brand new!)

**Goal**: Determine if Ω(√n) is tight or if stronger lower bounds exist.

## Current Status (December 2024)
- Ω(√n) bound just established
- Upper bound algorithms exist with O(√n log n) space
- Gap between upper and lower bounds remains

## Why Unsolved
Communication complexity reductions for LIS are subtle.

## Interdisciplinary Connection
- **Streaming Algorithms**: Fundamental problem in data streams
- **Data Structures**: Space-efficient sequence processing
- **Combinatorics**: Patience sorting and Robinson-Schensted correspondence

## Formalizability: HARD

## Success Probability: 25%

## References
- December 2024 Ω(√n) lower bound paper" && echo "✅ #34 created"

# Issue #35: PCR Space Lower Bounds
gh issue create \
  --repo kavanaghpatrick/aristotle-math-problems \
  --title "[SAT/CSP] Polynomial Calculus Resolution Space Lower Bounds (Success: 25%)" \
  --label "tier-2-high,sat-csp,verified-unsolved" \
  --body "## Problem Statement

Prove space lower bounds for Polynomial Calculus Resolution (PCR) on pebbling principles for specific graphs (n ≤ 15).

**PCR**: Proof system combining Polynomial Calculus with resolution-style reasoning.

## Current Status (2023-2024)
- Can verify for small pebbling formulas
- General characterization remains open
- Known techniques from resolution don't directly transfer

## Why Unsolved
PCR combines algebraic and logical reasoning, making space complexity analysis challenging.

## Interdisciplinary Connection
- **Automated Reasoning**: Memory requirements for SAT solvers
- **Proof Complexity**: Understanding power of algebraic proof systems
- **Constraint Satisfaction**: Space-time tradeoffs

## Formalizability: HARD

## Success Probability: 25%

## References
- ICALP 2024 PCR results
- Pebbling game literature" && echo "✅ #35 created"

# Issue #36: Lossless Bipartite Expanders
gh issue create \
  --repo kavanaghpatrick/aristotle-math-problems \
  --title "[EXPANDER GRAPHS] Lossless Bipartite Expanders - Unbalanced Settings (Success: 20-35%)" \
  --label "tier-2-high,expander-graphs,verified-unsolved" \
  --body "## Problem Statement

Construct explicit lossless bipartite expanders for unbalanced vertex sets (|L| ≠ |R|).

**Lossless expanders**: Every subset S ⊆ L satisfies |Γ(S)| ≥ |S| with minimal degree.

## Current Status (SODA 2024)
- Golowich solved balanced case (|L| = |R|) at SODA 2024
- Unbalanced case remains open
- Applications waiting for construction

## Why Unsolved
Explicit constructions require new spectral techniques for unbalanced graphs.

## Interdisciplinary Connection
- **Error-Correcting Codes**: LDPC code construction
- **Derandomization**: Explicit pseudorandom objects
- **Network Coding**: Capacity-achieving schemes

## Formalizability: HARD

## Success Probability: 20-35%

## References
- Golowich SODA 2024
- Guruswami-Umans-Vadhan expander survey" && echo "✅ #36 created"

# Issue #37: TEE Lower Bound
gh issue create \
  --repo kavanaghpatrick/aristotle-math-problems \
  --title "[TOPOLOGICAL QUANTUM] Topological Entanglement Entropy Lower Bound Characterization (Success: 20-30%)" \
  --label "tier-2-high,topological-quantum,verified-unsolved" \
  --body "## Problem Statement

**Theorem** (Kim et al., 2023): For any gapped topological state ρ on a 2D lattice:
TEE(ρ) ≥ log(D) where D is the total quantum dimension.

**Open**: Characterize when equality holds and provide tighter bounds for specific topological orders.

## Current Status (2023-2025)
- Universal lower bound proven in Phys. Rev. Lett. 131, 166601 (2023)
- Characterization of saturation conditions remains open
- Explicit calculations for specific anyonic models needed

## Why Unsolved
Requires deep understanding of entanglement structure in topological phases.

## Interdisciplinary Connection
- **Quantum Information**: Entanglement measures
- **Condensed Matter**: Topological order classification
- **Quantum Error Correction**: Code distance bounds

## Formalizability: MEDIUM-HARD

## Success Probability: 20-30%

## References
- Phys. Rev. Lett. 131, 166601 (2023)
- Kitaev-Preskill PRL 96, 110404 (2006)" && echo "✅ #37 created"

# Issue #38: Ingleton Inequality
gh issue create \
  --repo kavanaghpatrick/aristotle-math-problems \
  --title "[INFORMATION THEORY] Ingleton Inequality Maximum Violation (Success: 20-25%)" \
  --label "tier-2-high,information-theory,verified-unsolved" \
  --body "## Problem Statement

Determine the maximum violation δ_max of the Ingleton inequality for entropic polymatroids.

**Ingleton Inequality**: For four random variables A,B,C,D:
I(A:B) + I(C:D) + I(A,C:B,D) ≥ I(A,C:B) + I(A:B,D) + I(C:B,D) + I(A:D)

**Known**: Previous conjecture disproven; current best violation: δ = 0.0925000777

**Goal**: Find δ_max or prove current bound is optimal.

## Current Status (2023-2024)
- Systematic computational search underway
- Connection to network coding capacity regions
- Small improvements found but optimality unknown

## Why Unsolved
Search space of entropic regions is complex and high-dimensional.

## Interdisciplinary Connection
- **Network Coding**: Capacity region bounds
- **Information Theory**: Entropic polymatroid structure
- **Optimization**: Semidefinite programming bounds

## Formalizability: MEDIUM

## Success Probability: 20-25%

## References
- Dougherty et al. violated bound papers
- Yeung's Information Theory and Network Coding" && echo "✅ #38 created"

# Issue #39: Boolean Promise CSP
gh issue create \
  --repo kavanaghpatrick/aristotle-math-problems \
  --title "[SAT/CSP] Boolean Promise Constraint Satisfaction Dichotomy (Success: 20%)" \
  --label "tier-2-high,sat-csp,verified-unsolved" \
  --body "## Problem Statement

Prove a complexity dichotomy for Boolean Promise Constraint Satisfaction Problems (PCSPs).

**Background**: CSP dichotomy theorem solved in 2017 (Zhuk, Bulatov). PCSP extends CSP with promise constraints.

**Conjecture**: Every Boolean PCSP is either in P or NP-hard.

## Current Status (2023-2024)
- Many special cases resolved
- General Boolean case remains open
- Non-Boolean PCSP widely believed impossible to classify

## Why Unsolved
Promise structure adds significant complexity to algebraic dichotomy arguments.

## Interdisciplinary Connection
- **Approximation Algorithms**: Hardness of approximation
- **Learning Theory**: PAC learning complexity
- **Optimization**: Constraint programming

## Formalizability: MEDIUM-HARD

## Success Probability: 20%

## References
- Brakensiek-Guruswami STOC 2018
- PCSP survey papers (2022-2024)" && echo "✅ #39 created"

# Issue #40: Linear Programming Bound
gh issue create \
  --repo kavanaghpatrick/aristotle-math-problems \
  --title "[CODING THEORY] Linear Programming Bound Improvement for Binary Codes (Success: 18-28%)" \
  --label "tier-2-high,coding-theory,verified-unsolved" \
  --body "## Problem Statement

Improve the Linear Programming (LP) bound for binary codes in small cases (n ≤ 100, specific parameters).

**LP Bound**: Provides upper bounds on code size A(n,d) given length n and minimum distance d.

**Goal**: Find tighter bounds for specific (n,d) pairs where computational verification is feasible.

## Current Status (2020-2024)
- Computationally verified for n ≤ 100
- Best success/difficulty ratio among coding theory problems
- Incremental improvements possible with better LP techniques

## Why Unsolved
Finding optimal LP relaxations requires sophisticated optimization.

## Interdisciplinary Connection
- **Approximation Algorithms**: LP relaxation techniques
- **Combinatorial Optimization**: Sphere packing bounds
- **Quantum Error Correction**: Code parameter bounds

## Formalizability: MEDIUM

## Success Probability: 18-28%

## References
- Brouwer's code tables
- LP bound literature (Schrijver, etc.)" && echo "✅ #40 created"

# Issue #41: QAOA Depth-2
gh issue create \
  --repo kavanaghpatrick/aristotle-math-problems \
  --title "[QUANTUM COMPLEXITY] QAOA Depth-2 Optimality for MaxCut on 3-Regular Graphs (Success: 20%)" \
  --label "tier-2-high,quantum-complexity,verified-unsolved" \
  --body "## Problem Statement

**Conjecture**: Depth-2 Quantum Approximate Optimization Algorithm (QAOA) achieves approximation ratio α > 0.692 for MaxCut on 3-regular graphs.

**Current best**: α ≈ 0.6924 (Farhi et al.)

**Goal**: Prove optimal depth-2 performance or find better parameters.

## Current Status (2023-2024)
- Numerical optimization suggests α ≈ 0.6924 is optimal for depth-2
- Analytical proof lacking
- Higher depths harder to analyze

## Why Unsolved
QAOA landscape analysis is combinatorially complex even for small depths.

## Interdisciplinary Connection
- **Quantum Algorithms**: Near-term quantum computing
- **Optimization**: Approximation algorithm design
- **Statistical Physics**: Spin glass energy landscapes

## Formalizability: MEDIUM

## Success Probability: 20%

## References
- Farhi et al. original QAOA paper
- Wang et al. X + Arch 2024 depth-2 results" && echo "✅ #41 created"

echo ""
echo "✅ COMPLETE: Created 12 tier-2 high-value issues (#30-#41)"
