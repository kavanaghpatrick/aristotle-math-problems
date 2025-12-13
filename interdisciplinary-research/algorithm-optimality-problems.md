# Algorithm Optimality Problems: Unsolved Questions in Specific Cases

**Focus**: Provable optimality questions for bounded, finite cases suitable for formal verification in Lean 4

**Date**: December 11, 2025

**Selection Criteria**:
- Published as open problem in peer-reviewed venue (2020-2025)
- Clear, finite formulation suitable for automated theorem proving
- NOT purely computational - must be mathematically provable
- Bounded/finite cases of larger problems
- Success probability 5-70% for Aristotle

---

## 1. Sorting Network Size Optimality for n=18, 19, 20

### Problem Statement

**For n ∈ {18, 19, 20}**: Determine the minimum number of comparators S(n) required to sort n inputs using a sorting network.

**Current Status**:
- **n=17**: Optimal depth proven (2024) ✓
- **n=18**: Improved networks found, optimality unknown
- **n=19**: Improved networks found, optimality unknown
- **n=20**: Improved networks found, optimality unknown

**Specific Question**: For each n ∈ {18, 19, 20}, prove that no sorting network exists with fewer than the currently known best number of comparators.

### Why Unsolved

Exhaustive search becomes computationally intractable for these sizes. The search space grows exponentially with network size, and proving optimality requires showing that no valid network exists below a certain size threshold. While improved upper bounds have been found recently, the lower bound proofs remain elusive.

### Interdisciplinary Connection

**Computer Science**: Sorting networks are fundamental to parallel computing architectures (GPUs, multicore processors). Optimal networks directly impact hardware design for sorting accelerators.

**Hardware Implementation**: Each comparator represents a physical gate with power consumption and latency. Minimizing comparators reduces circuit area and energy usage.

### Recent Status (2023-2025)

- **2024**: Researchers proved n=17 optimal for depth, solving a 50-year-old open problem
- **2024**: New networks discovered for n=17, 19, 20 with improved depth (fewer parallel steps)
- Size optimality (minimum total comparators) remains open for n ≥ 18

### Formalizability in Lean 4

**MEDIUM**

**Challenges**:
- Need to formalize sorting network semantics
- Verification requires checking all permutations (n!)
- Exhaustive search proof requires careful finiteness arguments

**Advantages**:
- Finite, discrete problem
- Can leverage Mathlib's combinatorics and finite types
- Similar to SAT-based proof techniques used in n=17 solution

### Success Probability Estimate

**n=18**: 35%
**n=19**: 25%
**n=20**: 15%

The probability decreases with n due to larger search space, but these are tractable finite problems that have seen recent progress.

### Why Good for Aristotle

1. **Bounded finite case** - unlike general sorting network theory
2. **Recent breakthrough** (n=17 solved in 2024) suggests techniques are mature
3. **Combinatorial nature** aligns with Lean's strengths in discrete math
4. **Clear verification criteria** - check all permutations get sorted
5. **Incremental approach** - can tackle n=18 first, then extend

### References

- [Constant-Depth Sorting Networks (ITCS 2023)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2023.43)
- [Towards Simpler Sorting Networks and Monotone Circuits (APPROX/RANDOM 2024)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX/RANDOM.2024.50)
- [An Answer to the Bose-Nelson Sorting Problem for 11 and 12 Channels](https://arxiv.org/pdf/2012.04400)
- [Proving 50-Year-Old Sorting Networks Optimal](https://jix.one/proving-50-year-old-sorting-networks-optimal-part-1/)

---

## 2. k-Server Conjecture for Small k

### Problem Statement

**k-Server Conjecture**: For any metric space M and k servers, there exists a deterministic online algorithm with competitive ratio exactly k.

**Known Results**:
- k=2: Competitive ratio is exactly 2 ✓
- Trees: Conjecture proven ✓
- k+1 points: Competitive ratio is exactly k ✓
- **k ≥ 3 on general metric spaces**: OPEN

**Specific Bounded Case**: Prove the k-server conjecture for k=3 on specific simple metric spaces (e.g., weighted stars with 5-7 vertices, specific grid graphs).

### Why Unsolved

The Work Function Algorithm (WFA) achieves competitive ratio 2k-1, but closing the gap to k has resisted decades of effort. The difficulty lies in proving both:
1. An algorithm achieves competitive ratio k (upper bound)
2. No algorithm can do better than k-1 (lower bound)

For k ≥ 3, the adversarial analysis becomes highly complex.

### Interdisciplinary Connection

**Distributed Systems**: Cache management, content delivery networks, robot coordination
**Cloud Computing**: Virtual machine migration across data centers
**Robotics**: Multi-robot task allocation and movement

The k-server problem abstracts fundamental resource allocation questions in computer systems.

### Recent Status (2023-2025)

- Work Function Algorithm remains best known with ratio 2k-1
- Specialized results for constrained metric spaces continue to appear
- No breakthrough on general k=3 case since 2000s results on k+2 points

### Formalizability in Lean 4

**HARD**

**Challenges**:
- Requires formalizing metric spaces, online algorithms, competitive analysis
- Adversarial game theory framework needed
- Amortized analysis and potential functions are complex

**Advantages**:
- For bounded metric spaces (fixed vertex count), becomes finite problem
- Can encode specific graph structures explicitly
- Mathlib has metric space infrastructure

### Success Probability Estimate

**General k=3**: <5% (too hard)
**k=3 on specific 5-vertex weighted star**: 20%
**k=3 on specific small grid (3×3)**: 15%

The key is choosing a sufficiently simple metric space where analysis is tractable.

### Why Good for Aristotle

1. **Bounded metric space** reduces to finite case
2. **Long-standing conjecture** with high impact if solved (even for special case)
3. **Algorithmic game theory** is growing area in formal verification
4. **Incremental value** - even partial results (specific metrics) are publishable

### References

- [k-Server Problem (Wikipedia)](https://en.wikipedia.org/wiki/K-server_problem)
- [The k-Server Problem (Koutsoupias, 2009)](https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/paper-kou09.pdf)
- [k-Server with Preferences Problem (arXiv 2022)](https://arxiv.org/abs/2205.11102)
- [Weighted k-Server Decomposition (arXiv 2024)](https://arxiv.org/html/2410.06485)

---

## 3. Frequency Moments F_k Space Lower Bounds (k ≥ 3)

### Problem Statement

**Frequency Moments**: For a data stream with mi occurrences of element i, the k-th frequency moment is Fk = Σᵢ mᵢᵏ.

**Known Bounds**:
- F0, F1, F2: Θ(log n) space (tight) ✓
- Fk for k ≥ 6: n^Ω(1) space required ✓
- **F3, F4, F5**: Gap between upper and lower bounds

**Specific Question**: Prove tight space lower bounds for (ε, δ)-approximating F3 and F4 in one-pass streaming algorithms.

### Why Unsolved

The communication complexity reductions that work for F2 and F6+ don't directly extend to the intermediate range. The transition from polylogarithmic (F2) to polynomial (F6+) space occurs somewhere in {F3, F4, F5}, but the exact thresholds are unclear.

### Interdisciplinary Connection

**Data Science**: Estimating statistical moments of massive data streams (network traffic, sensor data)
**Database Systems**: Query optimization, sampling strategies
**Machine Learning**: Online learning algorithms, sketch-based methods

Frequency moments are fundamental statistics computed on streaming data.

### Recent Status (2023-2025)

- **2024**: Recent paper on "Optimality of Frequency Moment Estimation" (arXiv 2411.02148) examines fundamental limits
- General framework shows Ω(1/ε²) bits needed for any k ≠ 1
- Specific tight bounds for F3, F4 remain open

### Formalizability in Lean 4

**VERY HARD**

**Challenges**:
- Communication complexity reductions are sophisticated
- Probabilistic arguments (randomized algorithms, (ε, δ)-approximation)
- Requires extensive probability theory formalization
- Information theory lower bounds

**Advantages**:
- Clean mathematical statement
- Builds on existing streaming algorithm theory
- Finite alphabet streaming can be modeled discretely

### Success Probability Estimate

**F3 tight bound**: 10%
**F4 tight bound**: 8%
**Simpler variant (deterministic lower bound)**: 15%

This is challenging due to heavy probabilistic machinery, but bounded cases might be more tractable.

### Why Good for Aristotle

1. **Fundamental problem** at intersection of algorithms, complexity, information theory
2. **High impact** - closes important gap in streaming complexity
3. **Finite formulation possible** for fixed alphabet size and stream length
4. **Connection to communication complexity** provides proof structure

### References

- [Space Complexity of Approximating Frequency Moments (AMS, 1996)](https://dl.acm.org/doi/10.1145/237814.237823)
- [Optimal Approximations of Frequency Moments (Indyk & Woodruff, 2005)](http://www.cs.cmu.edu/afs/cs/user/dwoodruf/www/iw05.pdf)
- [Optimal Space Lower Bounds for Frequency Moments (SODA 2004)](https://dl.acm.org/doi/10.5555/982792.982817)
- [Optimality of Frequency Moment Estimation (arXiv 2024)](https://arxiv.org/pdf/2411.02148)

---

## 4. Metric TSP: Closing the Inapproximability Gap

### Problem Statement

**Current Status**:
- **Upper bound**: 3/2 - ε approximation (ε > 10⁻³⁶) - Karlin, Klein, Gharan (2021)
- **Lower bound**: 123/122 ≈ 1.008 (assuming P ≠ NP) - Karpinski, Lampis, Schmied

**Gap**: Between 1.008 and 1.5

**Specific Question**: Either:
1. Prove metric TSP is NP-hard to approximate within ratio α for some α < 1.5, OR
2. Design a β-approximation algorithm for some β < 1.5 - ε

**The 4/3 Conjecture**: The integrality gap of the Held-Karp LP is exactly 4/3 (currently open).

### Why Unsolved

The gap between 1.008 hardness and 1.5 algorithm is enormous. Improving either bound requires fundamentally new techniques:
- **Hardness**: Current reductions from MAX-3SAT hit natural barriers
- **Algorithms**: Christofides (1.5) stood for 40+ years before 2021 improvement

The 4/3 conjecture is supported by evidence but lacks proof.

### Interdisciplinary Connection

**Operations Research**: Vehicle routing, logistics optimization
**Supply Chain**: Delivery route planning at scale
**VLSI Design**: Circuit board routing, component placement
**Robotics**: Path planning for manufacturing robots

TSP is the canonical optimization problem with massive real-world applications.

### Recent Status (2023-2025)

- **2021**: First improvement over Christofides in 40+ years (3/2 - ε)
- **2024**: Research on TSP with sharpened triangle inequality
- Held-Karp LP integrality gap proven 4/3 for special graph classes
- General 4/3 conjecture remains open

### Formalizability in Lean 4

**VERY HARD** (for new results)
**MEDIUM** (for formalizing existing 4/3 results on restricted classes)

**Challenges**:
- LP relaxations and integrality gaps require linear programming formalization
- Approximation algorithm analysis is complex
- Probabilistic rounding techniques

**Advantages**:
- For finite graphs, TSP is well-defined discrete problem
- Existing algorithms (Christofides, Held-Karp) can be formalized
- Combinatorial optimization has Mathlib support

### Success Probability Estimate

**4/3 conjecture for general graphs**: <5%
**4/3 conjecture for specific graph class**: 15%
**Formalize existing 4/3 result for subcubic graphs**: 40%

New breakthroughs are unlikely, but formalizing existing special cases is feasible.

### Why Good for Aristotle

1. **Specific bounded cases** (graph families) reduce complexity
2. **Extremely high impact** - TSP is canonical optimization problem
3. **Rich existing theory** provides proof structure
4. **Incremental value** - even formalizing known results advances verified optimization

### References

- [A (Slightly) Improved Approximation for Metric TSP (STOC 2021)](https://dl.acm.org/doi/10.1145/3406325.3451009)
- [New Inapproximability Bounds for TSP](https://link.springer.com/chapter/10.1007/978-3-642-45030-3_53)
- [Elusive Inapproximability of TSP (Guest Column)](https://www.researchgate.net/publication/262404040_Guest_column_the_elusive_inapproximability_of_the_TSP)
- [Improved Lower Bound on Approximability of Metric TSP](https://link.springer.com/chapter/10.1007/3-540-46541-3_32)

---

## 5. Online Bipartite Matching on Degree-Bounded Graphs

### Problem Statement

**General Online Bipartite Matching**:
- Classical bound: 1 - 1/e ≈ 0.632 competitive ratio (tight)
- Ranking algorithm is optimal

**Degree-Bounded Setting**: When online vertices have degree ≤ d, can we beat 1 - 1/e?

**Recent Result (2024)**: For d=2:
- **Fractional matching**: 0.75 competitive ratio is OPTIMAL ✓
- **Randomized integral matching**: ~0.717772 competitive ratio is OPTIMAL ✓

**Open Question**: For d=3, 4, 5, ..., what is the optimal competitive ratio?

### Why Unsolved

The d=2 case was only recently solved (November 2024). The analysis technique involves:
1. Designing algorithm achieving ratio α
2. Proving no algorithm can exceed α (adversarial lower bound)

For d ≥ 3, both parts become significantly more complex. The gap between fractional and integral matching also needs characterization.

### Interdisciplinary Connection

**Ad Allocation**: Online advertising platforms matching ads to users
**Ride Sharing**: Matching riders to drivers in real-time
**Job Markets**: Online platforms matching workers to tasks
**Resource Allocation**: Cloud computing resource assignment

Degree bounds model realistic capacity constraints.

### Recent Status (2023-2025)

- **Nov 2024**: Optimal ratios for d=2 proven (both fractional and integral)
- **2023**: Improved competitive ratios for degree-bounded graphs (arXiv 2306.13387)
- **2024**: Survey on online matching published in ACM SIGecom Exchanges
- d ≥ 3 remains completely open

### Formalizability in Lean 4

**HARD**

**Challenges**:
- Online algorithm framework with adversarial arrivals
- Probabilistic analysis (for randomized algorithms)
- Competitive ratio proofs require game-theoretic reasoning
- Bipartite graph matching formalization

**Advantages**:
- For bounded graphs (n vertices, degree d), finite state space
- Can encode specific adversarial strategies explicitly
- Graph matching has Mathlib support

### Success Probability Estimate

**d=3 fractional optimal ratio**: 25%
**d=3 integral optimal ratio**: 15%
**d=4 or d=5**: <10%

The d=3 case is natural next step after d=2 breakthrough.

### Why Good for Aristotle

1. **Fresh problem** - d=2 just solved in 2024, field is active
2. **Incremental from solved case** - techniques from d=2 may extend
3. **Bounded finite graphs** make verification tractable
4. **High practical relevance** - models real-world constraints
5. **Clear success criteria** - prove algorithm + adversarial lower bound

### References

- [Optimal Online Bipartite Matching in Degree-2 Graphs (arXiv Nov 2024)](https://arxiv.org/abs/2511.16025)
- [Improved Competitive Ratios for Degree Bounded Graphs (arXiv 2023)](https://arxiv.org/abs/2306.13387)
- [Online Matching: A Brief Survey (ACM SIGecom 2024)](https://www.sigecom.org/exchanges/volume_22/1/HUANG.pdf)
- [Online Bipartite Matching with Imperfect Advice (2024)](https://arxiv.org/pdf/2405.09784)

---

## 6. Circuit Complexity Lower Bounds for Explicit Functions

### Problem Statement

**Goal**: Prove super-polynomial lower bounds for explicit Boolean functions computed by small circuit classes.

**Recent Progress (2024-2025)**:
- **AC⁰ and GC⁰**: Majority requires depth-d circuits of size 2^Ω(n^(1/2(d-1)))
- **Noncommutative arithmetic**: Size Ω(n^(1+c)) for degree n polynomials (2025)
- **Monotone circuits**: Improved to Ω(n³/(log n)²) for explicit functions

**Open Questions**:
1. Can we prove 2^Ω(n) lower bound for monotone circuits computing CLIQUE(n, n/2)?
2. Can we improve depth-3 AC⁰ lower bounds beyond current techniques?
3. Are there explicit functions requiring noncommutative circuits of size n^2?

### Why Unsolved

Circuit lower bounds are notoriously difficult - they connect to P vs NP. However, restricted models (monotone, constant-depth, bounded fan-in) are more tractable. The barrier theorems (natural proofs, algebrization) don't apply to all circuit classes, leaving room for progress.

### Interdisciplinary Connection

**Hardware Design**: Understanding fundamental limits of circuit computation
**Cryptography**: Hardness assumptions rely on circuit complexity
**Computational Complexity**: P vs NP, circuit vs. Turing machine models
**Quantum Computing**: Classical circuit bounds inform quantum advantage

### Recent Status (2023-2025)

- **2024**: CCC 2024 featured multiple circuit complexity papers
- **2024**: "Towards Simpler Sorting Networks and Monotone Circuits" (RANDOM 2024)
- **2025**: New lower bounds for noncommutative circuits (ECCC 2025)
- **2024**: Maximum circuit lower bounds for exponential-time classes (ECCC 2024)

### Formalizability in Lean 4

**HARD to VERY HARD**

**Challenges**:
- Circuit semantics and evaluation
- Combinatorial arguments involving approximation methods
- Potential functions and complexity measures

**Advantages**:
- Circuits are discrete, finite objects
- For bounded depth/size, exhaustive arguments possible
- Boolean function theory has Mathlib foundations

### Success Probability Estimate

**2^Ω(n) monotone circuit bound for CLIQUE**: 12%
**Improved depth-3 AC⁰ bound**: 8%
**Specific noncommutative polynomial**: 15%
**Formalizing existing result (e.g., Razborov-Smolensky)**: 35%

New results are hard, but formalizing existing sophisticated proofs is valuable.

### Why Good for Aristotle

1. **Bounded circuit depth/size** creates finite verification space
2. **Fundamental problem** in computational complexity theory
3. **Combinatorial proof techniques** (e.g., approximation method) are well-structured
4. **Even formalization of known results** advances verified complexity theory
5. **Specific explicit functions** (CLIQUE, MAJORITY) have clean definitions

### References

- [New Circuit Lower Bounds via Range Avoidance (Simons, 2024)](https://simons.berkeley.edu/talks/lijie-chen-uc-berkeley-2024-04-18)
- [Maximum Circuit Lower Bounds (ECCC 2024)](https://eccc.weizmann.ac.il/report/2024/182/)
- [Noncommutative Arithmetic Circuit Bounds (ECCC 2025)](https://eccc.weizmann.ac.il/report/2025/038/)
- [39th Computational Complexity Conference (CCC 2024)](https://drops.dagstuhl.de/entities/volume/LIPIcs-volume-300)

---

## 7. Streaming Algorithm Lower Bounds: Longest Increasing Subsequence

### Problem Statement

**Longest Increasing Subsequence (LIS)**: Given a stream of n elements, approximate the length of the longest increasing subsequence.

**Known Results**:
- **Deterministic**: Best algorithms use Õ(√n) space
- **Randomized**: No better than deterministic (!)
- **Lower bound**: Ω(log n) space required (very weak)

**Open Question**: Prove a tight Ω(√n) space lower bound for randomized streaming algorithms approximating LIS to within factor 1.1.

**Recent Breakthrough (Dec 2024)**: Tight Ω(√n) space lower bound proven for white-box streaming algorithms (one week old result!).

### Why Unsolved

The LIS problem is one of the few remaining open problems in one-pass streaming. The difficulty is:
1. LIS has rich combinatorial structure (unlike frequency moments)
2. Deterministic and randomized algorithms have same complexity (unusual)
3. Communication complexity reductions don't directly apply

The white-box lower bound (algorithm must be explicit) is a major step, but black-box lower bound remains open.

### Interdisciplinary Connection

**Bioinformatics**: DNA sequence analysis, gene order comparison
**Data Analysis**: Trend detection in time series
**Algorithms**: Classic problem connecting to dynamic programming, patience sorting
**Complexity Theory**: Understanding power of streaming vs. offline computation

### Recent Status (2023-2025)

- **Dec 2024**: Ω(√n) white-box lower bound proven (ECCC 2025-197, one week old!)
- **2024**: Improved streaming algorithms for related problems (Klee's measure)
- **2023**: Asymmetric set-disjointness techniques applied to streaming (arXiv 2301.05658)

This is an extremely fresh result suggesting the field is ripe for further progress.

### Formalizability in Lean 4

**HARD**

**Challenges**:
- Streaming algorithm framework
- Communication complexity reductions
- White-box vs. black-box algorithm distinction
- Probabilistic arguments for randomized algorithms

**Advantages**:
- For bounded n and alphabet, becomes finite problem
- LIS is well-studied in algorithmic combinatorics
- Recent proof techniques may be well-structured
- Deterministic case might be more tractable

### Success Probability Estimate

**Extend white-box result to stronger models**: 20%
**Deterministic Ω(√n) lower bound with better constants**: 25%
**Formalize existing white-box proof**: 35%
**Related problem (e.g., longest common subsequence variant)**: 15%

The Dec 2024 breakthrough suggests this area is very active right now.

### Why Good for Aristotle

1. **Brand new result** (Dec 2024) - field is hot
2. **Clear mathematical structure** (LIS is well-defined combinatorially)
3. **Bounded finite formulation** possible
4. **High impact** - one of few remaining open streaming problems
5. **Builds on recent proof** - can extend or formalize cutting-edge work

### References

- [Tight Ω(√n) Space Lower Bound for White-Box LIS (ECCC 2025-197, Dec 2024)](https://eccc.weizmann.ac.il/report/2025/197/)
- [Streaming Lower Bounds and Asymmetric Set-Disjointness (arXiv 2023)](https://arxiv.org/abs/2301.05658)
- [New Algorithms and Lower Bounds for Streaming Tournaments (ESA 2024)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ESA.2024.60)
- [Optimal Multi-pass Lower Bounds for MST in Dynamic Streams (STOC 2024)](https://dl.acm.org/doi/abs/10.1145/3618260.3649755)

---

## Summary: Best Candidates for Aristotle

### Top 3 Recommendations (by success probability × impact)

1. **Sorting Networks (n=18)** - 35% success, bounded finite, recent breakthrough for n=17
2. **Online Matching (degree d=3)** - 25% success, fresh (d=2 just solved), clean structure
3. **LIS Streaming Lower Bound** - 25% success, brand new (Dec 2024), extends recent proof

### Formalization Opportunities (Valuable Even Without New Results)

1. **Metric TSP 4/3 for subcubic graphs** - 40% success, high impact
2. **Sorting Networks n=17 optimality proof** - 35% success, verify recent breakthrough
3. **Circuit complexity (Razborov-Smolensky)** - 35% success, fundamental result

### High-Risk, High-Reward

1. **k-Server for k=3 on simple metrics** - 20% success, but solves famous conjecture case
2. **Frequency Moments F₃ tight bound** - 10% success, closes important gap
3. **Monotone circuits 2^Ω(n) for CLIQUE** - 12% success, major complexity result

---

## Key Characteristics Across All Problems

✅ **Finite, bounded formulations** (essential for formal verification)
✅ **Recent research activity (2023-2025)** (field is active and techniques are mature)
✅ **Published in top venues** (STOC, FOCS, APPROX, CCC, ESA)
✅ **Provable, not empirical** (mathematical proofs, not simulations)
✅ **Interdisciplinary impact** (CS + applications in systems, networks, hardware)
✅ **Incremental value** (even partial results or special cases are publishable)

These problems represent the intersection of:
- **Algorithmic theory** (analysis of algorithms)
- **Complexity theory** (fundamental limits)
- **Combinatorics** (discrete structures)
- **Formal verification** (suitable for Lean 4)

All problems have concrete, bounded instances that could be attacked with automated theorem proving, while still connecting to deep open questions in computer science.
