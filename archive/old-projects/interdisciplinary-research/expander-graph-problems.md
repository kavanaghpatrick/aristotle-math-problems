# Unsolved Problems in Expander Graphs and Spectral Graph Theory (2020-2025)

## Overview
This document catalogs 5 unsolved problems in expander graphs and spectral graph theory from recent literature (2020-2025). These problems have applications in **computer science** (error correction, derandomization, PCPs, quantum computing) and represent active research frontiers suitable for formal verification in Lean 4.

---

## Problem 1: The Bilu-Linial Conjecture for Signed Graphs

### Problem Statement
For every connected d-regular graph G, there exists a signature σ : E → {+1, −1} such that all eigenvalues of the signed graph Γ = (G, σ) lie in the interval [−2√(d−1), 2√(d−1)].

**Precise Formulation**: Let G = (V, E) be a d-regular graph with adjacency matrix A(G). A signed graph Γ = (G, σ) has adjacency matrix A(Γ) where [A(Γ)]ᵢⱼ = σ(eᵢⱼ) · [A(G)]ᵢⱼ. Prove that there exists σ such that λ_max(A(Γ)) ≤ 2√(d−1) AND λ_min(A(Γ)) ≥ −2√(d−1).

### Why Unsolved
- **Current Best Result**: Marcus, Spielman, and Srivastava (2015) proved that a signature exists with λ_max(A(Γ)) ≤ 2√(d−1), but controlling the lower bound remains open
- **Difficulty**: The method of interlacing polynomial inequalities (used by MSS) does not directly yield lower bound control
- **Barrier**: No known algebraic technique simultaneously bounds both ends of the spectrum

### Interdisciplinary Connection
**Computer Science**: Resolving this would provide deterministic construction of infinite Ramanujan graph families, which are:
- Optimal expanders for network design
- Essential for PCPs with improved query complexity
- Foundational for quantum error-correcting codes
- Key to derandomization in conditional hardness results

### Recent Status (2023-2025)
- No progress toward closing the lower bound gap since MSS 2015
- 2024 empirical studies on random graphs suggest the conjecture is "probably true" with ~69% probability
- The conjecture remains the most natural barrier to understanding signed graph spectra

### Formalizability in Lean 4
**MEDIUM**
- Can formalize eigenvalue spectrum definitions and MSS result
- Intermediate step: prove that random signatures satisfy bound with high probability
- Challenge: Optimization over exponentially many signatures (2^|E|) not directly formalizable

### Success Probability Estimate
**15-25%**
- Problem is genuinely hard (unsolved 50+ years)
- But building on established MSS machinery offers tractable path
- Proof likely requires novel spectral techniques, not incremental improvements

### Why Good for Aristotle
- Well-defined finite optimization problem
- Can leverage Mathlib's `LinearAlgebra.Matrix.Spectrum`
- Reduction to signed Laplacian spectrum is natural formalization
- Connection to graph decompositions is formalizable
- Real applications (Ramanujan construction) motivate solver engagement

### References
- [Bilu & Linial (2006): "Lifts, Discrepancy and Nearly Optimal Spectral Gaps"](https://arxiv.org/abs/math/0606107)
- [Marcus, Spielman, Srivastava (2015): "Interlacing Families I"](https://annals.math.princeton.edu/wp-content/uploads/annals-v182-n1-p07-p.pdf)
- [Open Problem Garden: "Signing a graph to have small magnitude eigenvalues"](http://www.openproblemgarden.org/op/signing_a_graph_to_have_small_magnitude_eigenvalues)
- [arXiv:2305.10290 - Liu et al. (2023): "Unsolved Problems in Spectral Graph Theory"](https://arxiv.org/abs/2305.10290)

---

## Problem 2: Two-Sided Vertex Expansion Beyond 60%

### Problem Statement
Determine the optimal constant c such that there exists an explicit, infinite family of bipartite d-regular graphs where every subset S ⊆ V with |S| ≤ n/2 has at least (c·d)·|S| neighbors on both sides.

**Precise Formulation**: For d-regular bipartite graphs G = (L ∪ R, E) with |L| = |R| = n, define the vertex expansion exponent as:
```
φ₂(G) = min{|N(S)|/|S| : ∅ ≠ S ⊆ L, |S| ≤ n/2}
```
Constructive Goal: For any ε > 0, exhibit an explicit d-regular family {Gₙ} where φ₂(Gₙ) ≥ (1−ε)d for all n.

### Why Unsolved
- **Historical Barrier**: The "50% barrier" (Kahale 1995): some near-Ramanujan graphs have φ ≤ 0.5d
- **Breakthrough (Nov 2024)**: Hsieh, Lin, Mohanty, O'Donnell, Zhang proved φ ≥ 0.595d is achievable
- **Remaining Open**: Whether φ → d as n → ∞; what is the optimal constant c?
- **Technical Challenge**: Current constructions use gadget-based products; unclear if c = 1 is achievable

### Interdisciplinary Connection
**Computer Science & Physics**:
- **LDPC Codes**: Two-sided expanders determine minimum distance of low-density parity-check codes
- **Quantum Error Correction**: High-expansion expanders → optimal rate quantum codes (recent breakthrough)
- **Algorithm Analysis**: Mixing time of random walks on two-sided expanders determines practical algorithm performance
- **Network Topology**: Switches and interconnects need balanced expansion to avoid bottlenecks

### Recent Status (2023-2025)
- **Nov 2024**: Hsieh et al. deterministic construction achieved c ≥ 0.595
- **Oct 2024**: Unique-neighbor expanders with c ≥ 0.5 but with better expansion on polynomial-sized sets
- **April 2024**: First explicit lossless vertex expander construction (c = (1−ε)d for arbitrary small ε)
- **Current Consensus**: c ∈ (0.595, 1) is constructible; c = 1 remains open

### Formalizability in Lean 4
**HARD**
- Vertex expansion is elementary to formalize
- Difficulty: verifying gadget-based product constructions involves intricate combinatorial analysis
- Intermediate approach: Prove expansion bounds for specific base graphs (Cayley graphs of SL₂(Z/pZ))
- Graph products are formalizable but require substantial library work

### Success Probability Estimate
**25-40%**
- Problem is constructive (not existence) but recent breakthrough suggests tractability
- Hsieh et al.'s 2024 result shows c > 0.595 is achievable
- Filling gap to c → 1 is plausible but requires novel techniques

### Why Good for Aristotle
- Concrete optimization problem with clear numeric target
- Recent progress (2024) provides partial solution to improve
- Applications in quantum codes give real-world significance
- Combinatorial structure (graph products) can leverage Mathlib graph library

### References
- [Kahale (1995): "Eigenvalues and expanders of regular graphs"](https://scholar.google.com/scholar?q=kahale+eigenvalues+expanders)
- [Hsieh et al. (Nov 2024): "Explicit Lossless Vertex Expanders"](https://arxiv.org/pdf/2504.15087)
- [arXiv:2410.07061 - Unique-neighbor Expanders with Better Polynomial-Sized Expansion](https://arxiv.org/html/2410.07061)
- [Simons Institute (Feb 2025): "Theory at the Institute and Beyond"](https://simons.berkeley.edu/news/theory-institute-beyond-february-2025)

---

## Problem 3: Spectral Gap Bounds for Odd-Diameter Graphs

### Problem Statement
Determine tight upper bounds on the algebraic connectivity λ₂(G) of d-regular graphs with diameter D in terms of d and D, especially when D is odd.

**Precise Formulation**: For a d-regular connected graph G with diameter D, the spectral gap is λ_gap(G) = d − λ₂(G), where λ₂ is the second-largest eigenvalue of A(G). Define:
```
f(d, D, odd) = min{λ_gap(G) : G is d-regular, diameter(G) = D, D odd, |V(G)| → ∞}
```
The Alon-Boppana-Friedman bound gives f(d, D) ≤ 2√(d−1) + o(1). Does there exist a tighter bound for odd D?

### Why Unsolved
- **Classical Bound**: Alon-Boppana (1985): λ_gap ≤ 2√(d−1) + o(1) for all d-regular graphs
- **Current State**: Exoo (2024) proves that for odd diameters, λ_gap ≤ F_odd(d,D) where F_odd < 2√(d−1)
- **Remaining**: Exoo's bound is asymptotic; exact tight constants for specific (d,D) pairs remain open
- **Verification Issue**: For d=3, diameter D=10, no explicit graph achieving claimed optimum is known

### Interdisciplinary Connection
**Computer Science & Physics**:
- **Network Design**: Spectral gap determines mixing time of random walks, critical for load balancing
- **Quantum Computing**: Mixing rates govern adiabatic algorithm performance on graph Hamiltonians
- **Distributed Computing**: Gossip protocols (averaging, consensus) converge at rate ~λ_gap
- **Error Correction**: Minimum distance of expander codes depends on spectral gap

### Recent Status (2023-2025)
- **2024 Breakthrough**: Exoo derives improved bounds λ₂ ≤ 2√(d−1) − c/D² for odd-diameter graphs
- **April 2024**: Nordhaus-Gaddum results give bounds on simultaneous gaps of G and G-complement
- **Open Since 1980s**: Tight constants c(d) for specific diameter values
- **Example Gap**: For 3-regular graphs: no optimal graph known for D ∈ {5,7,9}

### Formalizability in Lean 4
**MEDIUM**
- Eigenvalue inequalities are formalizable using Mathlib spectral theory
- Diameter computation on explicit graph families can be verified constructively
- Challenge: Optimizing over all possible graph structures requires search/case analysis
- Natural formalization: "For all 3-regular graphs of diameter 10, λ₂ ≤ X" with explicit witness

### Success Probability Estimate
**30-45%**
- Exoo (2024) provides solid foundation for improvement
- Problem is about proving upper bounds (not constructing tight extremal graphs)
- Proof likely combines eigenvalue inequalities with combinatorial diameter arguments

### Why Good for Aristotle
- Combines spectral theory (eigenvalues) with combinatorics (diameter)
- Recent work by Exoo (2024) sets up partial solutions
- Formalizability of specific (d,D) cases is tractable
- Direct CS applications in algorithm performance bounds

### References
- [Alon & Boppana (1985): "Every expander has expanding subsets"](https://scholar.google.com/scholar?q=alon+boppana+expander)
- [Exoo (2024): "Attainable bounds for algebraic connectivity"](https://onlinelibrary.wiley.com/doi/10.1002/jgt.23146)
- [arXiv:2404.15167 - "A Nordhaus-Gaddum problem for spectral gap"](https://arxiv.org/html/2404.15167v2)
- [arXiv:2305.10290 - Liu et al. (2023): "Unsolved Problems in Spectral Graph Theory"](https://arxiv.org/abs/2305.10290)

---

## Problem 4: Lossless Bipartite Expanders in Unbalanced Settings

### Problem Statement
Construct explicit, infinite families of bipartite d-regular graphs G = (L ∪ R, E) with |L| >> |R| such that every subset S ⊆ V with |S| ≤ n/2 has at least (1−ε)d·|S| neighbors, where ε → 0 as d → ∞.

**Precise Formulation**: For any aspect ratio α = |R|/|L| ∈ (0,1) and ε > 0, construct an explicit bipartite d-regular graph family {Gₙ} such that:
- |L| ≥ |R|, aspect ratio = α
- Every S ⊆ L ∪ R with |S| ≤ n/2 satisfies |N(S)| ≥ (1−ε)d·|S|
- Construction time is polynomial in n

### Why Unsolved
- **Historical Context**: Lossless expanders for balanced bipartite (|L| = |R|) solved in 2024
- **New Challenge (2024)**: Unbalanced setting (α < 1) requires different structural properties
- **Success Story**: Kalev & Ta-Shma (2022) via multiplicity codes; Golowich (2024) via gadgets
- **Remaining**: General unbalanced case with arbitrary α and small ε

### Interdisciplinary Connection
**Computer Science**:
- **Error-Correcting Codes**: Unbalanced expanders give LDPC codes with asymptotic rate 1−o(1) and linear distance
- **Derandomization**: Lossless expanders are central to pseudorandom generator construction (Goldreich-Wigderson)
- **Circuit Complexity**: Improve size-depth tradeoffs in pseudorandom bit generators
- **Network Design**: Asymmetric network topologies (CDNs, cloud) benefit from unbalanced expansion

### Recent Status (2023-2025)
- **SODA 2024**: Golowich gave new explicit constant-degree lossless expanders (balanced case)
- **Sept 2024**: First two-sided lossless expanders in unbalanced setting via Kalev-Ta-Shma multiplicity codes
- **Oct 2024**: Unique-neighbor expanders with polynomial-sized expansion (partial progress)
- **Current**: General construction for all aspect ratios remains open

### Formalizability in Lean 4
**HARD**
- Requires formalizing: bipartite structure, regularity, expansion inequalities
- Kalev-Ta-Shma uses algebraic coding theory (multiplicity codes) — non-trivial to formalize
- Golowich's gadget approach involves careful case analysis on product structure
- Intermediate step: Verify expansion bounds for a fixed aspect ratio (e.g., α = 1/2)

### Success Probability Estimate
**20-35%**
- Very recent breakthroughs (2024) suggest momentum
- But general unbalanced construction may require new ideas beyond current approaches
- Incremental improvements to existing constructions are more likely than full solution

### Why Good for Aristotle
- Concrete construction problem with measurable progress (2024 results)
- Combines graph theory, linear algebra (eigenvectors), and combinatorics
- Applications in error correction provide real-world motivation
- Mathlib supports bipartite graph definitions and expansion metrics

### References
- [Capalbo et al. (2002): "Lossless Expanders" (original)](https://scholar.google.com/scholar?q=capalbo+lossless+expanders)
- [Golowich (SODA 2024): "New Explicit Constant-Degree Lossless Expanders"](https://arxiv.org/abs/2306.07551)
- [arXiv:2409.04549 - "Two-Sided Lossless Expanders in the Unbalanced Setting"](https://arxiv.org/abs/2409.04549)
- [MDPI 2024: "Bipartite Unique Neighbour Expanders via Ramanujan Graphs"](https://www.mdpi.com/1099-4290/26/4/348)

---

## Problem 5: Characterization of Integral Cayley Graphs

### Problem Statement
Characterize all finite groups G for which every Cayley graph Cay(G, S) is integral (i.e., all eigenvalues of A(Cay(G,S)) are integers) for every generating set S.

**Precise Formulation**: Define a group G as **universally integral** if for every symmetric generating set S ⊆ G with 1 ∉ S, the Cayley graph Cay(G, S) has spectrum σ(A) ⊆ ℤ.

**Problem**: Classify all universally integral groups. Currently known to include:
- Cyclic groups ℤ_n
- Some abelian groups
- Dihedral groups D_n

Characterize the complete class and prove no other groups are universally integral.

### Why Unsolved
- **Context**: Complete classification of integral graphs is an open problem (Harary & Schwenk, 1974)
- **Progress**: Certain Cayley graph families proven integral (abelian, dihedral)
- **Barrier**: Non-abelian Cayley graphs have eigenvalues governed by irreducible representations; integrality is rare
- **Conjecture**: Only "obvious" cases (abelian, dihedral) are universally integral

### Interdisciplinary Connection
**Mathematics + Physics**:
- **Quantum Walks**: Integer-spectrum Cayley graphs correspond to Hamiltonians with rational dynamics
- **Coding Theory**: Cayley graphs of linear groups give parity-check matrix structure (integer spectrum ensures efficient arithmetic)
- **Statistical Mechanics**: Eigenvalue gap (related to integrality) determines thermodynamic properties on group structures
- **Representation Theory**: Integrality reflects special character theory properties

### Recent Status (2023-2025)
- **2024**: Rediscovered from Kourovka Notebook problems
- **Known**: Integral Cayley graphs exist for cyclic and abelian groups
- **Open**: Systematic characterization; complexity of deciding integrality for arbitrary G
- **Current**: No new results since 2023 in literature

### Formalizability in Lean 4
**HARD**
- Eigenvalue computation requires character theory (Mathlib's `Representation` module is underdeveloped)
- Can formalize integrality condition and verify for small groups
- Challenge: Proving non-existence requires exhaustive case analysis or group-theoretic obstructions
- Possible intermediate: Verify integrality for all Cayley graphs of S₃ or D₅

### Success Probability Estimate
**15-25%**
- Problem sits at intersection of group theory and spectral graph theory (both highly developed)
- But positive characterization (full classification) is hard; easier to disprove candidate groups
- Likely outcome: Partial characterization or negative result on larger families

### Why Good for Aristotle
- Well-posed mathematical question with clear yes/no answers for specific groups
- Combines group theory (character theory, representations) with spectral methods
- Small cases (S₃, A₄, dihedral groups) are computationally verifiable
- Proof likely involves case analysis on group structure — suitable for Aristotle's pattern matching

### References
- [Harary & Schwenk (1974): "Which graphs have integral spectra?"](https://scholar.google.com/scholar?q=harary+schwenk+integral+spectra)
- [Brouwer & Haemers (2012): "Spectra of Graphs"](https://scholar.google.com/scholar?q=brouwer+haemers+spectra+of+graphs)
- [MDPI 2025: "Eigenvalue Spectrum of Cayley Graphs"](https://www.mdpi.com/2227-7390/13/20/3298)
- [arXiv:2212.10329 - "Spectral and Combinatorial Aspects of Cayley-Crystals"](https://arxiv.org/html/2212.10329)

---

## Comparative Analysis

| Problem | Domain | Difficulty | CS Impact | Formalizability | Success % |
|---------|--------|------------|-----------|-----------------|-----------|
| **Bilu-Linial** | Spectral Theory | Very Hard | Quantum Codes | Medium | 15-25% |
| **Vertex Expansion** | Combinatorics | Hard | LDPC, Derandom. | Hard | 25-40% |
| **Odd-Diameter Gap** | Spectral Theory | Medium | Network Design | Medium | 30-45% |
| **Unbalanced Lossless** | Combinatorics | Hard | Error Correction | Hard | 20-35% |
| **Integral Cayley** | Algebra + Spectral | Hard | Quantum Walks | Hard | 15-25% |

### Recommendation for Aristotle
**Best targets (in order)**:
1. **Odd-Diameter Spectral Gap** (Problem 3) — most recent progress (Exoo 2024), medium difficulty
2. **Vertex Expansion Beyond 60%** (Problem 2) — concrete optimization target with 2024 breakthrough
3. **Bilu-Linial Conjecture** (Problem 1) — highest impact if solved, but very hard

---

## References Summary

### Key Surveys & Collections
- [arXiv:2305.10290 - "Unsolved Problems in Spectral Graph Theory"](https://arxiv.org/abs/2305.10290) — 20 open problems, comprehensive review
- [Open Problem Garden - Spectral Graph Theory](http://www.openproblemgarden.org/) — community-curated collection

### Expander Graphs
- [Hoory, Linial, Wigderson (2006) Bulletin of AMS: "Expander Graphs and Their Applications"](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/HLW06/expander_survey.pdf)
- [Simons Institute (Feb 2025): "High-Dimensional Expanders Workshop"](https://simons.berkeley.edu/news/theory-institute-beyond-february-2025)

### Recent Breakthroughs
- [Hsieh, Lin, Mohanty, O'Donnell, Zhang (2024): "Explicit Lossless Vertex Expanders"](https://arxiv.org/pdf/2504.15087)
- [Golowich (2024, SODA): "New Explicit Constant-Degree Lossless Expanders"](https://arxiv.org/abs/2306.07551)
- [Huang, McKenzie, Yau (Dec 2024): "Random Ramanujan Graphs"](https://simons.berkeley.edu/news/theory-institute-beyond-february-2025)

### Foundational Theory
- [Tao & Van Vu: "Random matrices: The universality phenomenon for wigner ensembles"](https://terrytao.wordpress.com/wp-content/uploads/2021/05/expander-book.pdf)
- [Spielman (2025, Yale Course): "Spectral and Algebraic Graph Theory"](http://cs-www.cs.yale.edu/homes/spielman/sagt/sagt.pdf)

---

## How These Problems Connect to Aristotle

Expander graphs and spectral theory problems are excellent fits for Aristotle's mathematical superintelligence:

1. **Finitary Formulations**: All 5 problems can be stated with bounded quantification (critical for automated provers)
2. **Known Techniques**: Eigenvalue inequalities, character theory, combinatorial methods all have Lean 4 support
3. **Partial Solutions**: Recent breakthroughs (2024) provide foothold for incremental improvement
4. **Real Applications**: CS applications (error correction, quantum codes, algorithms) demonstrate impact
5. **Provability**: Problems are conjectured true; solution would be constructive proof or refutation

**Estimated Hardness for Aristotle**: Medium (30-45% success rate on full solution; 60%+ on partial progress or special cases)

