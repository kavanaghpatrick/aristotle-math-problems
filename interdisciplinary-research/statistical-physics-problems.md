# Unsolved Mathematical Conjectures from Statistical Physics and Condensed Matter Theory

**Research Period**: 2020-2025
**Focus**: Problems with finite formulations suitable for formal proof in Lean 4
**Date**: December 11, 2025

---

## Problem 1: Site Percolation Threshold on Square Lattice

**Problem Statement**: Determine the exact analytical value of the critical threshold p_c for site percolation on the two-dimensional square lattice Z^2.

**Current Status**:
- Bond percolation on square lattice: p_c = 1/2 (exact, proven)
- Site percolation on square lattice: p_c ≈ 0.59274621 ± 0.00000013 (numerical only)
- No analytical derivation exists despite decades of research

**Why Unsolved**: While bond percolation has an exact solution via duality arguments, site percolation lacks the symmetry properties that make bond percolation tractable. The problem requires fundamentally different techniques.

**Interdisciplinary Connection**:
- Material science: models network connectivity in composite materials
- Epidemiology: disease spread through populations
- Physics: conductivity transitions in disordered media

**Recent Status (2023-2025)**:
- 2025 work estimated 64 percolation thresholds for extended neighborhoods on square lattice
- Power-law dependence observed: p_c ~ (effective coordination number)^(-1/2)
- Cardy's formula provides crossing probabilities for rectangles (conformal invariance)

**Formalizability in Lean 4**: MEDIUM
- Discrete probability theory available in Mathlib
- Graph theory infrastructure exists
- Requires formalization of percolation cluster definitions
- Numerical estimates provide guidance

**Success Probability Estimate**: 10-15%

**Why Good for Aristotle**:
- Well-defined finite lattice approximations
- Strong numerical evidence for target value
- Clear connection to graph connectivity (discrete mathematics)
- Bounded computational verification possible
- Physics intuition from conformal field theory

**References**:
- [Lower Limit of Percolation Threshold on Square Lattice](https://www.mdpi.com/1099-4300/27/4/361) (2025)
- [Percolation threshold Wikipedia](https://en.wikipedia.org/wiki/Percolation_threshold)

---

## Problem 2: Non-uniqueness of Ising Phase Transitions on Tree-like Graphs

**Problem Statement**: For which classes of tree-like graphs G does the Ising model exhibit non-unique phase transitions? Specifically, characterize the graphs where connection probabilities fail to be monotone in inverse temperature β.

**Current Status**:
- A 2024-2025 construction shows existence of graphs with non-unique phase transitions
- Loop O(1) model and single random current exhibit non-monotonicity on specific tree-like structures
- General characterization remains open

**Why Unsolved**: The interaction between graph topology (tree-like structure with cycles) and thermodynamic properties creates complex behavior not captured by classical mean-field or infinite-tree results.

**Interdisciplinary Connection**:
- Network theory: information propagation on social networks
- Quantum computing: quantum spin chains on irregular topologies
- Neuroscience: neural network dynamics with tree-like architecture

**Recent Status (2023-2025)**:
- October 2024 arXiv paper by Taggi et al. proves non-uniqueness for specific graph families
- Challenges traditional monotonicity assumptions
- Opens new questions about phase transition classification on finite graphs

**Formalizability in Lean 4**: MEDIUM-HARD
- Requires formalization of Ising model partition function
- Graph theory available but tree-like graphs need careful definition
- Monotonicity proofs are combinatorially tractable
- Connection probabilities require probability theory formalization

**Success Probability Estimate**: 20-30% (for specific finite cases)

**Why Good for Aristotle**:
- Finite graph instances can be studied explicitly
- Combinatorial characterization likely exists
- Recent progress provides concrete examples
- Bridge between combinatorics and statistical mechanics

**References**:
- [Non-uniqueness of phase transitions for Ising model on tree-like graphs](https://arxiv.org/abs/2410.22061) (2024)
- [arXiv HTML version](https://arxiv.org/html/2410.22061)

---

## Problem 3: Antiferromagnetic Potts Model - Tight Bounds on Partition Function

**Problem Statement**: For q ≥ 5 colors and 4-regular graphs G, prove that the number of proper q-colorings is maximized by a disjoint union of complete bipartite graphs K_{4,4}.

**Current Status**:
- March 2024 paper by Perkins, Jenssen, and Roberts proves first case
- "Almost proves" d=4 case of Galvin-Tetali conjecture
- General case for all regular graphs remains open
- 2023 paper proves uniqueness of Gibbs measure for 4-state model on (d+1)-regular trees when d ≥ 4

**Why Unsolved**: Requires understanding extremal structure of partition function over all graph topologies with bounded degree. The interplay between chromatic number, degree constraints, and thermodynamic properties is subtle.

**Interdisciplinary Connection**:
- Theoretical computer science: approximation algorithms for counting problems
- Constraint satisfaction: hard instances of graph coloring
- Quantum annealing: optimization landscapes for combinatorial problems

**Recent Status (2023-2025)**:
- Bencs and coauthors (2023+) confirm conjecture for q ≥ 5 when d is large
- Active research connecting chromatic polynomials to antiferromagnetic Potts zeros
- Lee-Yang zeros for Potts model on Cayley trees under investigation (2025)

**Formalizability in Lean 4**: MEDIUM
- Graph coloring well-formalized in Mathlib
- Partition function can be expressed as sum over colorings
- Extremal graph theory infrastructure exists
- Finite instances verifiable

**Success Probability Estimate**: 25-35% (for d=4 case)

**Why Good for Aristotle**:
- Purely combinatorial problem at heart
- Finite verification possible for small regular graphs
- Strong connection to classical graph coloring
- Recent progress provides proof strategies
- Clear extremal structure (K_{4,4} maximizers)

**References**:
- [Uniqueness of Gibbs measure for 4-state antiferromagnetic Potts](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/0EE86171BCA21ABE510C8CE98C733C41/S0963548322000207a.pdf) (2023)
- [Personal List of Unsolved Problems - Antiferromagnetic Potts](https://math-mprf.org/journal/articles/id884/)
- [Counting proper colourings via Potts model](https://ar5iv.labs.arxiv.org/html/1801.07547)

---

## Problem 4: Chromatic Polynomial Zeros for Series-Parallel Graphs

**Problem Statement**: Characterize the maximal region U in the complex plane such that U \ {1} contains no zeros of chromatic polynomials of series-parallel graphs. In particular, determine if there exists a uniform bound on Re(q) for zeros over all series-parallel graphs with bounded maximum degree.

**Current Status**:
- 2023 work by Bencs, Huijben, and Regts disproved Sokal's conjecture
- For each Δ sufficiently large, there exist series-parallel graphs with degree ≤ Δ having zeros with Re(q) > Δ
- Proved: chromatic zeros are dense in the half-plane Re(q) > 3/2
- Proved: exists region U containing (0, 32/27) where U \ {1} has no zeros

**Why Unsolved**: The distribution of chromatic zeros in the complex plane connects to phase transitions of antiferromagnetic Potts model. The series-parallel graph class is rich enough to exhibit complex behavior but structured enough to hope for characterization.

**Interdisciplinary Connection**:
- Complex analysis: zero distribution of polynomials with combinatorial meaning
- Statistical physics: antiferromagnetic Potts model phase transitions
- Computational complexity: approximation algorithms for chromatic polynomial

**Recent Status (2023-2025)**:
- July 2023 paper resolved long-standing Sokal conjecture negatively
- Established zero-free regions and density results
- Connection to Rogers-Ramanujan identities and modular forms explored (2024)

**Formalizability in Lean 4**: MEDIUM-HARD
- Chromatic polynomial definition available
- Series-parallel graphs need formalization
- Complex analysis for zeros requires significant infrastructure
- Finite instances can be verified computationally

**Success Probability Estimate**: 15-25%

**Why Good for Aristotle**:
- Combines combinatorics (graphs) with analysis (polynomial zeros)
- Series-parallel graphs have nice recursive structure
- Finite verification for small cases
- Recent negative result suggests boundary cases might be provable
- Zero-free regions have explicit descriptions

**References**:
- [On the location of chromatic zeros of series-parallel graphs](https://arxiv.org/abs/2204.10038) (2023)
- [Electronic Journal version](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v30i3p2)

---

## Problem 5: Kac-Ward Determinant Extension to Non-Planar Graphs

**Problem Statement**: The Kac-Ward formula expresses the Ising model partition function on a planar graph as a determinant. For a graph G embeddable on a surface of genus g, the partition function can be computed from 2^(2g) determinants. Conjecture: Find an explicit formula relating these determinants to topological invariants of the embedded graph.

**Current Status**:
- Planar case (g=0): Rigorously proved (1999, after Kac-Ward 1952)
- 2024 work provides streamlined derivation and extends to order-disorder correlators
- For critical isoradial graphs (g=0 or g=1): determinants satisfy generalized Kramers-Wannier duality
- Higher genus g ≥ 2: No explicit formula or complete understanding

**Why Unsolved**: The topological complexity increases exponentially with genus. Understanding how the 2^(2g) determinants combine to give the partition function requires deep connections between statistical mechanics and algebraic topology.

**Interdisciplinary Connection**:
- Topology: Riemann surface theory, covering spaces
- Quantum field theory: Conformal field theory on higher genus surfaces
- Algebraic geometry: theta functions and modular forms

**Recent Status (2023-2025)**:
- March 2024 publication extends Kac-Ward to non-planar interactions on Z^2
- Uses Bowen-Lanford graph zeta function as computational tool
- Provides solvable cases at special coupling parameters
- Order-disorder correlators now accessible via determinantal formula

**Formalizability in Lean 4**: HARD
- Requires determinant theory (available)
- Graph embeddings on surfaces need formalization
- Topology infrastructure under development in Mathlib
- Ising model partition function requires careful setup
- Finite instances tractable (small genus)

**Success Probability Estimate**: 10-20% (for g=1 specific cases)

**Why Good for Aristotle**:
- Finite graphs on torus (g=1) are computable
- Determinantal formulas are algebraic
- Strong connection to existing theory (planar case solved)
- Recent work provides concrete computational approaches
- Verification possible for specific small examples

**References**:
- [Kac-Ward formula extension to order-disorder correlators](https://ar5iv.labs.arxiv.org/html/1709.06052) (2024)
- [Critical Ising Model via Kac-Ward Matrices](https://link.springer.com/article/10.1007/s00220-012-1575-z)

---

## Problem 6: Lévy Spin Glass Model - Enriched Free Energy

**Problem Statement**: In the bipartite Lévy spin glass model with heavy-tailed interactions, prove Conjecture 4.2 regarding the enriched free energy. Specifically, establish convergence and characterize the limit for interactions with finite variance but infinite higher moments.

**Current Status**:
- 2025 paper by Chen, Kim, and Sen establishes partial results
- Conjecture 4.2 has supporting evidence but remains unproven
- Classical Sherrington-Kirkpatrick model (Gaussian interactions): fully solved via Parisi formula
- Lévy case (heavy tails): fundamentally harder due to lack of Gaussian concentration

**Why Unsolved**: Heavy-tailed distributions break the Gaussian toolbox (central limit theorem, concentration inequalities, Gaussian integration by parts). The Parisi variational principle, proved for Gaussian case by Guerra-Talagrand, doesn't directly extend.

**Interdisciplinary Connection**:
- Optimization: random optimization landscapes with fat-tailed disorder
- Machine learning: neural networks with heavy-tailed weight initialization
- Finance: portfolio optimization with fat-tailed returns

**Recent Status (2023-2025)**:
- January 2025 publication in Communications in Mathematical Physics
- Establishes rigorous results for certain parameter regimes
- Connection to stable processes and Lévy flights explored
- Finite-size systems exhibit different behavior than Gaussian case

**Formalizability in Lean 4**: HARD
- Spin glass model formalization needed
- Heavy-tailed probability distributions require careful treatment
- Free energy as limiting quantity requires measure theory
- Finite systems with bounded moments tractable

**Success Probability Estimate**: 8-15%

**Why Good for Aristotle**:
- Conjecture has explicit mathematical formulation
- Partial results provide proof strategies
- Finite-size approximations can be analyzed
- Recent paper (2025) provides technical machinery
- Bounded moment conditions create finite subcases

**References**:
- [Some Rigorous Results on the Lévy Spin Glass Model](https://link.springer.com/article/10.1007/s00220-025-05244-2) (2025)
- [Spin glass dynamics: experiment, theory and simulation](https://arxiv.org/html/2412.08381v1)

---

## Problem 7: Matrix Discrepancy - Kómlos Conjecture Lower Bound

**Problem Statement**: The Kómlos Conjecture states that there exists a universal constant K such that for all square n×n matrices A whose columns have unit ℓ_2 norm, the discrepancy disc(A) ≤ K (independent of n). Current best lower bound: K ≥ 1 + √2 (Kunisky, 2024). Improve this lower bound or prove K = 1 + √2 is optimal.

**Current Status**:
- Spencer's theorem (1985): K exists (non-constructive)
- Best known lower bound: K ≥ 1 + √2 ≈ 2.414 (Kunisky, 2024)
- Upper bounds: K ≤ O(1) but specific constant unknown
- Related to "six standard deviations" problem (best lower bound on deviations: 2)

**Why Unsolved**: Finding explicit matrices with high discrepancy is hard. Random matrix constructions haven't yielded better lower bounds. The problem requires understanding worst-case behavior over infinite families of matrices.

**Interdisciplinary Connection**:
- Theoretical computer science: derandomization, pseudorandomness
- Numerical analysis: condition number of matrices
- Quantum computing: unitary designs and quantum pseudorandomness
- Combinatorial optimization: rounding schemes for SDP relaxations

**Recent Status (2023-2025)**:
- 2024 "Randomstrasse101" document lists this as major open problem
- Kunisky's 1 + √2 lower bound is recent (within last 2 years)
- Connection to matrix concentration inequalities explored
- Hadamard matrix discrepancy for odd case remains open

**Formalizability in Lean 4**: MEDIUM
- Matrix theory well-developed in Mathlib
- Discrepancy definition straightforward
- Proving lower bounds requires explicit construction
- Finite matrices with small n can be checked exhaustively
- Universal constant claims require careful formalization

**Success Probability Estimate**: 15-25% (for improving lower bound to K ≥ 2.5)

**Why Good for Aristotle**:
- Purely linear algebra and combinatorics
- Finite instances verifiable computationally
- Clear optimization problem (maximize discrepancy)
- Recent progress (2024) provides new techniques
- Connection to random matrix theory provides intuition
- Bounded dimension cases fully decidable

**References**:
- [Randomstrasse101: Open Problems of 2024](https://arxiv.org/pdf/2504.20539) (2024)
- [Recent progress in combinatorial random matrix theory](https://projecteuclid.org/journals/probability-surveys/volume-18/issue-none/Recent-progress-in-combinatorial-random-matrix-theory/10.1214/20-PS346.pdf)

---

## Summary Table

| Problem | Discipline | Formalizability | Success % | Recent Activity |
|---------|-----------|-----------------|-----------|-----------------|
| Site Percolation Threshold | Statistical Mechanics | MEDIUM | 10-15% | 2025 numerical work |
| Ising on Tree-like Graphs | Statistical Mechanics | MEDIUM-HARD | 20-30% | 2024 arXiv paper |
| Antiferromagnetic Potts Bounds | Combinatorics + Physics | MEDIUM | 25-35% | 2023-2024 proofs |
| Chromatic Polynomial Zeros | Complex Analysis + Combinatorics | MEDIUM-HARD | 15-25% | 2023 conjecture refuted |
| Kac-Ward Higher Genus | Topology + Physics | HARD | 10-20% | 2024 extension paper |
| Lévy Spin Glass | Probability Theory | HARD | 8-15% | 2025 rigorous results |
| Kómlos Conjecture | Linear Algebra | MEDIUM | 15-25% | 2024 improved bound |

---

## Key Insights

### What Makes These Problems Tractable?

1. **Finite Approximations**: All problems have meaningful finite-dimensional versions
2. **Computational Verification**: Small cases can be checked numerically/symbolically
3. **Recent Progress**: Activity in 2023-2025 shows techniques are advancing
4. **Discrete Core**: Despite physics origins, all reduce to discrete mathematics
5. **Clear Boundaries**: Well-defined threshold/existence questions

### Physics Intuition vs Mathematical Proof

- **Site Percolation**: Conformal field theory predicts p_c but proof elusive
- **Ising Model**: Physics has replica symmetry breaking; math lacks rigorous foundation
- **Chromatic Zeros**: Potts model phase transitions guide but don't prove results
- **Spin Glasses**: Parisi solution verified for Gaussian case, not heavy-tailed
- **Kac-Ward**: Physics solved planar case; math now catching up to higher genus

### Why These Are Good for Aristotle

1. Strong existing Lean/Mathlib infrastructure for graphs, matrices, probability
2. Bounded finite cases allow verification without approximation
3. Recent papers provide proof strategies and partial results
4. Interdisciplinary nature means multiple attack angles
5. Success would bridge pure math and physics communities

---

## Recommended Starting Points for Aristotle

**Easiest**: Problem 3 (Antiferromagnetic Potts) - purely combinatorial, recent proof strategies
**Medium**: Problem 7 (Kómlos) - linear algebra, explicit constructions possible
**Challenging**: Problem 2 (Ising Tree-like) - combines graph theory with thermodynamics
**Ambitious**: Problem 5 (Kac-Ward genus 1) - requires topological formalization

---

## Sources

### Ising Model and Phase Transitions
- [Non-uniqueness of phase transitions for Ising model on tree-like graphs](https://arxiv.org/html/2410.22061)
- [arXiv version](https://arxiv.org/abs/2410.22061)
- [The Planar Ising Model and Total Positivity](https://www.semanticscholar.org/paper/The-Planar-Ising-Model-and-Total-Positivity-Lis/f1b69ab3c3795b847c00449ac23df839e139b8c7)
- [Grammar of the Ising model](https://royalsocietypublishing.org/doi/10.1098/rspa.2024.0579)

### Percolation Theory
- [Lower Limit of Percolation Threshold on Square Lattice](https://www.mdpi.com/1099-4300/27/4/361)
- [Percolation threshold Wikipedia](https://en.wikipedia.org/wiki/Percolation_threshold)
- [Exact percolation probabilities](https://arxiv.org/pdf/2204.01517)

### Phase Transitions and Critical Phenomena
- [Non-triviality of phase transition for percolation on finite graphs](https://ems.press/content/serial-article-files/51184)
- [Geometric conjecture about phase transitions](https://link.aps.org/doi/10.1103/PhysRevE.107.064107)
- [Geometric conjecture arXiv](https://arxiv.org/abs/2203.03154)
- [Inferring phase transitions with thermodynamic maps](https://www.pnas.org/doi/10.1073/pnas.2321971121)

### Spin Glass Theory
- [Lévy Spin Glass Model](https://link.springer.com/article/10.1007/s00220-025-05244-2)
- [Spin glass dynamics](https://arxiv.org/html/2412.08381v1)
- [Quantum transition of 2D Ising spin glass](https://www.nature.com/articles/s41586-024-07647-y)
- [Parisi replica symmetry breaking](https://hal.science/hal-05359404v1/document)

### Random Matrix Theory
- [Randomstrasse101: Open Problems of 2024](https://arxiv.org/pdf/2504.20539)
- [Recent progress in combinatorial random matrix theory](https://projecteuclid.org/journals/probability-surveys/volume-18/issue-none/Recent-progress-in-combinatorial-random-matrix-theory/10.1214/20-PS346.pdf)

### Potts Model and Chromatic Polynomials
- [Uniqueness of Gibbs measure for 4-state antiferromagnetic Potts](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/0EE86171BCA21ABE510C8CE98C733C41/S0963548322000207a.pdf)
- [On location of chromatic zeros of series-parallel graphs](https://arxiv.org/abs/2204.10038)
- [Electronic Journal version](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v30i3p2)
- [Personal List of Unsolved Problems](https://math-mprf.org/journal/articles/id884/)

### Kac-Ward and Transfer Matrix
- [Kac-Ward formula extension](https://ar5iv.labs.arxiv.org/html/1709.06052)
- [Critical Ising Model via Kac-Ward Matrices](https://link.springer.com/article/10.1007/s00220-012-1575-z)
- [Kac-Ward and order-disorder correlators](https://ui.adsabs.harvard.edu/abs/2018JSP...173.1755A/abstract)

### Lee-Yang Zeros
- [Exploring Lee-Yang and Fisher Zeros in 2D Ising model](https://arxiv.org/abs/2312.03178)
- [Revisiting Fermion Sign Problem from Lee-Yang Zeros](https://arxiv.org/html/2507.22779v1)
- [Yang-Lee zeros for real-space condensation](https://arxiv.org/pdf/2411.02967)

### Hard Models and Exact Solutions
- [Rogers-Ramanujan identities in Statistical Mechanics](https://arxiv.org/html/2405.08425)
- [Hard hexagon model Wikipedia](https://en.wikipedia.org/wiki/Hard_hexagon_model)
