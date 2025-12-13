# Unsolved Problems in Information Theory and Coding Theory

**Research Period**: 2020-2025
**Focus Areas**: Channel capacity bounds, error-correcting codes, network coding, information inequalities
**Selection Criteria**: Finite/bounded formulations suitable for Lean 4 formalization

---

## Problem 1: Gilbert-Varshamov Bound Asymptotic Exactness

### Problem Statement
**Conjecture (Goppa)**: The Gilbert-Varshamov bound is asymptotically exact for binary codes.

Formally: Let A₂(n, d) denote the maximum size of a binary code of length n and minimum distance d. The Gilbert-Varshamov bound states:

A₂(n, d) ≥ 2ⁿ / V(n, d-1)

where V(n, d) is the volume of a Hamming ball of radius d.

**Goppa's conjecture** asserts that this bound cannot be improved asymptotically for binary codes (q=2), i.e., that the bound is tight in the limit.

### Why Unsolved
The Tsfasman-Vladut-Zink breakthrough showed asymptotic improvement is possible for alphabets of size q ≥ 49, but for q < 46, no asymptotic improvements are known. The binary case (q=2) remains fundamentally hard because:

1. The Gilbert-Varshamov bound can be improved by logarithmic factors (shown: A₂(n, d) ≥ c·2ⁿ/(V(n,d-1)·log₂V(n,d-1)) for d/n ≤ 0.499)
2. Whether it can be improved by more than logarithmic factors asymptotically is unknown
3. The problem resists traditional algebraic geometry techniques that work for larger alphabets

### Interdisciplinary Connection
**Computer Science**: Binary codes are fundamental to digital communications, storage systems, and error correction in computation. Resolving this would determine fundamental limits of binary error correction.

**Communications Engineering**: Determines whether practical binary communication systems can asymptotically achieve better rates than currently known.

### Recent Status (2020-2025)
- Logarithmic improvements established using graph-theoretic frameworks with locally sparse graphs
- Binary linear concatenated codes with Reed-Solomon outer codes meet the Gilbert-Varshamov bound asymptotically (existence proven)
- No breakthrough on whether the bound is exactly tight (constant factor improvement unknown)

### Formalizability in Lean 4
**MEDIUM** - Requires:
- Hamming distance formalization (available in Mathlib)
- Combinatorial bounds
- Asymptotic analysis
- Graph theory infrastructure (partially available)

### Success Probability Estimate
**10-15%** - The conjecture has resisted proof for decades. A negative result (showing non-asymptotic exactness) might be more achievable than a positive proof.

### Why Good for Aristotle
1. Clear finite formulation for specific parameters (n, d)
2. Can verify logarithmic improvement cases
3. Strong combinatorial structure
4. Existing proof techniques well-documented
5. Could tackle bounded parameter cases before full asymptotic statement

### References
- [Asymptotic Improvement of Gilbert-Varshamov Bound](https://arxiv.org/pdf/math/0404325)
- [Selected Unsolved Problems in Coding Theory](https://link.springer.com/book/10.1007/978-0-8176-8256-9)
- [Open Problems in Coding Theory](https://gilkalai.wordpress.com/wp-content/uploads/2024/01/open_problems_in_coding_theory.pdf)

---

## Problem 2: Existence of Type I [56,28,12] Self-Dual Code

### Problem Statement
**Open Question**: Does there exist a Type I binary self-dual code with parameters [56, 28, 12]?

**Type I codes**: Binary self-dual codes that are singly-even (all codewords have even weight, but not all divisible by 4).

A [56, 28, 12] code would have:
- Length: 56 bits
- Dimension: 28 (2²⁸ codewords)
- Minimum distance: 12 (can correct up to 5 errors)

### Why Unsolved
New necessary conditions for existence have been established (2021-2024) through:
1. Neighborhood analysis of binary self-dual codes
2. Weight enumerator constraints
3. Divisibility conditions on weight distributions

However, neither existence nor non-existence has been proven. Known results:
- No better Type I code than best Type II code at same length
- Codes with parameters [56, 28, 10] exist (but distance 10, not 12)
- The [56, 28, 12] case sits at boundary of known bounds

### Interdisciplinary Connection
**Quantum Error Correction**: Self-dual codes relate to CSS quantum codes and stabilizer codes. The [56,28,12] code would have implications for quantum memory.

**Lattice Theory**: Self-dual codes connect to unimodular lattices via Construction A, relevant to sphere packing and crystallography.

**Cryptography**: Self-dual codes have applications in code-based cryptography and secure multi-party computation.

### Recent Status (2023-2024)
- **2021**: Hannusch & Major paper "The search for Type I codes" established this as open
- **2022-2024**: New necessary conditions from neighborhood analysis
- **2024**: Computer searches continue but have not resolved the question
- Five new [56, 28, 10] codes discovered (not the desired distance 12)

### Formalizability in Lean 4
**MEDIUM** - Requires:
- Linear code formalization (basic infrastructure available)
- Dual code properties
- Weight enumerator machinery
- Finite field arithmetic (well-supported in Mathlib)

### Success Probability Estimate
**25-30%** - Bounded search space makes this tractable:
1. Could prove non-existence through exhaustive constraints
2. Existence proof would require explicit construction or counting argument
3. Computational verification possible for candidate codes

### Why Good for Aristotle
1. **Finite, concrete parameters**: Can enumerate constraints systematically
2. **Strong algebraic structure**: Linear algebra over F₂
3. **Existing theory**: Weight enumerators, MacWilliams identities well-developed
4. **Verification straightforward**: Can check code properties algorithmically
5. **Bounded complexity**: Not an infinite family, single existence question

### References
- [The search for Type I codes](https://arxiv.org/pdf/2110.09244)
- [Neighborhoods of binary self-dual codes](https://arxiv.org/abs/2206.05588)
- [New binary self-dual codes of lengths 56, 58, 64](https://www.sciencedirect.com/science/article/pii/S1071579721000708)

---

## Problem 3: Quantum MDS Conjecture

### Problem Statement
**Conjecture**: The length n of a q-ary quantum MDS code is bounded by n ≤ q² + 2.

A quantum MDS code achieves the quantum Singleton bound: k + 2d ≤ n + 2, where:
- n = code length
- k = number of encoded qubits
- d = minimum distance

The conjecture limits how long an optimal quantum error-correcting code can be for a given alphabet size q.

### Why Unsolved
**Verified cases**: The conjecture has been proven only for:
- q = 2 (binary quantum codes)
- q = 3 (ternary quantum codes)
- Distance d = 3 codes (all alphabet sizes)

**What remains**: General case for q ≥ 4 and d ≥ 4 is open.

The difficulty stems from:
1. Quantum codes have more complex structure than classical MDS codes
2. CSS construction and stabilizer formalism add constraints
3. Algebraic geometry techniques for classical MDS don't directly translate
4. Connection to additive codes over GF(q²) is subtle

### Interdisciplinary Connection
**Quantum Computing**: Determines fundamental limits for quantum memory and quantum communication. Tight characterization affects:
- Fault-tolerant quantum computation architecture
- Quantum repeater design
- Optimal encoding strategies for quantum networks

**Quantum Cryptography**: Quantum key distribution protocols benefit from optimal quantum codes.

### Recent Status (2024-2025)
- **January 2025**: New constructions of quantum MDS codes with flexible parameters from Hermitian self-orthogonal GRS codes
- **March 2024**: Quantum codes proven to be "Hermitian almost MDS" when certain parameters are satisfied
- **2024**: MDS and Gilbert-Varshamov quantum codes constructed from generalized monomial-Cartesian codes
- Research focuses on constructing codes in region q+1 < n < q²+2, but conjecture bound unresolved

### Formalizability in Lean 4
**HARD** - Requires:
- Quantum code infrastructure (not yet in Mathlib)
- Stabilizer formalism
- Clifford group operations
- CSS construction framework
- Could start with classical MDS → quantum MDS translation

### Success Probability Estimate
**5-10%** - Very challenging:
1. Requires new techniques beyond current Lean 4 quantum infrastructure
2. Full conjecture likely out of reach
3. Might prove special cases (specific q and d values)

### Why Good for Aristotle
1. **Bounded cases tractable**: Could target specific (q, d) pairs
2. **Clear structure**: Quantum MDS codes have well-defined properties
3. **Verification possible**: Can check quantum Singleton bound
4. **Active research area**: New techniques emerging in 2024-2025
5. **High impact**: Even partial results would be significant

### References
- [Quantum MDS Codes over Small Fields](https://arxiv.org/abs/1502.05267)
- [New quantum MDS codes (January 2025)](https://arxiv.org/html/2501.17010)
- [MDS and Gilbert-Varshamov quantum codes (2024)](https://link.springer.com/article/10.1007/s11128-024-04297-x)

---

## Problem 4: Shannon Capacity of the Seven-Cycle C₇

### Problem Statement
Determine the Shannon capacity Θ(C₇) of the seven-cycle graph.

**Current bounds**: 3.2578 < Θ(C₇) ≤ 3.3178

The Shannon capacity of a graph G, denoted Θ(G), is defined as:

Θ(G) = lim(n→∞) α(G^⊗n)^(1/n)

where α(G^⊗n) is the independence number of the nth strong product power of G.

**Context**: Lovász solved the five-cycle case in 1979 (Θ(C₅) = √5 ≈ 2.236), but odd cycles ≥7 remain open.

### Why Unsolved
The seven-cycle case is notorious because:
1. Lovász theta function gives upper bound θ(C₇) ≈ 3.3178 but may not be tight
2. Computing α(G^⊗n) becomes exponentially harder as n grows
3. No general technique for odd cycles of length ≥7
4. Strong product structure creates combinatorial explosion

**Progress barrier**: Best lower bound required finding independent set of size 367 in C₇^⊗5 (Polak & Schrijver, 2018).

### Interdisciplinary Connection
**Information Theory**: Shannon capacity represents the zero-error capacity of a noisy channel, determining:
- Maximum rate of error-free communication
- Fundamental limits for coding over specific channel types
- Trade-offs between rate and error probability

**Quantum Information**: Entanglement-assisted Shannon capacity relates to quantum advantages in communication.

**Communications Engineering**: Determines achievable rates for channels where errors must be completely eliminated (safety-critical systems).

### Recent Status (2024)
- **2024**: New approaches using "asymptotic spectrum distance" and graph limits
- Unified framework for upper bound methods developed
- No breakthrough on exact value, but improved computational techniques
- Lower bound: Θ(C₇) ≥ 367^(1/5) > 3.2578 (2018, still best known)
- Upper bound: θ(C₇) ≈ 3.3178 (Lovász theta)

### Formalizability in Lean 4
**MEDIUM-HARD** - Requires:
- Graph theory (available in Mathlib)
- Independence number computation
- Strong product of graphs
- Limit supremum formalization
- Asymptotic bounds

### Success Probability Estimate
**5-8%** - Extremely difficult:
1. Might prove improved bounds rather than exact value
2. Could formalize lower bound proofs for specific products (C₇^⊗n)
3. Exact value likely requires new breakthrough technique

### Why Good for Aristotle
1. **Clear finite formulation**: Can work with specific powers C₇^⊗n
2. **Verification possible**: Independence sets can be checked
3. **Incremental progress**: Each improvement to bounds is publishable
4. **Well-studied**: Extensive literature and proof techniques
5. **High profile**: One of most famous open problems in graph theory/IT

### References
- [Shannon capacity of C7 (Open Problem Garden)](http://www.openproblemgarden.org/op/shannon_capacity_of_the_seven_cycle)
- [New lower bound on Shannon capacity of C7 (2018)](https://arxiv.org/abs/1808.07438)
- [Asymptotic spectrum distance (2024)](https://arxiv.org/html/2404.16763)

---

## Problem 5: Li-Li Conjecture (Network Coding for Multiple Unicast)

### Problem Statement
**Li-Li Conjecture (2004)**: In an undirected network with multiple unicast sessions, network coding provides no advantage over routing (multicommodity flow).

Formally: For k source-sink pairs (s₁,t₁), ..., (sₖ,tₖ) in an undirected graph G, the maximum achievable rate region using network coding equals the maximum multicommodity flow rate region.

Equivalently: Network coding rate = Multicommodity flow rate for undirected graphs.

### Why Unsolved
The conjecture has resisted proof since 2004 despite being verified for many special cases:

**Verified cases**:
- Butterfly network (directed, coding helps)
- K₃,₂ with four source-sink pairs (verified 2009 using entropy calculus)
- Networks with specific connectivity requirements (gap bounded by factor of 3)

**Difficulty**:
1. Even simple networks couldn't be verified initially
2. Gap amplification results show any small advantage amplifies to log(|G'|)^c
3. Equivalence to fundamental problems in circuit complexity and data structures

### Interdisciplinary Connection
**Theoretical Computer Science**: The conjecture has profound implications:

1. **Circuit Complexity**: If true, then constant-degree boolean circuits for multiplication must have size Ω(n log n), nearly settling multiplication circuit complexity.

2. **Data Structure Lower Bounds**: Conditional lower bounds for:
   - Sorting algorithms with external memory
   - Dynamic data structure problems

3. **Algorithm Design**: Determines whether sophisticated network coding provides fundamental advantages.

**Communications Networks**: Determines whether to invest in network coding hardware for undirected networks (fiber, Ethernet) versus simpler routing.

### Recent Status (2023-2024)
- **2023**: Network coding constructions for special class of three unicast sessions (Scientific Reports)
- **2024**: Work on external codes for multiple unicast networks via interference alignment (Designs, Codes and Cryptography)
- Conjecture remains open; no general proof or counterexample
- Active research on connecting to circuit complexity lower bounds

### Formalizability in Lean 4
**MEDIUM-HARD** - Requires:
- Graph theory (available)
- Network flow formalization
- Entropy calculus/information theory
- Linear algebra over finite fields
- Rate region characterization

### Success Probability Estimate
**15-20%** - Moderate difficulty:
1. Could prove for restricted graph classes
2. Negative result (counterexample) more likely than full proof
3. Connection to simpler problems (K₃,₂ case) already verified
4. Entropy calculus provides structured approach

### Why Good for Aristotle
1. **Finite cases tractable**: Can target specific small networks
2. **Verification algorithmic**: Can compute flows and coding rates
3. **Strong structure**: Linear network coding over finite fields
4. **High impact**: Connections to circuit complexity, data structures
5. **Active research**: New techniques developed 2023-2024
6. **Multiple approaches**: Graph theory, entropy calculus, linear algebra

### References
- [Network coding conjecture implies data structure lower bounds](https://www.tcs.tifr.res.in/web/events/1125)
- [On the Multiple Unicast Network Coding Conjecture](https://www.researchgate.net/publication/224106367_On_the_Multiple_Unicast_Network_Coding_Conjecture)
- [Network coding for three unicast sessions (2023)](https://www.nature.com/articles/s41598-023-47203-8)
- [Lower Bounds for Multiplication via Network Coding](https://arxiv.org/abs/1902.10935)

---

## Problem 6: Ingleton Inequality Maximum Violation

### Problem Statement
**Open Question**: What is the maximum possible violation (Ingleton score) of Ingleton's inequality for four random variables?

**Ingleton's inequality**: For random variables X₁, X₂, X₃, X₄:

I(X₁;X₂) + I(X₃;X₄) + I(X₁X₂;X₃X₄) ≥ I(X₁;X₃X₄) + I(X₂;X₃X₄) + I(X₃;X₁X₂) + I(X₄;X₁X₂)

The **Ingleton score** measures the maximum violation: max{0, RHS - LHS}

**Previous conjecture (Four-Atom Conjecture)**: Score cannot exceed 0.089373
**Status**: **DISPROVEN** - Matúš and Csirmaz found score 0.0925000777

**Current question**: What is the supremum of the Ingleton score?

### Why Unsolved
1. **Nonlinear optimization**: Finding extremal distributions over four random variables is computationally hard
2. **Non-Shannon inequalities**: Ingleton inequality is not derivable from Shannon's basic inequalities
3. **Counterexamples rare**: Most distributions satisfy the inequality; violations are sparse in distribution space
4. **Continuous parameter space**: Optimizing over all joint distributions is infinite-dimensional

Recent work shows:
- Best known score: 0.0925000777 (small four-atom distribution)
- No proof that this is maximal
- Computational searches haven't found larger violations

### Interdisciplinary Connection
**Network Coding**: Ingleton's inequality distinguishes linear from non-linear network codes:
- If satisfied: linear coding suffices
- If violated: non-linear coding may offer advantages

**Matroid Theory**: Ingleton inequality relates to representability of matroids over fields.

**Quantum Information**: Violations relate to quantum contextuality and non-locality measures.

### Recent Status (2020-2024)
- **2020**: Paper "Violations of the Ingleton inequality and revising the four-atom conjecture" (Kybernetika)
- **2023**: "No Eleventh Conditional Ingleton Inequality" proven (negative result on generalizations)
- **2024**: "Structural Properties of Entropic Vectors and Stability of Ingleton Inequality"
- Active research on conditional versions and generalizations

### Formalizability in Lean 4
**HARD** - Requires:
- Information theory infrastructure (mutual information, conditional entropy)
- Probability theory over discrete/continuous spaces
- Optimization framework
- Real analysis for supremum arguments

### Success Probability Estimate
**20-25%** - Moderate-high difficulty:
1. Could prove upper bound better than current constructions
2. Finite discrete distributions make this tractable
3. Symmetry arguments might reduce search space
4. Computational verification for candidate extremal distributions

### Why Good for Aristotle
1. **Bounded finite cases**: Can restrict to n-atom distributions
2. **Computational verification**: Can compute Ingleton score for specific distributions
3. **Algebraic structure**: Discrete probability, information theory
4. **Incremental progress**: Improved bounds are valuable
5. **Active research**: New techniques in 2023-2024

### References
- [Non-Shannon Information Inequalities in Four Random Variables](https://arxiv.org/abs/1104.3602)
- [Violations of Ingleton inequality (2020)](https://www.kybernetika.cz/content/2020/5/916/paper.pdf)
- [No Eleventh Conditional Ingleton Inequality (2023)](https://arxiv.org/html/2204.03971)
- [Structural Properties of Entropic Vectors (2024)](https://arxiv.org/html/2512.02767)

---

## Problem 7: Polar Codes Finite Blocklength Scaling Conjecture

### Problem Statement
**Conjecture**: For polar codes with rate R < I(W) (symmetric capacity of channel W), the blocklength n required for reliable communication with error probability ε scales as:

n = O((I(W) - R)^(-μ))

where the **scaling exponent μ** is conjectured to have specific optimal values.

**Known results**:
- Upper bound: μ ≤ 5.77 (proven)
- Conjectured: μ ≈ 3.63 or better for optimized polar codes
- For prime alphabet size p: similar improved polynomial degree bounds conjectured

The conjecture asks: **What is the optimal scaling exponent μ for polar codes?**

### Why Unsolved
Polar codes achieve capacity asymptotically (Arıkan 2009), but finite-length behavior is complex:

1. **Construction dependence**: Scaling depends on:
   - Channel polarization rate
   - Frozen bit selection algorithm
   - CRC-aided (CA) vs threshold-based decoding

2. **Computational difficulty**: Exact finite-length analysis requires:
   - Tracking all 2ⁿ polar subchannel capacities
   - Error probability analysis at each blocklength

3. **Gap between theory and practice**:
   - Proven bounds (μ ≤ 5.77) are loose
   - Simulations suggest μ ≈ 3.6-4.0
   - No tight theoretical characterization

### Interdisciplinary Connection
**5G/6G Communications**: Polar codes are used in 5G control channels. Finite blocklength performance determines:
- Latency in ultra-reliable low-latency communications (URLLC)
- Efficiency of short packet transmission
- Resource allocation in wireless networks

**Quantum Communication**: Polar codes adapted to quantum channels have similar finite-length questions.

**Storage Systems**: Short polar codes used in memory with limited redundancy.

### Recent Status (2024-2025)
- **March 2025**: New paper "Undetected Error Probability in the Short Blocklength Regime: Approaching Finite-Blocklength Bounds With Polar Codes"
  - Two novel achievability bounds outperform Forney's bound for binary-input AWGN channel
  - Threshold-based approach superior to CRC-based in short blocklength regime

- **2024**: Active work on:
  - Non-binary polar codes (conjectured similar results for prime alphabet size)
  - CRC-aided polar codes benchmarking
  - Improved polynomial degree bounds

### Formalizability in Lean 4
**MEDIUM-HARD** - Requires:
- Channel coding theory
- Probability theory (error probabilities)
- Asymptotic analysis
- Polynomial bounds
- Information theory (channel capacity, mutual information)

### Success Probability Estimate
**30-35%** - Higher probability because:
1. **Recent progress**: 2024-2025 papers provide new techniques
2. **Bounded cases**: Can prove results for specific channels (BSC, BEC, AWGN)
3. **Computational verification**: Can simulate and verify bounds
4. **Active research**: Multiple groups working on this
5. **Incremental results valuable**: Improved bounds are publishable

### Why Good for Aristotle
1. **Clear finite formulation**: Specific blocklengths n can be analyzed
2. **Practical importance**: 5G applications motivate the problem
3. **Multiple approaches**: Probabilistic, algebraic, combinatorial techniques
4. **Verification possible**: Simulation can confirm theoretical bounds
5. **Recent momentum**: 2024-2025 progress suggests approachable
6. **Structured problem**: Channel polarization is well-understood recursively

### References
- [Undetected Error Probability (March 2025)](https://arxiv.org/abs/2503.02782)
- [Improved Bounds on Finite Length Scaling](https://arxiv.org/abs/1307.5510)
- [Finite Length Scaling of Ternary Polar Codes](https://arxiv.org/abs/1502.02925)

---

## Summary Table: Problem Comparison

| Problem | Difficulty | Success % | Formalizability | Recent Progress | Impact |
|---------|-----------|-----------|-----------------|-----------------|--------|
| Gilbert-Varshamov | Hard | 10-15% | Medium | Logarithmic improvements | High (fundamental coding) |
| Type I [56,28,12] | Medium | 25-30% | Medium | New necessary conditions | Medium (code existence) |
| Quantum MDS | Very Hard | 5-10% | Hard | New constructions (2025) | High (quantum computing) |
| Shannon C₇ | Very Hard | 5-8% | Medium-Hard | New bounds methods (2024) | High (graph theory/IT) |
| Li-Li Conjecture | Hard | 15-20% | Medium-Hard | Special cases (2023-24) | Very High (complexity) |
| Ingleton Violation | Hard | 20-25% | Hard | Disproven bound (2020) | Medium (network coding) |
| Polar Codes Scaling | Medium-Hard | 30-35% | Medium-Hard | New bounds (2025) | High (5G/6G) |

---

## Sources

### General Information Theory Resources
- [Open Problems in Coding Theory](https://gilkalai.wordpress.com/wp-content/uploads/2024/01/open_problems_in_coding_theory.pdf)
- [Selected Unsolved Problems in Coding Theory](https://link.springer.com/book/10.1007/978-0-8176-8256-9)
- [List of open questions (a3nm.net)](https://a3nm.net/work/research/questions/)
- [Five Open Problems in Quantum Information Theory](https://link.aps.org/doi/10.1103/PRXQuantum.3.010101)

### Channel Capacity
- [Capacity Bounds for Broadcast Channels (2024)](https://arxiv.org/html/2406.20019)
- [Channel capacity - Wikipedia](https://en.wikipedia.org/wiki/Channel_capacity)
- [Shannon-Hartley theorem](https://en.wikipedia.org/wiki/Shannon–Hartley_theorem)

### Error-Correcting Codes
- [Pseudorandom Error-Correcting Codes (2024)](https://eprint.iacr.org/2024/235.pdf)
- [Tutorial on Quantum Error Correction (2024)](https://arxiv.org/html/2407.12737)
- [Complexity and order in approximate quantum error-correcting codes](https://www.nature.com/articles/s41567-024-02621-x)
- [Error Correction Zoo](https://errorcorrectionzoo.org/references)

### Network Coding
- [Network coding construction for three unicast sessions (2023)](https://www.nature.com/articles/s41598-023-47203-8)
- [Network Coding Conjecture implies Data Structure Lower Bounds](https://www.tcs.tifr.res.in/web/events/1125)
- [Lower Bounds for Multiplication via Network Coding](https://arxiv.org/abs/1902.10935)
- [Updates on Information Theory and Network Coding](https://www.mdpi.com/1099-4300/27/1/17)

### Information Inequalities
- [Inequalities in information theory - Wikipedia](https://en.wikipedia.org/wiki/Inequalities_in_information_theory)
- [Conjectures - Information Theory b-log](https://blogs.princeton.edu/blogit/category/conjectures/)
- [Non-Shannon Information Inequalities](https://arxiv.org/abs/1104.3602)
- [Graph Guessing Games and Non-Shannon Inequalities](https://www.researchgate.net/publication/267627213_Graph_Guessing_Games_and_Non-Shannon_Information_Inequalities)

### Specific Problems
- [Asymptotic Improvement of Gilbert-Varshamov Bound](https://arxiv.org/pdf/math/0404325)
- [The search for Type I codes (2021)](https://arxiv.org/pdf/2110.09244)
- [Neighborhoods of binary self-dual codes](https://arxiv.org/abs/2206.05588)
- [New quantum MDS codes (January 2025)](https://arxiv.org/html/2501.17010)
- [Quantum MDS Codes over Small Fields](https://arxiv.org/abs/1502.05267)
- [Shannon capacity of C7 (Open Problem Garden)](http://www.openproblemgarden.org/op/shannon_capacity_of_the_seven_cycle)
- [New lower bound on Shannon capacity of C7 (2018)](https://arxiv.org/abs/1808.07438)
- [Asymptotic spectrum distance (2024)](https://arxiv.org/html/2404.16763)
- [Violations of Ingleton inequality (2020)](https://www.kybernetika.cz/content/2020/5/916/paper.pdf)
- [No Eleventh Conditional Ingleton Inequality (2023)](https://arxiv.org/html/2204.03971)
- [Structural Properties of Entropic Vectors (2024)](https://arxiv.org/html/2512.02767)
- [Undetected Error Probability with Polar Codes (March 2025)](https://arxiv.org/abs/2503.02782)
- [Improved Bounds on Finite Length Scaling of Polar Codes](https://arxiv.org/abs/1307.5510)
