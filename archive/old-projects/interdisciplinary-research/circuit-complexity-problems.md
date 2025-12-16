# Circuit Complexity & Computational Complexity: Unsolved Problems for Aristotle

**Research Date**: December 11, 2025
**Focus**: Tractable, provable problems in circuit complexity with bounded parameters
**Target**: Problems suitable for automated theorem proving with Aristotle

---

## Executive Summary

After extensive research of 2023-2025 literature, I've identified **7 high-quality unsolved problems** in circuit complexity and computational complexity theory that are:
1. **Truly unsolved** (active research 2023-2025)
2. **Provable** (not just computational)
3. **Bounded/finite** formulations
4. **Interdisciplinary** (connections to CS theory, algorithm design, cryptography)
5. **Suitable for Lean 4** formalization

These problems avoid the P vs NP barrier by focusing on specific circuit models, bounded-depth circuits, communication complexity with finite parameters, and derandomization conjectures with tractable cases.

---

## Problem 1: Formula Size Bounds for Majority Function

### Problem Statement
Improve the known bounds for the De Morgan formula size of the Majority function on n Boolean variables.

**Current State**:
- **Lower bound**: Ω(n²) [classical result]
- **Upper bound (De Morgan)**: O(n^3.91) [Sergeev 2012]
- **Upper bound (monotone)**: O(n^5.3)
- **OPEN**: Close the gap between n² and n^3.91

**Specific Challenges**:
1. Prove a super-quadratic lower bound (e.g., Ω(n^2.5))
2. Improve the upper bound below n^3.5
3. For monotone formulas, reduce the gap from n^5.3

### Why Unsolved
The gap between quadratic lower bounds and cubic-plus upper bounds has persisted for decades despite numerous attempts using various techniques (rank methods, communication complexity, polynomial method). The problem requires understanding deep structural properties of Boolean functions.

### Interdisciplinary Connection
**Algorithm Design**: Formula complexity directly relates to:
- Boolean circuit optimization in hardware design
- Query complexity in database theory
- Decision tree complexity in machine learning
- Space-time tradeoffs in streaming algorithms

**Practical Impact**: Improved bounds would advance:
- Hardware synthesis tools
- SAT solver design
- Quantum circuit compilation

### Recent Status (2023-2025)
- Gal, Tal, and Trejo Nuñez (2019) achieved n³/polylog(n) lower bounds for functions composed with majority
- No improvements to the Majority function's direct bounds reported in 2024-2025
- Active area with ongoing polynomial method applications

### Formalizability in Lean 4: MEDIUM

**Why MEDIUM**:
- **✓ Pros**:
  - De Morgan formulas have clean recursive definition
  - Majority function is straightforward to define
  - Size counting is discrete and finite
  - Mathlib has Boolean function infrastructure

- **✗ Cons**:
  - Proving new bounds requires sophisticated techniques
  - May need linear algebra over GF(2)
  - Composition lemmas can be technical

**Lean 4 Formalization Sketch**:
```lean
-- Define De Morgan formulas
inductive DeMorganFormula (n : ℕ) where
  | var : Fin n → DeMorganFormula n
  | and : DeMorganFormula n → DeMorganFormula n → DeMorganFormula n
  | or : DeMorganFormula n → DeMorganFormula n → DeMorganFormula n
  | not : DeMorganFormula n → DeMorganFormula n

-- Formula size
def size : DeMorganFormula n → ℕ
  | .var _ => 1
  | .and f g => size f + size g + 1
  | .or f g => size f + size g + 1
  | .not f => size f + 1

-- Majority function
def majority (v : Fin n → Bool) : Bool :=
  2 * (Finset.univ.filter (fun i => v i)).card > n

-- Main theorem (open)
theorem majority_formula_lower_bound (n : ℕ) (hn : n ≥ 3) :
  ∀ f : DeMorganFormula n,
    (∀ v, eval f v = majority v) →
    size f ≥ n^2 := by sorry
```

### Success Probability Estimate: 5-15%

**Reasoning**:
- **5%**: Proving entirely new bounds (major breakthrough)
- **10%**: Finding special cases or restricted models
- **15%**: Formalizing existing proofs with minor improvements

This is a hard problem that has resisted decades of effort. Aristotle would likely formalize known results rather than prove new bounds, unless it discovers a novel proof technique.

### Why Good for Aristotle
1. **Clean finite structure**: Formulas are trees with discrete size
2. **Existing techniques**: Rank method, polynomial method are well-studied
3. **Incremental progress possible**: Could prove bounds for restricted cases (small n, specific subfunctions)
4. **Verification value**: Even formalizing known bounds would be valuable
5. **Composition-friendly**: Natural inductive structure

### References
- [Open Problems in Circuit Complexity Theory](https://cnchou.github.io/notes/openproblem.html)
- [Upper bounds for formula size of majority (arXiv:1208.3874)](https://arxiv.org/abs/1208.3874)
- [Cubic Formula Size Lower Bounds (ITCS 2019)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2019.35)

---

## Problem 2: Monotone Circuit Complexity Lower Bounds

### Problem Statement
Prove improved lower bounds for the monotone circuit complexity of explicit Boolean functions, particularly focusing on matching and connectivity problems.

**Current State**:
- **Perfect Matching**: 2^(n^Ω(1)) lower bound [Cavalar et al., July 2025 - BREAKTHROUGH]
- **Previous best**: n^Ω(log n) [Razborov 1985]
- **OPEN**: Improve bounds for other natural functions (st-connectivity depth, clique, etc.)

**Specific Targets**:
1. Prove st-connectivity requires monotone depth Ω(log²n)
2. Improve lower bounds for clique detection beyond current thresholds
3. Extend new techniques to other graph properties

### Why Unsolved
Monotone circuits are easier to analyze than general circuits (no negations), yet proving tight lower bounds remains difficult. The 2025 breakthrough on perfect matching shows the field is still active with major results possible.

### Interdisciplinary Connection
**Proof Complexity**: Monotone circuit lower bounds have direct connections to:
- Resolution proof complexity
- Cutting Planes proof systems
- Polynomial Calculus lower bounds

**Cryptography**: Monotone complexity relates to:
- Secure computation protocols
- Information-theoretic security
- Secret sharing schemes

### Recent Status (2023-2025)
- **July 2025 BREAKTHROUGH**: Perfect matching requires 2^(n^Ω(1)) size [Cavalar et al.]
- Bounded-depth monotone circuits for homomorphism polynomials characterized (2025)
- Connections to proof complexity strengthened (2024)

### Formalizability in Lean 4: MEDIUM-HARD

**Why MEDIUM-HARD**:
- **✓ Pros**:
  - Monotone circuits simpler than general circuits
  - Graph properties have natural definitions in Mathlib
  - Size and depth are discrete measures

- **✗ Cons**:
  - Lower bound techniques are sophisticated
  - May require sunflower lemmas, approximation arguments
  - Graph theory formalization can be verbose

**Lean 4 Formalization Sketch**:
```lean
-- Monotone circuits (only AND/OR, no NOT)
inductive MonotoneCircuit (n : ℕ) where
  | var : Fin n → MonotoneCircuit n
  | and : MonotoneCircuit n → MonotoneCircuit n → MonotoneCircuit n
  | or : MonotoneCircuit n → MonotoneCircuit n → MonotoneCircuit n

-- Perfect matching on n-vertex graphs
def hasPerfectMatching (G : SimpleGraph (Fin n)) : Bool := sorry

-- Main theorem (recently proved, but formalization would be valuable)
theorem perfect_matching_monotone_lower_bound (n : ℕ) :
  ∀ C : MonotoneCircuit (n*(n-1)/2),
    (∀ G, eval C (edgeVector G) = hasPerfectMatching G) →
    size C ≥ 2^(n^(1/10)) := by sorry  -- Simplified exponent
```

### Success Probability Estimate: 20-35%

**Reasoning**:
- **20%**: Full formalization of 2025 perfect matching result
- **30%**: Formalizing Razborov's classic techniques
- **35%**: Proving bounds for restricted subproblems

The 2025 breakthrough is very recent, making it an exciting target. Formalizing even the classical results would be valuable.

### Why Good for Aristotle
1. **Recent breakthrough**: 2025 result shows tractability
2. **Rich theory**: Decades of techniques to leverage
3. **Natural functions**: Graph properties are intuitive
4. **Proof complexity connections**: Cross-domain insights possible
5. **Finite formulations**: All problems have bounded-size instances

### References
- [Monotone Bounded-Depth Complexity (MFCS 2025)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2025.19)
- [Monotone Circuit Lower Bounds from Resolution](https://theoryofcomputing.org/articles/v016a013/)
- [ECCC TR25-102](https://eccc.weizmann.ac.il/report/2025/102/) - 2025 perfect matching result

---

## Problem 3: AC⁰[p] Separation for Composite Moduli

### Problem Statement
Determine the computational power of bounded-depth circuits with MOD m gates where m is a composite number (product of distinct primes).

**Current State**:
- **Known**: AC⁰[p] ≠ AC⁰[q] for distinct primes p, q [Razborov 1987, Smolensky 1986]
- **Known**: NEXP ⊄ AC⁰[6] [result from ~2010]
- **OPEN**: Is NP contained in AC⁰[6]? AC⁰[10]? AC⁰[m] for composite m?
- **OPEN**: What is the exact power of AC⁰[pq] for primes p, q?

**Specific Challenges**:
1. Prove or disprove: NP ⊆ AC⁰[6]
2. Characterize which functions are in AC⁰[6] vs AC⁰[2] ∪ AC⁰[3]
3. Prove separation results for AC⁰[6] vs other classes

### Why Unsolved
While Razborov-Smolensky techniques separate AC⁰[p] for distinct primes, these methods break down for composite moduli. The polynomial method doesn't extend naturally to MOD 6 gates, creating a fundamental barrier.

### Interdisciplinary Connection
**Cryptography**: MOD m circuits relate to:
- Modular arithmetic in cryptographic protocols
- Threshold schemes with composite moduli
- Lattice-based cryptography

**Algorithm Design**: Understanding AC⁰[m] power impacts:
- Parallel algorithm design
- Streaming algorithms with modular counters
- Constant-depth circuit optimization

### Recent Status (2023-2025)
- Research on generalized AC⁰ circuits (GC⁰(k)) interpolating between AC⁰ and TC⁰ (2023)
- Tight correlation bounds for circuits between AC⁰ and TC⁰ (CCC 2023)
- No major breakthrough on composite moduli, remains open

### Formalizability in Lean 4: MEDIUM

**Why MEDIUM**:
- **✓ Pros**:
  - Circuit model has clean definition
  - Modular arithmetic well-supported in Mathlib
  - Bounded-depth restriction simplifies analysis

- **✗ Cons**:
  - Separation proofs require advanced techniques
  - Need to formalize Razborov-Smolensky approximation method
  - Composite moduli interactions are subtle

**Lean 4 Formalization Sketch**:
```lean
-- AC⁰[m] circuits
inductive AC0Mod (m : ℕ) (n : ℕ) (depth : ℕ) where
  | var : Fin n → AC0Mod m n depth
  | const : Bool → AC0Mod m n depth
  | and : List (AC0Mod m n (depth-1)) → AC0Mod m n depth
  | or : List (AC0Mod m n (depth-1)) → AC0Mod m n depth
  | not : AC0Mod m n (depth-1) → AC0Mod m n depth
  | modm : List (AC0Mod m n (depth-1)) → AC0Mod m n depth
    -- modm gates: output true iff sum of inputs ≡ 0 (mod m)

-- Separation conjecture
theorem ac0_6_not_equals_np :
  ∃ f : (Fin n → Bool) → Bool,
    (f ∈ NP) ∧
    (∀ d : ℕ, ∀ C : AC0Mod 6 n d,
      size C < 2^(n^(1/d)) → ¬(agrees C f)) := by sorry
```

### Success Probability Estimate: 10-20%

**Reasoning**:
- **10%**: Proving new separation results (major result)
- **15%**: Formalizing known separations for prime moduli
- **20%**: Exploring specific function examples and partial results

This problem touches on deep open questions in complexity theory. More likely Aristotle would formalize existing results than prove the main conjecture.

### Why Good for Aristotle
1. **Well-studied structure**: AC⁰ circuits are thoroughly understood
2. **Discrete and finite**: Bounded depth means finite problem instances
3. **Rich landscape**: Many subproblems and special cases to explore
4. **Historical context**: Razborov-Smolensky is a famous proof to formalize
5. **Lean complexity work**: Recent P vs NP formalization in Lean provides infrastructure

### References
- [Tight Correlation Bounds Between AC⁰ and TC⁰ (arXiv:2304.02770)](https://arxiv.org/abs/2304.02770)
- [AC⁰ Wikipedia](https://en.wikipedia.org/wiki/AC0)
- [Complexity Zoo: AC⁰[m]](https://complexityzoo.net/Complexity_Zoo:A)

---

## Problem 4: Threshold Circuit Lower Bounds for Specific Functions

### Problem Statement
Prove exponential lower bounds for bounded-depth threshold circuits computing specific functions like Inner Product, Disjointness, or other communication complexity functions.

**Current State**:
- **Inner Product**: Size 2^Ω(n/e^d) required for depth-d circuits [2023 result]
- **Disjointness (DISJ_n)**: Ω(n) lower bounds for restricted models
- **OPEN**: Improve depth-3 threshold circuit lower bounds
- **OPEN**: Prove exp(Ω̃(n^(2/5))) → exp(Ω̃(n^(1/2))) for depth-3 circuits

**Specific Targets**:
1. Improve Inner Product lower bounds for small depth (d=3,4,5)
2. Prove tight bounds for Disjointness in depth-3 TC⁰
3. Separate depth-d from depth-(d+1) threshold circuits with concrete functions

### Why Unsolved
Threshold circuits (with linear threshold gates) are more powerful than AC⁰ but proving lower bounds remains difficult. The connection to communication complexity and weight/energy constraints makes progress challenging.

### Interdisciplinary Connection
**Neural Networks**: Threshold circuits are essentially:
- Single-layer perceptrons (depth-1)
- Multi-layer neural networks (depth-d)
- Biological neural computation models

**Hardware Design**: Threshold gates relate to:
- Analog circuit design
- Neuromorphic computing
- Energy-efficient computation

### Recent Status (2023-2025)
- **2023 breakthrough**: Exponential lower bounds for sub-linear depth circuits using rank-based methods
- Depth-d vs depth-(d+1) separation proved for specific regimes (STOC 2023)
- Connection to communication matrices established

### Formalizability in Lean 4: HARD

**Why HARD**:
- **✓ Pros**:
  - Linear threshold functions have algebraic definition
  - Communication complexity functions are well-defined
  - Size/depth/weight measures are discrete

- **✗ Cons**:
  - Linear algebra over reals required
  - Weight and energy complexity need real analysis
  - Communication matrix rank requires sophisticated linear algebra
  - Approximation arguments are technical

**Lean 4 Formalization Sketch**:
```lean
-- Linear threshold gate
structure LTGate (n : ℕ) where
  weights : Fin n → ℝ
  threshold : ℝ

def ltgEval (g : LTGate n) (x : Fin n → Bool) : Bool :=
  (Finset.univ.sum fun i => if x i then g.weights i else 0) ≥ g.threshold

-- Threshold circuits
inductive ThresholdCircuit (n : ℕ) (depth : ℕ) where
  | var : Fin n → ThresholdCircuit n 0
  | ltgate : (k : ℕ) → (Fin k → ThresholdCircuit n (depth-1)) →
             LTGate k → ThresholdCircuit n depth

-- Inner product function
def innerProduct (x y : Fin n → Bool) : Bool :=
  (Finset.univ.filter fun i => x i ∧ y i).card % 2 = 1

-- Main theorem
theorem innerProduct_threshold_lower_bound (n d : ℕ) :
  ∀ C : ThresholdCircuit (2*n) d,
    (∀ x y, eval C (x ++ y) = innerProduct x y) →
    size C ≥ 2^(n / 2^d) := by sorry
```

### Success Probability Estimate: 15-25%

**Reasoning**:
- **15%**: Full proof of new lower bounds
- **20%**: Formalizing 2023 results for specific functions
- **25%**: Proving bounds for small concrete cases (n ≤ 10, d ≤ 3)

The recent 2023 breakthrough makes this timely. Formalization of concrete small cases could be tractable.

### Why Good for Aristotle
1. **Recent progress**: 2023 results show tractability
2. **Concrete functions**: Inner product, disjointness are simple to define
3. **Small instances verifiable**: Can check n=5,6,7 computationally
4. **Multiple techniques**: Rank method, communication complexity, algebraic methods
5. **Practical relevance**: Neural network theory connection

### References
- [Exponential Lower Bounds for Threshold Circuits (arXiv:2107.00223)](https://arxiv.org/abs/2107.00223)
- [Depth-d Threshold Circuits vs AND-OR Trees (STOC 2023)](https://dl.acm.org/doi/10.1145/3564246.3585216)
- [ECCC TR16-121](https://eccc.weizmann.ac.il/report/2016/121/)

---

## Problem 5: Communication Complexity Lower Bounds for Collision Problems

### Problem Statement
Improve randomized communication complexity lower bounds for the collision detection problem and related problems.

**Current State**:
- **Collision**: Ω̃(N^(1/4)) randomized lower bound [2023]
- **Previous**: Ω̃(N^(1/12)) [Göös-Jain 2022]
- **OPEN**: Improve to Ω̃(N^(1/3)) or prove matching upper bound
- **OPEN**: Resolve gaps for related problems (element distinctness, set disjointness variants)

**Problem Setup**:
Alice and Bob each receive k uniformly random sets of size ~√N. They must determine if their sets have a collision (same element appearing in both).

**Specific Targets**:
1. Improve collision lower bound from N^(1/4) to N^(1/3)
2. Prove tight bounds for k-collision (≥k common elements)
3. Extend techniques to other randomized communication problems

### Why Unsolved
Randomized communication lower bounds are notoriously difficult. The collision problem has seen steady progress (N^(1/12) → N^(1/4) in 2023), suggesting the problem is tractable but not yet fully understood.

### Interdisciplinary Connection
**Streaming Algorithms**: Collision detection relates to:
- Approximate distinct elements counting
- Frequency moment estimation (F₀, F₂)
- Graph stream processing

**Cryptography**: Communication complexity lower bounds imply:
- Lower bounds for secure two-party computation
- Information-theoretic security limits
- Zero-knowledge proof complexity

**Database Theory**: Applications to:
- Distributed query processing
- Join size estimation
- Sampling algorithms

### Recent Status (2023-2025)
- **2023 breakthrough**: Ω̃(N^(1/4)) lower bound proved [ECCC TR23-159]
- Query-to-communication lifting extended to randomized setting (2024)
- Approximate degree lower bounds Ω(n/log²n) for related problems (2023)

### Formalizability in Lean 4: MEDIUM

**Why MEDIUM**:
- **✓ Pros**:
  - Communication protocols have clean formal definition
  - Finite number of bits exchanged
  - Probability theory well-developed in Mathlib4
  - Information theory basics available

- **✗ Cons**:
  - Randomized protocols require probability formalization
  - Lower bound techniques use information theory
  - Distributional arguments can be technical

**Lean 4 Formalization Sketch**:
```lean
-- Communication protocol
inductive Protocol (A_input B_input : Type) where
  | alice_speaks : (A_input → Bool) → (Bool → Protocol A_input B_input) → Protocol A_input B_input
  | bob_speaks : (B_input → Bool) → (Bool → Protocol A_input B_input) → Protocol A_input B_input
  | output : Bool → Protocol A_input B_input

-- Communication cost
def cost : Protocol A B → ℕ
  | .alice_speaks _ next => 1 + (max (cost (next true)) (cost (next false)))
  | .bob_speaks _ next => 1 + (max (cost (next true)) (cost (next false)))
  | .output _ => 0

-- Collision problem
def hasCollision (A_sets B_sets : Fin k → Finset (Fin N)) : Bool :=
  ∃ i j, (A_sets i ∩ B_sets j).Nonempty

-- Main theorem
theorem collision_comm_lower_bound (N k : ℕ) (ε : ℝ) :
  ∀ P : Protocol (Fin k → Finset (Fin N)) (Fin k → Finset (Fin N)),
    (prob_correct P hasCollision ≥ 2/3) →
    expected_cost P ≥ (N^(1/4) / log N) := by sorry
```

### Success Probability Estimate: 20-30%

**Reasoning**:
- **20%**: Proving improved bounds (significant breakthrough)
- **25%**: Formalizing the 2023 N^(1/4) result
- **30%**: Proving bounds for simplified variants or small parameters

The steady progress (2022 → 2023 improvement) suggests the problem is active and tractable. Formalization of recent results is very achievable.

### Why Good for Aristotle
1. **Recent breakthrough**: 2023 result is fresh and formalize-able
2. **Finite problem**: Can formalize exact problem for small N
3. **Clear structure**: Communication protocols are well-defined
4. **Practical importance**: Streaming algorithms connection
5. **Multiple approaches**: Information theory, Fourier analysis, discrepancy

### References
- [Communication Lower Bounds for Collision (ECCC TR23-159)](https://eccc.weizmann.ac.il/report/2023/159/)
- [Query-to-Communication Lifting (ECCC TR24-199)](https://eccc.weizmann.ac.il/report/2024/199/)
- [Approximate Degree Lower Bounds (ECCC TR23-024)](https://eccc.weizmann.ac.il/report/2023/024/)

---

## Problem 6: Derandomization of Arthur-Merlin Protocols

### Problem Statement
Prove or disprove that efficient derandomization of Arthur-Merlin protocols implies circuit lower bounds.

**Current State**:
- **Known**: If every AM protocol running in time n^c can only compute f correctly on finitely many inputs, then AM ⊆ NP
- **Known**: Refuting low-space probabilistic streaming ≡ prBPP = prP [Chen-Tell-Williams 2023]
- **OPEN**: What hardness assumptions are necessary and sufficient for AM derandomization?
- **OPEN**: Can we derandomize AM without pseudorandom generators?

**Specific Targets**:
1. Prove AM ⊆ NP under explicit hardness assumptions
2. Show derandomization implies circuit lower bounds for specific classes
3. Characterize the minimal assumptions needed

### Why Unsolved
The equivalence between derandomization and circuit lower bounds is a deep connection in complexity theory. Progress requires understanding both pseudorandomness and hardness amplification.

### Interdisciplinary Connection
**Algorithm Design**: AM protocols model:
- Interactive proofs in distributed systems
- Randomized verification algorithms
- Probabilistic proof checking

**Cryptography**: Derandomization relates to:
- Pseudorandom generators from one-way functions
- Hardness amplification
- Extractors and dispersers

**Proof Complexity**: AM derandomization connects to:
- Proof verification
- PCP theorem
- Interactive oracle proofs

### Recent Status (2023-2025)
- **2023**: Near-equivalence between hardness and derandomization in AM setting established
- **2023**: Derandomization vs refutation equivalence proved
- **2024**: BPL derandomization barriers identified
- Active research area with multiple 2023-2024 papers

### Formalizability in Lean 4: HARD

**Why HARD**:
- **✓ Pros**:
  - AM protocols have formal definition
  - Circuit complexity classes being formalized in Lean
  - Turing machines formalized in Mathlib

- **✗ Cons**:
  - Requires probabilistic computation formalization
  - Hardness assumptions are sophisticated
  - Pseudorandom generators need extensive infrastructure
  - Reduction proofs are very technical

**Lean 4 Formalization Sketch**:
```lean
-- Arthur-Merlin protocol
structure AMProtocol where
  verifier : ℕ → List Bool → List Bool → Bool
  time_bound : ℕ → ℕ

-- AM complexity class
def AM : Set (ℕ → Bool) :=
  {f | ∃ P : AMProtocol, ∀ x,
    f x = true → prob (∃ witness, P.verifier (encode x) (random) witness) ≥ 2/3 ∧
    f x = false → prob (∃ witness, P.verifier (encode x) (random) witness) ≤ 1/3}

-- Main conjecture
theorem am_derandomization_implies_lower_bounds :
  (∀ f ∈ AM, ∃ alg : ℕ → Bool, alg = f ∧ alg ∈ NP) →
  (∃ f : ℕ → Bool, ∀ C : Circuit, size C < 2^(n^(1/10)) → ¬(C computes f)) := by sorry
```

### Success Probability Estimate: 10-20%

**Reasoning**:
- **10%**: Proving main implications (very hard)
- **15%**: Formalizing existing equivalences from 2023 papers
- **20%**: Formalizing definitions and basic properties

This is deep theory requiring extensive infrastructure. More suitable as a long-term formalization project than a novel proof target.

### Why Good for Aristotle
1. **Rich theory**: Multiple 2023 results to formalize
2. **Clear definitions**: AM, BPP, NP are well-defined
3. **Important connections**: Links derandomization and lower bounds
4. **Modular structure**: Can formalize pieces independently
5. **Lean infrastructure**: Recent P vs NP formalization provides foundation

### References
- [Derandomization via Complexity Theory (ECCC TR23-094)](https://eccc.weizmann.ac.il/report/2023/094/)
- [Derandomization vs Refutation (ECCC TR23-105)](https://eccc.weizmann.ac.il/report/2023/105/)
- [Derandomizing Space-Bounded Computation](https://williamhoza.com/teaching/winter2025-derandomizing-space-bounded-computation/)

---

## Problem 7: Tensor Rank Lower Bounds for Explicit Matrices

### Problem Statement
Construct explicit matrices/tensors with provably high tensor rank, particularly focusing on determinant and permanent computations.

**Current State**:
- **Recent breakthrough**: Explicit tensor with superlinear rank [Björklund-Kaski, Pratt, STOC 2024]
- **Determinant**: Rank ≤ n-th Bell number; rank ≥ ? (lower bounds weak)
- **4×4 determinant over F₂**: Rank = exactly 12 [2024]
- **OPEN**: Prove tight bounds for n×n determinant for general n
- **OPEN**: Separate tensor rank from border rank

**Specific Targets**:
1. Prove tight tensor rank bounds for 5×5, 6×6 determinants
2. Improve lower bounds for permanent
3. Characterize rank over different fields

### Why Unsolved
Tensor rank is notoriously difficult to compute and bound. Even small cases (3×3, 4×4) required substantial effort. The 2024 breakthrough shows the area is active.

### Interdisciplinary Connection
**Quantum Computing**: Tensor networks relate to:
- Quantum circuit simulation
- Entanglement entropy
- Tensor network states

**Machine Learning**: Tensor decompositions used in:
- Deep learning optimization
- Tensor regression
- Multi-way data analysis

**Algebraic Complexity**: Tensor rank bounds imply:
- Matrix multiplication complexity
- Arithmetic circuit lower bounds
- Algebraic formula size

### Recent Status (2023-2025)
- **STOC 2024 breakthrough**: Explicit superlinear rank tensor constructed
- 4×4 determinant over F₂ rank determined exactly (2024)
- Border rank lower bounds improved (2024)
- Conditional lower bounds under NSETH (2024)

### Formalizability in Lean 4: MEDIUM-HARD

**Why MEDIUM-HARD**:
- **✓ Pros**:
  - Tensor rank has clean algebraic definition
  - Determinant well-defined in Mathlib
  - Finite field arithmetic supported
  - Linear algebra infrastructure mature

- **✗ Cons**:
  - Tensor rank optimization is complex
  - Border rank requires limits
  - Lower bound techniques are sophisticated

**Lean 4 Formalization Sketch**:
```lean
-- Tensor rank
def tensorRank {F : Type*} [Field F] (T : Fin n → Fin n → Fin n → F) : ℕ :=
  sInf {r | ∃ (a : Fin r → Fin n → F) (b : Fin r → Fin n → F) (c : Fin r → Fin n → F),
    ∀ i j k, T i j k = ∑ t, a t i * b t j * c t k}

-- Determinant tensor
def detTensor (n : ℕ) : Fin n → Fin n → Fin n → F :=
  fun i j k => if k = 0 then Matrix.det (standardBasis i j)
               else 0  -- Simplified encoding

-- Main theorem (small case)
theorem det_4x4_rank_f2 :
  tensorRank (detTensor 4 : Fin 4 → Fin 4 → Fin 4 → ZMod 2) = 12 := by sorry

-- General bound
theorem det_tensor_rank_upper_bound (n : ℕ) :
  tensorRank (detTensor n) ≤ bell n := by sorry
```

### Success Probability Estimate: 25-40%

**Reasoning**:
- **25%**: Proving new bounds for n≥5
- **35%**: Formalizing the 4×4 determinant F₂ result
- **40%**: Proving bounds for small specific cases

The 2024 results on small cases and the exact 4×4 result suggest concrete formalization is very achievable. This is one of the most tractable problems on this list.

### Why Good for Aristotle
1. **Recent concrete results**: 4×4 case solved in 2024
2. **Finite and computable**: Can verify small cases computationally
3. **Clean algebraic structure**: Pure linear algebra
4. **Multiple fields**: Can explore F₂, F₃, ℚ, ℝ separately
5. **Incremental progress**: Can tackle 3×3, 4×4, 5×5 sequentially

### References
- [Conditional Complexity Hardness (arXiv:2411.02936)](https://arxiv.org/abs/2411.02936)
- [Border Rank Lower Bounds (arXiv:2508.17845)](https://arxiv.org/abs/2508.17845)
- [ECCC: Tensor Rank](https://eccc.weizmann.ac.il/keyword/17599/)
- [Tensor Rank: Lower and Upper Bounds (arXiv:1102.0072)](https://arxiv.org/abs/1102.0072)

---

## Summary Table: Problem Comparison

| Problem | Formalizability | Success Prob | Recent Activity | Impact |
|---------|----------------|--------------|-----------------|---------|
| **Formula Size (Majority)** | MEDIUM | 5-15% | Active 2019 | High - hardware, algorithms |
| **Monotone Circuits** | MEDIUM-HARD | 20-35% | **2025 breakthrough** | High - proof complexity |
| **AC⁰[6] Separation** | MEDIUM | 10-20% | Active 2023-24 | Very High - complexity theory |
| **Threshold Circuits** | HARD | 15-25% | **2023 breakthrough** | High - neural networks |
| **Collision Communication** | MEDIUM | 20-30% | **2023 breakthrough** | High - streaming algorithms |
| **AM Derandomization** | HARD | 10-20% | Very active 2023 | Very High - complexity theory |
| **Tensor Rank** | MEDIUM-HARD | 25-40% | **2024 breakthrough** | High - quantum, ML |

---

## Recommendations for Aristotle

### Tier 1: Highest Priority (Most Tractable)
1. **Tensor Rank (4×4 determinant)** - Concrete 2024 result, finite case, pure algebra
2. **Collision Communication** - 2023 breakthrough, clean formalization target
3. **Monotone Circuits** - 2025 breakthrough, natural graph problems

### Tier 2: Medium Priority (Good Targets)
4. **Formula Size Bounds** - Clean discrete structure, incremental progress possible
5. **Threshold Circuits (small depth)** - Recent 2023 results, concrete functions

### Tier 3: Long-term (Infrastructure Building)
6. **AC⁰[6] Separation** - Requires extensive circuit complexity infrastructure
7. **AM Derandomization** - Deep theory, better as formalization project

---

## Why These Problems Avoid Known Barriers

### P vs NP Barrier
These problems focus on **restricted models** (bounded-depth, monotone, specific functions) rather than general P vs NP, avoiding the Razborov-Rudich natural proofs barrier.

### Natural Proofs Barrier
Several problems explicitly use **non-natural techniques**:
- Monotone circuits: Approximation method (Razborov)
- AC⁰: Polynomial method (Razborov-Smolensky)
- Communication: Information theory (doesn't apply to circuits directly)

### Algebrization Barrier
Tensor rank and communication problems operate in **different computational models** where algebrization doesn't apply.

### Relativization Barrier
All problems focus on **specific functions** and **concrete bounds**, not oracle-dependent separations.

---

## Formalization Strategy for Aristotle

### Phase 1: Infrastructure (Weeks 1-2)
1. Formalize circuit models (De Morgan, monotone, AC⁰, threshold)
2. Define size, depth, weight complexity measures
3. Implement basic functions (majority, inner product, collision)

### Phase 2: Classical Results (Weeks 3-4)
4. Formalize Razborov's monotone technique
5. Formalize Smolensky's AC⁰[p] separation for primes
6. Prove small concrete cases computationally

### Phase 3: Recent Breakthroughs (Weeks 5-8)
7. Target: 4×4 determinant tensor rank over F₂
8. Target: Collision communication N^(1/4) lower bound
9. Target: Perfect matching monotone circuit (if tractable)

### Phase 4: Novel Results (Weeks 9+)
10. Attempt improvements for small parameters
11. Explore restricted variants
12. Generalize techniques to related problems

---

## Conclusion

Circuit complexity offers a rich landscape of **tractable, provable problems** suitable for automated theorem proving. The **2023-2025 breakthroughs** in monotone circuits, threshold circuits, collision communication, and tensor rank demonstrate these problems are:

1. **Actively solvable** (not permanently stuck)
2. **Finitely formulate-able** (bounded parameters)
3. **Computationally verifiable** (small cases)
4. **Interdisciplinary** (CS, crypto, algorithms, ML, quantum)
5. **High-impact** (advance multiple fields)

**Best bet for Aristotle success**: Start with **Tensor Rank (4×4 determinant)** as warm-up, then tackle **Collision Communication (2023 result)**, building toward **Monotone Circuits (2025 perfect matching)**.

The field is alive with recent breakthroughs, suggesting these problems are at the frontier of tractability - perfect for AI-assisted theorem proving.
