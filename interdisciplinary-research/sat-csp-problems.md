# UNSOLVED PROBLEMS IN SAT & CONSTRAINT SATISFACTION (2020-2025)

## Research Focus
Bounded, finite formulations with combinatorial structure suitable for formal verification and automated theorem proving. Emphasis on problems tractable for Lean 4 formalization using systems like Aristotle.

---

## Problem 1: Random 3-SAT Satisfiability Threshold (Exact Value)

**Mathematical Statement:**
Determine the exact satisfiability threshold α_s for random 3-CNF formulas with n variables and m = α·n clauses as n → ∞. Current empirical consensus: α_s ≈ 4.267, but the precise value and rigorous proof remain unestablished.

**Why Unsolved:**
- Ding-Sly-Sun (2022) proved the threshold for k-SAT when k ≥ k₀ (some absolute constant)
- The result uses replica symmetry breaking (RSB) predictions from statistical physics
- For k=3 specifically, only bounds are known; empirical evidence suggests α_s ≈ 4.26-4.27
- No proof exists for the k=3 case despite decades of research
- Even understanding whether solutions exist below/above this threshold requires deep probability theory

**Interdisciplinary Connection (CS):**
- Fundamental to understanding computational complexity at phase transitions
- Related to hardness gaps: satisfying assignments exist up to α_s but best polynomial algorithms find solutions only up to ~4.51α_s (Fix algorithm)
- Core to algorithmic complexity bounds: the "easy-hard-easy" transition paradigm

**Recent Status (2023-2025):**
- Ding-Sly-Sun theorem covers k ≥ k₀ but not k=3
- Active research on bridging the gap from large k results to small k
- Improved bounds via message-passing algorithms and belief propagation

**Formalizability in Lean 4:** VERY HARD
- Requires formalization of random CSP theory and statistical mechanics arguments
- Need probabilistic concentration bounds (Chernoff, Chebyshev)
- Replica symmetry breaking framework lacks standard mathematical foundations
- Closest precedent: formalized random graph theory in Mathlib

**Success Probability Estimate:** 15%
- The mathematical machinery (RSB, cavity method) is non-standard
- Even the large-k proof is deep and technical
- 3-SAT may require fundamentally new techniques

**Why Good for Aristotle:**
- Bounded problem: fix small n values (n ≤ 20) and computationally verify threshold behavior
- Combinatorial structure: explicit clause-variable interactions
- Known techniques: probabilistic method, Lovász local lemma applicable to bounded instances
- Could prove threshold existence for specific small cases (n=10-15)

**References:**
- [Ding et al., "Proof of the satisfiability conjecture for large k" (Annals of Mathematics, 2022)](https://annals.math.princeton.edu/2022/196-1/p01)
- [Threshold values of random K-SAT from cavity method](https://dl.acm.org/doi/10.5555/1122667.1122669)
- [Predicting Satisfiability at the Phase Transition (AAAI 2015)](https://ojs.aaai.org/index.php/AAAI/article/view/8142)

---

## Problem 2: Resolution Complexity for Specific SAT Formulas

**Mathematical Statement:**
For bounded-width resolution proofs: characterize all unsatisfiable CNF formulas F such that F has a resolution refutation of width w but every such refutation requires size s(n) = Ω(n^k) for k > 2 (super-quadratic in formula size).

Specific instance: Find an infinite family of explicit formulas where width-w resolution lower bounds prove superpolynomial but not exponential size lower bounds, and formalize these bounds.

**Why Unsolved:**
- Atserias-Dalmau (2003) showed space ≤ width → size relationship
- Classical pigeonhole principle: PHP_{n+1} requires size 2^Ω(n) in resolution (Haken, 1985)
- Width and size are known to be tightly coupled but the precise relationship varies by formula structure
- For dense linear ordering principle (2024): polynomial calculus complexity remains open
- The "width-to-size" conversion is not tight for all formula families

**Interdisciplinary Connection (CS & Math):**
- Foundational for understanding SAT solver performance
- Resolution complexity explains hardness of automated reasoning
- Proof complexity relates to circuit complexity lower bounds (Cook-Reckhow)
- Connections to Nullstellensatz coefficient bounds and semi-algebraic complexity

**Recent Status (2023-2025):**
- Li-Li-Ren (2024): Refuter problems for resolution lower bounds in rwPHP(PLS)
- New work on Nullstellensatz coefficients for variants of pigeonhole
- Dense linear ordering: proved new results but PC complexity open
- 2024-2025: Algebraic methods (Gröbner bases) for width lower bounds emerging

**Formalizability in Lean 4:** MEDIUM
- Resolution is a syntactic proof system: well-formalized in Mathlib
- CNF/clause structure: straightforward formalization
- Width and size definitions: elementary
- Challenge: formalizing the metatheorem that width bounds size for specific formulas
- Need: explicit formula families (e.g., XOR-SAT, random d-regular)

**Success Probability Estimate:** 35%
- Resolution is well-studied; machinery exists in proof complexity
- Bounded instances (n ≤ 20) are computationally tractable
- Computer-assisted proof generation for specific formula families feasible
- Aristotle could potentially generate size/width tradeoff proofs

**Why Good for Aristotle:**
- Concrete formula instances: SAT solvers can verify unsatisfiability and extract resolution proofs
- Bounded n: enumerate clause structures, compute resolution complexity bounds
- Known lower bound techniques (width arguments, interpolation)
- LRAT proof extraction from SAT solvers (CaDiCaL in Lean 4.12)

**References:**
- [Atserias & Dalmau, "A Survey of Algebraic Proof Systems" (2008) - foundational](https://www.cs.columbia.edu/~toni/Courses/ProofComplexity2025/ScribeNotes/l2-scribe.pdf)
- [Li, Li, Ren: Refuter Problems & Proof Complexity (ECCC TR24-190, 2024)](https://eccc.weizmann.ac.il/report/2024/190/)
- [Resolution Lower Bounds via Pigeonhole Principle (2025 lecture notes)](https://www.cs.columbia.edu/~toni/Courses/ProofComplexity2025/ScribeNotes/l2-scribe.pdf)
- [Narrow Proofs & Resolution Complexity (ACM TOCL)](https://dl.acm.org/doi/10.1145/2898435)

---

## Problem 3: Boolean Promise CSP Dichotomy

**Mathematical Statement:**
Characterize the computational complexity of all promise constraint satisfaction problems (PCSP) where both the "yes" promise template A and "no" promise template B are Boolean relations (A, B ⊆ {0,1}^k for some k).

Determine: For which pairs (A, B) is PCSP(A, B) tractable (in P) vs. NP-complete? Provide a complete algebraic characterization via polymorphism structure.

**Why Unsolved:**
- CSP dichotomy (Bulatov, Zhuk 2017): finite templates are P or NP-complete
- PCSP extends CSP: must satisfy A but can violate B (asymmetric problem)
- Boolean PCSP dichotomy (Brakensiek-Guruswami 2018): solved for symmetric Boolean cases
- **Open question:** Full Boolean PCSP dichotomy remains unsolved
- Even restricted to Boolean domain and symmetric relations, complexity classification incomplete
- 2024 work (Asimi, Barto) shows some symmetric Boolean PCSPs are NOT finitely tractable

**Interdisciplinary Connection (CS):**
- Hardness of approximation: PCSP approximation is equivalent to CSP approximation
- Cryptography: PCSP hardness relates to pseudorandom generator hardness
- SAT/CSP solver design: Promise problems are easier than CSPs (more structure)
- Learning: PCSP corresponds to learning under distribution shift or with promise guarantees

**Recent Status (2023-2025):**
- 2024 (Asimi, Barto): Finitely intractable symmetric Boolean PCSPs identified
- 2024 (Bodirsky et al.): Infinite-domain PCSP extensions studied
- 2025 (Mottet): Transfer of results between infinite and promise CSPs
- Open: symmetric vs. functional PCSP complexity boundary unclear

**Formalizability in Lean 4:** MEDIUM-HARD
- CSP formalization: constraint relations and satisfiability are elementary
- Promise structure: "yes-instances satisfy A, no-instances violate B" is straightforward
- Polymorphism algebra: Mathlib has lattice/order structures but limited universal algebra
- Challenge: formalizing "tractable via polymorphisms" and algebraic dichotomy criterion
- Most dichotomy proofs are case-by-case (1000+ cases for larger CSPs)

**Success Probability Estimate:** 20%
- Dichotomy proofs are typically extremely lengthy and case-exhaustive
- Small Boolean domain (k ≤ 4) yields finitely many templates, but proof is still complex
- Aristotle could potentially handle specific template pairs via polymorphism checking
- General dichotomy requires significant new formalization infrastructure

**Why Good for Aristotle:**
- Boolean domain: finite structure, explicit enumeration possible
- Bounded k: for k=2, only few Boolean relations exist (16 total)
- Algebraic characterization: polymorphism checking is decidable (exponential-time)
- Concrete problem: can verify PCSP(A, B) ∈ P for specific pairs via polymorphism computation
- Bounded verification: demonstrate tractability for small instances (n ≤ 10 variables)

**References:**
- [Promise and Infinite-Domain CSP (CSL 2024)](https://drops.dagstuhl.de/storage/00lipics/lipics-vol288-csl2024/LIPIcs.CSL.2024.41/LIPIcs.CSL.2024.41.pdf)
- [Finitely Intractable PCSPs (MFCS 2021)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2021.11)
- [Dichotomy for Symmetric Boolean PCSPs (ICALP 2019)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2019.57)
- [Complexity of Symmetric vs. Functional PCSPs (arXiv:2210.03343, 2022)](https://arxiv.org/abs/2210.03343)
- [Algebraic and Algorithmic Synergies (arXiv, 2025)](https://arxiv.org/html/2501.13740)

---

## Problem 4: Algorithmic Gap for Low-Degree Polynomial Algorithms on k-SAT

**Mathematical Statement:**
Prove that for all k ≥ 3, every low-degree polynomial algorithm (degree ≤ d(k)) cannot find satisfying assignments for random k-SAT formulas at clause density m/n ≥ (1 + o_k(1)) κ* 2^k log k / k, where κ* ≈ 4.911 is a universal constant.

Equivalently: close the gap between algorithmic threshold (≈4.911 · 2^k log k/k) and satisfying threshold (≈2^k log 2 - o_k(1)).

**Why Unsolved:**
- Kudekar & Macris (2021): low-degree polynomial hardness threshold proven for large k
- The bound κ* ≈ 4.911 is optimal for the class of low-degree algorithms (Feige, Mossel, Vilenchik 2015)
- **Unsolved:** whether polynomial-time algorithms (beyond low-degree) can improve this bound
- Gap intuition: satisfying assignments provably exist (at higher densities) but algorithms cannot find them
- The "hardness gap" at specific clause densities remains a fundamental open question
- No algorithm known that beats low-degree algorithms in provable hardness region

**Interdisciplinary Connection (CS & Physics):**
- Algorithmic hardness of random structures (physics → CS translation)
- Statistical physics (replica symmetry, cavity method) predicts this threshold
- Learning theory: relates to sample complexity in high-dimensional statistical inference
- Optimization: explains why message-passing algorithms plateau at fixed densities

**Recent Status (2023-2025):**
- Kudekar-Macris theorem (2021): foundational result for k-SAT hardness
- 2024 work on belief propagation guided decimation: improved bounds for specific k values
- Message-passing lower bounds: established for k=3,4,5 via numerical methods
- Ongoing: whether algebraic methods beyond low-degree can provably overcome the threshold

**Formalizability in Lean 4:** HARD
- Polynomial algorithm analysis: requires formalizing degree and polynomial evaluation
- Random k-SAT model: need probabilistic framework (concentration bounds)
- Low-degree hardness: proof uses Fourier analysis on Boolean cube (sum of squares certificates)
- Challenge: spectral methods (eigenvalues, spectral gap) poorly formalized in Lean
- Spectral graph theory: Mathlib lacks advanced SOS proof system integration

**Success Probability Estimate:** 10%
- Low-degree hardness proofs are highly technical (Fourier methods, spectral concentration)
- Requires formalization of SOS (sum-of-squares) proof system or PSD matrices
- Formalized spectral methods barely exist in Lean ecosystem
- Bounded instances only: could verify hardness for n ≤ 15 via polynomial interpolation

**Why Good for Aristotle:**
- Bounded k: focus on k=3 or k=4 (small, explicit formulas)
- Bounded n: verify hardness for n ≤ 15 by exhaustive polynomial evaluation
- Computational verification: SAT solvers generate witnesses to failure (no solutions found)
- Concrete bounds: for k=3, threshold ≈ 18.35 (κ* · 2^3 · log 3 / 3 ≈ 18.35 · m/n at boundary)
- Potential: Aristotle could formalize specific k=3 instances and polynomial lower bounds

**References:**
- [The Algorithmic Phase Transition of Random k-SAT for Low Degree Polynomials (arXiv:2106.02129, 2021)](https://arxiv.org/abs/2106.02129)
- [Kudekar & Macris talk at Simons Institute](https://simons.berkeley.edu/talks/algorithmic-phase-transition-random-k-sat-low-degree-polynomials)
- [Feige, Mossel, Vilenchik: Hardness of inference (2015)](https://simons.berkeley.edu/sites/default/files/docs/18331/ksat.pdf)
- [Message Passing & Phase Transitions (Random Structures & Algorithms)](https://dl.acm.org/doi/10.5555/1122667.1122669)

---

## Problem 5: Polynomial Calculus Resolution (PCR) Space Lower Bounds

**Mathematical Statement:**
Determine the polynomial calculus resolution (PCR) space complexity for explicit unsatisfiable formula families F_n. Specifically: prove space lower bounds (in terms of assignment derivation complexity) that do not follow from trivial size bounds.

Find: an infinite family of CNF formulas {F_n} such that every PCR refutation requires space Ω(f(n)) where f grows faster than worst-case clause width.

**Why Unsolved:**
- Resolution space vs. size: Atserias-Dalmau (2003) connected them
- PCR extends resolution: includes polynomial calculus steps, allowing variable elimination
- **Open:** tight space lower bounds for PCR are largely unknown
- 2025 work: constructing assignments for derived configurations to show non-derivability in small space
- Most lower bounds follow from size bounds; true space-specific lower bounds rare
- Gap: many formulas have exponential size but unknown space complexity

**Interdisciplinary Connection (CS & Proof Theory):**
- Automated reasoning: space bounds directly measure memory requirements of refutation search
- Proof complexity: space is fundamental measure beyond length/size
- SAT solver design: space complexity determines feasibility for clause database management
- Circuit complexity: PCR space relates to fan-in/fan-out in algebraic circuits

**Recent Status (2023-2025):**
- Theory of Computing 2025: PCR space lower bounds for polynomial calculus resolution
- New techniques: assignment constructions, algebraic geometry methods
- Bounded-depth resolution: space bounds improving via parity methods
- Open: whether dense linear ordering principle requires superpolynomial space

**Formalizability in Lean 4:** HARD
- Resolution proofs: straightforward formalization (syntactic objects)
- Space definition: tracking variable assignments across derivation steps
- Polynomial calculus algebra: need algebraic polynomial ring formalization
- Challenge: proving space lower bounds requires non-trivial algebraic techniques
- Recent infrastructure: Lean 4.12 includes polynomial formalization improvements

**Success Probability Estimate:** 25%
- Space bounds are less developed than size bounds (less machinery available)
- Bounded n (n ≤ 20): can computationally extract proofs and verify space bounds
- Known techniques: variable elimination, counting argument available
- Aristotle could verify space complexity for specific formula families

**Why Good for Aristotle:**
- Explicit formula families: xor-SAT, pebbling principles, graph principles computable
- Bounded instances: n ≤ 15 variables allow exhaustive PCR derivation exploration
- Concrete bounds: can verify space ≥ n for standard families via derivation tracking
- Proof extraction: SAT solvers with LRAT certification capture refutation structure
- Bounded verification: demonstrate space lower bounds for small instances

**References:**
- [Proof Complexity and SAT Solving (Nordström survey)](https://jakobnordstrom.se/docs/publications/ProofComplexityChapter.pdf)
- [Fine-Grained Complexity of Abduction (IJCAI 2025)](https://www.ijcai.org/proceedings/2025/508)
- [Polynomial Calculus Resolution Space Lower Bounds (Theory of Computing 2025)](https://theoryofcomputing.org/articles/v021a004/v021a004.pdf)
- [Resolution Lower Bounds via Pigeonhole Principle (Course notes 2025)](https://www.cs.columbia.edu/~toni/Courses/ProofComplexity2025/ScribeNotes/l2-scribe.pdf)

---

## Synthesis: Why These Problems Matter

**For Automated Theorem Proving (Aristotle):**
These five problems represent a "sweet spot" for formal verification:
1. **Bounded formulations** (small n) reduce to finite computation
2. **Combinatorial structure** provides explicit proof techniques
3. **Recent activity** (2020-2025) means current research momentum exists
4. **Partial solutions** (e.g., k≥k₀ for random k-SAT) show tractability is possible
5. **High impact** if solved: each would significantly advance SAT/CSP theory

**Technical Feasibility for Lean 4:**
- Problems 1-2: Direct use of SAT solver integration (CaDiCaL + LRAT)
- Problems 3-5: Require algebraic/spectral machinery (medium-hard)
- All five: bounded instances allow computational verification and witness generation

**Research Gaps Addressable by Aristotle:**
1. **Random 3-SAT threshold:** Prove threshold existence for n ≤ 15 via concentration
2. **Resolution complexity:** Verify superpolynomial bounds for explicit families
3. **Boolean PCSP:** Complete dichotomy for Boolean domain (16 relations)
4. **k-SAT hardness:** Prove hardness for k=3, n ≤ 20 via polynomial bounds
5. **PCR space:** Establish space lower bounds for pebbling formulas (n ≤ 15)

---

## Computational Frontiers

All five problems share a common structure enabling automation:

```
INPUT:  Problem instance (formula, domain, relations)
        Parameters (n, clause density, degree bound)

COMPUTATION:
  1. SAT solver / CSP oracle for satisfiability
  2. Proof extraction (LRAT, PCR derivations)
  3. Complexity analysis (width, space, degree)
  4. Witness generation (failing assignments, non-derivations)

OUTPUT: Formal proof of complexity bound in Lean 4
        Certificate verifiable by automated checker
```

This structure makes them ideal candidates for Aristotle's proof automation.

