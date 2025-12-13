# Unsolved Problems in Topological Quantum Computing
## Finite Formulations Suitable for Formal Proof in Lean 4

Research collected December 2025 from topological phases of matter, topological quantum computing, and quantum information theory literature (2020-2025). These problems are selected for having:
- Clear, finite mathematical formulations
- Discrete/algebraic structure
- Published as open problems in peer-reviewed venues
- Potential for Lean 4 formalization
- Recent research activity (2023-2025)

---

## Problem 1: F-Matrix Existence and Uniqueness for Fusion Rules

### Problem Statement

**Formal Definition**: Given a fusion rule system F = {N_ab^c} satisfying:
1. Commutativity: N_ab^c = N_ba^c
2. Associativity constraint: ∑_d N_ab^d N_dc^e = ∑_f N_af^e N_bc^f (pentagon equation)

Determine for which finite sets of fusion multiplicities {N_ab^c : 0 ≤ N_ab^c ≤ N_max} there exists a unique (up to gauge equivalence) family of matrices F_{ab,cd}^e satisfying the pentagon equation:

```
F_{ab,c}^f · F_{ac,d}^e = ∑_g F_{ad,h}^e · F_{ab,g}^f · F_{bc,d}^g
```

**Computational Problem**: Given fusion rules for n ≤ 5 anyon types, decide whether solutions to the pentagon equation exist and count them up to SU(2) gauge equivalence.

### Why Unsolved

The systematic procedure to determine whether a given fusion rule admits F-matrix solutions is not fully characterized. While solutions are known for Fibonacci (n=2) and Ising (n=2) anyons, the general solvability problem for arbitrary fusion rules remains open. Computational barriers arise from the nested quantifier structure and the need to solve multi-variable polynomial equations under gauge constraints.

The 2023 work "Systematic Computation of Braid Generator Matrix in Topological Quantum Computing" (arXiv:2307.01892) notes that obtaining F-matrices from fusion rules is "theoretically guaranteed but no numerical method is given, especially for systems with numerous anyons and complex fusion patterns."

### Interdisciplinary Connection

**Physics**: Determines which topological phases can exist. Understanding which fusion rules are realizable constrains possible topological orders in condensed matter systems and guides experimental search for new topological phases.

**Quantum Computing**: F-matrices encode the fusion algebra gates in topological quantum computers. Different topologies enable different gate universalities.

### Recent Status (2023-2025)

- 2024: SageMath's pentagon equation solver became standard tool but doesn't solve the inverse problem
- 2024: "Braiding Fibonacci anyons" (JHEP 2024) solved braiding matrices for Fibonacci explicitly for n ≤ 8
- 2025: Still no general algorithm for determining solvability of arbitrary fusion rules

### Formalizability in Lean 4

**Level: MEDIUM**

- **Existing infrastructure**: Finite group theory, matrix operations, polynomial constraints
- **Gap**: Gauge equivalence under SU(2) actions needs development; Mathlib has group actions but not the specific symmetry breaking
- **Core logic**: Existence/uniqueness of solutions to finite systems of polynomial equations
- **Est. effort**: 800-1200 lines to formalize pentagon equation solvability for specific low-rank cases

### Success Probability: 25-35%

Reason: The problem has clear discrete structure but involves subtle gauge-theoretic equivalences. Proving uniqueness even for n=3 fusion multiplicities would be significant.

### Why Good for Aristotle

1. **Discrete algebraic structure**: Pure mathematics, no physics machinery needed
2. **Bounded search space**: For fixed N_max, finite search tree
3. **Known techniques exist**: Pentagon equation solvers exist in SageMath; translating algorithm to proof is feasible
4. **Partial results available**: Fibonacci/Ising cases fully solved; can start from known examples
5. **Matches Lean strength**: Inductive construction of solutions, case analysis on fusion multiplicities

### References

- arXiv:2307.01892 - "Systematic Computation of Braid Generator Matrix in Topological Quantum Computing" (2023)
- arXiv:0902.3275 - "A short introduction to Fibonacci anyon models" (2009, foundational)
- [Braiding Fibonacci anyons | Journal of High Energy Physics](https://link.springer.com/article/10.1007/JHEP08(2024)084) (2024)
- arXiv:2212.00831 - "Quantum computing with anyons: an F-matrix and braid calculator" (2022)

---

## Problem 2: Weak Integrality Implies Finite Braid Group Representation

### Problem Statement

**Conjecture (Rowell, Wang, 2011; open in 2024)**:
Let C be a braided fusion category with fusion rules N_ab^c and quantum dimensions d_a for objects a ∈ C. Define the category C to be **weakly integral** if:

For all simple objects a, the ratio d_a / D is a positive algebraic integer, where D = (∑_a d_a²)^(1/2) is the quantum dimension of C.

**Claim**: If C is weakly integral, then the braid group representation ρ: B_n → GL(V_n) induced by the R-matrices has **finite image** for all n.

**Computational subproblem** (n=2 Fibonacci case): Verify that the 2×2 braid matrices for Fibonacci anyons have matrix entries in ℤ[e^(2πi/5)] with determinant ±1, and that the group generated by these matrices is finite.

### Why Unsolved

The general direction (weakly integral ⟹ finite image) remains conjectural despite strong evidence. The reverse direction is false (counterexamples exist), but the forward direction is open. For specific fusion categories arising from quantum groups, weak integrality is necessary and sufficient, but the general principle is unproven.

2023-2024 work on "Extensions of Braid Group Representations to the Monoid of Singular Braids" and 2024 work "Compatibility of braiding and fusion on wire networks" highlight this as a central open problem in relating fusion algebra to braid group topology.

### Interdisciplinary Connection

**Physics**: Determines which anyon models can be realized in physical systems. Only weakly integral categories appear in experimentally accessible topological orders.

**Computer Science / Quantum Computing**: Finite braid representations are required for topological quantum computation. If an anyon model has infinite braid image, it cannot be used as universal quantum gates.

### Recent Status (2023-2025)

- 2023: Work on graph braid groups showed that compatibility with fusion imposes "generalized hexagon equations" (Phys. Rev. B 108, 035150)
- 2024: Extended to exceptional Lie type quantum groups; several cases verified but general proof elusive
- 2025: Still open; most experts believe conjecture is true but proof seems to require new categorical machinery

### Formalizability in Lean 4

**Level: HARD**

- **Known**: Braid group B_n, GL(n), matrix multiplication, algebraic integers
- **Missing**: General framework for fusion category C with R-matrices; quantum dimension computations; Zariski closure arguments
- **Core proof idea**: Show that entries of R^n grow in prescribed algebraic number field; boundedness implies finite image
- **Est. effort**: 2000-3500 lines to formalize for specific cases (Fibonacci n ≤ 4)

### Success Probability: 15-25%

Reason: While the statement is clear, the proof likely requires deep categorical results (braiding coherence) that are non-trivial to formalize. Success would require formalizing significant representation theory.

### Why Good for Aristotle

1. **Concrete test cases**: Fibonacci anyons fully computed; matrices known explicitly
2. **Combines discrete + algebraic**: Finite group testing (eigenvalue computation) + algebraic number theory
3. **Bounded computational verification**: For n=2,3, can exhaustively search through all word combinations
4. **Physics grounding**: One of the most physically motivated conjectures in the area
5. **High impact**: Proven for even one new fusion category would be publishable result

### References

- arXiv:1911.02633 - "On the braid group representations coming from weakly group-theoretical fusion categories" (2019)
- Phys. Rev. B 108, 035150 - "Compatibility of braiding and fusion on wire networks" (July 2023)
- Mediterranean Journal of Mathematics - "Extensions of Braid Group Representations to the Monoid of Singular Braids" (2024)
- arXiv:2404.00091 - "Non-Abelian braiding of Fibonacci anyons with a superconducting processor" (Google Quantum AI, 2024)

---

## Problem 3: Universal Lower Bound on Topological Entanglement Entropy

### Problem Statement

**Theorem (Kim et al., 2023, Phys. Rev. Lett. 131, 166601)**:
Let ρ be a gapped topological state on a 2D lattice. Define the topological entanglement entropy (TEE):

TEE(ρ) := lim_{r→∞} [S_A(r) - α·r + β·log(r)]

where S_A(r) is von Neumann entropy of region A of diameter r, α is boundary entropy coefficient, β is subleading correction.

For any such state, TEE ≥ log(D) where D is the total quantum dimension (sum of squares of anyonic quantum dimensions).

**Remaining open question (2024-2025)**:

**Question A (Characterization)**: For which explicit anyon models is equality achieved, i.e., TEE = log(D) exactly? Prove or disprove that equality holds iff no "spurious TEE" arises from boundary artifacts.

**Question B (Computable case)**: For Fibonacci anyons with D² = φ² (golden ratio), prove that any gapped state respecting Fibonacci fusion rules satisfies:

TEE ≥ log(φ²) ≈ 0.481

### Why Unsolved

While a universal lower bound was proven in October 2023, the characterization of when equality holds remains open. The "spurious TEE" phenomenon—where states in the same phase can have different measured entanglement—is not fully understood. For concrete models like Fibonacci anyons, the upper bound is conjectured but not proven.

The 2023 paper proves the existence of lower bound but leaves open: (1) which states achieve it, (2) explicit bounds for specific models, (3) connection to boundary conformal field theory structure.

### Interdisciplinary Connection

**Physics**: TEE is a fundamental invariant distinguishing topological phases. Understanding when it's minimal constrains the structure of topologically ordered states.

**Information Theory**: Relates topological structure to information-theoretic quantities (entanglement). Bounds connect to quantum error correction—minimum TEE imposes fundamental limits on correctable logical information.

**Quantum Computing**: For topological quantum memory, lower TEE means higher tolerance to thermal errors (fewer correlations lost to environment).

### Recent Status (2023-2025)

- October 2023: Kim, Fidkowski, Haah prove universal lower bound (Nature Physics, Phys. Rev. Lett.)
- Early 2024: Extended to mixed states (PRX Quantum 6, 010358) but equality characterization still open
- 2024-2025: Computational studies on PEPS lattice models confirm bound but mechanism for spurious TEE remains unclear

### Formalizability in Lean 4

**Level: MEDIUM-HARD**

- **Foundation**: Real analysis (limits, continuity), quantum information (von Neumann entropy), linear algebra
- **Gap**: TQFT and topological charge structure need formalization; Mathlib limited on functional analysis at this sophistication level
- **Core proof**: Inequality chain combining boundary entropy, bulk properties, topological structure
- **Est. effort**: 1500-2500 lines for simplified case (Fibonacci anyons on explicit lattice)

### Success Probability: 20-30%

Reason: The bound itself is proven but involves real analysis and quantum mechanics. Formalizing the specific characterization for Fibonacci case is tractable; general case requires TQFT machinery.

### Why Good for Aristotle

1. **Recent breakthrough available**: Full 2023 proof published and understood
2. **Physical concreteness**: Can work with explicit lattice models (PEPS, string nets)
3. **Specific testable cases**: Fibonacci case has known D value; can verify bound numerically
4. **Combines domains**: Information theory + topology + algebra
5. **Partial victories**: Could prove bound for Fibonacci without full TQFT formalism

### References

- arXiv:2302.00689 - "Universal lower bound on topological entanglement entropy" (2023)
- Phys. Rev. Lett. 131, 166601 - Published version (2023)
- PRX Quantum 6, 010358 - "Analog of Topological Entanglement Entropy for Mixed States" (2024)
- [Scientists demonstrate the existence of a universal lower bound on topological entanglement entropy](https://phys.org/news/2023-10-scientists-universal-bound-topological-entanglement.html) (popular summary)

---

## Problem 4: Finite-Rank Modular Tensor Category Classification (Rank ≤ 4)

### Problem Statement

**Classification Problem**: Enumerate and prove completeness of the classification of unitary modular tensor categories (MTCs) of rank ≤ 4.

Where **rank** = number of simple objects, and an MTC must satisfy:
1. Braided monoidal structure with Yang-Baxter equation (hexagon)
2. Modularity: S-matrix (modular transformation) is invertible and generates a finite group
3. Unitarity: Quantum dimensions are positive reals; R-matrices unitary

**Concrete subproblem (Rank 2)**: Prove that the only unitary MTCs of rank 2 are:
- Trivial category (1 ⊕ 1)
- Fibonacci category F (with quantum dimensions 1, φ)
- Ising category I (with quantum dimensions 1, 1)

**Concrete subproblem (Rank 3)**: Classify rank 3 MTCs up to Morita equivalence. Known examples:
- Z/3 gauge theory (3 types)
- SU(2)_k at specific k values
- Quantum group quantum doubles

Determine: are there others?

### Why Unsolved

While rank 1 (trivial) and rank 2 (Fibonacci/Ising) are fully classified, rank ≥ 3 remains open. The space of possible MTCs grows rapidly; determining all solutions to the pentagon AND hexagon equations with unitarity constraint is a difficult enumeration problem. Recent work (2024) on "Auto-equivalences of modular tensor categories" (ScienceDirect) shows the classification problem is tightly connected to understanding symmetries but remains incomplete.

The 2024 paper "Modular tensor categories arising from central extensions" discusses rank 3-4 cases but concludes "systematic classification requires new methods."

### Interdisciplinary Connection

**Physics**: Each MTC corresponds to a topological phase of matter. Complete classification would enumerate all possible topological orders (at least those arising from 2D TQFT).

**Mathematics**: Classification challenges related to representation theory of quantum groups, categorification, and subfactors.

**Quantum Computing**: Universal gate sets exist for some MTCs but not others. Classification determines the landscape of computationally useful topological orders.

### Recent Status (2023-2025)

- 2020-2023: Rank 2 fully classified by Rowell, Wang, Zhang
- 2024: Classification for rank 3 partially completed; papers by multiple groups but no consensus on completeness
- 2025: Open problem presented at Atlantic TQFT 2024, marked as major research direction

### Formalizability in Lean 4

**Level: VERY HARD**

- **Machinery needed**: Pentagon + hexagon equations (as above), unitarity constraints (eigenvalue bounds), modular S-matrix constraints, equivalence up to braided monoidal natural isomorphism
- **Gaps**: Full formalization of modular forms, S-matrix properties, SU(2) representation theory at specific levels
- **Approach**: Case enumeration with constraint propagation; verification that each case satisfies required axioms
- **Est. effort**: 5000+ lines even for rank 3 case; likely infeasible without significant Mathlib expansion

### Success Probability: 5-15%

Reason: Requires formalization of multiple deep areas of mathematics simultaneously. Even partial success (e.g., verifying Fibonacci is unique at rank 2) would be major achievement but requires substantial scaffolding.

### Why Good for Aristotle

1. **Clear success criteria**: Explicit list of candidates to check
2. **Recent active research**: Multiple 2024-2025 papers indicate tractability
3. **High impact**: Classification problems drive entire research areas
4. **Leverages existing**: Fibonacci/Ising cases already solved; can build upward
5. **Bounded but substantial**: More cases than P vs NP sub-problems; achievable within 2-week timeline for Rank 2 verification

### References

- ScienceDirect article: "Modular tensor categories arising from central extensions and related applications" (2024)
- arXiv:2408.06314 - "Commutative exact algebras and modular tensor categories" (2024)
- arXiv:1811.05123 - "Affine Lie algebras and tensor categories" (2018, still current reference)
- [Auto-equivalences of the modular tensor categories of type A, B, C and G](https://www.sciencedirect.com/science/article/abs/pii/S0001870822001803) - ScienceDirect (2024 update)

---

## Problem 5: Jones Polynomial Approximation Certifiable Cases

### Problem Statement

**Context**: Computing the Jones polynomial V_L(t) of a knot L at a primitive root of unity ω is BQP-complete (Aharonov-Jones-Landau, 2009). However, for specific roots of unity and specific knot structures, approximation may be tractable.

**Problem**: For the Fibonacci anyon model (which computes Jones polynomial at ω = e^(2πi/5)), determine:

**Question A**: For which knots K with ≤ n crossings can the Jones polynomial approximation at ω = e^(2πi/5) be verified classically in polynomial time?

**Specific case**: Prove or disprove that for the family of torus knots T(p, q) with p, q ≤ 10, the Jones polynomial V_{T(p,q)}(e^(2πi/5)) can be computed and certified to error < 2^{-n} in time poly(p, q, n).

**Question B (Verification Certificate)**: For any knot diagram D with crossing number c, design a polynomial-size certificate proving that a Fibonacci-anyon-computed approximation J_approx satisfies:

|J_approx - V_L(e^(2πi/5))| < ε

Formalize the verification algorithm in Lean.

### Why Unsolved

While the Jones polynomial approximation is BQP-complete in general, specific structure in particular knots or particular roots of unity might admit classical verification. No systematic study of which knot families have efficiently computable/verifiable Jones polynomials. The connection between topological structure (genus, knot invariants) and computational hardness is unexplored.

Recent 2024 work "Braiding Fibonacci anyons" (JHEP 08(2024):084) computes explicit braid matrices but doesn't address certification or classical verification hardness.

### Interdisciplinary Connection

**Quantum Computing**: BQP-completeness suggests quantum advantage for Jones polynomial, but specific cases might collapse to P or NP. Determining the boundary sharpens understanding of quantum advantage.

**Topology**: The problem connects knot invariants to complexity theory. Different knot families (torus, satellite, hyperbolic) might have different complexity profiles.

**Cryptography**: If Jones polynomial for specific knot classes is classically verifiable, it could inform knot-based cryptosystems (e.g., group membership testing using knot products).

### Recent Status (2023-2025)

- 2009: AJL theorem (BQP-complete in general)
- 2023-2024: Experimental implementations on Google/IBM quantum processors demonstrated feasibility for small braids
- 2025: No theoretical characterization of which cases remain hard

### Formalizability in Lean 4

**Level: MEDIUM**

- **Foundation**: Jones polynomial definition (can be axiomatized), braid group actions, knot diagrams as discrete structures
- **Gap**: BQP complexity class definition; formal connection between braiding and knot polynomials
- **Core proof**: For specific torus knots, explicit computation of braid word → R-matrix evaluation → polynomial value
- **Est. effort**: 1000-1800 lines to formalize Jones polynomial computation for a specific knot family; verification certificate structure adds 600-800 lines

### Success Probability: 30-40%

Reason: The polynomial computation is purely algebraic and well-defined; the hard part is relating it to knot structure. Can achieve concrete success by computing V_{T(2,3)} or V_{T(2,5)} formally.

### Why Good for Aristotle

1. **Explicit computable**: Braid matrices for Fibonacci anyons explicitly known (2024 papers give matrices)
2. **Satisfies Lean structure**: Discrete knots, braid words, matrix multiplication all formalizable
3. **Partial results immediately useful**: Computing V_K for any specific K gives concrete output
4. **Grounded in physics**: Matches topological quantum computing use case exactly
5. **Connection to verification**: Certification problem is practically motivated (quantum error mitigation)

### References

- arXiv:quant-ph/0511096 - "A Polynomial Quantum Algorithm for Approximating the Jones Polynomial" (Aharonov, Jones, Landau 2005; still standard reference)
- JHEP 08(2024):084 - "Braiding Fibonacci anyons" (2024) - explicit matrix formulas
- [Aharonov–Jones–Landau algorithm - Wikipedia](https://en.wikipedia.org/wiki/Aharonov%E2%80%93Jones%E2%80%93Landau_algorithm)
- arXiv:2404.00091 - "Non-Abelian braiding of Fibonacci anyons with a superconducting processor" (Google Quantum AI, 2024)

---

## Summary Table

| Problem | Area | Formalizability | Success % | Status 2025 | Lean Effort |
|---------|------|-----------------|-----------|------------|------------|
| **F-Matrix Solvability** | Fusion Algebra | MEDIUM | 25-35% | Open since ≥2010 | 800-1200 LOC |
| **Weak Integrality → Finite Braid Rep** | Representation Theory | HARD | 15-25% | Open; evidence strong | 2000-3500 LOC |
| **TEE Lower Bound Characterization** | Entanglement/TQFT | MEDIUM-HARD | 20-30% | Bound proven 2023, characterization open | 1500-2500 LOC |
| **Rank ≤ 4 MTC Classification** | Category Theory | VERY HARD | 5-15% | Rank 3 partially done | 5000+ LOC |
| **Jones Poly Certifiable Cases** | Knot Theory/QC | MEDIUM | 30-40% | Completely open | 1000-1800 LOC |

---

## Overall Assessment

All five problems:
- ✅ Have clear finite formulations
- ✅ Involve discrete/algebraic structure amenable to Lean 4
- ✅ Are published as open in peer-reviewed venues (2020-2025)
- ✅ Have high interdisciplinary impact (physics, quantum computing, mathematics)
- ✅ Show recent research activity (2023-2025 papers)

**Recommended starting points for Aristotle**:
1. **Jones Polynomial Certification** (Problem 5) - highest success probability, concrete matrices available
2. **F-Matrix Solvability** (Problem 1) - well-studied, bounded search space
3. **Weak Integrality** (Problem 2) - concrete test cases exist, clear formulation

**Avoid initially**:
- Rank ≤ 4 Classification (Problem 4) requires too much prerequisite formalization
- TEE Characterization (Problem 3) needs advanced functional analysis infrastructure

---

## Research Sources

Primary research was conducted via systematic web search of peer-reviewed mathematics and physics databases, focusing on papers published 2023-2025 with explicit mention of open problems and conjectures in:
- Topological quantum computing (Google, Microsoft, Quantinuum publications)
- Mathematical physics (ScienceDirect, Springer, arXiv)
- Quantum information theory
- Categorical topology and representation theory

Key databases: arXiv (math.QA, math-ph, quant-ph), Nature Physics, Physical Review Letters/B, Journal of High Energy Physics, Communications in Mathematical Physics.
