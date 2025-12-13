# Unsolved Mathematical Problems in Post-Quantum Cryptography

**Research Focus**: Lattice-based, code-based, and hash-based cryptography
**Literature Period**: 2020-2025
**Emphasis**: Problems with discrete/combinatorial structure, avoiding number-theoretic conjectures

---

## Problem 1: Optimal Modulus for SIS-to-SVP Reduction

### Problem Statement
**Open Question**: Determine the optimal modulus bound for the Short Integer Solution (SIS) problem that admits a worst-case reduction from the Shortest Vector Problem (SVP).

**Precise Formulation**: For dimension n, solution norm bound β, and modulus q, what is the minimal function f(n, β) such that SIS_{n,m,q,β} with q ≥ f(n, β) reduces to worst-case SVP on n-dimensional lattices?

**Current Best Known**: q ≥ β · n^δ for any constant δ > 0 (Micciancio & Peikert, 2013), improving upon earlier q > β · √(n log n). Lower bound: q ≤ β makes the problem trivial.

**Conjecture**: It is conjectured that for sufficiently large n, SIS_{n,m,q,β} is hard whenever q > β · poly(n), but the optimal polynomial degree remains unknown.

### Why Unsolved
The gap between the proven bound (q ≥ β · n^δ) and the conjectured sufficient condition (q > β · poly(n)) leaves open whether reductions exist for smaller moduli. Tightening this would directly impact the parameter sizes needed in lattice-based cryptosystems like Falcon and Dilithium.

### Interdisciplinary Connection
**Cryptography Impact**: Smaller moduli mean shorter public keys and signatures in lattice-based schemes. The NIST-standardized ML-DSA (Dilithium) and SLH-DSA rely on SIS hardness assumptions. Optimal bounds would allow minimal key sizes while maintaining security.

**Computational Complexity**: Relates to fine-grained hardness of lattice problems and whether polynomial-time reductions exist for cryptographically useful parameter ranges.

### Recent Status (2023-2025)
Active research area with ongoing work on:
- Fine-grained reductions between lattice problems
- Quantum vs classical reduction techniques for SIS
- Parameter optimization for NIST PQC standards (2024 standardization)

No major breakthrough on the optimal modulus bound since 2013, but extensive empirical validation through NIST competition analysis.

### Formalizability in Lean 4
**MEDIUM** - Requires:
- Lattice definitions and norms (partially in Mathlib)
- Computational complexity classes (NP-hardness)
- Reduction framework between problems
- Would need significant formalization of worst-case to average-case reductions

### Success Probability Estimate
**15-25%** - The problem involves:
- Well-understood mathematical structures (lattices, modular arithmetic)
- Clear reduction framework, but requires sophisticated analysis
- May require new proof techniques not yet formalized
- Partial results possible (e.g., improving constant factors)

### Why Good for Aristotle
- **Discrete Structure**: Purely combinatorial/algebraic problem over integers
- **Bounded Parameters**: Can focus on specific small cases (fixed dimension n)
- **Known Techniques**: Lattice reduction theory well-developed
- **Verification**: Results can be verified through explicit construction
- **Impact**: Any improvement would be publishable and impact real-world cryptography

### References
- [Short Integer Solution Problem - Wikipedia](https://en.wikipedia.org/wiki/Short_integer_solution_problem)
- [Hardness of SIS and LWE with Small Parameters (Micciancio, 2013)](https://web.eecs.umich.edu/~cpeikert/pubs/LWsE.pdf)
- [Finding short integer solutions when the modulus is small (Ducas, 2023)](https://eprint.iacr.org/2023/1125.pdf)
- [Lattice-Based Cryptography Slides (Peikert)](https://web.eecs.umich.edu/~cpeikert/pubs/slides-abit2.pdf)

---

## Problem 2: Classical Reduction from SVP to Learning With Errors (LWE)

### Problem Statement
**Open Question**: Does there exist a classical (non-quantum) reduction from worst-case lattice problems to the Learning With Errors (LWE) problem?

**Precise Formulation**: Construct a classical polynomial-time reduction showing that if LWE_{n,q,χ} can be solved in polynomial time, then worst-case GapSVP_γ (for appropriate approximation factor γ) can be solved in polynomial time.

**Current Status**: Only quantum reductions are known (Regev 2005, Peikert 2009). All existing worst-case hardness proofs for LWE rely on quantum algorithms.

### Why Unsolved
The quantum reduction uses superposition and quantum sampling in fundamental ways. No classical analogue is known for the core "smudging" technique that makes the reduction work. This represents a significant gap in our understanding of LWE's hardness.

### Interdisciplinary Connection
**Cryptography**: LWE underlies NIST-standardized schemes ML-KEM (Kyber) and ML-DSA (Dilithium). A classical reduction would strengthen confidence in their security without quantum assumptions about hardness.

**Quantum Computing Theory**: Resolving this would clarify whether quantum advantage is inherent to certain cryptographic reductions or merely a technical limitation.

**Complexity Theory**: Relates to understanding the power of quantum reductions versus classical reductions in average-case/worst-case connections.

### Recent Status (2023-2025)
- **2024**: NIST finalized ML-KEM (FIPS 203) and ML-DSA (FIPS 204), both relying on Module-LWE
- Listed as major open problem in LWE surveys (Regev's 2024 update)
- Recent work on benchmarking LWE attacks (NIST 2024) but no progress on classical reductions
- Structured LWE variants (Ring-LWE, Module-LWE) unified in 2024 (Peikert & Pepin) but classical reduction remains open

### Formalizability in Lean 4
**HARD** - Requires:
- Advanced lattice theory (discrete Gaussian sampling)
- Probability theory over lattices
- Reduction frameworks and complexity classes
- The quantum reduction's classical verification is tractable, but proving impossibility would be very hard

### Success Probability Estimate
**5-10%** - Extremely challenging:
- Open since 2005 despite significant attention
- May require entirely new techniques
- Possible that no classical reduction exists (separation result)
- More likely to prove hardness of classical reduction than find one

### Why Good for Aristotle
- **Clear Mathematical Structure**: Well-defined lattice problems and probability distributions
- **Verification**: Any claimed reduction could be verified by checking the construction
- **Smaller Target**: Could attempt restricted cases (specific moduli, dimensions, error distributions)
- **High Impact**: Would be a major breakthrough in cryptography foundations
- **Alternative Approaches**: Could explore barriers to classical reductions (impossibility results)

### References
- [The Learning with Errors Problem (Regev Survey)](https://cims.nyu.edu/~regev/papers/lwesurvey.pdf)
- [Learning with Errors - Wikipedia](https://en.wikipedia.org/wiki/Learning_with_errors)
- [Benchmarking Attacks on Learning with Errors (NIST 2024)](https://csrc.nist.gov/csrc/media/Projects/post-quantum-cryptography/documents/pqc-seminars/presentations/17-benchmarking-lwe-attack-08062024.pdf)
- [On Lattices, Learning with Errors, Random Linear Codes (2024)](https://arxiv.org/abs/2401.03703)

---

## Problem 3: SVP to SIS Reduction with Optimal Parameters

### Problem Statement
**Open Question**: Prove a reduction from worst-case Shortest Vector Problem (SVP) to average-case Short Integer Solution (SIS), rather than from the weaker SIVP (Shortest Independent Vectors Problem).

**Precise Formulation**: Given an oracle that solves SIS_{n,m,q,β} in polynomial time, construct a polynomial-time algorithm for SVP_γ on n-dimensional lattices for approximation factor γ = poly(n).

**Current Best Known**: Reductions exist from SIVP to SIS (Ajtai 1996, Micciancio-Regev 2004), but not from the more natural SVP.

**Related Open Problem**: Show a reduction from approximate SIVP to SIS with modulus q = O(1) (constant modulus).

### Why Unsolved
SVP is believed to be a harder problem than SIVP, and the averaging techniques that work for SIVP don't obviously extend to SVP. The problem requires new ideas about lattice covering and sampling.

### Interdisciplinary Connection
**Cryptographic Foundation**: SVP is the most natural lattice problem and the gold standard for hardness. A SVP-to-SIS reduction would provide the strongest possible theoretical foundation for SIS-based schemes (digital signatures, hash functions).

**Algorithmic Lattice Theory**: Understanding this reduction would clarify the relationship between different fundamental lattice problems and their average-case variants.

### Recent Status (2023-2025)
- Identified in Peikert's 2024 work "Some Mathematical Problems Behind Lattice-Based Cryptography" as a major open problem
- No significant progress reported in recent literature
- Related work on fine-grained SVP hardness (2020-2024) but no breakthroughs on SIS connection
- Constant modulus variant remains particularly interesting for practical applications

### Formalizability in Lean 4
**MEDIUM-HARD** - Requires:
- SVP and SIVP definitions (basic lattice theory in Mathlib)
- SIS problem formalization
- Reduction framework and average-case analysis
- Probabilistic arguments over lattice distributions

### Success Probability Estimate
**10-15%** - Challenging but potentially tractable:
- Clear problem statement with known related results
- May require extending existing SIVP techniques
- Could attempt weaker versions (larger approximation factors, restricted parameters)
- Partial results (improved parameters) more likely than full solution

### Why Good for Aristotle
- **Well-Structured**: Clear reduction framework, concrete lattice problems
- **Building on Known Work**: Can leverage existing SIVP-to-SIS reduction techniques
- **Bounded Cases**: Could target specific dimensions or approximation factors
- **Verification**: Reductions can be verified by checking correctness of construction
- **Incremental Progress Possible**: Improving parameters or approximation factors would be valuable

### References
- [Some Mathematical Problems Behind Lattice-Based Cryptography (2024)](https://arxiv.org/pdf/2506.23438)
- [Lattice-based cryptography - Wikipedia](https://en.wikipedia.org/wiki/Lattice-based_cryptography)
- [Fine-grained hardness of lattice problems: Open questions (Simons Institute Blog, 2020)](https://blog.simons.berkeley.edu/2020/05/fine-grained-hardness-of-lattice-problems-open-questions/)

---

## Problem 4: Bounded Distance Decoding Hardness for Large p-Norms

### Problem Statement
**Open Question**: Determine the optimal distance parameter α for which Bounded Distance Decoding in ℓ_p norms (BDD_{p,α}) is NP-hard and has fine-grained hardness, particularly for large values of p.

**Precise Formulation**: For which values of p ∈ [1,∞) and distance parameters α (as a function of p) is it true that:
1. BDD_{p,α} is NP-hard under randomized reductions?
2. There is no 2^{(1-ε)n/C}-time algorithm for BDD_{p,α} for constants C > 1, ε > 0, assuming randomized SETH?

**Recent Result (2020)**: Proven that BDD_{p,α} is NP-hard for α approaching 1/2 as p→∞, and fine-grained hard assuming SETH. For p > 4.2773, improved NP-hardness bounds compared to prior 2008 work.

**Open**: Determine optimal α for all p, especially p ∈ (1,4.2773), and tighten fine-grained bounds.

### Why Unsolved
Different norms require different geometric techniques. The transition region for intermediate p values lacks complete understanding. Fine-grained complexity connections to SETH and ETH are recent (2020) and not fully explored.

### Interdisciplinary Connection
**Cryptography**: BDD algorithms directly determine security of LWE-based cryptosystems. Understanding BDD hardness for different norms impacts parameter selection for lattice-based schemes.

**Algorithm Analysis**: BDD solvers are used to estimate concrete security of NIST PQC standards. Hardness results provide lower bounds on attack complexity.

**Computational Complexity**: Connects classical complexity (NP-hardness) with fine-grained complexity (SETH, ETH) for geometric problems.

### Recent Status (2023-2025)
- 2020 paper by Bennett & Peikert improved NP-hardness and gave first fine-grained hardness for BDD in ℓ_p norms
- Active area: BDD algorithms crucial for evaluating LWE security in NIST PQC process (2022-2024)
- 2024 work on batch BDD and improved BDD solvers for cryptanalysis
- Gap remains: optimal α for all p not determined

### Formalizability in Lean 4
**MEDIUM** - Requires:
- Lattice definitions (partially available)
- ℓ_p norms and geometric properties
- NP-hardness reductions (complexity theory)
- Potentially some analysis for limiting behavior as p→∞
- Fine-grained complexity (would need new Lean formalization)

### Success Probability Estimate
**20-30%** - Moderately promising:
- Recent progress (2020) suggests problem is active and tractable
- Clear mathematical structure with geometric intuition
- Could target specific p values or improved constants
- Reduction techniques from existing work could extend
- Partial results (tightening bounds, specific p values) very feasible

### Why Good for Aristotle
- **Concrete Bounds**: Problem asks for specific constants and parameters
- **Geometric Intuition**: ℓ_p norms have well-understood properties
- **Incremental Progress**: Improving α bounds for specific p would be valuable
- **Verification**: NP-hardness reductions can be verified by construction
- **Crypto Relevance**: Direct impact on understanding LWE security

### References
- [Hardness of Bounded Distance Decoding on Lattices in ℓ_p Norms (Bennett & Peikert)](https://web.eecs.umich.edu/~cpeikert/pubs/bdd-hardness.pdf)
- [Hardness of BDD on Lattices in ℓ_p Norms (arXiv, 2020)](https://arxiv.org/abs/2003.07903)
- [On Bounded Distance Decoding for General Lattices (Liu & Lyubashevsky)](https://cseweb.ucsd.edu//~vlyubash/papers/bdd.pdf)
- [Exploring Trade-offs in Batch Bounded Distance Decoding (2020)](https://link.springer.com/chapter/10.1007/978-3-030-38471-5_19)

---

## Problem 5: MinRank Problem Exact Complexity and Quantum Resistance

### Problem Statement
**Open Question**: Determine the exact computational complexity of the MinRank problem and prove rigorous bounds on quantum algorithm performance.

**Precise Formulation**: Given matrices M₁, ..., M_m ∈ F^{n×n} over a finite field F and target rank r, find coefficients x₁, ..., x_m ∈ F such that rank(∑ᵢ xᵢMᵢ) ≤ r.

**Known**: MinRank is NP-complete (proven).

**Open Questions**:
1. What is the optimal time complexity for solving MinRank instances with specific parameter ranges (n, m, r, |F|)?
2. Are there quantum algorithms achieving more than polynomial speedup over classical algorithms?
3. What are the optimal parameters for cryptographic security against both classical and quantum adversaries?

### Why Unsolved
MinRank has rich algebraic structure that can be exploited through multiple attack strategies (Kipnis-Shamir, minors modeling, Gröbner bases). The relative performance of these methods depends on parameters in complex ways. Quantum resistance remains conjectured but not rigorously proven.

### Interdisciplinary Connection
**Post-Quantum Cryptography**: MinRank underlies several NIST PQC candidates including GeMSS and MIRA. Rainbow (finalist) was broken via MinRank attack in 2022, showing the importance of understanding this problem.

**Algebraic Geometry**: MinRank solving via Gröbner bases connects to computational algebraic geometry and ideal theory.

**Quantum Computing**: Determining whether quantum algorithms provide super-polynomial advantage impacts design of multivariate cryptosystems.

### Recent Status (2023-2025)
- **2022**: Beullens' MinRank attack broke Rainbow signature scheme, causing NIST rejection
- **2023-2024**: Extensive research on MinRank solvers for security evaluation of UOV-based schemes (7 NIST submissions)
- **2024**: New work on "algebra of MinRank problem" studying Gröbner basis complexity
- **2024**: SupportMinors modeling techniques analyzed for improved complexity bounds
- Active research on optimal parameters for MinRank-based schemes vs attack algorithms

### Formalizability in Lean 4
**MEDIUM** - Requires:
- Linear algebra over finite fields (partially in Mathlib)
- Matrix rank computation
- Polynomial systems and ideals (Gröbner bases harder)
- NP-completeness framework
- Complexity bounds formalization

### Success Probability Estimate
**25-35%** - Promising target:
- Well-defined algebraic problem with clear parameters
- Active research with recent progress
- Could target specific cases: small r, specific fields, bounded n
- Proving lower bounds or optimality results feasible
- Quantum resistance analysis might be tractable for restricted cases

### Why Good for Aristotle
- **Pure Algebra**: Finite fields, matrices, rank - all well-formalized domains
- **Bounded Parameters**: Can focus on small instances (e.g., r=2, small n, specific fields)
- **Multiple Approaches**: Could analyze different solving algorithms
- **Verification**: Solutions verifiable by rank computation
- **Practical Impact**: Direct relevance to NIST PQC standardization process
- **Recent Breakthroughs**: 2022 Rainbow break shows problem is active and important

### References
- [The complexity of the SupportMinors Modeling for the MinRank Problem (2024)](https://arxiv.org/html/2506.06547)
- [Progress in Multivariate Cryptography: Systematic Review (ACM Computing Surveys)](https://dl.acm.org/doi/10.1145/3571071)
- [Recent progress in security evaluation of multivariate public-key cryptography (2023)](https://ietresearch.onlinelibrary.wiley.com/doi/full/10.1049/ise2.12092)
- [The algebra of the MinRank problem in post-quantum cryptography](https://qics.sorbonne-universite.fr/algebra-minrank-problem-post-quantum-cryptography-grobner-bases-complexity-and-implementations)

---

## Problem 6: Syndrome Decoding in Quasi-Cyclic Codes - Complexity Gaps

### Problem Statement
**Open Question**: Determine the exact complexity of syndrome decoding for Quasi-Cyclic (QC) codes compared to random linear codes, and identify parameter regimes where QC structure provides or prevents computational advantage for attackers.

**Precise Formulation**: Let QC-SDP_{n,k,w} be the syndrome decoding problem for quasi-cyclic codes of length n, dimension k, and error weight w.
1. For which parameters is QC-SDP provably harder than general SDP?
2. Are there efficient algorithms exploiting QC structure that outperform generic decoding for specific parameter ranges?
3. What is the optimal tradeoff between code structure (for compact keys) and security degradation?

**Recent Result (2023)**: QC-SDP proven NP-hard and decision variant D-QC-SDP proven NP-complete, answering a fundamental question in code-based cryptography.

**Open**: Quantify security degradation vs random codes for specific QC parameters used in cryptographic schemes (BIKE, HQC).

### Why Unsolved
Structured codes enable smaller keys but may introduce vulnerabilities. The QC structure provides algebraic handles that could potentially be exploited, but the extent and parameter dependence is not fully understood. Recent ML attacks (DeepDistinguisher, 2025) add new dimension to analysis.

### Interdisciplinary Connection
**Code-Based Cryptography**: QC-MDPC codes underlie BIKE (Round 4 NIST alternate). HQC selected for standardization (2025, expected 2026-2027). Understanding QC-SDP is critical for parameter selection.

**Coding Theory**: Relates classical coding theory (random codes) to structured codes with algebraic properties.

**Machine Learning + Crypto**: 2025 DeepDistinguisher work shows transformers can distinguish structured codes from random, opening new attack surface requiring analysis.

**Computational Complexity**: NP-completeness established but fine-grained complexity unclear.

### Recent Status (2023-2025)
- **2023**: NP-completeness proof for QC-SDP (Dominguez Fiallo)
- **2025**: HQC selected by NIST for standardization (finalization 2026-2027)
- **2025**: AI-based distinguishing attacks on QC codes (DeepDistinguisher paper) show ML can distinguish Goppa and QC-MDPC from random with high accuracy in certain settings
- Active research: Optimal parameters balancing key size vs security for BIKE and HQC
- Gap: Precise quantification of security loss due to QC structure for cryptographic parameters

### Formalizability in Lean 4
**MEDIUM** - Requires:
- Linear codes over finite fields (basic coding theory)
- Quasi-cyclic structure (polynomial rings, circulant matrices)
- Syndrome decoding problem definition
- NP-completeness (complexity theory)
- Could formalize specific parameter cases and security bounds

### Success Probability Estimate
**30-40%** - Strong candidate:
- Recent progress (NP-completeness 2023) suggests active development
- Concrete parameter ranges from NIST schemes provide targets
- Could analyze specific cases: BIKE parameters, HQC parameters
- Proving bounds for restricted cases very feasible
- Alternative: analyze impact of ML distinguishers mathematically

### Why Good for Aristotle
- **Concrete Cryptographic Parameters**: BIKE and HQC provide specific n, k, w to analyze
- **Recent Formalization**: NP-completeness proof provides foundation
- **Bounded Cases**: Can focus on specific QC structures (e.g., index 2, specific circulant patterns)
- **Verification**: Decoding algorithms can be verified by checking syndrome
- **Timely Impact**: NIST standardization (2026-2027) makes this highly relevant
- **Discrete Structure**: Pure combinatorics and algebra over finite fields

### References
- [Decoding Quasi-Cyclic codes is NP-complete (Dominguez Fiallo, 2023)](https://eprint.iacr.org/2023/1064.pdf)
- [Challenges for code-based problems (Decoding Challenge)](https://decodingchallenge.org/home/documentation)
- [AI for Code-based Cryptography (2025)](https://eprint.iacr.org/2025/440.pdf)
- [On the hardness of the decoding problem (arXiv)](https://arxiv.org/pdf/1404.3482)

---

## Problem 7: QROM Security Proofs - Generic Lifting Theorems

### Problem Statement
**Open Question**: Determine which classes of cryptographic schemes admit generic "lifting theorems" from Random Oracle Model (ROM) security to Quantum Random Oracle Model (QROM) security, and identify fundamental barriers.

**Precise Formulation**: For a class C of cryptographic schemes (e.g., signature schemes, KEMs, hash functions):
1. Does there exist a generic transformation T such that if scheme S ∈ C is secure in ROM, then T(S) is secure in QROM?
2. If not, characterize exactly which additional properties are required for lifting.
3. For schemes without lifting, quantify the security degradation in QROM vs ROM.

**Known Results**:
- Some schemes secure in ROM are insecure in QROM (separation results exist)
- Fiat-Shamir cannot be proven secure in QROM via black-box reductions from computational special soundness + HVZK (unlike ROM)
- Constrained lifting theorems exist for specific classes but fully general lifting is impossible
- One-Way to Hiding (O2H) lemma and semi-classical O2H provide tools but not complete solution

**Open**: Classify schemes admitting lifting vs requiring new proof techniques vs fundamentally insecure in QROM.

### Why Unsolved
Quantum adversaries can query oracles in superposition, breaking classical proof techniques:
- **Reprogramming problem**: Cannot reprogram oracle without disturbing quantum queries
- **Forking lemma**: Classical rewinding doesn't extend to quantum setting
- **Measurement disturbance**: Observing quantum queries changes adversary state

These represent fundamental differences requiring new mathematical tools.

### Interdisciplinary Connection
**Post-Quantum Cryptography**: All PQC schemes must be secure against quantum adversaries with quantum oracle access. QROM is the appropriate security model for hash-based, lattice-based schemes using hash functions.

**Quantum Computing Theory**: Understanding quantum query complexity and limitations of quantum reductions.

**Cryptographic Foundations**: Clarifies which classical proof techniques are quantum-robust and which require fundamental rethinking.

### Recent Status (2023-2025)
- **2019-2020**: SC-O2H lemma (Ambainis et al., CRYPTO 2019) partially addresses reprogramming
- **2023**: Interactive Oracle Arguments in QROM (applications to quantum computation verification)
- **2024**: "Double-sided tight proofs for guessing games in QROM" - improved bounds via O2H refinements
- **Ongoing**: NIST PQC schemes require QROM security analysis (ML-KEM, ML-DSA, SLH-DSA all use hash functions)
- **Open**: Generic Fiat-Shamir security from lossy identification schemes in QROM

### Formalizability in Lean 4
**VERY HARD** - Requires:
- Quantum computation formalization (basic quantum circuits)
- Random oracles and hash functions
- Cryptographic security definitions (IND-CCA, EUF-CMA)
- Probability theory and advantage bounds
- Quantum query complexity
- Most of this infrastructure not yet in Mathlib

### Success Probability Estimate
**5-12%** - Extremely challenging but potentially groundbreaking:
- Fundamental open problem since quantum cryptography emerged
- May require entirely new mathematical frameworks
- More tractable: prove impossibility results for specific schemes
- Alternative: formalize barriers to lifting (meta-theorems about what cannot be proven)
- Could target very specific cases: particular signature schemes, specific security notions

### Why Good for Aristotle
- **High Impact**: Would significantly advance PQC foundations
- **Clear Structure**: Well-defined security games and reductions
- **Alternative Approaches**: Could prove impossibility results rather than constructions
- **Building Blocks**: Could formalize intermediate results (O2H lemma variants, specific scheme analysis)
- **Verification**: Security proofs are mathematical statements, verifiable in principle

**Challenges**:
- Requires significant quantum formalization infrastructure
- May be too ambitious for current automated provers
- Better suited as longer-term target after building quantum libraries

### References
- [Classical vs Quantum Random Oracles (Yamakawa & Zhandry, 2020)](https://eprint.iacr.org/2020/1270.pdf)
- [Interactive Oracle Arguments in the QROM (2023)](https://eprint.iacr.org/2023/421)
- [Double-sided tight proofs for guessing games in QROM (2024)](https://link.springer.com/article/10.1186/s42400-024-00228-6)
- [A Concrete Treatment of Fiat-Shamir in QROM](https://link.springer.com/chapter/10.1007/978-3-319-78372-7_18)

---

## Summary Comparison Table

| Problem | Area | Formalizability | Success Prob | Impact | Discrete Structure |
|---------|------|-----------------|--------------|--------|-------------------|
| 1. Optimal SIS Modulus | Lattice | MEDIUM | 15-25% | High | ✓ Modular arithmetic |
| 2. Classical LWE Reduction | Lattice | HARD | 5-10% | Very High | ✓ Lattices, probability |
| 3. SVP-to-SIS Reduction | Lattice | MEDIUM-HARD | 10-15% | High | ✓ Lattice theory |
| 4. BDD p-Norm Hardness | Lattice | MEDIUM | 20-30% | Medium | ✓ Geometric combinatorics |
| 5. MinRank Complexity | Multivariate | MEDIUM | 25-35% | High | ✓ Finite fields, matrices |
| 6. QC Syndrome Decoding | Code-based | MEDIUM | 30-40% | High | ✓ Coding theory |
| 7. QROM Lifting Theorems | Foundations | VERY HARD | 5-12% | Very High | △ Quantum circuits |

**Legend**: ✓ = Fully discrete/combinatorial, △ = Requires quantum formalization

---

## Recommended Priorities for Aristotle

### Tier 1 (Highest Success Probability, High Impact)
1. **QC Syndrome Decoding (Problem 6)**: 30-40% success, NIST-relevant, concrete parameters
2. **MinRank Complexity (Problem 5)**: 25-35% success, recent breakthroughs, pure algebra

### Tier 2 (Moderate Success Probability, Very High Impact)
3. **BDD p-Norm Hardness (Problem 4)**: 20-30% success, geometric intuition, incremental progress feasible
4. **Optimal SIS Modulus (Problem 1)**: 15-25% success, well-structured, parameter optimization

### Tier 3 (Lower Probability but Major Breakthroughs)
5. **SVP-to-SIS Reduction (Problem 3)**: 10-15% success, but any progress publishable
6. **Classical LWE Reduction (Problem 2)**: 5-10% success, but would be landmark result
7. **QROM Lifting (Problem 7)**: 5-12% success, requires infrastructure but highest foundational impact

### Starting Point Recommendation
**Begin with Problem 6 (QC Syndrome Decoding)** because:
- Highest success probability (30-40%)
- Recent NP-completeness proof provides foundation
- Concrete NIST parameters (BIKE, HQC) provide clear targets
- Pure combinatorics over finite fields (well-suited to Lean)
- Timely: HQC standardization in 2026-2027

**Alternative: Problem 5 (MinRank)** if algebraic geometry tools available:
- Second highest success probability (25-35%)
- Rainbow break (2022) shows current relevance
- Multiple approaches possible (Gröbner bases, linear algebra, quantum resistance)
- Immediate NIST application (UOV-based schemes)

---

## Key Themes Across All Problems

1. **Post-Quantum Security**: All problems directly impact NIST PQC standardization
2. **Parameter Optimization**: Tradeoffs between security and efficiency
3. **Structure vs Security**: Structured objects (QC codes, ideal lattices, polynomial rings) enable compact keys but may weaken security
4. **Classical vs Quantum**: Complexity in both models must be understood
5. **Worst-Case to Average-Case**: Cryptography requires average-case hardness from worst-case assumptions
6. **Fine-Grained Complexity**: ETH/SETH connections crucial for concrete security
7. **Discrete Mathematics**: All problems fundamentally combinatorial/algebraic (except QROM which requires quantum formalization)

These problems represent the cutting edge of mathematical cryptography research, with solutions directly impacting the security of systems deployed worldwide in the post-quantum era.
