# Improved HQC/QCSD Problem Statement for Aristotle

**Date:** 2025-12-11
**Original Issue:** #22 - QC Syndrome Decoding Complexity (NIST HQC Standard)
**Current Result:** Partial (97 lines, Prange lower bound only)

---

## EXECUTIVE SUMMARY

**Goal:** Move from "specific attack lower bound" → "general complexity characterization"

**Current:** Proved Prange ≥ 2^100 (one algorithm)
**Target:** Prove average-case hardness for ALL algorithms via reduction to established hard problem

---

## KEY INSIGHTS FROM RESEARCH

### Recent Developments (2023-2025)

1. **NP-completeness (2023):**
   - [Decoding Quasi-Cyclic codes is NP-complete](https://eprint.iacr.org/2023/1064.pdf)
   - Proves worst-case hardness
   - **Gap:** Cryptography needs average-case hardness!

2. **Independence Assumptions (January 2025):**
   - [On the Independence Assumption in QC Code-Based Cryptography](https://arxiv.org/html/2501.02626)
   - Analyzes structural assumptions
   - Key open question: Are quasi-cyclic codes as hard as random codes?

3. **HQC Specifications (August 2025):**
   - [Latest HQC Specs](https://pqc-hqc.org/doc/hqc_specifications_2025_08_22.pdf)
   - Defines 3-QCSD-PT problem formally
   - Parameters: n, ω, b1, b2, b3, ℓ

4. **Community Consensus:**
   - Decoding QC codes is "considered hard" but lacks rigorous proof
   - **Critical gap:** No worst-case to average-case reduction

---

## GROK'S RECOMMENDATIONS

### 1. Main Goal (Ambitious)
**Theorem:** For HQC parameters (n=17669, k=13893, t=66), the **average-case** complexity of QCSD is at least 2^128, **assuming LPN hardness**.

**Approach:** Reduction from LPN to HQC QCSD

### 2. Backup Goals (If Main Too Hard)
- **Level 1:** Prove average-case ≥ 2^100 (weaker bound)
- **Level 2:** Formalize the reduction framework (without full proof)
- **Level 3:** Analyze specific attack families (ISD variants)

### 3. Key Lemmas Needed
1. Quasi-cyclic structure formalization
2. Polynomial-time LPN → QCSD transformation
3. Probability preservation lemma
4. Running time preservation up to polynomial factors

---

## IMPROVED PROBLEM STATEMENT FOR ARISTOTLE

### Version 1: Full Reduction (Most Ambitious)

```markdown
# Problem: Average-Case Hardness of HQC via LPN Reduction

## Background
The Hamming Quasi-Cyclic (HQC) cryptosystem, selected by NIST in March 2025,
relies on the hardness of the Quasi-Cyclic Syndrome Decoding (QCSD) problem.

Define:
- HQC parameters: n=17669, k=13893, t=66, r=3 (quasi-cyclic index)
- QCSD: Given parity-check matrix H (quasi-cyclic structure) and syndrome s,
  find error vector e with weight ≤ t such that He^T = s^T
- LPN(n, τ): Learning Parity with Noise with noise rate τ = t/n

## Goal
Prove that the average-case complexity of QCSD for HQC parameters is at least
2^λ operations (for some security parameter λ ≥ 100), under the assumption
that LPN(n, t/n) is hard.

## Approach
Construct a reduction:
1. Given an LPN instance (samples {(a_i, b_i)}), construct a QCSD instance (H, s)
2. The construction should preserve:
   - Quasi-cyclic structure of HQC
   - Error weight distribution
   - Average-case complexity
3. Prove: Solving QCSD instance implies solving LPN instance with high probability
4. Conclude: QCSD complexity ≥ LPN complexity

## Deliverables
1. Formalize quasi-cyclic code structure in Lean
2. Define LPN problem formally
3. Construct explicit reduction algorithm
4. Prove reduction correctness
5. Calculate concrete security parameter λ for HQC parameters

## Success Criteria
- Formal proof of reduction in Lean 4
- Concrete bound λ ≥ 100 (ideally λ ≥ 128)
- Novel contribution beyond existing NP-completeness result
```

---

### Version 2: Structural Analysis (More Feasible)

```markdown
# Problem: Quasi-Cyclic Structure and Decoding Complexity

## Background
While QCSD is NP-complete in general, the specific quasi-cyclic structure
used in HQC might admit faster algorithms. The open question: Does the
quasi-cyclic structure reduce security?

## Goal
Prove lower bounds on the complexity of QCSD that account for the quasi-cyclic
structure, showing it does NOT significantly reduce hardness.

## Approach
1. Formalize the quasi-cyclic structure (circulant blocks)
2. Analyze known attack families:
   - Information Set Decoding (ISD) variants
   - Statistical attacks exploiting structure
   - Algebraic attacks on circulant matrices
3. For each family, prove lower bound using:
   - Information-theoretic arguments
   - Algebraic complexity
   - Combinatorial counting

## Deliverables
1. Classification of attack families
2. For each family, prove complexity ≥ 2^λ
3. Union bound: ALL algorithms require ≥ 2^λ operations

## Success Criteria
- Covers major attack families (ISD, statistical, algebraic)
- Concrete bound λ ≥ 100
- Accounts for quasi-cyclic structure explicitly
```

---

### Version 3: Information-Theoretic Approach (Most Novel)

```markdown
# Problem: Information-Theoretic Lower Bounds for QCSD

## Background
Even with unlimited computational power, some information about the error
vector is information-theoretically unrecoverable from the syndrome alone.

## Goal
Prove information-theoretic lower bounds on the number of operations required
to recover the error vector, independent of specific algorithms.

## Approach
1. Formalize information content:
   - Syndrome entropy: H(s)
   - Error entropy: H(e)
   - Mutual information: I(s; e)
2. Prove: Any algorithm must process at least 2^{H(e|s)} candidates
3. For HQC parameters, calculate H(e|s) and derive complexity bound

## Deliverables
1. Entropy calculations for HQC parameters
2. Information-theoretic impossibility result
3. Translation to computational complexity via counting arguments

## Success Criteria
- Novel information-theoretic perspective
- Complements existing computational hardness results
- Provides fundamental lower bound independent of algorithm class
```

---

## CONCRETE INPUT FOR ARISTOTLE

### Recommended Approach: Start with Version 2 (Most Feasible)

**Why Version 2?**
- More concrete than full reduction (Version 1)
- More substantial than current result
- Aligns with Aristotle's strengths (formalization, case analysis)
- Achieves genuine novelty without requiring breakthrough reduction

### Aristotle Input File: `hqc_improved_input.txt`

```markdown
# Quasi-Cyclic Syndrome Decoding Complexity for HQC

## Problem Statement

The NIST HQC post-quantum cryptosystem (selected March 2025) relies on the
hardness of the Quasi-Cyclic Syndrome Decoding (QCSD) problem.

Parameters:
- n = 17669 (code length)
- k = 13893 (code dimension)
- t = 66 (error weight)
- r = 3 (quasi-cyclic index)

The parity-check matrix H has quasi-cyclic structure: it consists of r×r blocks
of n₀×n₀ circulant matrices (where n = r·n₀).

## Background Definitions

1. **Circulant Matrix**: An n×n matrix where each row is a cyclic shift of the
   previous row. Fully determined by first row.

2. **Quasi-Cyclic Code**: A linear code with generator/parity-check matrix
   having circulant block structure.

3. **QCSD Problem**: Given H (quasi-cyclic parity-check matrix) and syndrome s,
   find error vector e with weight ≤ t such that He^T = s^T.

4. **Information Set Decoding (ISD)**: Class of algorithms that:
   - Pick k positions as "information set"
   - Solve linear system for those positions
   - Check if resulting error has weight ≤ t
   - Repeat until success

5. **Statistical Attacks**: Exploit statistical properties of circulant structure
   to gain information about error positions.

## Your Task

Prove lower bounds on the complexity of solving QCSD for HQC parameters that
account for the quasi-cyclic structure.

### Part 1: ISD Lower Bound

Prove: Any ISD algorithm requires at least C(n,t) / C(n-k,t) ≈ 2^100 iterations
in expectation, even exploiting quasi-cyclic structure.

Key insight: Quasi-cyclic structure doesn't reduce the search space significantly
for ISD algorithms.

### Part 2: Statistical Attack Lower Bound

Prove: Statistical attacks exploiting circulant structure require at least 2^λ
operations (for some λ ≥ 80).

Approach: Use concentration inequalities to show statistical signals are too weak
to significantly reduce search space.

### Part 3: Union Bound

Combine bounds from Parts 1-2 to show: ALL known attack families require ≥ 2^λ
operations.

## Expected Output

Lean 4 formalization including:
1. Quasi-cyclic code structure definitions
2. ISD algorithm model and complexity analysis
3. Statistical attack model and lower bound
4. Union bound combining all attack families
5. Concrete security parameter λ for HQC parameters

## Success Criteria

- Formal proofs in Lean 4 (200-400 lines)
- Concrete bound λ ≥ 100 (ideally λ ≥ 120)
- Explicitly accounts for quasi-cyclic structure
- Novel contribution beyond existing work
```

---

## COMPARISON: CURRENT VS. IMPROVED

| Aspect | Current (v1) | Improved (v2) | Gain |
|--------|--------------|---------------|------|
| **Scope** | Prange only | All attack families | 4-5x broader |
| **Structure** | Ignores QC | Explicitly analyzes QC | Novel angle |
| **Lines** | 97 | ~250-400 | 2.5-4x deeper |
| **Novelty** | Known bound | New structural analysis | Genuine contribution |
| **Rating** | 4/10 | 7-8/10 target | Major improvement |

---

## IMPLEMENTATION STRATEGY

### Phase 1: Formalization (50-100 lines)
- Define circulant matrices in Lean
- Formalize quasi-cyclic structure
- Define QCSD problem formally
- Set up HQC parameters

### Phase 2: ISD Analysis (80-120 lines)
- Model ISD algorithm class
- Prove search space lower bound
- Account for QC structure exploitation attempts
- Calculate concrete bound for HQC

### Phase 3: Statistical Attacks (80-120 lines)
- Model statistical distinguishers
- Use concentration inequalities
- Prove information-theoretic limits
- Derive computational lower bound

### Phase 4: Union Bound (40-60 lines)
- Combine all attack families
- Prove overall lower bound
- Calculate final security parameter λ

**Total estimate:** 250-400 lines (vs. current 97)

---

## RISK ASSESSMENT

### Main Challenges:

1. **Circulant matrix formalization:** Lean has matrices, need to add circulant structure
   - **Mitigation:** Start with simple definition, expand as needed

2. **Statistical attack modeling:** Requires probability theory
   - **Mitigation:** Use Mathlib's probability tools, keep model simple

3. **Union bound technicalities:** Combining different complexity models
   - **Mitigation:** Use conservative bounds, avoid overly precise accounting

### Success Probability Estimate:

- **High confidence (80%):** Formalization + ISD analysis
- **Medium confidence (60%):** Statistical attack analysis
- **Lower confidence (40%):** Full union bound with tight constants

**Recommended:** Aim for full result, but partial results still valuable.

---

## NEXT STEPS

1. ✅ **This document** - Problem statement refined
2. **Create Aristotle input file** - Clean, focused problem description
3. **Launch Aristotle** - Submit improved problem
4. **Monitor progress** - Check for partial results
5. **Iterate if needed** - Adjust based on what Aristotle achieves

---

## SOURCES

### Key References:

1. [NP-completeness of QC decoding (2023)](https://eprint.iacr.org/2023/1064.pdf)
2. [Independence assumptions in QC codes (Jan 2025)](https://arxiv.org/html/2501.02626)
3. [HQC specifications (Aug 2025)](https://pqc-hqc.org/doc/hqc_specifications_2025_08_22.pdf)
4. [HQC official site](https://pqc-hqc.org/)
5. [NIST HQC presentation (2024)](https://csrc.nist.gov/csrc/media/Presentations/2024/hqc/images-media/gaborit-hqc-pqc2024.pdf)
6. [Decoding Challenge - QCSD](https://decodingchallenge.org/q-c)

### Grok Brainstorming:
- Temperature 0.7 for creativity
- Suggested LPN reduction approach
- Proposed backup goals
- Identified key lemmas

---

**Recommendation:** Proceed with **Version 2 (Structural Analysis)** - most feasible while still achieving genuine novelty.

**Estimated improvement:** From 4/10 → 7-8/10 rating
**Success probability:** 40-60% (vs. current 100% for partial result)
**Value if successful:** Genuine contribution to HQC security analysis
