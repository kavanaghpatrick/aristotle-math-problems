# ULTRATHINK: Groundbreaking Problem Discovery for Aristotle

## Context: What We Know Works

**The Boris Pattern (90% Success)**:
- Boris Alexeev solved Erdős #124 (open since 1979) by submitting formal statement and going to bed
- Zero intervention = maximum success
- Key insight: The less you specify, the better Aristotle performs

**Proven Success Factors**:
1. **Bounded Complexity**: Search space < 2^20 (rule of thumb)
2. **Clear Formal Statement**: Precise math, not vague descriptions
3. **Algebraic/Combinatorial Structure**: Aristotle excels at these
4. **Recent Progress**: Problems with 2023-2025 breakthroughs suggest tractability
5. **Certificate Verification**: Verify UNSAT certificates, not find SAT assignments

**What Failed**:
- Quantum Collision (16^16 state space) - timed out
- Prescriptive theorem specifications - 55% failure rate
- Vague problem statements - 70% failure rate

## The Question

We seek **groundbreaking open problems** that would be significant if solved AND are tractable for Aristotle.

Not:
- Competition problems (IMO/Putnam have solutions)
- Famous intractable problems (P=NP, Riemann)
- Vague conjectures without formal statements

Yes:
- Long-standing open problems with clear formal statements
- Problems where recent progress suggests tractability
- Problems that would advance a field if solved
- Certificate verification for hard instances

## Domains to Explore

### 1. Proof Complexity
- Resolution width lower bounds for specific formulas
- Trade-offs between proof system resources
- Optimal dag-like vs tree-like separations

### 2. Coding Theory
- Existence of codes with specific parameters [n,k,d]
- Self-dual code constructions
- MDS conjecture variants for specific fields

### 3. Combinatorics
- Ramsey number bounds (small instances: R(5,5), R(4,6))
- Erdős problems beyond #124
- Turán-type extremal problems

### 4. Graph Theory
- Chromatic number of specific graphs (Kneser, Schrijver)
- Specific cases of Hadwiger's conjecture
- Reconstruction conjecture for small n

### 5. Number Theory
- Specific Diophantine equations
- Bounds on arithmetic progressions (small cases)
- Density Hales-Jewett (bounded dimensions)

### 6. Algebraic Combinatorics
- Specific Stanley conjecture cases
- Polytope combinatorics (f-vector problems)
- Macdonald polynomial identities

### 7. Computational Algebra
- Word problem instances for specific groups
- Gröbner basis complexity for specific ideals
- Polynomial identity testing instances

### 8. Logic & Foundations
- Independence results for bounded arithmetic
- Specific finite model theory questions
- Proof complexity of specific tautologies

## Evaluation Criteria

For each candidate problem:

1. **Groundbreaking Score (1-10)**: How significant would a solution be?
   - 10: Would make headlines, advance entire field
   - 7-9: Would be a major result, multiple citations
   - 4-6: Solid contribution, specialist interest
   - 1-3: Incremental, limited impact

2. **Tractability Score (1-10)**: How likely is Aristotle to solve it?
   - 10: Perfect fit (bounded, algebraic, clear statement)
   - 7-9: Good fit (some complexity but structured)
   - 4-6: Uncertain (may hit limits)
   - 1-3: Poor fit (likely to fail)

3. **Formalizability Score (1-10)**: How easy to state in Lean 4?
   - 10: Trivial to formalize
   - 7-9: Standard Mathlib constructs
   - 4-6: Requires custom definitions
   - 1-3: Fundamentally hard to formalize

4. **Combined Priority**: Groundbreaking × Tractability × Formalizability / 100

## Output Format

For each recommended problem:

```
### [Problem Name]

**Statement**: [Precise mathematical statement]

**Domain**: [Area of mathematics]

**Open Since**: [Year, if known]

**Why Groundbreaking**: [1-2 sentences on significance]

**Why Tractable**: [Specific reasons Aristotle can handle it]

**Search Space Estimate**: [Rough bound on complexity]

**Recent Progress**: [Any 2023-2025 developments]

**Scores**:
- Groundbreaking: X/10
- Tractability: X/10
- Formalizability: X/10
- Priority: X.XX

**Boris Submission Strategy**: [How to frame for minimal intervention]
```

## Task

Identify 10-15 groundbreaking open problems that maximize:
- Significance if solved
- Probability of Aristotle success
- Clarity of formal statement

Rank by combined priority score. Be specific about WHY each problem is tractable (bounded parameters, algebraic structure, etc.).

Think deeply. This is not about quantity - it's about finding the problems that would genuinely advance mathematics AND that Aristotle can actually solve.
