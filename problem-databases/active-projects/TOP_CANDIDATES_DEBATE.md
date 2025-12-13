# ULTRATHINK: Top Candidate Prioritization Debate

## Context
We have 15 problems all scoring 100 (max tractability). We need to prioritize which to submit to Aristotle first using the Boris pattern.

## Proven Aristotle Success Patterns
- **Boris Pattern (90%)**: Minimal intervention, formal statement only
- **Bounded Combinatorics (85%)**: Finite search space < 2^20
- **Sidon Sets**: Erdős #124 SOLVED - this is our gold standard
- **Certificate Verification (90%)**: Verify witness, not find it
- **Algebraic Structure (80%)**: Well-founded recursion

## Proven Failure Patterns
- Huge state spaces (16^16 = timeout)
- Asymptotic/infinite problems
- Over-prescribing proof strategies

## Top 15 Candidates (Score: 100)

### Sidon Set Problems (HIGHEST PRIORITY - Erdős #124 was Sidon!)
1. **#152**: Sidon set gaps - "For any M≥1, if A⊂ℕ is sufficiently large Sidon set, there are ≥M gaps in A+A"
2. **#153**: Sidon set sum gaps squared - variance of gaps → ∞
3. **#530**: Maximal Sidon subset in any finite set A⊂ℝ

### Ramsey/Graph Problems
4. **#174**: Ramsey characterization - which finite sets are Ramsey?
5. **#1014**: Ramsey number limits - prove lim R(k,l)^(1/l) exists
6. **#1105**: Anti-Ramsey numbers
7. **#1111**: Anticomplete sets in graphs

### Extremal Graph Theory
8. **#180**: Extremal numbers for graph families
9. **#575**: Same as #180 (possible duplicate?)
10. **#706**: Unit distance graphs in R²
11. **#750**: Infinite chromatic number with large independent sets

### Geometric/Structural
12. **#130**: Infinite set in R² - no 3 collinear, no 4 concyclic
13. **#601**: Limit ordinals and infinite paths

### MathOverflow
14. **#60011**: Trees in exponential growth groups
15. **#462981**: Open problems for computation (meta-problem)

## Debate Questions

1. **Which 3 should we submit FIRST?** Consider:
   - Similarity to Erdős #124 (Sidon sets!)
   - Bounded vs asymptotic
   - Constructive vs existential
   - Search space size

2. **Which should we AVOID?** Consider:
   - Infinite/asymptotic conditions
   - Vague problem statements
   - Huge search spaces

3. **Estimate success probability** for top 5 candidates

4. **Any candidates need problem statement cleanup before submission?**

## Your Task
Analyze each candidate. Rank top 5 by Boris-pattern success probability.
Identify any that should be excluded and why.
