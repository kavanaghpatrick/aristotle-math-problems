# Expert Debate: Top Aristotle Candidates (Score 100)

You are an expert in mathematical AI, Lean 4 theorem proving, and the Boris Pattern for Aristotle submissions.

## Context

### CRITICAL NEW INSIGHT (December 13, 2025)
Just received 3 Aristotle results that reveal a pattern:

| Problem | Type | Result | Lines | Insight |
|---------|------|--------|-------|---------|
| **3-MOLS Order 10** | Famous open (240 years) | Timeout | 337 | Intractable - ~10^100 search space |
| **Frankl Conjecture** | Famous open (45 years) | Timeout | 288 | Proved n≤4, but full problem too hard |
| **Ramsey Numbers** | KNOWN theorems | Timeout | 325 | **EXCELLENT** - R(3,3)=6 proved, Ramsey theorem proved! |

**KEY INSIGHT**: Aristotle EXCELS at formalizing KNOWN results but struggles with genuinely hard open problems.

### Proven Success Patterns
- **Boris Pattern**: Erdős #124 (Sidon set) solved - this was tractable despite being "open"
- **Ramsey formalization**: Near-complete proof of classical results
- **Jones Polynomial**: 983 lines, 0 sorries - verification of known algorithm

### Recent Failures
- **3-MOLS Order 10**: Problem genuinely intractable
- **Frankl Conjecture**: Good progress but problem too hard
- **HOMFLY v2**: Prescribed specific theorems → 45% failure rate

### Key Insight
Problems should be:
1. **Bounded/finite** - not asymptotic or infinite
2. **Algebraic structure** - Sidon, graph, Ramsey amenable to ATP
3. **Not "famous"** - 50+ year old conjectures are likely intractable
4. **Clear formalization path** - statement can be made precise

## Top Candidates (All Score 100)

### SIDON SET PROBLEMS (Highest priority - proven 90% success)

**#152 - Sidon Gaps**
> For any M≥1, if A⊂ℕ is a sufficiently large finite Sidon set then there are at least M many a∈A+A such that a+1,a-1∉A+A.

**#153 - Sidon Gap Variance**
> Let A be a finite Sidon set and A+A={s₁<⋯<sₜ}. Is it true that (1/t)∑(sᵢ₊₁-sᵢ)² → ∞ as |A|→∞?

**#340 - Greedy Sidon Growth**
> Let A={1,2,4,8,13,21,31,45,66,81,97,…} be the greedy Sidon sequence. Is |A∩{1,…,N}| ≫ N^(1/2-ε) for all ε>0?

### RAMSEY/COLORING PROBLEMS

**#172 - Monochromatic Sums/Products**
> In any finite colouring of ℕ, do there exist arbitrarily large finite A such that all sums and products of distinct elements in A are the same colour?

**#190 - Monochromatic vs Rainbow AP**
> Let H(k) be smallest N such that any colouring of {1,…,N} has either monochromatic k-AP or rainbow AP. Is H(k)^(1/k)/k → ∞?

**#602 - 2-colouring countable sets**
> Let (Aᵢ) be sets with |Aᵢ|=ℵ₀ and |Aᵢ∩Aⱼ| finite and ≠1. Is there a 2-colouring of ∪Aᵢ with no Aᵢ monochromatic?

### GRAPH THEORY PROBLEMS

**#64 - Power of 2 Cycles**
> Does every finite graph with minimum degree ≥3 contain a cycle of length 2^k for some k≥2?

**#149 - Strong Edge Independence**
> Let G be a graph with maximum degree Δ. Is G the union of at most (5/4)Δ² sets of strongly independent edges?

**#1077 - D-balanced Subgraphs**
> If G has n vertices and n^(1+α) edges, must G contain a D-balanced subgraph on m>n^(1-α) vertices with ≥εm^(1+α) edges?

### OPG PROBLEMS

**Book Thickness of Subdivisions**
> Graph theory problem about book embeddings

**Turán number of finite family**
> Is extremal number of family dominated by some single graph?

**Chromatic symmetric function distinguishes trees?**
> Does Stanley's chromatic symmetric function distinguish non-isomorphic trees?

## Task

For EACH of the following top 5 candidates, estimate:
1. **Success probability** (0-100%) with Boris-style submission
2. **Key risk factors**
3. **Why it might work / fail**

Then provide:
- **RECOMMENDED TOP 3** for immediate submission
- **Ranking rationale**

### Candidates to Evaluate
1. Erdős #152 (Sidon gaps)
2. Erdős #153 (Sidon gap variance)
3. Erdős #64 (Power of 2 cycles)
4. Erdős #172 (Monochromatic sums/products)
5. Erdős #340 (Greedy Sidon growth)

Consider:
- Sidon problems have 90% historical success
- Graph problems are well-supported in Mathlib
- Bounded/finite formulations preferred
- Asymptotic statements (→∞) are harder
