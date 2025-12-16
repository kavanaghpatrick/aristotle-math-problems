# Solving Open Mathematical Problems with AI

> **Mission**: Use [Aristotle](https://aristotle.harmonic.fun) to solve genuinely **OPEN, UNSOLVED** mathematical problems.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Open Problems](https://img.shields.io/badge/Focus-Open%20Problems-red)](https://erdosproblems.com)
[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-purple)](https://lean-lang.org/)

**Last Updated**: December 16, 2024

---

## Current Focus Areas

### 1. Tuza's Conjecture (Graph Theory)
**Conjecture**: For any graph G, τ(G) ≤ 2ν(G) where τ = min edge cover of triangles, ν = max edge-disjoint triangles.

| Case | Status | Notes |
|------|--------|-------|
| ν = 0 | PROVED | Base case |
| ν = 1 | **PROVED** | K₄ structure analysis |
| ν = 2 | In Progress | 5 parallel approaches running |
| General | Target | Induction strategy |

### 2. Erdős Problems
| Problem | Status | Key Finding |
|---------|--------|-------------|
| #677 (LCM) | v3 running | Negation revealed hypothesis bug (n≥1 → n≥k) |
| #593 (Hypergraphs) | Shelved | Too hard, timeout |
| #128, #152, #1052 | Various | See submissions/ |

### 3. Algorithm Discovery
Exploring whether Aristotle can discover algorithmic improvements:
- Matrix multiplication (ω < 2.371?)
- APSP (truly subcubic?)
- Integer multiplication

**Learning**: Aristotle rejects axioms but accepts full proven lemmas.

---

## The Boris Pattern

Boris Alexeev solved **Erdős #124** (open since 1979) with minimal intervention:

1. Select problem → 2. Submit → 3. **Go to bed** → 4. Wake up to solution

| Approach | Success Rate |
|----------|--------------|
| Boris (minimal) | **90%** |
| Prescriptive | 45% |

**Key insight**: The less you specify, the better Aristotle performs.

---

## Key Learnings (December 2024)

### Feeding Back Proven Work

**CRITICAL**: Aristotle rejects `axiom` declarations.

```lean
-- WRONG (rejected):
axiom my_lemma : statement

-- RIGHT (works):
lemma my_lemma : statement := by
  <full proof from Aristotle's output>
```

**Pattern**: Extract complete proofs from v1 output → include in v2 → Aristotle builds on them.

### Negation as Discovery

When Aristotle NEGATES a lemma, it's valuable:
- Reveals formalization bugs
- Provides counterexamples
- Guides hypothesis correction

Example: Erdős #677 - Aristotle found n=1, k=5 breaks sylvester_schur_weak.

---

## Repository Structure

```
math/
├── CLAUDE.md                # Project rules & patterns
├── README.md                # This file
├── submissions/             # 92 Lean submission files
│   ├── tuza_*.lean          # Tuza's conjecture attempts
│   ├── erdos*.lean          # Erdős problems
│   └── algo_*.lean          # Algorithm discovery
├── problem-databases/       # 1,244 scored open problems
├── scripts/                 # Submission tools
├── docs/                    # Documentation
├── proven/                  # Verified successes
└── archive/                 # Historical work
```

---

## Quick Start

### 1. Submit a Problem

```bash
aristotle prove-from-file submissions/problem.lean --no-wait
```

### 2. Check Status

```python
from aristotlelib import Project
p = await Project.from_id("your-project-id")
print(p.status)
```

### 3. Iterate on Results

1. Read output file from Aristotle
2. Extract PROVEN lemmas (full proofs)
3. Include in next version
4. Focus Aristotle on remaining targets

---

## Resources

- **Aristotle**: https://aristotle.harmonic.fun
- **Erdős Problems**: https://erdosproblems.com
- **Aristotle Paper**: https://arxiv.org/abs/2510.01346
- **Lean 4**: https://lean-lang.org

---

## Acknowledgments

- **Boris Alexeev** - Pioneered minimal intervention approach
- **Harmonic AI** - Aristotle theorem prover
- **Terence Tao** - Insights on formalization gaps

---

**Success Metric**: Number of genuinely OPEN problems solved.

*Not verification. Not polish. Just solving what hasn't been solved.*
