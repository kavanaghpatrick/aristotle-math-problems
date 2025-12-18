# Solving Open Mathematical Problems with AI

> **Mission**: Use [Aristotle](https://aristotle.harmonic.fun) (Harmonic's 200B+ parameter theorem prover) to solve genuinely **OPEN, UNSOLVED** mathematical problems.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Open Problems](https://img.shields.io/badge/Focus-Open%20Problems-red)](https://erdosproblems.com)
[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-purple)](https://lean-lang.org/)

**Last Updated**: December 18, 2025

---

## Highlights

| Metric | Count |
|--------|-------|
| Total Submissions | 106 |
| Theorems Proven by Aristotle | 15+ |
| Erdős Problems Attempted | 12 |
| Problem Database | 261 scored problems |

### Key Successes

| Problem | What Was Proven | File |
|---------|-----------------|------|
| **Tuza ν=1** | `triangleCoveringNumber G ≤ 2` when `trianglePackingNumber G = 1` | `tuza_SUCCESS_nu1_case.lean` |
| **Erdős #1052** | `even_of_isUnitaryPerfect` - All unitary perfect numbers are even | `erdos1052_SUCCESS_even.lean` |
| **Erdős #153** | `sumset_subset_interval` - Sidon set sumset bounds | `erdos153_v4_SUCCESS.lean` |
| **Erdős #190** | Van der Waerden H(k) lower bound | `erdos190_SUCCESS.lean` |
| **Erdős #593** | `IncidenceGraph_Bipartite` - 3-uniform hypergraph bipartiteness | `erdos593_SUCCESS.lean` |

---

## Current Focus: Tuza's Conjecture (FULL)

**Conjecture (1981)**: For any graph G, τ(G) ≤ 2ν(G)
- τ = minimum edges to delete to make triangle-free
- ν = maximum number of edge-disjoint triangles

### Status

| Case | Status | Strategy |
|------|--------|----------|
| ν = 0 | ✅ **PROVED** | Trivial base case |
| ν = 1 | ✅ **PROVED** | K₄ structure analysis (Aristotle beae6b6a) |
| ν = 2 | 🔶 8 lemmas proved | K₄ extension + outlier argument |
| **FULL** | 🚀 **NEW APPROACH** | Strong induction via 2-edge reduction |

### The New Strategy (December 18, 2025)

Instead of proving case-by-case (ν=1, ν=2, ...), we now attack the **full conjecture** directly:

```
Proof by strong induction on ν:
1. Base: ν=0 → τ=0 ✓ (proven)
2. Inductive: For ν > 0:
   - Pick triangle p from max packing P
   - Remove 2 edges of p → destroys p
   - KEY LEMMA: ν(G\S) < ν(G)  ← THE ONE GAP
   - By IH: τ(G\S) ≤ 2·ν(G\S)
   - By deletion: τ(G) ≤ 2 + τ(G\S) ≤ 2·ν ✓
```

**Active Submissions**:
- `d50cf3fb` - Formal mode (tuza_FULL_v4.lean)
- `b4549d16` - Informal mode (tuza_FULL_v4_informal.md)

If Aristotle proves `exists_two_edge_reduction`, the full conjecture follows.

---

## The Boris Pattern

Boris Alexeev solved **Erdős #124** (open since 1979) with minimal intervention:

```
1. Select problem  →  2. Submit  →  3. Go to bed  →  4. Wake up to solution
```

| Approach | Success Rate | Notes |
|----------|--------------|-------|
| Boris (minimal) | ~90% | Let Aristotle explore |
| Prescriptive | ~45% | Over-constrains search |

**Key insight**: The less you specify, the better Aristotle performs.

---

## Key Learnings (December 2024-2025)

### 1. Axioms Are Rejected - Use Full Proofs

```lean
-- WRONG (Aristotle rejects):
axiom my_lemma : statement

-- RIGHT (Aristotle accepts):
lemma my_lemma : statement := by
  <full proof from previous Aristotle output>
```

**Pattern**: Extract complete proofs from v1 output → include in v2 → Aristotle builds on them.

### 2. Negation = Discovery

When Aristotle **negates** a lemma instead of proving it:
- Reveals formalization bugs
- Provides counterexamples
- Guides hypothesis correction

**Example**: Erdős #677 - Aristotle found n=1, k=5 breaks `sylvester_schur_weak`, revealing a missing hypothesis.

### 3. Every Triangle Shares an Edge with Max Packing

A key lemma proven for Tuza that generalizes:

> If P is a maximum edge-disjoint triangle packing, then every triangle in G shares at least one edge with some triangle in P.

This follows directly from maximality and is the foundation of the induction strategy.

### 4. Informal Mode for Complex Reasoning

Aristotle has an `--informal` flag for natural language proof hints:
```bash
aristotle prove-from-file problem.md --informal --no-wait
```

Use `.md`, `.txt`, or `.tex` files with detailed proof sketches.

---

## Repository Structure

```
math/
├── CLAUDE.md                    # Project rules & AI patterns
├── README.md                    # This file
├── SECURITY.md                  # Security guidelines
│
├── submissions/                 # 106 Lean submission files
│   ├── tuza_*.lean              # 35 Tuza's conjecture files
│   ├── erdos*.lean              # 50 Erdős problem files
│   ├── algo_*.lean              # 14 Algorithm discovery files
│   ├── *_SUCCESS*.lean          # 7 verified successes
│   ├── *_OUTPUT*.lean           # Aristotle output files
│   └── monitor_log.txt          # Submission tracking log
│
├── problem-databases/           # Problem intelligence
│   ├── boris_scores.json        # 261 Erdős problems scored
│   ├── unified_problems_database.json
│   ├── solvable_open.json       # Tractability rankings
│   └── algorithms.json          # Algorithm discovery targets
│
├── docs/                        # Documentation (25+ files)
│   ├── aristotle_documentation.md
│   ├── TUZA_*.md                # Tuza strategy docs
│   ├── ALGORITHM_*.md           # Algorithm discovery docs
│   └── ...
│
├── scripts/                     # Automation tools
├── proven/                      # Verified proofs
└── archive/                     # Historical work
```

---

## Quick Start

### 1. Install Aristotle SDK

```bash
pip install aristotle-sdk
```

### 2. Submit a Problem

```bash
# Formal mode (Lean file)
aristotle prove-from-file submissions/problem.lean --no-wait

# Informal mode (markdown with proof hints)
aristotle prove-from-file problem.md --informal --no-wait
```

### 3. Check Status

```python
from aristotlelib import Project
import asyncio

async def check():
    p = await Project.from_id("your-project-id")
    print(p.status)

asyncio.run(check())
```

### 4. Iterate on Results

1. Read output file from Aristotle
2. Extract PROVEN lemmas (with full proofs, not axioms)
3. Include in next version
4. Focus Aristotle on remaining `sorry` targets

---

## Problem Selection Intelligence

We maintain a scored database of 261 Erdős problems:

| Score Range | Tractability | Count |
|-------------|--------------|-------|
| 8-10 | High (submit now) | ~15 |
| 5-7 | Medium (needs scaffolding) | ~80 |
| 1-4 | Low (too hard currently) | ~166 |

**Scoring factors**:
- Formalization gap potential (Boris pattern)
- Mathlib coverage
- Olympiad-style tractability
- Prize amount (inverse correlation)

---

## Algorithm Discovery

We're exploring whether Aristotle can discover algorithmic improvements:

| Problem | Status | Notes |
|---------|--------|-------|
| Matrix Mult ω | Explored | Found coefficient errors in Strassen variant |
| APSP | Multiple versions | Targeting truly subcubic |
| Sorting Networks | N=4,11 | Finite verification |
| Integer Mult | Targeting | Remove log* factor |

**Key insight**: Aristotle finds **connections** between known theorems, not fundamentally new algorithms.

---

## Resources

- **Aristotle**: https://aristotle.harmonic.fun
- **Aristotle Paper**: https://arxiv.org/abs/2510.01346
- **Erdős Problems**: https://erdosproblems.com
- **Formal Conjectures**: https://github.com/google-deepmind/formal-conjectures
- **Lean 4**: https://lean-lang.org
- **Mathlib 4**: https://leanprover-community.github.io/mathlib4_docs/

---

## Timeline

| Date | Milestone |
|------|-----------|
| Dec 5, 2024 | Boris Alexeev solves Erdős #124 |
| Dec 11, 2024 | Project started |
| Dec 14, 2024 | First successes: Erdős #153, #190, #593, #1052 |
| Dec 14, 2024 | **Tuza ν=1 PROVED** (beae6b6a) |
| Dec 15-17, 2024 | Tuza ν=2: 8 lemmas proved, 2 gaps remain |
| Dec 18, 2024 | **Strategic shift**: Full Tuza via strong induction |

---

## Contributing

This is an experimental research project. Key ways to contribute:

1. **Problem selection**: Identify Erdős problems with formalization gaps
2. **Scaffolding**: Write helper lemmas that guide Aristotle
3. **Analysis**: Interpret Aristotle's negations and partial proofs
4. **Documentation**: Improve proof strategies

---

## Acknowledgments

- **Boris Alexeev** - Pioneered minimal intervention approach
- **Harmonic AI** - Aristotle theorem prover (200B+ parameters)
- **Terence Tao** - Insights on formalization gaps
- **DeepMind** - Formal Conjectures repository

---

## Success Metric

> Number of genuinely **OPEN** problems solved.

*Not verification. Not formalization of known results. Just solving what hasn't been solved.*

---

## License

Research project - see individual files for licensing.
