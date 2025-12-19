# Solving Open Mathematical Problems with AI

> **Mission**: Use [Aristotle](https://aristotle.harmonic.fun) (Harmonic's 200B+ parameter theorem prover) to solve genuinely **OPEN, UNSOLVED** mathematical problems.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Open Problems](https://img.shields.io/badge/Focus-Open%20Problems-red)](https://erdosproblems.com)
[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-purple)](https://lean-lang.org/)

**Last Updated**: December 19, 2025

---

## Highlights

| Metric | Count |
|--------|-------|
| Total Submissions | 110+ |
| Theorems Proven by Aristotle | 20+ |
| Counterexamples Found | 3 |
| Erdős Problems Attempted | 12 |

### Key Results

| Problem | Result | File |
|---------|--------|------|
| **Tuza ν=1** | ✅ `τ(G) ≤ 2` when `ν(G) = 1` | `tuza_SUCCESS_nu1_case.lean` |
| **Tuza weak** | ✅ `τ(G) ≤ 3ν(G)` for all graphs | `tuza_v8_OUTPUT_tau_le_3nu.lean` |
| **Tuza ν=2** | 🔶 10+ lemmas proven, 2 gaps remain | `tuza_nu2_v11_case_analysis.lean` |
| **Erdős #1052** | ✅ All unitary perfect numbers are even | `erdos1052_SUCCESS_even.lean` |
| **Erdős #153** | ✅ Sidon set sumset bounds | `erdos153_v4_SUCCESS.lean` |

### Counterexamples Discovered

Aristotle's negation capability revealed flaws in proof strategies:

| Lemma | What Aristotle Found | Impact |
|-------|---------------------|--------|
| `TuzaReductionProperty` | 2 triangles sharing edge break reduction | Strong induction approach invalid |
| `two_edges_cover_nearby` | K₄ counterexample | "Nearby triangles" approach invalid |
| `two_K4_almost_disjoint` | 6-vertex counterexample with shared edge | Revised to case analysis |

---

## Current Focus: Tuza's Conjecture

**Conjecture (Tuza, 1981)**: For any graph G, τ(G) ≤ 2ν(G)
- τ(G) = minimum edges to hit all triangles (triangle covering number)
- ν(G) = maximum edge-disjoint triangles (triangle packing number)

### Known Results (Literature)

| Result | Source |
|--------|--------|
| τ ≤ (66/23)ν ≈ 2.87ν for all graphs | Haxell 1999 |
| Holds for planar graphs | Tuza 1985 |
| Holds for tripartite graphs | Haxell 1993 |
| Holds for treewidth ≤ 6 | Botler et al. 2021 |
| Tight at K₄ and K₅ | Tuza 1990 |

**Note**: Small cases (ν ≤ 7) do not appear to be explicitly proven in the literature. Our research using Playwright to access Wikipedia, Google Scholar, DIMACS, and Springer found no specific results for the ν=2 case.

### Our Progress

| Case | Status | Notes |
|------|--------|-------|
| ν = 0 | ✅ Proven | Trivial base case |
| ν = 1 | ✅ Proven | K₄ structure argument (400+ lines) |
| τ ≤ 3ν | ✅ Proven | Weak bound, all graphs (v7 minimal approach) |
| ν = 2 | 🔶 In progress | 10+ lemmas proven, case analysis approach |

### The ν=2 Case: Current Strategy

**Goal**: Prove τ(G) ≤ 4 when ν(G) = 2

**Approach** (after counterexample-driven refinement):
1. When τ > 4 with ν = 2, each packing triangle extends to K₄
2. Get K₄s s₁ ⊇ T₁ and s₂ ⊇ T₂ where T₁, T₂ are edge-disjoint
3. Case analysis on |s₁ ∩ s₂|:
   - **0-1 vertices**: Independent K₄s, τ ≤ 2+2 = 4
   - **2 vertices** (shared edge): Shared edge covers both, τ ≤ 3
   - **3 vertices**: Union is K₅, τ(K₅) = 4
   - **4 vertices**: Same K₄, τ = 2

**Key Lemmas Proven**:
- `exists_disjoint_in_K4`: Outlier triangle avoidance in K₄ (proven by Aristotle v9)
- `k4_avoidance_helper`: In 4-set, any edge has a 3-subset avoiding it
- `triangle_shares_edge_with_packing`: Every triangle shares edge with max packing
- `extensions_form_K4`: Packing triangles extend to K₄ when τ > 2ν

**Remaining Gaps**:
- `two_K4_cover_by_cases`: Case analysis covering argument
- `extensions_form_K4`: Full proof (currently sorry)

**Novelty Assessment**:
The ν=2 case appears unstudied in existing literature. Our K₄ extension + intersection case analysis approach is novel. If completed, this would be the first formal (machine-verified) proof of any non-trivial Tuza case.

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
- Reveals invalid assumptions in proof strategies
- Provides concrete counterexamples with verified proofs
- Guides hypothesis correction and strategy refinement

**Examples**:
- Erdős #677: Aristotle found n=1, k=5 breaks `sylvester_schur_weak`
- Tuza: Three separate counterexamples refined our ν=2 proof strategy
- `two_K4_almost_disjoint`: Fin 6 counterexample with s₁∩s₂ = 2 vertices

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
| Dec 14, 2024 | **Tuza ν=1 PROVED** |
| Dec 15-17, 2024 | Tuza ν=2: 8 lemmas proved |
| Dec 18, 2024 | Full Tuza attempted; **τ ≤ 3ν PROVED** (weak bound) |
| Dec 18, 2024 | Counterexamples to reduction property and nearby triangles approach |
| Dec 19, 2024 | **exists_disjoint_in_K4 PROVED** by Aristotle (v9) |
| Dec 19, 2024 | Counterexample to `two_K4_almost_disjoint` found; strategy revised |
| Dec 19, 2024 | Literature review confirms ν=2 case appears unstudied |

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
