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
| Total Submissions | 120+ |
| Theorems Proven by Aristotle | 20+ |
| Counterexamples Found | 3 |
| Erdős Problems Attempted | 12 |
| **Active Aristotle Jobs** | **7** |

### Key Results

| Problem | Result | File |
|---------|--------|------|
| **Tuza ν=1** | ✅ `τ(G) ≤ 2` when `ν(G) = 1` | `tuza_SUCCESS_nu1_case.lean` |
| **Tuza weak** | ✅ `τ(G) ≤ 3ν(G)` for all graphs | `tuza_v8_OUTPUT_tau_le_3nu.lean` |
| **Tuza ν=2** | 🔶 5 submissions running | `tuza_nu2_v12_*.lean` |
| **Tuza ν≤3 (Parker)** | 🔶 2 submissions running | `parker_nu3_*.lean` |
| **Erdős #1052** | ✅ All unitary perfect numbers are even | `erdos1052_SUCCESS_even.lean` |
| **Erdős #153** | ✅ Sidon set sumset bounds | `erdos153_v4_SUCCESS.lean` |

### Active Aristotle Submissions (Dec 19, 2025)

| File | UUID | Target | Method |
|------|------|--------|--------|
| `tuza_nu2_v12_minimal.lean` | `8a5948f4` | ν=2 | K₄-extension (Boris) |
| `tuza_nu2_v12_minimal.md` | `f398b5a5` | ν=2 | K₄-extension (informal) |
| `tuza_nu2_v12_scaffolded.lean` | `232aa9cd` | ν=2 | K₄-extension (scaffolded) |
| `parker_nu3_v1.lean` | `d096deb8` | ν≤3 | Parker (Boris) |
| `parker_nu3_v2_scaffolded.lean` | `a2f49fd5` | ν≤3 | Parker (scaffolded) |

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
| **ν ≤ 3 ⟹ τ ≤ 2ν** | **Parker 2025** ⭐ NEW |
| Holds for planar graphs | Tuza 1985 |
| Holds for tripartite graphs | Haxell 1993 |
| Holds for treewidth ≤ 6 | Botler et al. 2021 |
| Tight at K₄ and K₅ | Tuza 1990 |

**🆕 Critical Discovery (Dec 2025)**: Alex Parker's paper ([arXiv:2406.06501](https://arxiv.org/abs/2406.06501), published EJC May 2025) proves Tuza for **ν ≤ 3** using hypergraph (k-1)-matchings.

**Our Value Shift**: Our ν=2 work is now the **first machine-verified proof** using a **different method** (K₄-extension vs Parker's hypergraph approach). Both the formalization and the novel proof technique remain valuable.

### Our Progress

| Case | Status | Method | Notes |
|------|--------|--------|-------|
| ν = 0 | ✅ Proven | - | Trivial base case |
| ν = 1 | ✅ Proven | K₄-extension | First machine-verified (400+ lines) |
| τ ≤ 3ν | ✅ Proven | Greedy | Weak bound, all graphs |
| ν = 2 | 🔶 In progress | K₄-extension | 5 submissions running |
| ν ≤ 3 | 🔶 In progress | Parker's method | 2 submissions running |
| **ν = 4** | 🎯 Next target | Hybrid? | **Genuinely open** |

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
Our K₄-extension approach is different from Parker's hypergraph method. If completed, this would be the first machine-verified proof of ν=2, using a novel technique.

### Parker's Method (ν ≤ 3)

We're also formalizing Parker's 2025 proof for comparison:

**Key Definitions**:
- **M**: Maximum edge-disjoint triangle packing (|M| = ν)
- **T_e**: Triangles sharing an edge with e ∈ M
- **S_e**: Triangles sharing edge with e but NOT with any other f ∈ M

**Key Lemmas**:
- **Lemma 2.2**: ν(S_e) = 1 (any two triangles in S_e share an edge)
- **Lemma 2.3**: ν(G \ T_e) = ν - 1 (removing T_e reduces packing by 1)

**Induction**: τ(G) ≤ τ(T_e) + 2(ν-1). For Tuza bound, need τ(T_e) ≤ 2.

### Why ν = 4 Is the Real Target

Parker's proof works for ν ≤ 3 but **not ν = 4**:
- At ν = 4, case analysis can't guarantee τ(T_e) ≤ 2 for any e ∈ M
- More complex matching configurations allow τ(T_e) = 3+
- The extra edge breaks the 2ν bound in induction

**ν = 4 would be genuinely new mathematics** - not covered by any existing proof.

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

### Key Papers (Tuza's Conjecture)

- **Parker 2025**: [arXiv:2406.06501](https://arxiv.org/abs/2406.06501) - Proves ν ≤ 3 via (k-1)-matchings
- **Haxell 1999**: τ ≤ (66/23)ν for all graphs
- **Tuza 1981**: Original conjecture (τ ≤ 2ν)

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
| Dec 19, 2025 | **Parker 2025 discovery**: ν ≤ 3 already proven in literature |
| Dec 19, 2025 | Strategic pivot: ν=2 for machine-verification, **ν=4 for new math** |
| Dec 19, 2025 | Parker's method formalized; 7 Aristotle submissions active |

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
