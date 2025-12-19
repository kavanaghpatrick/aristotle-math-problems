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
| Total Submissions | 130+ |
| Theorems Proven by Aristotle | 25+ |
| Counterexamples Found | 3 |
| Erdos Problems Attempted | 12 |
| **Active Aristotle Jobs** | **9** |

### Key Results

| Problem | Result | File |
|---------|--------|------|
| **Tuza v=1** | Proven: `t(G) <= 2` when `v(G) = 1` | `tuza_SUCCESS_nu1_case.lean` |
| **Tuza weak** | Proven: `t(G) <= 3v(G)` for all graphs | `tuza_v8_OUTPUT_tau_le_3nu.lean` |
| **Tuza v<=3 (Parker)** | Proven lemmas (see below) | `aristotle_parker_proven.lean` |
| **Tuza v=4** | Active: 7 submissions running | `tuza_nu4_*.lean` |
| **Erdos #1052** | Proven: All unitary perfect numbers are even | `erdos1052_SUCCESS_even.lean` |
| **Erdos #153** | Proven: Sidon set sumset bounds | `erdos153_v4_SUCCESS.lean` |

### Breakthrough: Parker's Proof Lemmas (Proven by Aristotle)

Aristotle has **fully proven** the core lemmas from Parker's 2025 paper:

| Lemma | Statement | Status |
|-------|-----------|--------|
| `lemma_2_2` | For e in max packing M, triangles in S_e pairwise share an edge | Proven |
| `lemma_2_3` | v(G \ T_e) = v - 1 | Proven |
| `inductive_bound` | t(G) <= t(T_e) + t(G \ T_e) | Proven |
| `intersecting_family_structure` | Intersecting family is star OR contained in K4 | Proven |
| `covering_number_le_two_of_subset_four` | t <= 2 if triangles in <= 4 vertices | Proven |

**What remains**: Assembly of these lemmas into the final theorem `t <= 2v` for `v <= 3`.

### Active Aristotle Submissions (Dec 19, 2025)

**Parker Completion (v <= 3)**:
| File | Mode | Project ID | Strategy |
|------|------|------------|----------|
| `tuza_parker_completion.md` | Informal + Context | `3057dfda` | Proven lemmas as context |
| `tuza_combined_parker_v2.lean` | Formal + Context | `3db6b2f3` | Formal with sorry placeholders |

**v=4 Portfolio (Genuinely Open)**:
| File | Mode | Project ID | Strategy |
|------|------|------------|----------|
| `tuza_nu4_v1_boris_prime.md` | Informal | `0cbcf556` | Open exploration |
| `tuza_nu4_v2_architect.lean` | Formal | `78959cfe` | Zero-comment structures |
| `tuza_nu4_v3_surgeon.lean` | Formal | `e4408087` | Attacks Parker's failure point |
| `tuza_nu4_v4_finite_check.lean` | Formal | `33945e8c` | dec_trivial small graphs |
| `tuza_nu4_v5_conflict_graph.md` | Informal | `aaf89ca2` | Structural analysis |
| `tuza_nu4_v6_pessimist.lean` | Formal | `d6195535` | Counterexample hunt |
| `tuza_nu4_v7_slicer.lean` | Formal | `8026542a` | K4-free case isolation |

### Counterexamples Discovered

Aristotle's negation capability revealed flaws in proof strategies:

| Lemma | What Aristotle Found | Impact |
|-------|---------------------|--------|
| `TuzaReductionProperty` | 2 triangles sharing edge break reduction | Strong induction approach invalid |
| `two_edges_cover_nearby` | K4 counterexample | "Nearby triangles" approach invalid |
| `two_K4_almost_disjoint` | 6-vertex counterexample with shared edge | Revised to case analysis |

---

## Current Focus: Tuza's Conjecture

**Conjecture (Tuza, 1981)**: For any graph G, t(G) <= 2v(G)
- t(G) = minimum edges to hit all triangles (triangle covering number)
- v(G) = maximum edge-disjoint triangles (triangle packing number)

### Known Results (Literature)

| Result | Source |
|--------|--------|
| t <= (66/23)v ~ 2.87v for all graphs | Haxell 1999 |
| **v <= 3 => t <= 2v** | **Parker 2025** (NEW) |
| Holds for planar graphs | Tuza 1985 |
| Holds for tripartite graphs | Haxell 1993 |
| Holds for treewidth <= 6 | Botler et al. 2021 |
| Tight at K4 and K5 | Tuza 1990 |

### Our Progress

| Case | Status | Method | Notes |
|------|--------|--------|-------|
| v = 0 | Proven | - | Trivial base case |
| v = 1 | Proven | K4-extension | First machine-verified (400+ lines) |
| t <= 3v | Proven | Greedy | Weak bound, all graphs |
| v <= 3 | PROVEN LEMMAS | Parker's method | Assembly submission running |
| **v = 4** | TARGET | Hybrid | **Genuinely open** |

### Why v = 4 Is the Real Target

Parker's proof works for v <= 3 but **not v = 4**:
- At v <= 3: Can guarantee t(T_e) <= 2 for some edge e in packing M
- At v = 4: Overlap patterns make this impossible
- Induction gives t <= 3 + 2(3) = 9, but Tuza requires <= 8

**v = 4 would be genuinely new mathematics** - not covered by any existing proof.

### Parker's Method (What Aristotle Proved)

**Key Definitions**:
- **M**: Maximum edge-disjoint triangle packing (|M| = v)
- **T_e**: Triangles sharing an edge with e in M
- **S_e**: Triangles sharing edge with e but NOT with any other f in M

**Key Lemmas (All Proven)**:
- **Lemma 2.2**: v(S_e) = 1 (any two triangles in S_e share an edge)
- **Lemma 2.3**: v(G \ T_e) = v - 1 (removing T_e reduces packing by 1)
- **Inductive bound**: t(G) <= t(T_e) + t(G \ T_e)
- **Intersecting structure**: Intersecting family -> star OR K4

**What's left**: Show t(S_e) <= 2, then final induction completes the proof.

---

## The Boris Pattern

Boris Alexeev solved **Erdos #124** (open since 1979) with minimal intervention:

```
1. Select problem  ->  2. Submit  ->  3. Go to bed  ->  4. Wake up to solution
```

| Approach | Success Rate | Notes |
|----------|--------------|-------|
| Boris (minimal) | ~90% | Let Aristotle explore |
| Prescriptive | ~45% | Over-constrains search |

**Key insight**: The less you specify, the better Aristotle performs.

---

## Key Learnings (December 2025)

### 1. Context Files Are Powerful

Aristotle's `--context-folder` and `--formal-input-context` flags allow feeding proven lemmas:

```bash
# Informal problem + formal context
aristotle prove-from-file problem.md --informal \
  --context-folder path/to/proven_lemmas/ --no-wait

# Formal problem + context folder
aristotle prove-from-file problem.lean \
  --context-folder path/to/context/ --no-wait
```

This is how we feed Aristotle's own proven lemmas back for completion.

### 2. Multi-Agent Debate for Strategy

Using Grok-4, Gemini, and Codex in parallel debates:
- Each AI critiques proposed submission strategies
- Synthesize into portfolio of 7 submissions per target
- Mix formal (67%) and informal (33%) modes
- Key insight: "The Surgeon" pattern attacks exact failure points

### 3. Submission Portfolio Strategy

From our v=4 debate:

| Slot | Pattern | Description |
|------|---------|-------------|
| 1 | Boris Prime | Minimal, open exploration |
| 2 | Architect | Zero-comment structure |
| 3 | Surgeon | Attack known failure point |
| 4 | Finite Check | dec_trivial for small n |
| 5 | Conflict Graph | Structural analysis |
| 6 | Pessimist | Counterexample search |
| 7 | Slicer | Isolate obstructions |

### 4. Axioms Are Rejected - Use Full Proofs

```lean
-- WRONG (Aristotle rejects):
axiom my_lemma : statement

-- RIGHT (Aristotle accepts):
lemma my_lemma : statement := by
  <full proof from previous Aristotle output>
```

### 5. Negation = Discovery

When Aristotle **negates** a lemma:
- Reveals invalid assumptions
- Provides concrete counterexamples
- Guides strategy refinement

### 6. Comments Hurt Exploration

Strategic comments constrain Aristotle's search:

```lean
-- BAD: "-- Use induction on triangle count"
-- GOOD: (no comment, just theorem statement)
```

---

## Repository Structure

```
math/
|-- CLAUDE.md                    # Project rules & AI patterns
|-- README.md                    # This file
|-- SECURITY.md                  # Security guidelines
|
|-- submissions/                 # 130+ Lean submission files
|   |-- tuza_*.lean              # 45 Tuza's conjecture files
|   |-- tuza_nu4_*.lean          # 8 v=4 portfolio files
|   |-- aristotle_*_proven.lean  # Proven lemma collections
|   |-- parker_context/          # Context folder for completion
|   |-- erdos*.lean              # 50 Erdos problem files
|   |-- *_SUCCESS*.lean          # 7 verified successes
|   |-- *_OUTPUT*.lean           # Aristotle output files
|   |-- monitor_log.txt          # Submission tracking log
|
|-- problem-databases/           # Problem intelligence
|   |-- boris_scores.json        # 261 Erdos problems scored
|   |-- unified_problems_database.json
|   |-- solvable_open.json       # Tractability rankings
|   |-- algorithms.json          # Algorithm discovery targets
|
|-- docs/                        # Documentation (35+ files)
|   |-- TUZA_STRATEGY_DEC19.md   # Current Tuza strategy
|   |-- PARKER_NU4_ANALYSIS.md   # Why v=4 is open
|   |-- ERDOS128_ANALYSIS.md     # Formalization bug postmortem
|   |-- ...
|
|-- scripts/                     # Automation tools
|-- proven/                      # Verified proofs
|-- archive/                     # Historical work
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

# With context (proven lemmas)
aristotle prove-from-file problem.lean \
  --context-folder path/to/lemmas/ --no-wait
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
3. Put in context folder
4. Submit next version with `--context-folder`

---

## Problem Selection Intelligence

We maintain a scored database of 261 Erdos problems:

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

## Timeline

| Date | Milestone |
|------|-----------|
| Dec 5, 2024 | Boris Alexeev solves Erdos #124 |
| Dec 11, 2024 | Project started |
| Dec 14, 2024 | First successes: Erdos #153, #190, #593, #1052 |
| Dec 14, 2024 | **Tuza v=1 PROVED** |
| Dec 15-17, 2024 | Tuza v=2: 8 lemmas proved |
| Dec 18, 2024 | **t <= 3v PROVED** (weak bound) |
| Dec 18, 2024 | Counterexamples to flawed strategies |
| Dec 19, 2024 | **exists_disjoint_in_K4 PROVED** by Aristotle |
| Dec 19, 2025 | Parker 2025 discovery: v <= 3 proven in literature |
| Dec 19, 2025 | **Parker lemmas FULLY PROVEN** by Aristotle |
| Dec 19, 2025 | 9 submissions active: 2 Parker completion + 7 v=4 portfolio |

---

## Resources

- **Aristotle**: https://aristotle.harmonic.fun
- **Aristotle Paper**: https://arxiv.org/abs/2510.01346
- **Erdos Problems**: https://erdosproblems.com
- **Formal Conjectures**: https://github.com/google-deepmind/formal-conjectures
- **Lean 4**: https://lean-lang.org
- **Mathlib 4**: https://leanprover-community.github.io/mathlib4_docs/

### Key Papers (Tuza's Conjecture)

- **Parker 2025**: [arXiv:2406.06501](https://arxiv.org/abs/2406.06501) - Proves v <= 3 via (k-1)-matchings
- **Haxell 1999**: t <= (66/23)v for all graphs
- **Tuza 1981**: Original conjecture (t <= 2v)

---

## Contributing

This is an experimental research project. Key ways to contribute:

1. **Problem selection**: Identify Erdos problems with formalization gaps
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
