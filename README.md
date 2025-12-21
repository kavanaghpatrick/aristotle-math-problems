# Solving Open Mathematical Problems with AI

Using [Aristotle](https://aristotle.harmonic.fun) (Harmonic's theorem prover) to solve open mathematical problems.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-purple)](https://lean-lang.org/)

**Last Updated**: December 20, 2025

---

## Verified Results

### Erdős Problems (Fully Proven, No Sorry)

| Problem | Result | File |
|---------|--------|------|
| **Erdős #153** | Sidon set sumset bounds | `erdos153_v4_SUCCESS.lean` |
| **Erdős #190** | Divisibility result | `erdos190_SUCCESS.lean` |
| **Erdős #593** | Partition result | `erdos593_SUCCESS.lean` |

### Tuza's Conjecture Infrastructure

**Conjecture (Tuza, 1981)**: For any graph G, τ(G) ≤ 2ν(G)
- τ(G) = minimum edges to hit all triangles
- ν(G) = maximum edge-disjoint triangles

#### Proven Lemmas (No Sorry, Correct Definitions)

| Lemma | Description | File |
|-------|-------------|------|
| **Parker Lemma 2.2** | S_e triangles pairwise share edges | `aristotle_parker_proven.lean` |
| **Base Case ν=0** | ν=0 implies τ=0 | `aristotle_tuza_nu1_PROVEN.lean` |

#### Correct Definitions Required

Triangle covering must use **actual graph edges** (not arbitrary Sym2 elements):

```lean
def isTriangleCover (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧  -- MUST be subset of graph edges
  ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2
```

---

## Current Status

### What's Proven
- Parker's structural lemmas for the inductive approach
- Base case ν=0
- Several Erdős problems

### What's In Progress
- Correct formalization of τ(T_e) ≤ 2 for ν ≤ 3
- Submission `tuza_nu3_FIXED.lean` (UUID: 4736da84) running with correct definitions

### Known Issues
- Earlier submissions used incorrect definitions that allowed non-graph edges
- These have been archived in `submissions/CORRUPTED/`
- All new work uses `G.edgeFinset.powerset` restriction

---

## Repository Structure

```
math/
├── submissions/
│   ├── aristotle_parker_proven.lean    # Parker Lemma 2.2 (verified)
│   ├── aristotle_tuza_nu1_PROVEN.lean  # Base case (verified)
│   ├── erdos*_SUCCESS.lean             # Erdős successes
│   ├── tuza_nu3_FIXED.lean             # Correct definitions (running)
│   └── CORRUPTED/                      # Archived invalid files
├── docs/
│   └── CONTAMINATION_REPORT.md         # Details on formalization issues
└── README.md
```

---

## Quick Start

```bash
# Validate before submitting
lake env lean submissions/file.lean

# Submit to Aristotle
aristotle prove-from-file submissions/file.lean --no-wait
```

---

## Resources

- **Aristotle**: https://aristotle.harmonic.fun
- **Erdős Problems**: https://erdosproblems.com
- **Lean 4**: https://lean-lang.org

---

## License

Research project - see individual files for licensing.
