# Solving Open Mathematical Problems with AI

Using [Aristotle](https://aristotle.harmonic.fun) (Harmonic's theorem prover) to solve open mathematical problems.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-purple)](https://lean-lang.org/)

**Last Updated**: December 22, 2025

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

#### Key Breakthrough (December 22, 2025)

**`tau_union_le_sum` PROVEN** - The critical union bound lemma:
```lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B
```

This enables the full inductive proof for Tuza ν ≤ 4.

#### Proven Lemmas (No Sorry, Correct Definitions)

| Lemma | Description | File |
|-------|-------------|------|
| **tau_union_le_sum** | τ(A ∪ B) ≤ τ(A) + τ(B) | `proven/tuza/lemmas/tau_union_le_sum.lean` |
| **tau_v_decomposition** | V-decomposition corollary | `proven/tuza/lemmas/tau_union_le_sum.lean` |
| **tuza_nu2** | ν=2 implies τ≤4 | `proven/tuza/nu2/tuza_nu2_PROVEN.lean` |
| **Parker Lemma 2.2** | S_e triangles pairwise share edges | `proven/tuza/lemmas/parker_lemmas.lean` |
| **Parker Lemma 2.3** | ν(G\T_e) = ν(G) - 1 | `proven/tuza/lemmas/parker_lemmas.lean` |
| **inductive_bound** | τ(G) ≤ τ(T_e) + τ(G\T_e) | `proven/tuza/lemmas/parker_lemmas.lean` |
| **tau_S_le_2** | τ(S_e) ≤ 2 | `proven/tuza/lemmas/parker_lemmas.lean` |
| **Base Case ν=0** | ν=0 implies τ=0 | `proven/tuza/lemmas/parker_lemmas.lean` |

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
- **tau_union_le_sum** - The key union bound (December 22, 2025)
- **tuza_nu2** - Full proof for ν=2 case
- Parker's structural lemmas (2.2, 2.3, inductive_bound, tau_S_le_2)
- Base cases ν=0, ν=1
- Several Erdős problems

### What's In Progress
- **tuza_nu4** - Using `tau_union_le_sum` for full inductive proof
- Submission `slot17_tuza_nu4.lean` ready (awaiting slot availability)
- 13 Aristotle jobs currently running

### Proof Strategy for ν=4
```
τ(G) ≤ τ(T_e) + τ(G\T_e)     [inductive_bound]
     ≤ 2 + τ(G\T_e)          [tau_Te_le_2]
     where ν(G\T_e) = 3      [lemma_2_3]
     ≤ 2 + 6 = 8             [tuza_nu3 recursively]
```

### Known Issues
- Earlier submissions used incorrect definitions that allowed non-graph edges
- These have been archived in `submissions/CORRUPTED/`
- All new work uses `G.edgeFinset.powerset` restriction

---

## Repository Structure

```
math/
├── proven/
│   └── tuza/
│       ├── lemmas/
│       │   ├── tau_union_le_sum.lean   # THE BREAKTHROUGH
│       │   └── parker_lemmas.lean      # All Parker infrastructure
│       ├── nu0/                        # Base case proofs
│       ├── nu1/
│       └── nu2/
│           └── tuza_nu2_PROVEN.lean    # Full ν=2 proof
├── submissions/
│   ├── nu4_portfolio/
│   │   ├── slot17_tuza_nu4.lean        # Main closing submission
│   │   └── slot16_tau_union_v2.lean    # tau_union_le_sum (PROVEN)
│   ├── erdos*_SUCCESS.lean             # Erdős successes
│   └── CORRUPTED/                      # Archived invalid files
├── submissions/tracking.db             # SQLite database
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
