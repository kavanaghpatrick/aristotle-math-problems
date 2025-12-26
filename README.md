# Solving Open Mathematical Problems with AI

Using [Aristotle](https://aristotle.harmonic.fun) (Harmonic's theorem prover) to make progress on genuinely open mathematical problems.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-purple)](https://lean-lang.org/)

**Last Updated**: December 25, 2024

---

## Mission

**Goal**: Use AI-powered theorem proving to make genuine progress on open mathematical problems—not just re-formalize known results.

**Primary Focus**: Tuza's Conjecture for ν = 4 (genuinely OPEN - Parker's 2024 proof breaks here)

---

## Current Status: ν = 4

### 3/7 Cases Proven, 4 Remaining

| Case | Sharing Graph | Status | Method |
|------|---------------|--------|--------|
| **star_all_4** | K₄ (apex) | ✅ PROVEN | 4 spokes from shared vertex |
| **three_share_v** | K₁,₃ + isolated | ✅ PROVEN | 3 shared + 1 isolated |
| **scattered** | K̄₄ (disjoint) | ✅ PROVEN | Vertex-disjoint → τ(S_e)≤2 each |
| **cycle_4** | C₄ (4-cycle) | 🔶 IN PROGRESS | All-Middle approach (see below) |
| **path_4** | P₄ (path) | 🔶 IN PROGRESS | Hybrid approach |
| **two_two_vw** | 2K₂ (matching) | 🔶 IN PROGRESS | S_e decomposition |
| **matching_2** | 2K₂ | 🔶 IN PROGRESS | Same as two_two_vw |

### Key Breakthrough: All-Middle Property (slot73)

For **cycle_4**, we have proven the crucial structural lemma:

```lean
lemma cycle4_all_triangles_contain_shared :
    ∀ t ∈ G.cliqueFinset 3, v_ab ∈ t ∨ v_bc ∈ t ∨ v_cd ∈ t ∨ v_da ∈ t
```

**What this means**: Every triangle in a graph with cycle_4 packing structure contains at least one of the 4 shared vertices.

### Current Approach

```
1. ✅ PROVEN: Every triangle contains a shared vertex (All-Middle)
2. 🔶 TO PROVE: τ(triangles at each shared vertex) ≤ 2 (disjoint triples argument)
3. → CONCLUDE: τ ≤ 4 × 2 = 8
```

The "disjoint triples" argument: If we need 3+ edges to cover triangles at vertex v, then 3 edge-disjoint triangles exist at v. These can replace 2 packing elements, contradicting maximality.

---

## Proven Infrastructure

### Validated Lemmas

| Lemma | Description | Status |
|-------|-------------|--------|
| **tau_union_le_sum** | τ(A ∪ B) ≤ τ(A) + τ(B) | ✅ Full 100-line proof |
| **tau_containing_v_in_pair_le_4** | 4 spokes cover containing triangles | ✅ Proven |
| **tau_avoiding_v_in_pair_le_2** | 2 base edges cover avoiding triangles | ✅ Proven |
| **tau_S_le_2** | τ(S_e) ≤ 2 for any packing element | ✅ Proven |
| **triangle_shares_edge_with_packing** | Maximality theorem | ✅ Proven |
| **cycle4_all_triangles_contain_shared** | All-Middle property | ✅ Proven |
| **diagonal_bridges_empty** | No bridges between disjoint pairs | ✅ Proven |

---

## The ν=4 Sharing Graph

When ν=4, the **sharing graph** determines the structure:

```
Sharing Graph Types for ν=4:

┌─────────────────────────────────────────────────────────────────┐
│                                                                 │
│  CONNECTED (≥3 share apex)           DISCONNECTED               │
│  ─────────────────────────           ────────────               │
│                                                                 │
│  ┌───┐                               ┌───┐   ┌───┐              │
│  │ A │──┐     star_all_4 ✅          │ A │   │ C │  scattered ✅│
│  └───┘  │                            └───┘   └───┘              │
│    │    ▼                              (no edges = disjoint)    │
│    │  ┌───┐                                                     │
│    └─▶│ v │◀── All share apex        ┌───┐───┌───┐              │
│       └───┘                          │ A │   │ B │  two_two 🔶  │
│         ▲                            └───┘   └───┘              │
│  ┌───┐  │                            ┌───┐   ┌───┐              │
│  │ B │──┘                            │ C │   │ D │              │
│  └───┘                               └───┘   └───┘              │
│                                       (two pairs, each shares)  │
│  PATH CONFIGURATION                                             │
│  ──────────────────                  CYCLE CONFIGURATION        │
│                                      ───────────────────        │
│  A ─── B ─── C ─── D    path_4 🔶                               │
│                                      A ─── B                    │
│  (linear sharing chain)              │     │     cycle_4 🔶     │
│                                      D ─── C                    │
│                                                                 │
│                                      (4-cycle, opposite pairs   │
│                                       are vertex-disjoint)      │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Repository Structure

```
math/
├── proven/                          # Verified Aristotle outputs
│   └── tuza/
│       └── nu4/                     # ν=4 proven cases & lemmas
│           ├── slot73_eb28d806/     # All-Middle breakthrough
│           ├── slot69-72/           # Infrastructure lemmas
│           └── ...
│
├── submissions/
│   ├── nu4_final/                   # Current attack files
│   ├── nu4_strategy/                # Strategy explorations
│   └── tracking.db                  # SQLite tracking database
│
├── docs/
│   └── STRATEGIC_MAP_V2.md          # Current strategic map
│
├── scripts/                         # Validation & submission scripts
│   ├── aristotle_queue.py           # Queue monitoring
│   └── submit.sh                    # Submission wrapper
│
└── CLAUDE.md                        # AI workflow instructions
```

---

## Statistics

| Metric | Count |
|--------|-------|
| Total Aristotle submissions | 100+ |
| ν=4 cases proven | **3/7** |
| ν=4 cases remaining | **4** |
| Active Aristotle jobs | 4 |
| Validated TRUE lemmas | 15+ |

---

## Resources

- **Aristotle**: https://aristotle.harmonic.fun
- **Tuza's Conjecture**: Tuza (1981), "A conjecture on triangles of graphs"
- **Parker's Proof**: Parker (2024), proves ν ≤ 3 case
- **Lean 4**: https://lean-lang.org

---

## License

Research project - see individual files for licensing.
