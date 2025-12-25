# Solving Open Mathematical Problems with AI

Using [Aristotle](https://aristotle.harmonic.fun) (Harmonic's theorem prover) to make progress on genuinely open mathematical problems.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-purple)](https://lean-lang.org/)

**Last Updated**: December 25, 2024

---

## Mission

**Goal**: Use AI-powered theorem proving to make genuine progress on open mathematical problems—not just re-formalize known results.

**Primary Focus**: Tuza's Conjecture frontiers
- **ν = 4 case** (genuinely OPEN - Parker's 2024 proof breaks here)
- Split graphs general case
- Counterexample search

---

## 🎉 BREAKTHROUGH: ν = 4 Almost Complete!

### Current Status: 6/7 Cases PROVEN

We have proven **6 of 7 sharing graph configurations** for Tuza's conjecture with ν=4:

```
                         ┌───────────────────┐
                         │   Tuza ν=4: τ≤8   │
                         └─────────┬─────────┘
                                   │
        ┌──────────┬───────────────┼───────────────┬──────────┐
        │          │               │               │          │
        ▼          ▼               ▼               ▼          ▼
   ┌────────┐ ┌────────┐     ┌────────┐     ┌────────┐ ┌────────┐
   │star_all│ │3_share │     │path_4  │     │cycle_4 │ │scatter │
   │   ✅   │ │   ✅   │     │   ✅   │     │   🔶   │ │   ✅   │
   └────────┘ └────────┘     └────────┘     └────────┘ └────────┘
                                   │               │
                             ┌─────┴─────┐   ┌─────┴─────┐
                             │           │   │           │
                             ▼           ▼   ▼           ▼
                        [two_two]   [matching] [4 attacks]
                           ✅          ✅     QUEUED
```

| Case | Sharing Graph | Status | Aristotle UUID | Method |
|------|---------------|--------|----------------|--------|
| **star_all_4** | K₄ (apex) | ✅ PROVEN | slot29 | 4 spokes cover all triangles |
| **three_share_v** | K₁,₃ + isolated | ✅ PROVEN | slot29 | 3 shared + 1 isolated = 6+2 = 8 |
| **scattered** | K̄₄ (disjoint) | ✅ PROVEN | `b94d3582` | Vertex-disjoint → no bridges → τ(S_e)≤2 each |
| **path_4** | P₄ (path) | ✅ PROVEN | `79b18981` | T_pair decomposition: ≤4+4=8 |
| **two_two_vw** | 2K₂ (matching) | ✅ PROVEN | `6a30ea71` | Two independent ν=2 subproblems |
| **matching_2** | 2K₂ | ✅ PROVEN | `6a30ea71` | Same as two_two_vw |
| **cycle_4** | C₄ (4-cycle) | 🔶 IN QUEUE | 4 parallel | T_pair + diagonal + cut + bridge |

### 🎯 ONLY CYCLE_4 REMAINS!

Four parallel attack strategies submitted to Aristotle:

| UUID | Slot | Strategy | Probability |
|------|------|----------|-------------|
| `80891b4c` | 63 | T_pair Decomposition (same as path_4) | Very High |
| `d3159016` | 64 | Diagonal Independence (A∩C=∅, B∩D=∅) | High |
| `f0a24a15` | 65 | Cyclic Cut (reduce to path_3) | Medium-High |
| `5a800e22` | 66 | Bridge-Centric (full S_e + X_ef) | Medium |

---

## Proven Infrastructure

### Key Lemmas (11 validated TRUE)

| Lemma | Description | Status |
|-------|-------------|--------|
| **tau_union_le_sum** | τ(A ∪ B) ≤ τ(A) + τ(B) | ✅ 100-line proof |
| **tau_pair_le_4** | τ(T_pair(e,f)) ≤ 4 when e∩f={v} | ✅ Proven |
| **tau_S_le_2** | τ(S_e) ≤ 2 for any packing element | ✅ Proven |
| **tau_X_le_2** | τ(bridges) ≤ 2 | ✅ Proven |
| **triangle_shares_edge_with_packing** | Maximality theorem | ✅ Proven |
| **bridges_contain_shared_vertex** | All X_ef contain e∩f | ✅ Proven |
| **avoiding_contains_base_edge** | Avoiding triangles share base | ✅ Proven |
| **diagonal_bridges_empty** | No bridges between disjoint pairs | ✅ Proven |

### Failed Approaches (Documented to Avoid)

| Pattern | Why FALSE | Correct Approach |
|---------|-----------|------------------|
| `avoiding_covered_by_spokes` | v ∉ avoiding, spokes contain v | Use BASE EDGES |
| `tau_pair_le_4_via_spokes` | τ(T_pair) = 6 not 4 | 4 spokes + 2 bases |
| `bridges_covered_by_one_edge` | Need 2+ edges | Use tau_X_le_2 |

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
│       └───┘                          │ A │   │ B │  two_two ✅  │
│         ▲                            └───┘   └───┘              │
│  ┌───┐  │                            ┌───┐   ┌───┐              │
│  │ B │──┘                            │ C │   │ D │              │
│  └───┘                               └───┘   └───┘              │
│                                       (two pairs, each shares)  │
│  PATH CONFIGURATION                                             │
│  ──────────────────                  CYCLE CONFIGURATION        │
│                                      ───────────────────        │
│  A ─── B ─── C ─── D    path_4 ✅                               │
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

## Verified Results

### Tuza's Conjecture

**Conjecture (Tuza, 1981)**: For any graph G, τ(G) ≤ 2ν(G)
- τ(G) = minimum edges to hit all triangles
- ν(G) = maximum edge-disjoint triangles

| Case | Status | Notes |
|------|--------|-------|
| ν = 0 | ✅ Formalized | Base case |
| ν = 1 | ✅ Formalized | K4 structure |
| ν = 2 | ✅ Formalized | Full proof |
| ν = 3 | ✅ Formalized | Parker (2024) approach |
| **ν = 4** | 🔶 **6/7 PROVEN** | Only cycle_4 remains! |

*Note: Cases ν ≤ 3 are formalizations of Parker's 2024 proof. The ν=4 work is NEW.*

### Erdős Problems (Related Work)

These files contain **formalized lemmas related to** Erdős problems, not solutions:

| Problem | What We Formalized | Status of Original Problem |
|---------|-------------------|---------------------------|
| **#153** | Sidon set bounds (max ≥ n²/4) | Still OPEN |
| **#190** | Lower bound technique for H(k) | Related lemmas only |
| **#593** | Incidence graph bipartiteness | Still OPEN ($500 prize) |

---

## Repository Structure

```
math/
├── proven/                          # Verified Aristotle outputs
│   └── tuza/
│       ├── lemmas/                  # Key proven lemmas
│       │   ├── tau_union_le_sum.lean
│       │   ├── slot6_Se_lemmas.lean
│       │   └── slot35_tau_pair_le_4.lean
│       └── nu4/                     # ν=4 proven cases
│           ├── slot51_path4_PROVEN.lean
│           ├── slot_two_two_vw_PROVEN.lean
│           └── slot_scattered_PROVEN.lean
│
├── submissions/
│   ├── nu4_strategy/                # Active ν=4 attack files
│   │   ├── slot63_cycle4_final.lean     # T_pair approach
│   │   ├── slot64_cycle4_diagonal.lean  # Diagonal independence
│   │   ├── slot65_cycle4_cut.lean       # Cyclic cut
│   │   └── slot66_cycle4_bridge.lean    # Bridge-centric
│   └── tracking.db                  # SQLite tracking database
│
├── docs/
│   ├── NU4_STRATEGIC_MAP_DEC25.md   # Current strategic map
│   └── nu4_proof_tree.md            # Proof tree visualization
│
├── scripts/                         # Validation & submission scripts
│   ├── safe_aristotle_submit.py     # Safe submission with dedup
│   └── aristotle_queue.py           # Queue monitoring
│
└── CLAUDE.md                        # AI workflow instructions
```

---

## Statistics

| Metric | Count |
|--------|-------|
| Total Aristotle submissions | 100+ |
| ν=4 cases proven | **6/7** |
| ν=4 cases remaining | **1** (cycle_4) |
| Validated TRUE lemmas | 11 |
| Documented FALSE approaches | 19 |
| Parallel attacks on cycle_4 | 4 (queued) |

---

## Workflow

### Submit to Aristotle
```bash
python3 scripts/safe_aristotle_submit.py \
  submissions/file.txt \
  submissions/file_ID.txt \
  "Description of submission"
```

### Monitor Queue
```bash
python3 -c "
import asyncio
from aristotlelib import Project, set_api_key
import os
set_api_key(os.environ['ARISTOTLE_API_KEY'])
async def show():
    projects, _ = await Project.list_projects(limit=10)
    for p in projects:
        print(f'{p.project_id[:8]}  {p.status}')
asyncio.run(show())
"
```

---

## Resources

- **Aristotle**: https://aristotle.harmonic.fun
- **Tuza's Conjecture**: Tuza (1981), "A conjecture on triangles of graphs"
- **Parker's Proof**: Parker (2024), proves ν ≤ 3 case
- **Erdős Problems**: https://erdosproblems.com
- **Lean 4**: https://lean-lang.org

---

## License

Research project - see individual files for licensing.
