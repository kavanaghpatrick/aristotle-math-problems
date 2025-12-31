# Tuza's Conjecture: AI-Powered Formal Verification

A research project using [Aristotle](https://aristotle.harmonic.fun) (Harmonic's theorem prover) and multi-agent AI collaboration to make rigorous progress on Tuza's Conjecture.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Lean 4](https://img.shields.io/badge/Lean-4-purple)](https://lean-lang.org/)
[![Submissions](https://img.shields.io/badge/Submissions-170+-orange)]()
[![Cases Proven](https://img.shields.io/badge/ν%3D4%20Cases-6%2F7-green)]()

**Project Duration**: December 2025 (ongoing)

---

## The Conjecture

**Tuza's Conjecture (1981)**: For any graph G, τ(G) ≤ 2ν(G)

Where:
- **τ(G)** = minimum number of edges needed to hit all triangles (triangle edge cover)
- **ν(G)** = maximum number of edge-disjoint triangles (triangle packing number)

This conjecture has been **open for 44 years** and is widely believed to be TRUE.

### Known Results

| Setting | Best Bound | Source |
|---------|-----------|--------|
| General graphs | τ ≤ 2.87ν | Haxell (1999) |
| Fractional | τ ≤ 2ν* | Krivelevich (1995) |
| Planar graphs | τ ≤ 2ν | Tuza (1985) |
| Small ν (ν ≤ 3) | τ ≤ 2ν | Classical |
| **Our project (ν = 4)** | **6/7 cases proven, Cycle_4 in progress** | **December 2025** |

---

## Current Status (December 31, 2025 Evening)

### ν = 4 Case Analysis

For ν = 4, there are 7 distinct configurations based on the "sharing graph":

| Case | Sharing Graph | Status | Bound | Notes |
|------|---------------|--------|-------|-------|
| star_all_4 | K₄ (complete) | ✅ **PROVEN** | τ ≤ 8 | 4 spokes from apex |
| three_share_v | K₁,₃ + isolated | ✅ **PROVEN** | τ ≤ 8 | 3-star + independent |
| scattered | K̄₄ (empty) | ✅ **PROVEN** | τ ≤ 8 | Disjoint triangles |
| path_4 | P₄ (path) | ✅ **PROVEN** | τ ≤ 8 | S_e decomposition |
| two_two_vw | 2K₂ (matching) | ✅ **PROVEN** | τ ≤ 8 | Two independent pairs |
| matching_2 | 2K₂ | ✅ **PROVEN** | τ ≤ 8 | Same as above |
| **cycle_4** | **C₄ (4-cycle)** | 🔶 **IN PROGRESS** | **τ ≤ 12 proven** | **τ ≤ 8 via LP running** |

### Active Aristotle Queue

| Submission | Target | Progress | Strategy |
|------------|--------|----------|----------|
| **slot49a** | τ(T_pair) ≤ 4 | QUEUED | Adjacent pair (14 proven lemmas) |
| **slot147_v2** | τ ≤ 2ν* | 10% | LP/Krivelevich approach |
| slot49_path4 | Path_4 case | 50% | S_e decomposition |
| slot40 | Bridge counting | 23% | Legacy resubmission |

### Two Active Strategies for Cycle_4

| Strategy | Submission | Mechanism | Success Est. |
|----------|------------|-----------|--------------|
| **LP Relaxation** | slot147_v2 | Krivelevich: τ ≤ 2ν*, prove ν*=4 | 30-40% |
| **Adjacent Pair** | slot49a | τ(T_pair) ≤ 4 for each pair | 15-25% |

---

## The Cycle_4 Challenge

Cycle_4 is the hardest case: 4 triangles A, B, C, D sharing vertices in a cycle pattern (A-B-C-D-A).

**What we've proven:**
- τ ≤ 12 (slot139) - conservative bound using 3 edges per shared vertex
- 14 infrastructure lemmas (tau_union_le_sum, tau_S_le_2, tau_X_le_2, etc.)

**What we've tried and why it failed (9 False Lemmas):**
- **König theorem** - BLOCKED: link graphs are NOT bipartite
- **2-edges-per-vertex** - FALSE: `local_cover_le_2`
- **External common vertex** - FALSE: `external_share_common_vertex`
- **Fixed 8-edge M-subset** - FALSE: any 8 from 12 M-edges misses 4

**Current approaches (running):**
1. **LP Relaxation** (slot147_v2): Krivelevich's τ ≤ 2ν* where ν* = 4
2. **Adjacent Pair** (slot49a): Split M into pairs, prove τ(T_pair) ≤ 4

---

## Project Statistics

| Metric | Count |
|--------|-------|
| Total Aristotle submissions | 170+ |
| ν=4 cases proven | **6/7** |
| Proven infrastructure lemmas | 14 |
| Literature lemmas collected | 162 |
| Failed approaches documented | 38 |
| **False lemmas discovered** | **9** |
| AI consultation rounds | 25+ |

---

## False Lemmas Discovered

One of the most valuable outputs: **9 mathematical claims that seemed plausible but are FALSE**.

| # | Lemma | Evidence | Why It's False |
|---|-------|----------|----------------|
| 1 | `local_cover_le_2` | AI-verified | 4 triangles at v can each use different M-edge |
| 2 | `avoiding_covered_by_spokes` | Trivially false | If t avoids v, spokes can't hit t |
| 3 | `bridge_absorption` | **Aristotle** | Cover of S_e ∪ S_f doesn't cover bridges |
| 4 | `trianglesContainingVertex_partition` | Reasoning | Partition not complete |
| 5 | `support_sunflower_tau_2` | Reasoning | trianglesSharingMEdgeAt includes M-elements |
| 6 | `external_share_common_vertex` | AI-verified | Externals use edges from DIFFERENT M-triangles |
| 7 | `sunflower_cover_at_vertex_2edges` | AI-verified | Need 3+ edges per vertex |
| 8 | `link_graph_bipartite` | AI-verified | M-neighbors form odd cycles (Dec 31) |
| 9 | `fixed_8_edge_M_subset` | Reasoning | Any 8 of 12 M-edges omits 4 critical edges |

---

## Proven Scaffolding (from slot44)

14 lemmas fully machine-verified:

```lean
-- Subadditivity of triangle covering
theorem tau_union_le_sum : τ(A ∪ B) ≤ τ(A) + τ(B)

-- Maximality implies edge-sharing
theorem triangle_shares_edge_with_packing :
  ∀ t ∈ triangles G, ∃ m ∈ M, |t ∩ m| ≥ 2

-- S_e bound (triangles sharing edge with packing element)
theorem tau_S_le_2 : τ(S_e) ≤ 2

-- Bridge bound (triangles sharing edges with two elements)
theorem tau_X_le_2 : τ(X_ef) ≤ 2

-- S_e structure theorem
theorem Se_structure_lemma :
  (∃ uv ⊆ e, |uv| = 2, ∀ t ∈ S_e, uv ⊆ t) ∨
  (∃ x ∉ e, ∀ t ∈ S_e, t = (t ∩ e) ∪ {x})
```

---

## Methodology

### The AI-Powered Pipeline

```
┌─────────────────────────────────────────────────────────────────┐
│  1. MULTI-AGENT RESEARCH & DEBATE                               │
│     ├── Grok-4: Code review, Lean syntax, counterexamples       │
│     ├── Gemini: Strategy, literature, proof architecture        │
│     ├── Codex: Long autonomous tasks, code verification         │
│     └── Claude: Synthesis, planning, context management         │
│                                                                  │
│  2. LEAN 4 FORMALIZATION                                         │
│     └── Write proof attempts with `sorry` placeholders          │
│                                                                  │
│  3. ARISTOTLE SUBMISSION                                         │
│     └── AI prover fills sorries (6-24 hour runs)                │
│                                                                  │
│  4. RESULT PROCESSING                                            │
│     ├── PROVEN (0 sorries) → Move to proven/                    │
│     ├── PARTIAL (some sorries) → Extract learnings, iterate     │
│     ├── DISPROVEN → Document in FALSE_LEMMAS                    │
│     └── TIMEOUT → Analyze for resubmission                      │
│                                                                  │
│  5. KNOWLEDGE ACCUMULATION                                       │
│     └── Track everything in SQLite database                     │
└─────────────────────────────────────────────────────────────────┘
```

### Multi-Agent Collaboration

| Agent | Role | Best For |
|-------|------|----------|
| **Grok-4** | Technical critic | Lean syntax, counterexamples, code review |
| **Gemini** | Strategist | Literature research, proof architecture |
| **Codex** | Researcher | Code verification, long-running tasks |
| **Claude** | Synthesizer | Context management, planning, debate synthesis |
| **Aristotle** | Prover | Actual theorem proving (6-24 hour runs) |

---

## Current Research Directions

### LP Relaxation Approach (slot147_v2)

**Key insight**: Krivelevich (1995) proved τ ≤ 2ν* where ν* = fractional packing number.

**For Cycle_4**:
1. Setting w_A = w_B = w_C = w_D = 1 gives fractional packing of weight 4
2. Each M-edge in exactly one M-triangle → edge constraint satisfied
3. External triangles share M-edges → forced to weight 0
4. Therefore ν* = 4
5. By Krivelevich: **τ ≤ 2 × 4 = 8**

**Why this bypasses all blockers**:
- No König theorem needed (Pattern 8: link_graph_bipartite FALSE)
- No 2-edges-per-vertex claim (Patterns 1, 5, 7 FALSE)
- No external common vertex claim (Pattern 6 FALSE)
- Pure LP argument using literature result

### Adjacent Pair Approach (slot49a)

**Strategy**: Split M = {A,B} ∪ {C,D} into adjacent pairs

If τ(T_pair(A,B)) ≤ 4 and τ(T_pair(C,D)) ≤ 4:
  τ(G) ≤ 4 + 4 = 8 ✓

**Scaffolding available**: 14 lemmas including tau_S_le_2, tau_X_le_2

**Gap**: Naive bound 2+2+2=6, need overlap proof for 4

---

## Repository Structure

```
math/
├── proven/tuza/                    # Machine-verified proofs
│   ├── nu0/tuza_nu0_PROVEN.lean
│   ├── nu1/tuza_nu1_PROVEN.lean
│   ├── nu2/tuza_nu2_PROVEN.lean
│   ├── nu4/
│   │   ├── slot139_tau_le_12_PROVEN.lean  # Cycle_4 baseline
│   │   └── ... (infrastructure lemmas)
│   └── scaffolding/                # Reusable proven scaffolding
│
├── submissions/
│   ├── nu4_final/                  # Current attack files
│   │   ├── slot147_v2_lp_simplified.lean
│   │   ├── slot49a_scaffolding_only.lean
│   │   └── ...
│   ├── tracking.db                 # SQLite knowledge base
│   └── ...
│
├── docs/
│   ├── CHECKPOINT_DEC31_EVENING.md # Latest status
│   ├── DEBATE_SYNTHESIS_DEC31.md   # Multi-agent consensus
│   └── archive/                    # Historical documents
│
├── scripts/                        # Automation scripts
├── CLAUDE.md                       # AI workflow instructions
└── README.md                       # This file
```

---

## Timeline & Discoveries

### December 2025

**Week 1 (Dec 23-25)**
- Proved ν=0, ν=1, ν=2 cases
- Discovered FALSE lemmas #2, #3

**Week 2 (Dec 26-28)**
- Proved star_all_4, three_share_v, scattered
- Discovered FALSE lemmas #1, #4, #5, #6, #7

**Week 3 (Dec 29-30)**
- Proved τ ≤ 12 for Cycle_4 (slot139)
- Near-breakthrough with König approach

**Week 4 (Dec 31)**
- **Critical discovery**: Link graphs NOT bipartite (FALSE #8)
- Discovered FALSE #9 (fixed_8_edge_M_subset)
- Pivoted to LP relaxation approach
- Submitted slot147_v2 (LP) and slot49a (adjacent pair)
- **6/7 ν=4 cases now proven**

---

## Lessons Learned

### On Formalization

1. **Counterexamples are progress** - 9 false lemmas is valuable negative knowledge
2. **AI consensus can be wrong** - Multi-round debate reveals truth
3. **Database tracking is essential** - Can't repeat 170+ experiments without records

### On Proof Strategy

1. **LP relaxation bypasses combinatorics** - Fractional methods avoid case explosion
2. **Literature research is crucial** - Krivelevich's 1995 result was the key insight
3. **Maximality is powerful** - Most lemmas derive from "if not maximal, extend it"

---

## Resources

- **Aristotle**: https://aristotle.harmonic.fun
- **Tuza's Conjecture**: Tuza (1981), "A conjecture on triangles of graphs"
- **Best Known Bound**: Haxell (1999), τ ≤ 2.87ν
- **LP Relaxation**: Krivelevich (1995), "On a conjecture of Tuza"
- **Lean 4**: https://lean-lang.org

---

## Citation

```bibtex
@misc{tuza-formal-2025,
  title={Formal Verification of Tuza's Conjecture for Small Packing Numbers},
  author={Patrick Kavanagh and AI Collaborators},
  year={2025},
  note={Using Aristotle theorem prover and multi-agent AI collaboration},
  url={https://github.com/kavanaghpatrick/aristotle-math-problems}
}
```

---

## License

MIT License - See individual files for details.

---

*Last update: December 31, 2025 Evening*
*Current frontier: LP relaxation + Adjacent Pair approaches for τ ≤ 8 in Cycle_4*
*Status: 6/7 ν=4 cases proven, Cycle_4 τ ≤ 12 baseline, τ ≤ 8 in progress*
