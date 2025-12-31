# Tuza's Conjecture: AI-Powered Formal Verification

A research project using [Aristotle](https://aristotle.harmonic.fun) (Harmonic's theorem prover) and multi-agent AI collaboration to make rigorous progress on Tuza's Conjecture.

[![Aristotle](https://img.shields.io/badge/Powered%20by-Aristotle-blue)](https://aristotle.harmonic.fun)
[![Lean 4](https://img.shields.io/badge/Lean-4-purple)](https://lean-lang.org/)
[![Submissions](https://img.shields.io/badge/Submissions-168-orange)]()
[![Proven](https://img.shields.io/badge/Fully%20Proven-14-green)]()

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
| **Our project (ν = 4)** | **τ ≤ 12 proven, τ ≤ 8 in progress** | **December 2025** |

---

## Current Status

### ν = 4 Case Analysis

For ν = 4, there are 7 distinct configurations based on the "sharing graph" (how the 4 packing triangles share vertices):

| Case | Sharing Graph | Status | Bound | Notes |
|------|---------------|--------|-------|-------|
| star_all_4 | K₄ (complete) | ✅ **PROVEN** | τ ≤ 8 | 4 spokes from apex |
| three_share_v | K₁,₃ + isolated | ✅ **PROVEN** | τ ≤ 8 | 3-star + independent |
| scattered | K̄₄ (empty) | ✅ **PROVEN** | τ ≤ 8 | Disjoint triangles |
| path_4 | P₄ (path) | 🔶 Partial | τ ≤ 8 | Near-complete |
| two_two_vw | 2K₂ (matching) | 🔶 Partial | τ ≤ 8 | Two pairs |
| matching_2 | 2K₂ | 🔶 Partial | τ ≤ 8 | Same as above |
| **cycle_4** | **C₄ (4-cycle)** | 🔶 **Partial** | **τ ≤ 12 proven** | **τ ≤ 8 via LP in progress** |

### The Cycle_4 Challenge

Cycle_4 is the hardest case: 4 triangles A, B, C, D sharing vertices in a cycle pattern (A-B-C-D-A).

**What we've proven:**
- τ ≤ 12 (slot139, 0 sorries) - conservative bound using 3 edges per shared vertex

**What we've tried and why it failed:**
- **König theorem approach** - BLOCKED because link graphs are NOT bipartite (discovered Dec 31)
- **2-edges-per-vertex sunflower** - FALSE lemma `local_cover_le_2`
- **External common vertex** - FALSE lemma `external_share_common_vertex`
- **Fixed 8-edge M-subset** - FALSE lemma `fixed_8_edge_M_subset`

**Current approach (in progress):**
- **LP Relaxation** (slot147, submitted): Using Krivelevich's τ ≤ 2ν* where ν* = fractional packing
- Key insight: If ν* = 4 for Cycle_4, then τ ≤ 8 immediately, bypassing all König issues

---

## Project Statistics

| Metric | Count |
|--------|-------|
| Total Aristotle submissions | 168 |
| Fully proven (0 sorries) | 14 |
| Completed submissions | 80 |
| Literature lemmas collected | 162 |
| Validated true lemmas | 54 |
| Failed approaches documented | 38 |
| **False lemmas discovered** | **9** |
| AI consultation rounds | 21 |

---

## False Lemmas Discovered

One of the most valuable outputs of this project: **9 mathematical claims that seemed plausible but are FALSE**.

| # | Lemma | Evidence | Why It's False |
|---|-------|----------|----------------|
| 1 | `local_cover_le_2` | AI-verified | 4 triangles at v_ab can each use different M-edge |
| 2 | `avoiding_covered_by_spokes` | Trivially false | If t avoids v, then v ∉ t, so spokes can't hit t |
| 3 | `bridge_absorption` | **Aristotle-verified** | Cover of S_e ∪ S_f doesn't automatically cover bridges |
| 4 | `trianglesContainingVertex_partition` | Reasoning | Triangle can contain v but share M-edge elsewhere |
| 5 | `support_sunflower_tau_2` | Reasoning | trianglesSharingMEdgeAt INCLUDES M-elements |
| 6 | `external_share_common_vertex` | AI-verified | Externals can use edges from DIFFERENT M-triangles |
| 7 | `sunflower_cover_at_vertex_2edges` | AI-verified | Need 3+ edges: one for A, one for B, one for externals |
| 8 | `link_graph_bipartite` | AI-verified | M-neighbors can form odd cycles (Dec 31 discovery) |
| 9 | `fixed_8_edge_M_subset` | Reasoning | Any 8 of 12 M-edges omits 4 edges some triangle needs |

Full details with counterexamples: See `docs/FALSE_LEMMAS.md` (auto-generated from database)

---

## Methodology

### The AI-Powered Pipeline

```
┌─────────────────────────────────────────────────────────────────┐
│  1. MULTI-AGENT RESEARCH & DEBATE                               │
│     ├── Grok-4: Code review, Lean syntax, counterexamples       │
│     ├── Gemini: Strategy, literature, proof architecture        │
│     ├── Codex: Web research, long autonomous tasks              │
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
| **Grok-4** | Technical critic | Lean syntax errors, counterexamples, code review |
| **Gemini** | Strategist | Literature research, proof architecture, big picture |
| **Codex** | Researcher | Web search, long-running autonomous tasks |
| **Claude** | Synthesizer | Context management, planning, debate synthesis |
| **Aristotle** | Prover | Actual theorem proving (6-24 hour runs) |

### Database-Driven Tracking

All knowledge is stored in `submissions/tracking.db`:

```sql
-- Key tables
submissions       -- All 168 Aristotle jobs with results
literature_lemmas -- 162 lemmas from papers and proofs
failed_approaches -- 38 documented failures with reasons
false_lemmas      -- 9 disproven claims with counterexamples
nu4_cases         -- Status of each ν=4 configuration
ai_consultations  -- 21 multi-agent debate records
```

---

## Key Proven Results

### Infrastructure Lemmas (Machine-Verified)

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
```

### Case-Specific Results

```lean
-- Star case: all 4 triangles share a common vertex
theorem tau_le_8_star_all_4 : τ(G) ≤ 8

-- Scattered case: 4 disjoint triangles
theorem tau_le_8_scattered : τ(G) ≤ 8

-- Cycle_4 conservative bound
theorem tau_le_12_cycle4 : τ(G) ≤ 12
```

---

## Promising Resubmission Candidates

Analysis of 168 submissions identified these high-value candidates:

### Tier 1: Immediate Resubmit (Clean Timeouts)

| Slot | Sorries | Proven | Assessment | Action |
|------|---------|--------|------------|--------|
| slot44 | 1 | 11 | Clean timeout, high-value | ✅ **Resubmit** |
| slot70 | 1 | 9 | Budget reached, main proven | ✅ **Resubmit** |
| slot71 | 1 | 5 | 99% complete, exact? timeout | ✅ **Resubmit** |
| slot72 | 1 | 9 | Clean, high probability | ✅ **Resubmit** |
| slot51 | 2 | 5 | Main theorem proven! | ✅ **Resubmit** |

### Tier 2: Fix Then Resubmit

| Slot | Sorries | Proven | Issue | Fix Required |
|------|---------|--------|-------|--------------|
| slot61 | 1 | 15 | Sym2.mk syntax | Change to `Sym2.mk (a, b)` |
| slot40 | 2 | 10 | Missing scaffolding | Copy proofs from slot29 |
| slot49 | 1 | 6 | Incomplete proof | Add explicit cover construction |

### Tier 3: Extract Proven Lemmas Only

| Slot | Sorries | Proven | Issue | Salvage |
|------|---------|--------|-------|---------|
| slot41 | 1 | 8 | **Already SUCCESS** | Main theorems proven! |
| slot127 | 3 | 6 | Math difficulty | Extract 4 disjoint lemmas |
| slot144 | 5 | 3 | König FALSE | Extract 3 proven lemmas |

### Tier 4: Do Not Resubmit (FALSE Lemmas)

| Slot | Sorries | Proven | Problem |
|------|---------|--------|---------|
| slot39 | 1 | 16 | Contains `bridge_absorption` FALSE lemma |
| slot60 | 1 | 20 | Contains `avoiding_covered_by_spokes` FALSE |
| slot57 | 1 | 10 | Contains `avoiding_covered_by_spokes` FALSE |

---

## Repository Structure

```
math/
├── proven/tuza/                    # Machine-verified proofs (38 files)
│   ├── nu0/tuza_nu0_PROVEN.lean
│   ├── nu1/tuza_nu1_PROVEN.lean
│   ├── nu2/tuza_nu2_PROVEN.lean
│   ├── nu4/
│   │   ├── slot139_tau_le_12_PROVEN.lean  # Current best for Cycle_4
│   │   └── ... (infrastructure lemmas)
│   └── lemmas/                     # Reusable proven lemmas
│
├── submissions/
│   ├── nu4_final/                  # Current attack files
│   │   ├── slot147_lp_relaxation.lean  # LP approach (in progress)
│   │   └── ...
│   ├── tracking.db                 # SQLite knowledge base
│   └── ...
│
├── docs/
│   ├── FALSE_LEMMAS.md             # Auto-generated from database
│   ├── CHECKPOINT_DEC31_FINAL.md   # Latest status checkpoint
│   └── archive/                    # Historical documents
│
├── scripts/
│   ├── generate_false_lemmas_md.sh # Regenerate docs from DB
│   └── ...
│
├── CLAUDE.md                       # AI workflow instructions
└── README.md                       # This file
```

---

## Timeline & Discoveries

### December 2025

**Week 1 (Dec 23-25)**
- Proved ν=0, ν=1, ν=2 cases
- Started ν=4 systematic attack
- Discovered FALSE lemma #2 (avoiding_covered_by_spokes)
- Discovered FALSE lemma #3 (bridge_absorption) via Aristotle

**Week 2 (Dec 26-28)**
- Proved star_all_4, three_share_v, scattered cases
- Discovered FALSE lemmas #1, #4, #5 (local_cover_le_2, etc.)
- AI debate revealed external triangle structure issues

**Week 3 (Dec 29-30)**
- Near-breakthrough with König theorem approach
- Proved τ ≤ 12 for Cycle_4 (slot139)
- Discovered FALSE lemmas #6, #7 (external_share_common_vertex)

**Week 4 (Dec 31)**
- **Critical discovery**: Link graphs are NOT bipartite (FALSE lemma #8)
- König approach invalidated
- Discovered FALSE lemma #9 (fixed_8_edge_M_subset)
- Pivoted to LP relaxation approach
- Submitted slot147 (Krivelevich τ ≤ 2ν*)

---

## Current Research Direction

### LP Relaxation Approach (slot147)

**Key insight**: Krivelevich (1995) proved τ ≤ 2ν* where ν* = fractional packing number.

**For Cycle_4**:
1. Setting x_A = x_B = x_C = x_D = 1 gives fractional packing of weight 4
2. This saturates all M-edges (each M-edge in exactly one M-triangle)
3. External triangles share M-edges → forced to weight 0
4. Therefore ν* = 4
5. By Krivelevich: **τ ≤ 2 × 4 = 8**

**Why this bypasses all blockers**:
- No König theorem needed (Pattern 8: link_graph_bipartite FALSE)
- No 2-edges-per-vertex claim (Patterns 1, 5, 7 FALSE)
- No external common vertex claim (Pattern 6 FALSE)
- Pure LP argument using literature result

**Status**: Submitted to Aristotle (UUID: d5e0feb5-5b3d-463e-be95-79e4612535ac)

---

## Lessons Learned

### On Formalization

1. **Counterexamples are progress** - 9 false lemmas is valuable negative knowledge
2. **AI consensus can be wrong** - Dec 30 said "bipartite"; Dec 31 proved FALSE
3. **Multi-round debate reveals truth** - Single-round consensus is unreliable
4. **Database tracking is essential** - Can't repeat 168 experiments without records

### On Proof Strategy

1. **Existential beats constructive** - Proving ∃ cover is easier than building one
2. **LP relaxation bypasses combinatorics** - Fractional methods avoid case explosion
3. **Literature research is crucial** - Krivelevich's 1995 result was the key insight
4. **Maximality is powerful** - Most lemmas derive from "if not maximal, extend it"

### On Multi-Agent Collaboration

1. **Different agents have different strengths** - Use Grok for code, Gemini for strategy
2. **Parallel research is efficient** - 6 agents analyzing simultaneously
3. **Debate synthesizes truth** - Disagreement leads to counterexamples
4. **Track consultations** - Recommendations without outcomes aren't learnings

---

## Future Directions

### Immediate (January 2025)
1. Complete LP relaxation proof (slot147 result)
2. Resubmit promising timeout candidates (slot44, slot70, slot71, slot72)
3. Fix and resubmit slot61 (syntax issues only)

### Short-term (Q1 2025)
1. Complete all ν=4 cases with τ ≤ 8 bounds
2. Begin ν=5 characterization
3. Formalize LP relaxation machinery in Mathlib
4. Publish: "Tuza's Conjecture for ν ≤ 4: A Formal Proof"

### Medium-term (2025)
1. Attack special graph classes (chordal, interval - still OPEN!)
2. Build inductive framework: ν=k → ν=k+1
3. Investigate computational search for τ > 2ν counterexamples
4. Contribute LP machinery to Mathlib

---

## How to Contribute

### Areas Where Help is Welcome

1. **LP/Fractional relaxation** - Formalizing τ* = ν* machinery in Lean
2. **Counterexample search** - Computational search for graphs with τ > 2ν
3. **Special graph classes** - Proving Tuza for chordal, interval graphs
4. **Mathlib contributions** - Missing lemmas for fractional optimization
5. **Documentation** - Improving proof explanations and tutorials

### Getting Started

```bash
# Clone the repository
git clone https://github.com/kavanaghpatrick/aristotle-math-problems.git
cd aristotle-math-problems

# Explore the database
sqlite3 submissions/tracking.db

# Key queries
SELECT * FROM nu4_cases;                    -- Case status
SELECT * FROM false_lemmas;                 -- What NOT to use
SELECT * FROM failed_approaches LIMIT 10;  -- What didn't work
```

---

## Resources

- **Aristotle**: https://aristotle.harmonic.fun
- **Tuza's Conjecture**: Tuza (1981), "A conjecture on triangles of graphs"
- **Best Known Bound**: Haxell (1999), τ ≤ (66/23)ν ≈ 2.87ν
- **LP Relaxation**: Krivelevich (1995), "On a conjecture of Tuza"
- **Lean 4**: https://lean-lang.org
- **Mathlib**: https://github.com/leanprover-community/mathlib4

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

*Last update: December 31, 2025*
*Current frontier: LP relaxation for τ ≤ 8 in Cycle_4*
*Status: 3/7 ν=4 cases fully proven, 4 partial, τ ≤ 12 baseline established*
