# Tuza ν=4 Proof Strategy Debate Context
## Date: January 31, 2026

## Mission
Prove Tuza's conjecture τ(G) ≤ 2ν(G) for the case ν=4, meaning τ ≤ 8.

---

## CURRENT STATUS

### What IS Proven (Mathematically Sound)
| Case | Status | Details |
|------|--------|---------|
| **path_4** | ✅ COMPLETE | 107 theorems via 3-case split (slot451-453) |
| **cycle_4** | ✅ τ≤8 PROVEN | slot139, tau_le_8_cycle4 |
| **star_all_4** | Partial | 2 sorries in tau_le_8_triple_apex |
| **three_share_v** | Partial | 2 sorries in tau_le_8_triple_apex |
| **scattered** | Partial | τ≤12 proven, τ≤8 has sorry |
| **two_two_vw** | Partial | τ≤12 proven, τ≤8 needs work |
| **matching_2** | Partial | Same as two_two_vw |

### Key Proven Lemmas (70+ validated)
- `tau_S_le_2`: τ(S_e) ≤ 2 for exclusive externals
- `tau_X_le_2`: τ(X_ef) ≤ 2 for bridges
- `tau_pair_le_6`: τ(T_pair) ≤ 6 (4 spokes + 2 bases) - **CORRECT bound**
- `tau_union_le_sum`: Subadditivity of covering number
- `triangle_shares_edge_with_packing`: Maximality of packing
- `externals_share_edge`: Two X-externals must share an edge (5-packing)
- `K4free_externals_distinct_thirds`: If K4-free and x=y, then False (K4 forms)

---

## FALSE LEMMAS (38 Total - Aristotle/AI Verified)

### Critical False Patterns

#### Pattern 1: "All Three Edge-Types" Arguments FAIL
| Lemma | Evidence | Counterexample |
|-------|----------|----------------|
| `not_all_three_types_Se` | 🔴 Aristotle | K4: externals share apex vertex 3 |
| `not_all_three_types_K4free` | 🔴 Aristotle | **OCTAHEDRON**: externals use DIFFERENT vertices 3,4,5 |
| `externals_on_at_most_two_edges` | 🟠 AI | K4 on {a,b,c,v} has externals on all 3 edges |

**Key Insight**: The "5-packing from 3 externals" argument fails in TWO ways:
1. **K4 case**: All 3 externals share same vertex → no 5-packing (share 2 vertices)
2. **Octahedron case**: 3 externals have different vertices → no K4, but also no 5-packing (externals share vertices with OTHER packing elements)

#### Pattern 2: Local Cover Bounds FAIL
| Lemma | Evidence | Counterexample |
|-------|----------|----------------|
| `local_cover_le_2` | 🟠 AI | 4 triangles at v using different M-edges |
| `tau_pair_le_4` | ⚪ Trivial | Avoiding triangles need base edges, not spokes |
| `triangles_at_vertex_cover_le_2` | 🔴 Aristotle | 3+ triangles at v with no common edge |

**Key Insight**: τ(at vertex v) can require arbitrarily many edges. The bound τ ≤ 2 only works for RESTRICTED sets like S_e.

#### Pattern 3: K4 Split Strategy FAILS
| Lemma | Evidence | Why |
|-------|----------|-----|
| `not_all_three_types_K4free` | 🔴 Aristotle | Octahedron is K4-free but has all 3 types |
| `distinct_thirds_5packing` | 🔴 Aristotle | External shares edge with one M-element |

**Key Insight**: The K4 vs K4-free split (recommended by Grok/Codex/Gemini) is INVALID. The octahedron counterexample shows K4-free graphs can still have all 3 edge-types with externals.

#### Pattern 4: Bridge Assumptions FAIL
| Lemma | Evidence | Counterexample |
|-------|----------|----------------|
| `bridge_absorption` | 🔴 Aristotle | Cover of S_e∪S_f misses bridges |
| `bridge_auto_covered_by_pigeonhole` | 🟠 AI | Edge incident to v ≠ edge OF triangle |
| `triangle_in_some_Se_or_M` | 🔴 Aristotle | Bridges excluded from ALL S_e sets |

**Key Insight**: Bridges require EXPLICIT handling. They are NOT automatically covered by S_e covers.

#### Pattern 5: Sym2 Self-Loop Bug
| Lemma | Evidence | Why |
|-------|----------|-----|
| `sym2_cover_cardinality` | 🔴 Aristotle | Finset.sym2 includes s(v,v) self-loops |
| `triangle_sym2_card_3` | 🔴 Aristotle | A.sym2 has 6 elements, not 3 |

**Key Insight**: NEVER use `A.sym2` for edge enumeration. Use explicit `{s(a,b), s(b,c), s(a,c)}`.

---

## THE OCTAHEDRON COUNTEREXAMPLE (NEW)

Aristotle found this in slot531. It breaks the K4-free strategy:

```
Graph: 6 vertices (0-5), 12 edges
Structure: Octahedron (vertices of an octahedron, edges connecting adjacent vertices)

Edges (24 directed = 12 undirected):
{0,1}, {0,2}, {0,3}, {0,5}, {1,2}, {1,3}, {1,4}, {2,4}, {2,5}, {3,4}, {3,5}, {4,5}

Packing M (4 triangles, edge-disjoint):
  {0,1,2}, {1,3,4}, {2,4,5}, {0,3,5}

For triangle e = {0,1,2}:
  - Edge {0,1}: external {0,1,3} (third vertex = 3)
  - Edge {1,2}: external {1,2,4} (third vertex = 4)
  - Edge {0,2}: external {0,2,5} (third vertex = 5)

Key properties:
  ✅ K4-free (no 4-clique exists)
  ✅ All 3 edge-types have externals
  ✅ Third vertices 3,4,5 are DISTINCT (no K4 formed)
  ✅ ν = 4 (packing is maximal - only 12 edges, 4×3=12)
```

**Why 5-packing fails**: Each external shares vertices with OTHER packing elements:
- {0,1,3} shares vertex 3 with {1,3,4} and {0,3,5}
- {1,2,4} shares vertex 4 with {1,3,4} and {2,4,5}
- {0,2,5} shares vertex 5 with {2,4,5} and {0,3,5}

So externals are NOT edge-disjoint from the rest of the packing!

---

## FAILED STRATEGIES (38 approaches)

### Wrong Direction (Most Common)
1. **Parker induction** - T_e can have 5+ triangles
2. **τ_containing_vertex ≤ 2** - FALSE, can be arbitrarily large
3. **avoiding_covered_by_spokes** - Spokes contain v, avoiding triangles don't
4. **link_graph_bipartite** - Link graphs can have odd cycles
5. **K4-free split** - Octahedron breaks this

### Definition Bugs
1. **sym2_edge_enumeration** - Self-loops included
2. **local_cover_le_2_self_loop** - Proof uses s(v,v)
3. **cycle4_missing_distinctness** - Need explicit distinctness axioms

### Technical Issues
1. **mislabeled_proven_sorry** - Tracking confusion
2. **lp_relaxation_krivelevich** - Too complex for Aristotle

---

## WHAT ACTUALLY WORKS

### Proven Cover Construction for PATH_4
```
Cover (8 edges):
  - S_A: 2 edges (fan apex in A)
  - X_AB: 2 edges (bridges via shared vertex)
  - S_B ∪ S_C: covered by middle structure
  - X_BC: 2 edges
  - X_CD: 2 edges
  - S_D: 2 edges (fan apex in D)
```

### Key Structural Insights
1. **Fan Structure**: Externals of SAME M-element using DIFFERENT edges share common external vertex x
2. **Bridge Decomposition**: Every bridge contains the shared vertex of its two parent M-elements
3. **Maximality**: Every triangle shares edge with some packing element

---

## DEBATE QUESTION

Given:
- K4-free split FAILS (octahedron)
- 5-packing arguments fail in multiple ways
- PATH_4 and CYCLE_4 are proven
- Remaining cases have τ≤12 but need τ≤8

**What is the correct strategy to complete the proof?**

Options to consider:
1. **Enumerate remaining configurations**: Star, scattered, two_two_vw have specific structures
2. **Unified cover construction**: Find 8-edge cover that works for all configurations
3. **LP duality approach**: Use ν* = τ* and bound ν* ≤ 4
4. **Different classification**: Not K4 vs K4-free, but some other structural property
5. **Strengthen existing proofs**: The 2-sorry cases might be fixable

---

## CONTEXT FOR AI DEBATERS

### Aristotle Capabilities
- **Tier 1 (70-90%)**: Counterexamples on Fin 5-7, decidable predicates
- **Tier 2 (30-50%)**: Simple induction, LP witnesses, packing construction
- **Tier 3 (10-20%)**: Deep combinatorics with human-outlined structure
- **Tier 4 (<5%)**: Asymptotics, optimal selection - AVOID

### What's in Mathlib
- `SimpleGraph.Basic`, `SimpleGraph.Clique`, `SimpleGraph.Triangle`
- Finite types: `Fin n` with decidability
- No built-in Tuza machinery

### Files Available
- 108 Lean files in submissions/nu4_final/
- tracking.db with 70 proven lemmas, 38 failed approaches, 38 false lemmas
