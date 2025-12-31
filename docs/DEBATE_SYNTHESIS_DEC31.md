# DEBATE SYNTHESIS: τ ≤ 8 for Cycle_4 - December 31, 2025

## Executive Summary

**4 Rounds of AI Debate** between Grok-4, Gemini, and Codex agents.

**Key Discovery**: The checkpoint's claim that "link graphs are bipartite" is **FALSE**.
Despite this, τ ≤ 8 likely still holds via adaptive/charging arguments.

---

## What The Checkpoint Claimed (Dec 30)

| Claim | Status After Debate |
|-------|---------------------|
| Link graphs L_v are bipartite | **FALSE** - Counterexample found |
| König theorem gives τ(L_v) ≤ 2 | **INVALID** - Requires bipartiteness |
| τ ≤ 8 is mathematically TRUE | **LIKELY TRUE** - But proof needs new approach |
| External vertices isolated in L_v | **PARTIALLY TRUE** - External-external edges blocked |

---

## Round 1: The Bipartite Question

**Question**: Are link graphs L_v bipartite in Cycle_4 under ν = 4?

**CONSENSUS: NO**

### Grok's Counterexample
In Cycle_4, add edges:
- {v_da, b_priv}
- {a_priv, b_priv}

This creates triangle {v_da, a_priv, b_priv} in L_{v_ab} (a 3-cycle = odd cycle).
Graph has 14 edges, ν still = 4.

### Codex's Counterexample
At v_ab, if G has:
- Edge {a_priv, b_priv}
- Edge {b_priv, v_da}

Then L_{v_ab} contains 3-cycle: v_da - a_priv - b_priv - v_da

### Why The Checkpoint Was Wrong
Round 5 correctly proved "external vertices cannot be adjacent to each other in L_v"
but INCORRECTLY concluded bipartiteness. The M-neighbors (v_da, a_priv, v_bc, b_priv)
can form additional edges creating odd cycles through non-M-edges added to G.

---

## Round 2: Does τ ≤ 8 Still Hold?

**Question**: If König fails, can we still achieve τ ≤ 8?

**CONSENSUS: YES (likely)**

Both Grok and Codex attempted to construct counterexamples (graphs with ν=4 but τ>8)
and FAILED to find any.

### Grok's Charging Argument
- Assign 2 "charge units" per M-triangle (total budget = 8)
- Extra triangles from non-bipartite L_v are offset by overlaps elsewhere
- Key: Cycle_4 structure prevents unbounded independent odd cycles

### Codex's Edge Deletion Argument
- Start with 12 M-edges (proven τ ≤ 12)
- Show 4 can be removed while maintaining coverage
- Key: Identify which M-edges are "redundant"

---

## Round 3: Concrete Proof Strategies

### Strategy A: Grok's Charging (Abstract)
```
charging_assignment: Each M-triangle assigns 2 charge units
cycle4_bound: Cap on independent odd cycles per L_v
overlap_offset: Non-bipartite implies overlapping charges
total_charge_bound: Total ≤ 8
charging_to_cover: Charge bound implies cover bound
```
**Estimated sorries**: ~17

### Strategy B: Codex's Direct Construction (Concrete)
```
The 8 edges:
1. {v_ab, v_da}   - ring edge
2. {v_ab, v_bc}   - ring edge
3. {v_bc, v_cd}   - ring edge
4. {v_cd, v_da}   - ring edge
5. {v_ab, a_priv} - private spoke
6. {v_bc, b_priv} - private spoke
7. {v_cd, c_priv} - private spoke
8. {v_da, d_priv} - private spoke
```
**Estimated sorries**: ~10

---

## Round 4: Counterexample to Codex's Construction!

**Critical Finding**: Codex's specific 8-edge cover FAILS.

### The Counterexample
Triangle T = {a_priv, v_da, z} where z is an external vertex:
- T shares edge {a_priv, v_da} with A (satisfies maximality)
- None of the 8 edges hit T:
  - Edge 1 {v_ab, v_da}: v_ab ∉ T ❌
  - Edge 5 {v_ab, a_priv}: v_ab ∉ T ❌
  - Edge 8 {v_da, d_priv}: d_priv ≠ z ❌

### Why It Fails
Codex's 8 edges miss {v_da, a_priv} (the "other" private edge of A).
External triangles sharing this edge are NOT covered.

### Missing Edges (4 total, one per M-triangle)
- {v_da, a_priv} from A
- {v_ab, b_priv} from B
- {v_bc, c_priv} from C
- {v_cd, d_priv} from D

---

## The Core Insight

**A FIXED 8-edge subset of M-edges cannot work universally.**

Each M-triangle has 3 edges. A fixed 8-edge cover from 12 M-edges must omit 4 edges.
If an external triangle shares one of those 4 omitted edges, it's uncovered.

**SOLUTION**: The 8-edge cover must be ADAPTIVE:
1. Include non-M-edges (edges from external triangles themselves)
2. Adapt selection based on which external triangles exist in G

---

## What We KNOW For Certain

| Fact | Status |
|------|--------|
| τ ≤ 12 for Cycle_4 | **PROVEN** (slot139, 0 sorries) |
| Link graphs not bipartite | **PROVEN** (counterexample) |
| König approach invalid | **CONFIRMED** |
| Fixed 8-edge M-subset fails | **PROVEN** (Round 4 counterexample) |
| τ ≤ 8 mathematically | **LIKELY TRUE** (no counterexample found) |

---

## Proven Lemmas from Aristotle (Still Valid)

From slot144 (3 PROVEN):
- `exists_maximal_matching` - Greedy maximal matching exists
- `link_matching_le_2` - Matching in L_v has size ≤ 2
- `vertexToEdgeCover_covers` - Vertex cover → edge cover

From slot145 (5 PROVEN):
- `triangle_shares_edge_with_packing` - Maximality
- `external_covered_by_M_edge` - Externals share M-edge
- `M_edges_through_v_card` - Edge count bound
- `triangle_contains_shared` - All triangles contain shared vertex
- `adaptiveCoverAt` - Definition

---

## Path Forward: Three Options

### Option 1: Accept τ ≤ 12 (SAFE)
- Already proven, no risk
- Conservative but guaranteed success
- Matches the general bound τ ≤ 2ν for most strategies

### Option 2: Adaptive 8-Edge Cover (MEDIUM RISK)
- Cover selection depends on G's structure
- May require case analysis on external triangle configurations
- Proof complexity: HIGH

### Option 3: Charging Argument (HIGH RISK)
- Abstract, elegant
- Aristotle is weak on abstract counting
- Proof complexity: VERY HIGH, likely timeout

---

## Recommended Next Steps

1. **Document the bipartite counterexample** in FALSE_LEMMAS.md
2. **Update checkpoint** with debate findings
3. **Create slot147** with adaptive approach OR
4. **Accept τ ≤ 12** and move to other frontiers

The debate has clarified:
- WHY König approach failed (bipartiteness false)
- WHY fixed 8-edge cover failed (missing edges)
- WHAT would be needed for τ ≤ 8 (adaptive selection)

The question is whether the effort for τ ≤ 8 is worth it given τ ≤ 12 is proven.

---

---

## Round 5: Final Path Forward

### Grok's Adaptive Proof Sketch

When external triangle T = {a_priv, v_da, z} shares an omitted M-edge {a_priv, v_da}:
- T introduces edges {a_priv, z} and {v_da, z}
- Use {v_da, z} instead of {a_priv, v_da} to cover T
- This "adaptive swap" maintains total edge count at 8

**Claimed result**: Adaptive selection gives τ ≤ 8

**Caveat**: Proof sketch only, not rigorous. Would need Aristotle verification.

---

## FINAL RECOMMENDATIONS

### Option A: Accept τ ≤ 12 (RECOMMENDED for now)
- **Pro**: Already PROVEN (slot139, 0 sorries)
- **Pro**: No further research needed
- **Pro**: Matches general bound τ ≤ 2ν for most configurations
- **Con**: Not optimal (Tuza predicts τ ≤ 8)

### Option B: Pursue Adaptive τ ≤ 8 (Future work)
- **Pro**: Would prove tight bound matching Tuza
- **Con**: Complex proof structure (adaptive selection)
- **Con**: High Aristotle timeout risk
- **Con**: May require 30+ sorries

### Option C: Research Specific Construction (Medium effort)
- Study which configurations actually require 9+ edges
- If none exist, prove τ ≤ 8 by exhaustive case analysis
- If some exist, document as open problem

---

## Summary Table

| Round | Key Finding |
|-------|-------------|
| 1 | Link graphs NOT bipartite |
| 2 | τ ≤ 8 likely holds (no Tuza counterexample) |
| 3 | Two strategies: Charging vs Construction |
| 4 | Fixed 8-edge construction FAILS |
| 5 | Adaptive construction might work |

---

## New False Lemmas Discovered

1. `link_graph_bipartite` - FALSE (odd cycles among M-neighbors possible)
2. `fixed_8_edge_cover` - FALSE (any specific 8-subset of M-edges fails)

---

## For Future Aristotle Submissions

**DO NOT**:
- Assume link graphs bipartite
- Use König's theorem
- Use fixed 8-edge M-subset
- Use local_cover_le_2
- Use external_share_common_vertex

**DO USE**:
- triangle_shares_edge_with_packing (PROVEN)
- link_matching_le_2 (PROVEN)
- tau_le_12_cycle4 (PROVEN)
- All triangles contain shared vertex (PROVEN)

---

*Debate synthesis created: 2025-12-31*
*Participants: Grok-4, Gemini, Codex, Claude*
*Rounds: 5 complete*
*Status: τ ≤ 12 PROVEN, τ ≤ 8 OPEN*
