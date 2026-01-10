# τ ≤ 8 for PATH_4: Gap Analysis

## Status: PROOF STRATEGY BLOCKED, THEOREM STILL OPEN

**CRITICAL UPDATE (Jan 9, 2026):**
- The "2 edges per apex" proof strategy FAILS
- BUT τ ≤ 8 may still be TRUE! Grok found a 5-edge cover for the counterexample configuration.
- Need a DIFFERENT proof strategy.

The standard approach of "2 edges per packing element from apex" does NOT work for PATH_4 due to the **forced apex separation gap**.

## The Gap

### Configuration
PATH_4: M = {A, B, C, D} where:
- A = {v1, a1, a2}
- B = {v1, v2, b}
- C = {v2, v3, c}
- D = {v3, d1, d2}

### Problematic Scenario
When:
1. B's apex (common vertex of B-externals) is v1
2. C's apex (common vertex of C-externals) is v3
3. Edge {b, c} exists in G

Then bridge T = {v2, b, c} is NOT covered by any of the 8 edges:
- B's edges: {v1, v2}, {v1, b} - neither hits T
- C's edges: {v2, v3}, {v3, c} - neither hits T
- A's edges: both at v1 - don't hit T
- D's edges: both at v3 - don't hit T

## Failed Attempts to Close the Gap

### Attempt 1: Prove edge {b,c} forces apex
**Claim**: If edge {b,c} exists, B's apex must be v2 or b
**Result**: FALSE (Gemini counterexample)

**Counterexample**: Add vertex x with edges to v1, v2, b (tetrahedron on B).
- E1 = {v1, b, x} is B-external (shares edge {v1, b})
- E2 = {v1, v2, x} is B-external (shares edge {v1, v2})
- Common vertex of E1, E2 is v1
- Edge {b, c} can independently exist
- Bridge T = {v2, b, c} exists but B's apex is v1

### Why the Counterexample Works
The tetrahedron vertex x creates B-externals that force apex to v1, while the edge {b,c} is independent and creates an uncovered bridge.

## Proven Lemmas (Still Valid)

| Lemma | UUID | Status |
|-------|------|--------|
| two_externals_share_edge | slot306 | PROVEN |
| all_externals_share_common_vertex | slot306 | PROVEN |
| two_edges_cover_all_externals | slot306 | PROVEN |
| bridge_triangle_contains_shared_vertex | slot309 | PROVEN |
| bridge_covered_if_shared_is_common | slot309 | PROVEN |

## What IS Known

1. **τ ≤ 12 for all ν=4 cases**: Proven in slot139 (0 sorry, 0 axiom)
2. **Externals can be covered with 8 edges**: Proven (2 per element)
3. **Bridges contain shared vertex**: Proven (slot309)
4. **Bridges covered IF apex is at shared vertex**: Proven (slot309)

## What is NEEDED

To prove τ ≤ 8 for PATH_4, need ONE of:

1. **Structural constraint**: Prove bridges cannot exist when apexes avoid shared vertices
   - Status: FALSE (counterexample exists)

2. **Alternative cover**: Find 8-edge cover that handles bridges differently
   - Need edges that cover bridges independently of apex choice

3. **Bound reduction**: Accept τ ≤ 9 or τ ≤ 10 for PATH_4
   - Add 1-2 dedicated bridge edges

4. **Case split**: Different cover strategies for bridge/no-bridge cases

## Next Steps

1. Count maximum number of bridges in PATH_4
2. Determine if τ ≤ 9 is achievable (8 + 1 bridge edge)
3. Explore structural constraints on triple bridges (at v1, v2, v3 simultaneously)

## References

- slot306: Common vertex exists for externals
- slot309: Bridge properties
- slot310: Failed τ ≤ 8 attempt
- slot312: Failed apex forcing attempt
- false_lemmas table: edge_bc_forces_apex_v2
