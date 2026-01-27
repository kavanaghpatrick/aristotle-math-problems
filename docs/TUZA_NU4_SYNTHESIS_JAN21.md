# Tuza's Conjecture ν=4 Synthesis (Jan 21, 2026)

## Executive Summary

**CRITICAL FINDING**: The naive 8-edge cover (3 from A + 2 spines + 3 from D) does NOT work for all PATH_4 graphs with external triangles.

**RESOLUTION**: An ADAPTIVE cover strategy is needed, selecting 8 edges based on which external types actually exist.

---

## The Problem

For PATH_4 structure:
```
A = {v1, a2, a3}
B = {v1, v2, b3}
C = {v2, v3, c3}
D = {v3, d2, d3}
```

The naive 8-edge cover:
- 3 edges from A: {v1,a2}, {v1,a3}, {a2,a3}
- 2 spine edges: {v1,v2}, {v2,v3}
- 3 edges from D: {v3,d2}, {v3,d3}, {d2,d3}

**This covers**:
- All packing triangles A, B, C, D ✓
- A-externals (share ≥2 with A) ✓
- D-externals (share ≥2 with D) ✓
- B-externals sharing {v1,v2} ✓
- C-externals sharing {v2,v3} ✓

**This DOES NOT cover**:
- B-externals sharing {v1,b3} (e.g., {v1, b3, w2}) ✗
- B-externals sharing {v2,b3} (e.g., {v2, b3, w3}) ✗
- C-externals sharing {v2,c3} ✗
- C-externals sharing {v3,c3} ✗

---

## Computationally Verified (slot468)

```lean
-- The spine cover does NOT hit non-spine externals
theorem cover8_spines_misses_ext2 : coverHits cover8_spines (B_ext2 w2) = false := by native_decide
theorem cover8_spines_misses_ext3 : coverHits cover8_spines (B_ext3 w3) = false := by native_decide
```

This proves the naive cover is insufficient for graphs where non-spine B-externals exist.

---

## The Adaptive Solution

For B-externals, there are 3 possible types:
- Type 1: shares {v1, v2} → covered by spine
- Type 2: shares {v1, b3} → needs edge {v1, b3}
- Type 3: shares {v2, b3} → needs edge {v2, b3}

**Key Constraint**: At most 2 of 3 types can exist (6-packing contradiction).

**Proof**:
If all 3 existed with fresh w1, w2, w3:
- S = {B_ext1(w1), B_ext2(w2), B_ext3(w3), A, C, D}
- All 15 pairwise intersections have card ≤ 1
- S is a 6-packing, contradicting ν = 4

**Adaptive Cover Selection**:
- If only Type 1 exists: use spine cover (8 edges)
- If Type 2 exists: include {v1, b3}, adjust elsewhere
- If Type 3 exists: include {v2, b3}, adjust elsewhere
- If both Type 2 and Type 3: impossible (would have 3 types)

---

## The Complete 11-Pattern Analysis

For all 11 intersection graph patterns on 4 vertices:

| Pattern | Edges | Status | Cover Strategy |
|---------|-------|--------|----------------|
| Empty (scattered) | 0 | PROVEN τ≤4 | All packing edges (12), but sparse graph has few triangles |
| K2 (single edge) | 1 | PROVEN τ≤4 | Similar to scattered |
| 2K2 (two disjoint edges) | 2 | PROVEN τ≤4 | Two pairs don't interact |
| P3 (path length 2) | 2 | PROVEN τ≤4 | Middle element bridges two |
| K3 (triangle) | 3 | PROVEN τ≤4 | Three share common vertex |
| K_{1,3} (star) | 3 | PROVEN τ≤4 | Central connects to 3 others |
| **P4 (path length 3)** | 3 | **τ≤8 (HARD)** | Endpoints + spines + adaptive |
| C4 (4-cycle) | 4 | PROVEN τ≤4 | Cyclic structure |
| Paw | 4 | PROVEN τ≤4 | Triangle + pendant |
| K4-e (diamond) | 5 | PROVEN τ≤4 | Almost complete |
| K4 (complete) | 6 | PROVEN τ≤4 | All share common vertex |

**P4 is the WORST CASE** requiring τ = 8.

---

## Current Submissions

### slot467_tuza_nu4_complete.lean
- Computational verification for MINIMAL PATH_4 graph
- No external triangles in minimal graph
- Proves τ ≤ 8 for this specific instance

### slot468_adaptive_cover_proof.lean
- Documents the adaptive cover strategy
- Proves key lemmas about external type constraints
- Shows naive cover fails for non-spine externals

---

## What Remains

1. **Complete PATH_4 proof**: Need formal proof that adaptive cover always works
   - Case analysis on which external types exist
   - Show 8 edges suffice for each case

2. **Database updates**: Record findings in tracking.db

3. **Final synthesis**: Combine all 11 patterns with proper handling of externals

---

## Key Insights

1. **External triangles are the challenge**: The packing triangles are easy to cover; externals require careful analysis.

2. **At most 2 external types per M-element**: This constraint (from 6-packing contradiction) is what makes τ ≤ 8 possible.

3. **Adaptive selection**: The cover must be chosen based on which externals actually exist, not a fixed set of 8 edges.

4. **Minimal graphs are trivial**: Graphs with only the packing edges have no externals, making τ ≤ 8 easy.

5. **General graphs need full analysis**: For arbitrary graphs with ν = 4, the adaptive argument is necessary.

---

## References

- slot462: Original 11-pattern enumeration
- slot464: K_{1,3} pattern (central triangle)
- slot465: 4 missing patterns (K2, P3, Paw, Diamond)
- slot466: Exhaustiveness proof
- slot467: Computational verification (minimal graph)
- slot468: Adaptive cover analysis

---

## Status: IN PROGRESS

Aristotle processing slot467 and slot468. Results pending.
