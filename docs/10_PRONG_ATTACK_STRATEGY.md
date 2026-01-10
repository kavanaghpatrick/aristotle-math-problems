# 10-PRONG ATTACK STRATEGY: PATH_4 τ ≤ 8

Generated from multi-agent debate (January 8, 2026)

## EXECUTIVE SUMMARY

**Status**: τ ≤ 10 is PROVEN (slot300). τ ≤ 8 remains OPEN with identified gaps.

**Key Proven Lemmas**:
1. `two_externals_share_edge` (slot182): Any two A-externals share an edge
2. `different_edges_share_external_vertex` (slot224f): A-externals using different edges share external vertex

**Key False Lemmas**:
- `fan_apex_outside_A`: FALSE - externals using SAME edge don't share apex outside A
- `all_triangles_touch_spine`: FALSE - base-private triangles avoid spine vertices

---

## THE 10-PRONG ATTACK

### PRONG 1: Direct 8-Edge Verification (RECOMMENDED - HIGHEST PRIORITY)

**Strategy**: Enumerate ALL possible triangle types and verify each is covered.

**Proposed Cover**:
```
{v1,a1}, {v1,a2}, {a1,a2}, {v2,b}, {v2,c}, {v3,c}, {v3,d1}, {d1,d2}
```

**Verification Table**:
| Triangle Type | Covered By |
|--------------|------------|
| A = {v1,a1,a2} | {v1,a1} ✓ |
| B = {v1,v2,b} | {v2,b} only if v2∈t... NEED {v1,v2} or {v1,b}! |

**GAP IDENTIFIED**: This cover doesn't include {v1,v2} or {v1,b}, missing B-externals!

**Corrected Cover (9 edges)**:
```
{v1,a1}, {v1,a2}, {a1,a2}, {v1,b}, {v2,b}, {v2,c}, {v3,c}, {v3,d1}, {d1,d2}
```

**This is 9 edges, not 8!**

### PRONG 2: Fan Apex Exploitation

**Key Insight**: From `different_edges_share_external_vertex`, A-externals using different edges share common apex x.

**Strategy**:
1. Find x_A (fan apex for A-externals)
2. Use edges incident to x_A to cover ALL A-externals with 2 edges
3. Similarly for D-externals with x_D
4. Cover B, C with 2 edges each

**Challenge**: x_A might be v1 (inside A) or might be outside!
- If x_A = v1: Use {v1,a1}, {v1,a2} (covers all A-externals)
- If x_A = a1: Use {v1,a1}, {a1,a2} (covers all A-externals)
- If x_A is NEW: Need edges to x_A from outside A

**Submission Target**: Prove x_A ∈ {v1, a1, a2} (fan apex is in A).

### PRONG 3: τ ≤ 10 Fallback Already Proven

**Proven** (slot300): τ ≤ 10 with cover:
```
{v1,a1}, {v1,a2}, {a1,a2}, {v1,v2}, {v2,b}, {v2,v3}, {v3,c}, {v3,d1}, {v3,d2}, {d1,d2}
```

This is our fallback if τ ≤ 8 is impossible.

### PRONG 4: Prove Some External Types Cannot Coexist

**Strategy**: Show that in any PATH_4 graph, certain "bad" external triangles cannot all exist simultaneously.

**Specifically**: If {v1, a2, x} exists with x ∉ {a1, v2, b, ...}, show this constrains other externals.

**Mathematical approach**: Use the packing constraint ν = 4 to derive structural limits.

### PRONG 5: LP/Fractional Relaxation

**Strategy**: Formulate as LP and prove fractional τ* ≤ 8.

**Variables**: x_e ∈ [0,1] for each edge e
**Constraints**: ∀ triangle T: Σ_{e ∈ T} x_e ≥ 1
**Objective**: minimize Σ x_e

**Challenge**: Need rounding lemma to go from fractional to integral.

### PRONG 6: Endpoint-Middle Asymmetry

**Key Observation** (from Strategist C):
- Endpoints (A, D): Each needs 3 edge-types covered (2 apex + 1 base)
- Middles (B, C): Each needs 3 edge-types but only 1 private vertex

**Potential savings**: Middle elements share TWO vertices with neighbors, so their externals may already be covered by endpoint edges.

**Specifically**:
- {v1,b,x} shares v1 with A → if x ∈ A, covered by A-edges
- {v3,c,y} shares v3 with D → if y ∈ D, covered by D-edges

### PRONG 7: Contradiction from ν = 4

**Strategy**: Assume τ ≥ 9 and derive contradiction.

**Approach**: Show that if 8 edges don't suffice, we can find a 5-packing.

**Challenge**: Need to construct explicit 5-packing from 8-edge insufficiency.

### PRONG 8: Finite Case Verification

**Strategy**: Reduce to finite number of graphs and verify each.

**Approach**: PATH_4 has 9 vertices. On at most 9 vertices, enumerate all simple graphs containing PATH_4 packing with ν = 4.

**Challenge**: Exponential in number of possible edges. May need SAT/SMT solver.

### PRONG 9: Leverage two_externals_share_edge Globally

**Key Lemma**: Any two A-externals share an edge.

**Extension**: What if we consider externals across DIFFERENT M-elements?

**Observation**: Bridge triangles (sharing edges with 2+ M-elements) might provide overlap.

**Strategy**: Show bridges are covered by edges that also cover other externals.

### PRONG 10: Symmetric 2+2+2+2 Cover

**Strategy**: Instead of 3+3+1+1 for ABCD, find 2+2+2+2 by clever edge sharing.

**Proposed Cover**:
```
{v1,a1}, {a1,a2}  -- A (2 edges)
{v1,v2}, {v2,b}   -- B (2 edges, reusing v1)
{v2,v3}, {v3,c}   -- C (2 edges, reusing v2)
{v3,d1}, {d1,d2}  -- D (2 edges)
```
Total: 8 edges!

**Verification**:
- A = {v1,a1,a2}: {v1,a1} ✓ or {a1,a2} ✓
- B = {v1,v2,b}: {v1,v2} ✓ or {v2,b} ✓
- C = {v2,v3,c}: {v2,v3} ✓ or {v3,c} ✓
- D = {v3,d1,d2}: {v3,d1} ✓ or {d1,d2} ✓

**External Check (THE CRITICAL STEP)**:
- A-externals through {v1,a1}: ✓ by {v1,a1}
- A-externals through {v1,a2}: ✗ NOT COVERED!
- A-externals through {a1,a2}: ✓ by {a1,a2}

**GAP: {v1, a2, x} triangles are NOT covered!**

---

## RECOMMENDED PRIORITY

1. **PRONG 2**: Prove fan apex is in A (most likely to work)
2. **PRONG 4**: Prove {v1,a2,x} cannot exist for x outside specific set
3. **PRONG 10**: If PRONG 2 or 4 work, this cover becomes valid
4. **PRONG 6**: Exploit asymmetry to reduce middle element budget
5. **PRONG 3**: Fall back to τ ≤ 10 if above fail

---

## NEXT SUBMISSIONS

### Submission 1: Fan Apex In A
```lean
theorem fan_apex_in_A : ∀ x, (∀ T, isExternalOf G M A T → x ∈ T) → x ∈ A
```

### Submission 2: v1-a2 Externals Constrained
```lean
theorem v1_a2_externals_limited :
  ∀ T, isExternalOf G M A T → T ∩ A = {v1, a2} →
  ∃ y ∈ {a1, v2, b}, y ∈ T
```

### Submission 3: 8-Edge Cover (contingent on above)
```lean
theorem tau_le_8_path4 : triangleCoveringNumber G ≤ 8
```

---

## DEBATE PARTICIPANTS' FINAL POSITIONS

| Agent | Position | Key Insight |
|-------|----------|-------------|
| Agent A | τ > 8 possible | 8 edge-types, 4 slots after mandatory |
| Critic A | τ = 8 via careful overlap | Interior triangles have 2 apex vertices |
| Critic B | Agent B's spine cover fails | Base-privates avoid spine |
| Strategist C | Fan apex saves us | All A-externals share common vertex |
| Gemini | Adaptive cover needed | Case split on external structure |

**Consensus**: τ ≤ 8 is PLAUSIBLE but requires proving structural constraints on externals.
