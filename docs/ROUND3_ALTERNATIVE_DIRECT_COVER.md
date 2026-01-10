# ROUND 3: Alternative Direct Cover Approach Analysis
## January 3, 2026

---

## EXECUTIVE SUMMARY

| Question | Answer |
|----------|--------|
| How many distinct fan apexes? | Up to 4 (one per M-element), NOT constrained to coincide |
| Can overlap reduce 12 to 8? | ONLY with ADAPTIVE selection, NOT with fixed cover |
| Can M-edges serve as spokes? | Sometimes, but not guaranteed |
| 8-edge cover possible? | YES, but requires external_edge_sharing lemma |

**VERDICT**: tau <= 8 requires the ADAPTIVE approach from Round 7. No fixed 8-edge subset works universally.

---

## UNDERSTANDING THE FAN STRUCTURE

### What We Know (PROVEN)

1. **slot182**: Two externals of the SAME M-element X must share an edge (nu=4 contradiction)
2. **Pattern 16**: Pairwise edge-sharing does NOT imply common edge (Helly fails)
3. **Key Insight**: Externals of X form a FAN - share common VERTEX x, not common edge

### The Fan Structure

For M-element X = {a, b, c}, externals form a fan:
- All externals contain the "fan apex" x
- Each external uses a DIFFERENT edge of X
- External using edge {a,b}: T = {a, b, x}
- External using edge {b,c}: T' = {b, c, x}
- External using edge {a,c}: T'' = {a, c, x}

**Coverage**: Spoke edges {a,x}, {b,x}, {c,x} cover ALL externals of X (3 edges worst case)

---

## FAN APEX ANALYSIS IN CYCLE_4

### The Cycle_4 Configuration

```
M = {A, B, C, D} in cycle configuration:

A = {v_ab, v_da, a_priv}
B = {v_ab, v_bc, b_priv}
C = {v_bc, v_cd, c_priv}
D = {v_cd, v_da, d_priv}

Intersections:
A inter B = {v_ab}
B inter C = {v_bc}
C inter D = {v_cd}
D inter A = {v_da}
```

### Fan Apexes per M-Element

| M-element | Fan Apex | Required Spoke Edges |
|-----------|----------|---------------------|
| A | x_A | {v_ab, x_A}, {v_da, x_A}, {a_priv, x_A} |
| B | x_B | {v_ab, x_B}, {v_bc, x_B}, {b_priv, x_B} |
| C | x_C | {v_bc, x_C}, {v_cd, x_C}, {c_priv, x_C} |
| D | x_D | {v_cd, x_D}, {v_da, x_D}, {d_priv, x_D} |

### Can Fan Apexes Coincide?

**Pattern 6 (external_share_common_vertex is FALSE)** proves they need NOT coincide:

At shared vertex v_ab:
- External T1 = {v_ab, v_da, y1} uses edge from A
- External T2 = {v_ab, v_bc, y2} uses edge from B
- T1 and T2 share only v_ab; y1 and y2 can be DIFFERENT

**Conclusion**: Fan apexes for different M-elements are NOT constrained to be equal, even at the same shared vertex.

---

## EDGE COUNT ANALYSIS

### Layer 1: M-Element Coverage (4 edges)

The 4 cycle edges cover all M-elements:
```
{v_ab, v_da} covers A (edge of A)
{v_ab, v_bc} covers B (edge of B)
{v_bc, v_cd} covers C (edge of C)
{v_cd, v_da} covers D (edge of D)
```

### Layer 2: Bridge Coverage (0 additional edges)

All bridges contain a shared vertex (proven).
Since bridges are covered by spokes from shared vertices, and cycle edges ARE spokes, bridges are already covered.

### Layer 3: External Coverage (where complexity lies)

**Case A: External uses cycle edge**
- Example: T = {v_ab, v_da, x} uses edge {v_ab, v_da} from A
- ALREADY COVERED by cycle edge {v_ab, v_da}
- Cost: FREE

**Case B: External uses private edge**
- Example: T = {v_ab, a_priv, x} uses edge {v_ab, a_priv} from A
- NOT covered by cycle edges
- Need additional edge containing a_priv or x

---

## CAN WE CONSTRUCT AN 8-EDGE COVER?

### Attempt 1: Cycle + Diagonals

```
E_8_attempt = {
  {v_ab, v_da},   -- covers A
  {v_ab, v_bc},   -- covers B
  {v_bc, v_cd},   -- covers C
  {v_cd, v_da},   -- covers D
  {v_ab, v_cd},   -- diagonal 1
  {v_bc, v_da},   -- diagonal 2
  ?, ?            -- 2 more needed
}
```

**FAILURE**: External T = {v_ab, a_priv, x} is not covered!
- Contains no shared vertex except v_ab
- Diagonals don't contain a_priv
- Need edge containing a_priv

### Attempt 2: Cycle + Private Spokes

```
E_8_attempt = {
  {v_ab, v_da},   -- covers A
  {v_ab, v_bc},   -- covers B
  {v_bc, v_cd},   -- covers C
  {v_cd, v_da},   -- covers D
  {v_ab, a_priv}, -- covers some externals of A
  {v_bc, b_priv}, -- covers some externals of B
  {v_cd, c_priv}, -- covers some externals of C
  {v_da, d_priv}  -- covers some externals of D
}
```

**FAILURE**:
- External T = {v_da, a_priv, x} uses edge {v_da, a_priv}
- Neither {v_ab, a_priv} nor any other edge in E_8_attempt covers it!
- The "wrong" spoke was chosen

### Pattern 9 (FALSE LEMMA) Confirms This

**fixed_8_edge_M_subset is FALSE**:
> Any 8-edge subset of 12 M-edges must omit 4 edges.
> External triangles using the omitted edges are NOT covered.

Specifically, the 4 "outside spokes" are:
```
{v_da, a_priv}  (A's spoke not through v_ab)
{v_ab, b_priv}  (B's spoke not through v_bc)
{v_bc, c_priv}  (C's spoke not through v_cd)
{v_cd, d_priv}  (D's spoke not through v_da)
```

If externals exist using ALL of these edges, the fixed 8-edge cover fails.

---

## THE ADAPTIVE SOLUTION

### The Only Way to Achieve tau <= 8

**Construction (from Round 7)**:
```
E_8 = E_cycle UNION E_external

E_cycle = {
  {v_ab, v_da},
  {v_ab, v_bc},
  {v_bc, v_cd},
  {v_cd, v_da}
}

E_external = { e_A, e_B, e_C, e_D }
where:
  e_X = the common edge shared by all externals of X
```

**Why This Works**:
1. By external_edge_sharing (slot182), externals of X share a common edge
2. This common edge covers ALL externals of X with ONE edge
3. 4 cycle edges + 4 external-covering edges = 8 total

**The Catch**: Must PROVE external_edge_sharing!

---

## ANALYSIS OF FAN APEX OVERLAP

### Question: What if all fan apexes are the same?

**Scenario**: x_A = x_B = x_C = x_D = x (single global apex)

Then spoke edges {v, x} for v in {v_ab, v_bc, v_cd, v_da} cover ALL externals.

But wait - we also need edges for private vertices: {a_priv, x}, {b_priv, x}, etc.

**Total spokes from x**: Up to 8 (4 shared + 4 private)

Even with global apex coincidence, we still need 8 edges to cover all externals!

### Question: What if fan apexes coincide pairwise?

**Scenario**: x_A = x_B and x_C = x_D

Then:
- Spokes from x_A cover externals of A and B: {v_ab, x_A}, {v_da, x_A}, {a_priv, x_A}, {v_bc, x_A}, {b_priv, x_A}
- Spokes from x_C cover externals of C and D: similar

**Overlap**: {v_bc, x_A} could coincide with {v_bc, x_C} if x_A = x_C

This creates some savings, but the fundamental constraint remains: we need edges hitting private vertices.

---

## THE STRADDLING TRIANGLE PROBLEM

### Pattern 17: Externals Don't Partition by M-Element

**FALSE LEMMA**: externals_partition_by_M_element

**Counterexample**: Triangle t = {v_ab, a_priv, b_priv}
- Shares edge {v_ab, a_priv} with A
- Shares edge {v_ab, b_priv} with B
- This is a "straddling" external!

### Impact on Coverage

The straddling triangle t = {v_ab, a_priv, b_priv} is NOT covered by:
- Cycle edges (don't contain a_priv or b_priv together)
- External edge e_A (may not contain b_priv)
- External edge e_B (may not contain a_priv)

**Resolution**: The straddling triangle MUST be covered by either e_A or e_B.

If e_A = {v_ab, a_priv} (the shared edge with A), does it hit t?
- Check: {v_ab, a_priv} in t.sym2? YES!

So if we choose e_A to be the edge t shares with A, it covers t.

The adaptive approach handles this naturally - we choose e_X based on what actually exists.

---

## FINAL ANSWER

### 1. Fan Apex Count: UP TO 4 DISTINCT

There is no structural constraint forcing fan apexes to coincide. Pattern 6 explicitly shows externals at the same shared vertex can have different apexes.

### 2. Edge Overlap: INSUFFICIENT FOR FIXED COVER

Even with maximal apex overlap, we still need edges to private vertices. No fixed 8-edge set handles all cases.

### 3. M-Edges as Spokes: SOMETIMES

When fan apex x happens to be a vertex of M (e.g., x_A = v_bc), some M-edges serve as spokes. But this is not guaranteed.

### 4. The 8-Edge Cover

**CAN be constructed ADAPTIVELY**:
```
E_8 = {
  {v_ab, v_da},   -- cycle edge, covers A + bridges
  {v_ab, v_bc},   -- cycle edge, covers B + bridges
  {v_bc, v_cd},   -- cycle edge, covers C + bridges
  {v_cd, v_da},   -- cycle edge, covers D + bridges
  e_A,            -- common edge of Ext(A) - ADAPTIVE
  e_B,            -- common edge of Ext(B) - ADAPTIVE
  e_C,            -- common edge of Ext(C) - ADAPTIVE
  e_D             -- common edge of Ext(D) - ADAPTIVE
}
```

**REQUIRES**: Proof of external_edge_sharing (all externals of X share a common edge)

### 5. If No Common Edge Exists

If external_edge_sharing FAILS (externals of X don't share a common edge), then:
- Each external of X needs a separate edge
- Worst case: 3 externals per M-element, each using different X-edge
- tau >= 4 (M-elements) + 4*3 (externals) = 16

But overlap with cycle edges reduces this:
- Externals using cycle edges are FREE
- Worst case for private-edge externals: tau <= 12 (proven)

---

## SUMMARY TABLE

| Scenario | tau Bound | Achievable? |
|----------|-----------|-------------|
| Fixed 8-edge M-subset | <= 8 | NO (Pattern 9) |
| Adaptive with external_edge_sharing | <= 8 | YES (Round 7) |
| No external_edge_sharing | <= 12 | YES (slot113) |
| Global fan apex (hypothetical) | <= 8 | Would work if true |

---

## RECOMMENDATION

**Primary Path**: Prove external_edge_sharing via nu=4 packing contradiction (Round 7 approach)

**Fallback**: Accept tau <= 12 as the proven bound

**Do NOT attempt**: Fixed 8-edge constructions (all fail by Pattern 9)

---

## APPENDIX: Why Fixed Covers Fail

### The Fundamental Obstruction

Consider graph G with:
- Cycle_4 packing M = {A, B, C, D}
- External T_i = {v_{i}, p_{i}, x_i} for each of 4 shared vertices

Where each T_i uses a DIFFERENT private vertex p_i.

To cover T_i, we need an edge containing p_i.
But there are only 4 such slots in an 8-edge cover.
If each T_i is at a DIFFERENT shared vertex with a DIFFERENT private vertex, we need 4 specific private-containing edges.

The 4 cycle edges don't help (they don't contain private vertices).
So the 4 remaining edges MUST be the 4 specific private edges.

But Pattern 9 shows: this leaves the OTHER 4 private edges uncovered.
If externals exist using those edges too, the cover fails.

**Conclusion**: No fixed 8-edge construction survives all possible external configurations.
