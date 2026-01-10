# ROUND 3 DEBATE VERDICT: Middle-Element Externals Through Private Vertices

## The Question

Can there exist a triangle T = {v1, b, x} in PATH_4 where:
- B = {v1, v2, b} is a middle element with private vertex b
- x is a vertex not in the 9 vertices of M = {A, B, C, D}?

## VERDICT: YES, SUCH TRIANGLES CAN EXIST

### Proof of Existence

**Configuration:**
```
PATH_4: A = {v1, a1, a2}
        B = {v1, v2, b}    ← b is private to B
        C = {v2, v3, c}
        D = {v3, d1, d2}

M = {A, B, C, D} is a maximum packing with ν = 4
```

**The triangle T = {v1, b, x} where x ∉ {v1, v2, v3, a1, a2, b, c, d1, d2}:**

1. **T is valid** - If G contains edges (v1,b), (v1,x), (b,x), then T is a triangle
2. **T satisfies maximality** - T shares edge {v1,b} with B, so T cannot join M (would violate edge-disjointness)
3. **T is a B-external** - T ∉ M and T ∩ B = {v1, b} has cardinality ≥ 2

**Nothing in the PATH_4 definition forbids such triangles.**

The `isPath4` predicate only constrains:
- M = {A, B, C, D} exactly
- Intersection structure between adjacent/non-adjacent pairs
- No constraint on additional vertices or triangles outside M

### Mathematical Classification

T = {v1, b, x} is:
- A **B-external** (shares edge with B, not in M)
- In `trianglesSharingEdge(B)` ✓
- In `T_pair(A, B)` ✓
- In `trianglesContaining(T_pair(A,B), v1)` ✓
- Covered by spoke edge {v1, b} in the optimal cover

## Impact on Critic A's Proposed Cover

**Critic A's cover:**
```
{v1,a1}, {v1,a2}, {v2,c}, {v3,d1}, {v3,d2}, {v1,v2}, {v2,v3}
```

**Missing edges:**
- {v1,b} - spoke from B at v1
- {v3,c} - spoke from C at v3
- Base edges from A and D

**Critic A's cover FAILS to cover:**
- Triangle T = {v1, b, x} (contains edge {v1,b} ∉ cover)
- Avoiding-v1 externals of A (need base {a1,a2})
- Avoiding-v3 externals of D (need base {d1,d2})

## The Correct Bound: τ ≤ 12 (Proven) vs τ ≤ 8 (Open)

### Database Evidence

From `false_lemmas` table:

```
Lemma: tau_pair_le_4
Claim: τ(T_pair(e,f)) ≤ 4 when e ∩ f = {v}
Status: FALSE

Why false: T_pair splits into containing(v) and avoiding(v).
           - Containing needs 4 spokes from v
           - Avoiding needs 2 base edges
           Total = 6, NOT 4
```

### Implications

The approach in `slot51_path4_PROVEN.lean` uses the FALSE lemma `tau_pair_le_4`.

**Correct bounds:**
- τ(T_pair(A,B)) ≤ 6 (4 spokes from v1 + 2 base edges)
- τ(T_pair(C,D)) ≤ 6 (4 spokes from v3 + 2 base edges)
- Union bound: τ ≤ 12

**Current status:**
- ✅ τ ≤ 12 is PROVEN for PATH_4 (slot290_tau_le_12_fixed.lean - 0 sorry, 0 axiom)
- ❓ τ ≤ 8 remains OPEN

### The 8-Edge Question

To achieve τ ≤ 8, we need to find overlaps between the covers for T_pair(A,B) and T_pair(C,D).

**Potential overlaps:**
- Bridge triangles at v2 (in both T_pair(A,B) and T_pair(C,D))
- Internal edges {v1,v2}, {v2,v3} might cover multiple regions
- Some base edges might not be needed (if avoiding triangles don't exist)

**This requires careful enumeration and is the OPEN PROBLEM.**

## Recommendations

1. **Move `slot51_path4_PROVEN.lean` to `partial/`** - Contains false lemma
2. **Update database** - Mark tau_pair_le_4 submissions as targeting false lemma
3. **Focus on τ ≤ 12 → τ ≤ 8 reduction** - Enumerate actual edges needed, find overlaps
4. **Alternative: Construct explicit counterexample** - Show τ = 9 or 10 for some PATH_4 graph

## Summary Table

| Claim | Status | Evidence |
|-------|--------|----------|
| Middle-element externals through private vertices exist | ✅ TRUE | Structural argument |
| Critic A's 7-edge cover is valid | ❌ FALSE | Missing {v1,b}, bases |
| τ(T_pair(e,f)) ≤ 4 | ❌ FALSE | Database + decomposition |
| τ(T_pair(e,f)) ≤ 6 | ✅ TRUE | 4 spokes + 2 bases |
| τ ≤ 12 for PATH_4 | ✅ PROVEN | Slot290, 0 sorry, 0 axiom |
| τ ≤ 8 for PATH_4 | ❓ OPEN | 1 sorry, depends on false lemma |
