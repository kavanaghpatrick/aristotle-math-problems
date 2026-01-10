# ROUND 3 DEBATE: Executive Summary

## The Question

**Can middle-element externals through private vertices exist in PATH_4?**

Specifically: Can triangle T = {v1, b, x} exist where B = {v1, v2, b} is a middle element and x is a "wild" vertex outside M?

## Answer: YES

### Why They Exist

1. **No structural prohibition** - `isPath4` only constrains M's intersection structure
2. **Maximality satisfied** - T shares edge {v1,b} with B, so cannot join packing
3. **Classification** - T is a valid B-external triangle

### Example Construction

```
PATH_4: A = {v1, a1, a2}
        B = {v1, v2, b}    ← b is private to B
        C = {v2, v3, c}
        D = {v3, d1, d2}

Triangle: T = {v1, b, x}   ← x can be any vertex with edges to v1 and b
```

## Impact on Covers

### Critic A's Proposed 7-Edge Cover: INVALID

**Missing:**
- Spoke {v1,b} from B → fails to cover T = {v1, b, x}
- Spoke {v3,c} from C
- Base edges for avoiding-vertex externals

### The Correct Bounds

| Approach | Bound | Status | Evidence |
|----------|-------|--------|----------|
| τ(T_pair(e,f)) ≤ 4 | ❌ FALSE | Database | False lemma #11 |
| τ(T_pair(e,f)) ≤ 6 | ✅ TRUE | Math | 4 spokes + 2 bases |
| PATH_4: τ ≤ 12 | ✅ PROVEN | Slot290 | 0 sorry, 0 axiom |
| PATH_4: τ ≤ 8 | ❓ OPEN | - | Depends on false lemma |

## Key Finding: False Lemma

**From database (`false_lemmas` table):**

```
Lemma: tau_pair_le_4
Claim: 4 edges suffice to cover T_pair(e,f) when e ∩ f = {v}
Status: FALSE
Reason: Requires 4 spokes + 2 base edges = 6, not 4
```

**Consequence:** File `slot51_path4_PROVEN.lean` contains sorry in false lemma.

## Mathematical Explanation

### Why 6 Edges Are Needed

For e = {v, a1, a2} and f = {v, b1, b2} sharing vertex v:

**Triangles containing v:**
- Covered by 4 spokes: {v,a1}, {v,a2}, {v,b1}, {v,b2}

**Triangles avoiding v:**
- Those sharing base {a1,a2} with e → need edge {a1,a2}
- Those sharing base {b1,b2} with f → need edge {b1,b2}

**Total: 6 edges**

### Why Middle-Element Externals Matter

Triangle T = {v1, b, x}:
- Contains edge {v1,b} (spoke from B)
- Contains v1 (shared vertex)
- Is in `trianglesContaining(T_pair(A,B), v1)`
- **Must be covered by spoke {v1,b}**

If cover omits {v1,b}, it FAILS.

## Current State of PATH_4

✅ **PROVEN:** τ ≤ 12 (slot290_tau_le_12_fixed.lean)

❓ **OPEN:** τ ≤ 8

### Path to τ ≤ 8

**Option 1: Find edge overlaps**
- T_pair(A,B) needs ≤ 6 edges
- T_pair(C,D) needs ≤ 6 edges
- Union bound: ≤ 12
- **Challenge:** Identify which 4 edges can be shared/eliminated

**Option 2: Different decomposition**
- Abandon T_pair approach
- Use alternative covering strategy
- Target specific PATH_4 structure

**Option 3: Prove τ = 9 or 10**
- Construct explicit counterexample
- Show 8 edges insufficient for some PATH_4 graph
- Close the question with a bound > 8

## Recommendations

1. **Database cleanup** - Mark slot51 as containing false lemma
2. **File organization** - Move slot51 to `partial/` (contains sorry in false lemma)
3. **Strategic pivot** - Either prove τ = 9/10 or find new approach for τ ≤ 8
4. **Document learnings** - Add to `failed_approaches` if τ ≤ 8 via tau_pair is impossible

## Bottom Line

**Middle-element externals through private vertices DO exist.**

**Critic A's cover is INVALID.**

**The τ ≤ 8 proof attempt is blocked by a FALSE LEMMA.**

**τ ≤ 12 is the current proven bound for PATH_4.**
