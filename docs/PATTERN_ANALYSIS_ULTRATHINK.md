# Pattern Analysis: Why PATH_4 is the Hardest Case

## Key Question
Under ν = 4, can S_e externals exist for each pattern?

---

## Analysis by Pattern

### 1. STAR_ALL_4: A={0,1,2}, B={0,3,4}, C={0,5,6}, D={0,7,8}

**Claim**: Under ν = 4, NO S_e externals can exist.

**Proof**:
Consider S_e(A) external on base edge {1,2}:
- E = {1, 2, x} for some x
- E edges: {1,2}, {1,x}, {2,x}
- B edges: {0,3}, {0,4}, {3,4} → no overlap (1,2 ∉ B)
- C edges: {0,5}, {0,6}, {5,6} → no overlap (1,2 ∉ C)
- D edges: {0,7}, {0,8}, {7,8} → no overlap (1,2 ∉ D)

So E is edge-disjoint from B, C, D!
Therefore {A, B, C, D, E} would be a 5-packing → contradicts ν = 4!

**Conclusion**: star_all_4 under ν = 4 has no externals. Only bridges exist.
Bridges like {0,1,3} are covered by spokes.
**τ ≤ 4** ✓

---

### 2. SCATTERED: A={0,1,2}, B={3,4,5}, C={6,7,8}, D={9,10,11}

**Claim**: Under ν = 4, NO externals and NO bridges exist.

**Proof (Externals)**:
Any S_e(A) external E is edge-disjoint from B, C, D (completely different vertices).
So {A, B, C, D, E} is a 5-packing → contradiction!

**Proof (Bridges)**:
A bridge needs to share 2 vertices with each of two elements.
But elements are vertex-disjoint (A ∩ B = ∅, etc.)
A triangle has only 3 vertices, can't share 2 with each of 2 disjoint sets.

**Conclusion**: scattered under ν = 4 has only M-triangles.
**τ = 4** (exact) ✓

---

### 3. THREE_SHARE_V: A={0,1,2}, B={0,3,4}, C={0,5,6}, D={7,8,9}

**Claim**: Under ν = 4, NO externals exist.

**Proof**:
S_e(A) external E on {1,2}: edges {1,2}, {1,x}, {2,x}
- B,C edges all contain 0 (shared vertex)
- D = {7,8,9} is separate, edges {7,8}, {7,9}, {8,9}
- E has no overlap with B, C, D!

So {A, B, C, D, E} is 5-packing → contradiction!

Similarly, S_e(D) externals would be disjoint from A, B, C → 5-packing.

**Conclusion**: three_share_v under ν = 4 has only M-triangles and bridges within 3-star.
**τ ≤ 4** ✓

---

### 4. TWO_TWO_VW: A={0,1,2}, B={0,3,4}, C={5,6,7}, D={5,8,9}

**Claim**: Under ν = 4, NO externals exist.

**Proof**:
S_e(A) external E on {1,2}: edges {1,2}, {1,x}, {2,x}
- B edges: {0,3}, {0,4}, {3,4} → 1,2 ∉ B, no overlap
- C edges: {5,6}, {5,7}, {6,7} → 1,2 ∉ C, no overlap
- D edges: {5,8}, {5,9}, {8,9} → 1,2 ∉ D, no overlap

E is edge-disjoint from B, C, D!
{A, B, C, D, E} is 5-packing → contradiction!

**Conclusion**: two_two_vw under ν = 4 has only M-triangles and bridges within pairs.
**τ ≤ 4** ✓

---

### 5. CYCLE_4: A={0,1,2}, B={1,3,4}, C={3,5,6}, D={5,0,7}

**Claim**: Under ν = 4, NO externals exist.

**Proof**:
S_e(A) external E on {0,2}:
- Must avoid D (contains 0): {0,x} mustn't be D-edge → x ∉ {5,7}
- Must avoid B (contains 1): already OK (0,2 ∉ B except shared vertex)
- Must avoid C: 0,2 ∉ C

For x ∉ {1,3,4,5,6,7} (i.e., x ≥ 8), E is edge-disjoint from B, C, D.
{A, B, C, D, E} is 5-packing → contradiction!

**Conclusion**: cycle_4 under ν = 4 has only M-triangles and bridges.
Bridges covered by "spine" edges {0,1}, {1,3}, {3,5}, {5,0}.
**τ ≤ 4** ✓

---

### 6. PATH_4: A={0,1,2}, B={2,3,4}, C={4,5,6}, D={6,7,8}

**THE HARD CASE!**

**Why different?**

S_e(B) external E_B = {2,3,9}:
- Shares edge {2,3} with B
- Check disjoint from A: A edges {0,1}, {0,2}, {1,2} → no {2,3} → disjoint!
- Check disjoint from C: C edges {4,5}, {4,6}, {5,6} → 2,3 ∉ C → disjoint!
- Check disjoint from D: D edges {6,7}, {6,8}, {7,8} → 2,3 ∉ D → disjoint!

So E_B ∈ S_e(B) can exist without creating 5-packing (because E_B shares edge with B).

Similarly E_C ∈ S_e(C) can exist.

**The Problem**:
If bridge T = {3,4,5} exists AND E_B doesn't cover T AND E_C doesn't cover T:
- {A, D, T, E_B, E_C} are pairwise edge-disjoint!
- 5-packing!

**slot451 proves**: This scenario implies ν ≥ 5.
**Contrapositive**: Under ν = 4, at most one of {E_B, E_C} can exist.

**slot452-453 prove**: With ≤1 forcing external, τ ≤ 8.

**Conclusion**: PATH_4 under ν = 4 has τ ≤ 8 (not 4, because of bridge complexity).

---

## SUMMARY TABLE

| Pattern | Externals under ν=4? | Bridges? | τ bound |
|---------|----------------------|----------|---------|
| star_all_4 | NO (5-packing) | Yes (trivial) | ≤ 4 |
| scattered | NO (5-packing) | NO | = 4 |
| three_share_v | NO (5-packing) | Within 3-star | ≤ 4 |
| two_two_vw | NO (5-packing) | Within pairs | ≤ 4 |
| cycle_4 | NO (5-packing) | Yes (trivial) | ≤ 4 |
| **path_4** | **S_e CAN exist** | Yes (complex) | **≤ 8** |

---

## WHY PATH_4 IS SPECIAL

In PATH_4, S_e(B) and S_e(C) externals:
1. Share edge with B or C respectively
2. Are edge-disjoint from A and D (the endpoints)
3. Can be edge-disjoint from each other

This allows S_e externals to exist without creating 5-packing (they share edges with middle elements).

In other patterns, any S_e external would be edge-disjoint from ALL other packing elements, creating 5-packing.

---

## CONCLUSION

**PATH_4 is the ONLY pattern requiring τ ≤ 8 analysis under ν = 4.**

All other patterns have τ ≤ 4 because:
- Either no externals exist (5-packing contradiction)
- Or bridges are trivially covered by spoke/spine edges

**slot375-379 are COMPLETE** for non-PATH_4 patterns.
**slot451-453 are COMPLETE** for PATH_4.

Together: **τ ≤ 8 for ALL ν = 4 graphs!**
