# Debate Context: New Decomposition Strategy for PATH_4 τ ≤ 8

## Problem Setting

We are proving **Tuza's conjecture for ν=4**: τ(G) ≤ 2ν = 8.

**PATH_4 structure**: A packing M = {A, B, C, D} where:
- A—B—C—D (path graph on packing elements)
- A∩B = {v1}, B∩C = {v2}, C∩D = {v3}
- A∩C = ∅, A∩D = ∅, B∩D = ∅
- A = {v1, a1, a2}, B = {v1, v2, b}, C = {v2, v3, c}, D = {v3, d1, d2}
- M is a maximum packing (ν = 4) AND maximal (every non-M triangle shares ≥2 vertices with some M element)

## What's PROVEN (Aristotle-verified, sorry=0, axiom=0)

### slot553: 5-Packing Contradiction
If three non-M "witness" triangles F={a1,a2,x}, T={v1,a2,y}, S={v1,a1,z} exist with x, y, z **pairwise distinct** and all outside A, then {F, T, S, C, D} is a 5-packing → contradiction with ν=4.

**Corollary**: For any three witnesses, x=y OR x=z OR y=z. So |X ∪ Y ∪ Z| ≤ 2 where X,Y,Z are the sets of extra vertices in each fan.

### slot554: Apex → 2-Edge Cover
If some u ∈ A is in every non-M T_e(A) triangle, then {s(u,w1), s(u,w2)} covers all T_e(A). So τ(T_e(A)) ≤ 2 when a universal apex exists.

### slot548: PATH_4 τ≤8 when no base-edge external
When endpoint A has no "base-edge external" triangle {a1,a2,w} (w∉A), then v1 is automatically in every non-M T_e(A) triangle, so τ(T_e(A))≤2 and the old assembly works.

### slot552: Base-edge external cannot bridge to adjacent element
|{a1,a2,w} ∩ B| ≤ 1 (trivially, since a1,a2 ∉ B). BUT this does NOT mean w ∉ B!

## What's FALSE (Aristotle-verified counterexamples)

### τ(T_e(A)) ≤ 2 — FALSE (slot556)
**Counterexample on Fin 9:**
- A={0,1,2}, B={0,3,4}, C={3,5,6}, D={5,7,8}
- PATH_4: A—[0]—B—[3]—C—[5]—D
- Extra edges: 1-3, 1-4, 2-3, 2-4 (making w1=3, w2=4 adjacent to all of {0,1,2})
- **w1=3 ∈ B, w2=4 ∈ B** ← this is the key
- T_e(A) has 7 triangles (A + 6 non-M), τ(T_e(A)) = 3
- ν = 4 (no 5-packing exists)
- **BUT τ(G) = 6 ≤ 8** (Tuza bound still holds for the full graph!)

### Why the old decomposition is broken
- T_e(A) + T_e(D) + remaining gave 2+2+4 = 8
- Now τ(T_e(A)) can be 3, so best bound is 3+3+4 = 10

### Why the debate consensus was wrong
The Feb 9 debate concluded "all-six ⇒ ν≥5" via the 5-packing {v1,a1,w1},{v1,a2,w2},B,C,D.
This **fails when w1,w2 ∈ B**: the triangles {v1,a_i,w_j} share 2 vertices with B (since v1 ∈ B and w_j ∈ B), so |{v1,a_i,w_j} ∩ B| = 2 ≥ 2, violating the packing condition.

### Other falsified approaches (do NOT retry)
- Apex-based bridge coverage (slot543)
- 6-packing argument (K4 counterexample)
- LP duality (too complex)
- Universal apex for endpoints (Fin 10 K4 counterexample)

## Key Observations About the Counterexample

In the Fin 9 graph where τ(T_e(A)) = 3:

1. **T_e(D) is trivial**: Only D itself (1 triangle). τ(T_e(D)) = 1.
2. **T_e(B) heavily overlaps T_e(A)**: 4 of 6 non-M T_e(A) triangles are also in T_e(B)
   - {v1,a1,w1}, {v1,a1,w2}, {v1,a2,w1}, {v1,a2,w2} all share 2 vertices with B (v1 + w_j)
   - Only {a1,a2,w1}, {a1,a2,w2} are in T_e(A) but NOT T_e(B)
3. **Remaining (after T_e(A) ∪ T_e(D))**: 4 triangles {B, C, {1,3,4}, {2,3,4}}, τ = 2
4. **Actual total**: τ(T_e(A)) + τ(T_e(D)) + τ(remaining) = 3 + 1 + 2 = 6 ≤ 8

**The parts compensate**: When τ(T_e(A)) is large, the other parts shrink.

## Potential New Strategies

### Strategy A: S_A∪S_B Partition (Frontier Approach)
- Group 1: S_A ∪ S_B = triangles sharing ≥2 with A or ≥2 with B
- Group 2: Everything else (shares ≤1 with A and ≤1 with B, so shares ≥2 with C or D)
- ν(Group 1) ≤ 3 (insert D → |P|+1 ≤ 4)
- Parker's result: ν ≤ 3 → τ ≤ 6
- ν(Group 2) ≤ 2 (insert A and B)
- Tuza ν ≤ 2: τ ≤ 4
- **Problem: 6 + 4 = 10, not 8**
- But: Can we prove τ(Group 2) ≤ 2? Or τ(Group 1) ≤ 4?

### Strategy B: Compensating Decomposition
- Keep T_e(A) + T_e(D) + remaining
- Prove: τ(T_e(A)) + τ(T_e(D)) + τ(remaining) ≤ 8 JOINTLY
- When all-six pattern exists (τ(T_e(A))=3): τ(remaining) shrinks because w1,w2 ∈ B constrains remaining
- Need: If τ(T_e(A)) = 3 then τ(remaining) ≤ 2 (so 3+3+2=8 or 3+2+2=7)

### Strategy C: Direct 8-Edge Construction
- Construct 8 specific edges that cover all triangles
- Not necessarily from M's edges — can include non-M edges
- Case-split on whether base-edge externals exist, and where their extras land

### Strategy D: Modified Parker Partition
- Part 1: T_e(A) ∪ T_e(B) ∪ T_e(C) (everything except T_e(D)-only)
  - ν unknown, can't easily insert other elements
- Part 2: T_e(D) only
  - ν(Part 2) ≤ 1 (insert A, B, C) → τ ≤ 2
- Would need τ(Part 1) ≤ 6

### Strategy E: Three-Way Split
- Left: T_e(A) (shares ≥2 with A, ≤1 with D by disjointness)
- Right: T_e(D) (shares ≥2 with D, ≤1 with A)
- Middle: remaining (shares ≤1 with A and ≤1 with D)
- ν(Left) ≤ 2 (insert C, D), so τ(Left) ≤ 4
- ν(Right) ≤ 2 (insert A, B), so τ(Right) ≤ 4
- ν(Middle) ≤ 2 (insert A, D), so τ(Middle) ≤ 4
- **Problem: 4 + 4 + 4 = 12, much too loose**
- BUT: τ(Left) + τ(Right) + τ(Middle) might be ≤ 8 jointly (trade-off argument)

### Strategy F: Vertex-Based Cover
- Choose 4 vertices, one from each M element (e.g., v1, v2, v3, and one more)
- Take all edges incident to these 4 vertices
- Prove they cover all triangles
- Count the minimum edges needed → bound by 8

## Questions for Debate

1. **Which strategy is most promising?** Strategies B and C seem most likely to work but hardest to prove. Strategy A gives 10, not 8.

2. **Can we prove the compensating bound (Strategy B)?** Specifically: when w1,w2 ∈ B and τ(T_e(A)) = 3, can we prove τ(remaining) ≤ 2?

3. **Is Parker's result for ν≤3 (τ≤6) available as an axiom?** Is it published and trusted enough?

4. **What structure does w1,w2 ∈ B impose?** This makes T_e(A) and T_e(B) heavily overlap. Can we exploit this?

5. **Should we try an entirely different proof method** (e.g., fractional relaxation, specific graph structure theorems)?

## Verified Facts for This Graph (Fin 9)

| Property | Value |
|----------|-------|
| ν | 4 |
| τ(G) | ≤ 6 (witness: edges 0-1, 3-4, 5-6, 7-8, 2-3, 2-4) |
| τ(T_e(A)) | 3 |
| τ(T_e(D)) | 1 |
| τ(remaining after T_e(A)∪T_e(D)) | 2 |
| τ(S_A∪S_B) | ≤ 4 (witness: edges 1-3, 2-4, 0-1, 0-3) |
| |S_A∪S_B| | 10 triangles |
| |remaining after S_A∪S_B| | 2 triangles (C, D) |

## Practical Constraints
- Must be formalizable in Lean 4 / Mathlib
- Aristotle verifies sorry=0 files reliably
- native_decide on Fin 6-12 is fast and reliable
- Falsification tests should precede proof attempts
- Parker's ν≤3 → τ≤6 is a known result but needs axiom treatment
- Tuza ν≤2 → τ≤4 is already used as an axiom (trusted)
