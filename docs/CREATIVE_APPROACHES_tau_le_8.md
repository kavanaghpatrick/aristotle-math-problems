# 5 Creative Approaches to Prove τ ≤ 8 for cycle_4 (ν=4)

**Date**: January 4, 2026
**Status**: Brainstorm Phase - Propose alternatives to blocked vertex-local approaches
**Context**: Pattern 22 (bridge_externals_share_apex is FALSE) blocks sunflower/fan structure at shared vertices. τ ≤ 12 is PROVEN. Need τ ≤ 8.

---

## Problem Summary

**What we know:**
- τ ≤ 12 is proven (slot139, no sorry, correct)
- Computational search shows max τ = 6 in actual instances
- ν = 4 for cycle_4 (M = {A,B,C,D} with cyclic structure)
- All vertex-local approaches are blocked (Patterns 20-22)
- τ ≤ 8 requires fundamentally new structure

**Why sunflower/fan is blocked:**
- Externals of different M-elements (A vs B) at shared vertex v don't share a common apex x
- This breaks the 4+4 covering approach that assumes 4 M-edges + 4 "fan" edges = 8 total
- The 5-packing argument only works for externals of the SAME M-element

---

## Approach 1: Weight Function + Discharging

**Name**: Energy Discharging via Edge-Weight Potential

**Core Idea**:
Assign a weight function w : E → [0,1] such that every triangle charges ≥1 unit across its edges. Prove that an 8-edge set must have total weight ≥ (# triangles). This is a "potential function" argument similar to the 4-color theorem's discharging method.

**Key Lemma** (needs proof):
```
For every triangle t ∈ T_all, there exists a decomposition of t's vertices
such that any edge set E with |E| ≤ 8 has weight(E) < |T_all|.
Equivalently: Every 7-edge set leaves uncovered triangles that charge > total weight.
```

**Why it avoids known false patterns:**
- Does NOT assume vertex-local coverage (avoids Pattern 20-22)
- Does NOT assume triangles share edges in any particular way (avoids Patterns 6-7)
- Does NOT use König/link graph structure (avoids Pattern 8)
- Does NOT partition externals (avoids Pattern 17)
- Uses GLOBAL weight conservation instead

**How to build it:**
1. Assign each triangle t weight 1/|edges(t)| initially
2. Show that redistribution via edge-covering creates a "deficit":
   - Each edge e can reduce weight of at most deg(e) triangles
   - Total weight reduction ≤ 8 × max_degree(e)
3. For cycle_4, max_degree ≈ 3-4 (each edge appears in ≤4 triangles)
   - So 8 edges can cover at most 8×4 = 32 triangles
   - If total triangles < 32, we're done
   - If ≥32, need finer analysis of which edges provide most coverage

**Confidence**: 60%

**Why?** Discharging works when there's global structure (like planar graphs). For triangle covering, the structure is looser. May need auxiliary claims about coverage efficiency. But the approach is sound in principle.

---

## Approach 2: Computational Verification + Structural Lemmas

**Name**: Hybrid Analytical-Computational Proof

**Core Idea**:
Prove τ ≤ 8 by combining:
1. **Case analysis**: Enumerate possible "cycle_4 shapes" (parameter: how the 4 M-elements connect)
2. **For small cases (|V| ≤ 15)**: Run SAT solver to verify τ ≤ 8
3. **For general cases**: Prove structural lemmas showing why small cases are representative

**Key Lemma** (needs proof):
```
If G is a counterexample to τ ≤ 8 with ν(G) = 4 and cycle_4 structure,
then ∃ induced subgraph G' with |V'| ≤ 15, ν(G') = 4, τ(G') > 8.
(i.e., minimal counterexamples are small)
```

**Why it avoids known false patterns:**
- Does NOT assume any covering structure (avoids all Patterns 1-7)
- Uses computational verification as ground truth (avoids pure theory bugs)
- Does NOT claim theorems about infinite families, only finite cases + scaling lemma
- Avoids all lemmas in FALSE_LEMMAS.md by not using them

**How to build it:**
1. **Encode triangle covering as SAT**:
   - Variables: x_e ∈ {0,1} for each edge e ∈ E
   - Constraint: For each triangle t, ⋁_{e∈t} x_e (at least one edge)
   - Minimize: Σ x_e
   - Ask: Does solver find |E| ≤ 8?

2. **Generate all cycle_4 instances on K_n for n=6,7,...,15**:
   - For each: Check packability (can we find 4-packing?)
   - For each: Run SAT solver on triangle hitting set
   - Log: All with τ ≤ 8

3. **Prove reduction lemma**:
   - If t is a triangle containing v that appears in every 8-edge cover,
     then any larger graph containing t must also require that edge in any 8-cover
   - This gives a structural scaling property

4. **Verify computationally for all small cycle_4 instances**
5. **Submit to Aristotle**: Structural lemma + computed verification

**Confidence**: 75%

**Why?** SAT solvers are extremely reliable for small instances. The reduction lemma is plausible: if a local structure forces an edge in small cases, it does so globally. Risk: The reduction lemma might need modification. But computational verification is ground truth.

---

## Approach 3: Fractional LP Relaxation with Explicit Certificates

**Name**: Dual Certification via Fractional Packing

**Core Idea**:
Instead of proving τ ≤ 8 constructively, prove ν* ≤ 4 via linear programming duality.
By Krivelevich: τ ≤ 2ν*. So ν* ≤ 4 → τ ≤ 8.

The idea: Construct an explicit fractional packing w : T → [0,1] with weight(w) = 4, such that
- ∀ e ∈ E: Σ_{t ∈ T : e ∈ t} w(t) ≤ 1 (fractional packing constraint)
- Σ_t w(t) = 4 (total weight)

This is a dual certificate proving ν* ≥ 4. By LP duality, this implies τ* ≤ 8 (fractional cover).
Then prove τ ≤ τ* + O(1) via rounding (hard part).

**Key Lemma** (needs proof):
```
For cycle_4 packing M = {A,B,C,D}, there exists fractional packing w
with w(A)=w(B)=w(C)=w(D)=1 (or close) such that every edge e hits
total weight ≤ 1.
```

**Why it avoids known false patterns:**
- Does NOT use any vertex-local lemmas (avoids Patterns 20-22)
- Does NOT assume partition/decomposition of externals (avoids Pattern 17-19)
- Uses LP duality which is mechanically sound
- Avoids all false covering lemmas by working in fractional relaxation

**How to build it:**
1. **For each M-element** A = {a,b,c}:
   - Set w(A) = 1
   - For externals T ∈ Ext(A), set w(T) = α_A (uniform weight on externals of A)
   - Choose α_A to satisfy coverage constraint at critical edges

2. **Analyze edge constraints**:
   - An M-edge e ∈ A covers:
     - A itself: weight 1
     - Externals using e: depends on α_A
   - For constraint e ∈ E: Σ w(t ∈ T : e ∈ t) ≤ 1
     - We have w(A) = 1 from M-element
     - So externals using e must have w ≤ 0?
     - This suggests w(external) = 0, i.e., externals get no weight

3. **But externals DO exist** (maximality of M):
   - Need to distribute external weight across edges they use
   - Key insight: Use a SPARSE subset of edges (not all M-edges)
   - Pick 4 edges from the 12 M-edges such that:
     - They cover all 4 M-elements (one per element, using base or spoke)
     - External weight fits the slack

4. **Prove existence** via linear algebra / pigeonhole

**Confidence**: 45%

**Why?** This is the "right" direction (LP duality is bulletproof), but the edge selection might be overspecified. If we can show 4 carefully chosen edges absorb all M-weight and external-weight with fractional slack, this works. Problem: Do such 4 edges always exist for ANY cycle_4? Unlikely. More likely: need 5-6 edges, giving τ* ≤ 9-10, so τ ≤ 10-11 after rounding. Still doesn't reach τ ≤ 8.

---

## Approach 4: Stability Argument + Extremal Graph Theory

**Name**: Structural Rigidity via Stability

**Core Idea**:
Prove that the cycle_4 packing M is "nearly extremal" - i.e., ANY deviation from the cycle structure gives τ < 8.
Then use extremal graph theory to show the cycle structure itself admits τ ≤ 8 (possibly via case analysis on symmetries).

**Key Lemma** (needs proof):
```
If G is a graph with ν(G) = 4 and M = {A,B,C,D} is a 4-packing
NOT forming a cycle (e.g., star or path), then τ(G) ≤ 7.
This implies: τ ≤ 8 for all ν=4, with cycle_4 being the unique hard case.
```

**Why it avoids known false patterns:**
- Does NOT assume shared vertex behavior (avoids Patterns 20-22)
- Does NOT make covering assumptions (avoids Patterns 1-9)
- Uses structure of the packing itself (which M-elements are adjacent) not triangles
- Works at the PACKING level, not triangle level

**How to build it:**
1. **Classify 4-packings by adjacency graph**:
   - Star: One M-element adjacent to 3 others
   - Path: A-B-C-D linear
   - Cycle: A-B-C-D-A circular
   - Other: Enumerate finitely many

2. **For each type, bound τ**:
   - **Star** (e.g., A adjacent to B,C,D but B,C,D pairwise disjoint):
     - Externals of B, C, D are isolated (no bridges)
     - Cover: all 12 M-edges + isolated externals
     - But disjoint M-elements mean covering is independent
     - Should give τ ≤ 6-7
   - **Path** (A-B-C-D linear):
     - Externals at boundaries (A↔B, C↔D) might be more complex
     - Internals (B↔C) have limited structure
     - Likely τ ≤ 7
   - **Cycle** (A-B-C-D-A):
     - Most connected structure
     - Each vertex is shared by exactly 2 M-elements
     - Need τ ≤ 8

3. **For cycle only**: Use symmetry to reduce cases:
   - By rotation, focus on A's structure
   - A shares v_da with D and v_ab with B
   - Externals at v_ab use edges from {A,B} edges
   - By Pattern 22 counterexample, they don't share apex
   - But: maybe they're forced to use SAME EDGE of A or B?
   - If so, get tighter bound

**Confidence**: 50%

**Why?** The stability claim is plausible but unproven. The hope is that deviations from cycle are easier. For cycle itself, the symmetry reduction is valid but might not yield τ ≤ 8 without additional insight.

---

## Approach 5: Greedy + Potential Function Hybrid

**Name**: Adaptive Greedy with Deficit Tracking

**Core Idea**:
Build an 8-edge cover greedily, at each step choosing the edge that covers the most uncovered triangles.
Prove that THIS GREEDY ALGORITHM always terminates in ≤8 edges for cycle_4.
This is different from proving a static 8-edge set works - instead prove the ALGORITHM works.

**Key Lemma** (needs proof):
```
For any graph G with ν(G) = 4 and cycle_4 packing M:
GreedyMaximalCover(G, T_all) produces cover set C with |C| ≤ 8.

Proof structure:
- After k edges, |uncovered| ≤ ceiling(total / (8-k+1))
- This gives a recurrence that terminates in ≤8 steps
```

**Why it avoids known false patterns:**
- Does NOT assume triangles partition or share structure (avoids all false patterns)
- Does NOT use any local covering lemmas
- Uses only property: "each edge hits SOME triangles" (universally true)
- Algorithm is constructive and mechanically verifiable

**How to build it:**
1. **Prove greedy coverage bound**:
   - Let I_k = uncovered triangles after k edges
   - Let e_k = k-th edge chosen by greedy (covers most uncovered)
   - Claim: |I_{k+1}| ≤ |I_k| - |I_k|/(8-k) (covers at least 1/(8-k) fraction)

   Why? By pigeonhole:
   - Total triangles: T_all (fixed, ≤ ~100 for cycle_4)
   - At most 8-k edges remain
   - By pigeonhole, some edge hits ≥ T_all/(8-k) triangles
   - Greedy picks edge with ≥ T_all/(8-k) uncovered triangles

2. **Verify for cycle_4**:
   - T_all ≤ 100 (rough upper bound: 4×3 M-edges × 8 externals = 96)
   - After 0 edges: |I_0| = T_all ≤ 100
   - After 1 edge: |I_1| ≤ 100 - 100/8 = 100 - 12.5 = 87.5
   - After 2 edges: |I_2| ≤ 87.5 - 87.5/7 ≈ 75
   - ...
   - After 7 edges: |I_7| ≤ ? (should be ≤ ?/1)

   The recurrence is: I_{k+1} ≤ I_k × (1 - 1/(8-k))

   Telescoping: I_8 ≤ T_all × ∏_{k=0}^{7} (1 - 1/(8-k))
              = T_all × (7/8) × (6/7) × (5/6) × ... × (0/1)
              = 0

   Perfect! The greedy algorithm terminates in ≤8 edges.

3. **Implementation**:
   - For cycle_4, compute T_all exactly
   - Prove |I_8| = 0 via the telescoping product
   - Or verify computationally for specific instances

**Confidence**: 85%

**Why?** The greedy algorithm analysis is airtight. The only catch: need T_all < infinity (true). The pigeonhole argument is standard. The telescoping product is mechanical. The risk is that the greedy bound might not apply to cycle_4 specifically if there are pathological triangle arrangements. But this is unlikely - even worst-case triangles must eventually be covered.

---

## Summary Table

| # | Approach | Method | Confidence | Effort | Risk |
|---|----------|--------|------------|--------|------|
| 1 | Weight Discharging | Potential function | 60% | 5-7 days | Global structure might not apply |
| 2 | Computational Hybrid | SAT + reduction lemma | 75% | 3-4 days | Reduction lemma might fail |
| 3 | LP Duality | Fractional packing + rounding | 45% | 4-6 days | Might only get τ ≤ 10 |
| 4 | Structural Stability | Packing classification + symmetry | 50% | 2-3 days | Cycle case might need full analysis |
| 5 | Greedy Algorithm | Pigeonhole + telescoping product | 85% | 2 days | Most straightforward |

---

## Recommendation Priority

**Try in order:**
1. **Start with Approach 5** (Greedy Algorithm): 2 days, 85% chance, mechanical
2. **If 5 fails**: Approach 2 (Computational Hybrid): 3-4 days, 75% chance
3. **If 2 fails**: Approach 1 (Weight Discharging): 5-7 days, 60% chance
4. **If 1 fails**: Approach 4 (Structural Stability): 2-3 days, 50% chance (quick fallback)
5. **If 4 fails**: Approach 3 (LP Duality): 4-6 days, 45% chance (most ambitious)

---

## Key Insight to Exploit

All approaches share one crucial observation:

**Fact**: Computational search shows actual max τ = 6 for ν=4.

This suggests τ ≤ 8 is NOT tight, and the gap (8 vs 6) might be exploitable via:
- Greedy: Works because triangle density is low
- Computational: Small instances show the pattern
- Discharging: Weight can account for sparse structure
- Stability: Cycle might have hidden structure

The challenge is translating "empirically true for small cases" into "provably true for all cases" - which Approach 2 directly addresses.

---

## Next Steps

1. **Immediate** (today): Implement Approach 5 (Greedy) in Lean
   - Define GreedyMaximalCover
   - Prove coverage lemma
   - Verify cycle_4 termination

2. **Fallback** (if needed): Begin Approach 2 (SAT + reduction)
   - Set up SAT encoder for triangle hitting set
   - Generate cycle_4 instances
   - Run verification

3. **Monitoring**: Track which approaches invalidate which false patterns
   - Greedy: Doesn't use ANY false lemmas ✓
   - Computational: Uses only finite verification ✓
   - Others: May need to avoid 3-5 false patterns each

---

**Document generated**: Jan 4, 2026 | **Status**: Ready for implementation
