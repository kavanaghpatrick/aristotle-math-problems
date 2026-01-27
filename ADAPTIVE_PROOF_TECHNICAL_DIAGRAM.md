# Technical Diagram: Where Adaptive Selection Breaks

## Data Flow of the Proof

```
INPUT:
  - Graph G with ν(G) ≤ 4
  - M = {A, B, C, D} maximal packing (PATH_4)
  - Each X ∈ M has 3 edges

┌─────────────────────────────────────────────────────────────────┐
│ STEP 1: Externals Use ≤ 2 Edges (PROVEN ✓)                     │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│ For each X ∈ M:                                                │
│   IF externals S_X use all 3 edges {e₁, e₂, e₃}:              │
│     ∃ T₁ = {a,b,x₁}, T₂ = {a,c,x₂}, T₃ = {b,c,x₃}            │
│     {T₁, T₂, T₃} is a packing (pairwise |∩| = 1)              │
│     {T₁, T₂, T₃} ∪ (M\{X}) is size 6 packing                  │
│     ⟹ Contradiction with ν ≤ 4                                  │
│   ∴ S_X uses ≤ 2 edges                                          │
│                                                                 │
│ OUTPUT: ∃ e₁, e₂ such that ∀ T ∈ S_X, T.sym2 ∩ {e₁,e₂} ≠ ∅   │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│ STEP 2: Choose 2 Edges per X (UNPROVEN ?)                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│ For each X ∈ M:                                                │
│   Choose E_X ⊆ X.edges with |E_X| = 2                         │
│   Requirement: ∀ T ∈ S_X, ∃ e ∈ E_X, e ∈ T.sym2              │
│   (This is POSSIBLE per Step 1)                                │
│                                                                 │
│ But wait... this only covers EXTERNALS (S_X)!                  │
│ What about:                                                     │
│   • The M-element X itself? (It's a triangle in G!)            │
│   • Bridges that share edge with X and Y?                      │
│   • Triangles that share edge with X but don't share edge      │
│     with any OTHER M-element (not external to X)?              │
│                                                                 │
│ ISSUE: E_X ⊆ X.edges, and X is a 3-edge triangle.             │
│        2 edges ≠ all 3 edges, so X itself not fully covered!   │
│                                                                 │
│ OUTPUT: ✗ INCOMPLETE COVERAGE                                  │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│ STEP 3: M-Element Coverage (NOT ADDRESSED)                     │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│ Problem: How are M-elements (A, B, C, D) themselves covered?   │
│                                                                 │
│ A = {a, b, c} is a triangle with 3 edges: {a,b}, {a,c}, {b,c} │
│ If E_A = {{a,b}, {a,c}}, then:                                 │
│   • Edge {a,b} ∈ A.sym2 ✓                                       │
│   • Edge {a,c} ∈ A.sym2 ✓                                       │
│   • But {b,c} ∉ E_A ✗                                           │
│                                                                 │
│ For A to be covered, we need ∃ e ∈ E_A, e ∈ A.sym2            │
│ This is true! Both E_A edges are in A.                         │
│ ✓ M-elements ARE covered (trivially, by their edges)           │
│                                                                 │
│ OUTPUT: ✓ M-elements covered (as a side effect)                │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│ STEP 4: Bridge Coverage (UNPROVEN ✗)                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│ Bridge T between A and B:                                       │
│   • Shares 2 vertices with A (so shares an edge)                │
│   • Shares 2 vertices with B (so shares an edge)                │
│   • May NOT share a vertex with any other M-element             │
│                                                                 │
│ Example: T = {a, v_ab, b}  where:                              │
│   • a ∈ A \ {v_ab, b, ...}  (private to A)                     │
│   • v_ab = A ∩ B (shared)                                       │
│   • b ∈ B \ {v_ab, a, ...}  (private to B)                     │
│                                                                 │
│ Edges of T.sym2:                                               │
│   {a, v_ab}   -- one in A, one in A ∩ B                        │
│   {a, b}      -- one in A, one in B (NOT both in any M-element)
│   {v_ab, b}   -- one in A ∩ B, one in B                        │
│                                                                 │
│ For coverage, need ∃ e ∈ E_A ∪ E_B, e ∈ T.sym2                │
│                                                                 │
│ Case 1: {a, v_ab} ∈ E_A?                                       │
│   E_A ⊆ A.edges = {{a,b_A}, {a,c_A}, {b_A,c_A}}              │
│   where b_A, c_A ≠ v_ab in general                             │
│   So {a, v_ab} might NOT be in E_A ✗                           │
│                                                                 │
│ Case 2: {v_ab, b} ∈ E_B?                                       │
│   E_B ⊆ B.edges = {{v_ab, b_B}, {v_ab, c_B}, {b_B, c_B}}      │
│   where v_ab ∈ B, b ∈ B (from definition)                      │
│   So {v_ab, b} could be in E_B IF we choose it                 │
│   But Step 2 only guarantees E_B covers S_B, NOT bridges!      │
│                                                                 │
│ KEY INSIGHT: Bridge coverage requires SPECIFIC edge choices    │
│             (e.g., edges incident to shared vertices)          │
│             but Step 1-2 only guarantee external coverage      │
│             → Need global coordination (MISSING!)               │
│                                                                 │
│ OUTPUT: ✗ BRIDGES NOT GUARANTEED COVERED                       │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│ STEP 5: Bridge Coordination via Spine Edges (CLAIMED ✗)        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│ PATH_4: A — B — C — D                                           │
│ Shared vertices: v_ab, v_bc, v_cd (spine)                      │
│                                                                 │
│ Claim: "If we include spine edge in E_B, all bridges covered"  │
│                                                                 │
│ Problem: Which spine edge?                                      │
│   • B = {v_ab, v_bc, b_priv}                                    │
│   • B.edges = {{v_ab, v_bc}, {v_ab, b_priv}, {v_bc, b_priv}}   │
│   • E_B contains 2 of these 3 edges                             │
│   • Includes spine edge {v_ab, v_bc}? Maybe, maybe not.         │
│                                                                 │
│ Even if spine edge ∈ E_B:                                       │
│   • Bridge T = {a, v_ab, z} where a ∈ A, z ∉ B                │
│   • T.sym2 contains {a, v_ab}, {a, z}, {v_ab, z}              │
│   • {v_ab, z}? Not necessarily in B.edges (z ∉ B)             │
│   • {a, v_ab}? In A.edges only (a ∈ A, v_ab ∈ A ∩ B)         │
│                                                                 │
│ For {a, v_ab} to be covered:                                    │
│   Need {a, v_ab} ∈ E_A (since {a, v_ab} ∉ B.edges generally)  │
│   But Step 1-2 don't guarantee this choice!                    │
│                                                                 │
│ OUTPUT: ✗ SPINE EDGE ARGUMENT INCOMPLETE                       │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│ FINAL: Global Coverage (UNPROVEN ✗)                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│ Claim: E = E_A ∪ E_B ∪ E_C ∪ E_D covers all triangles in G     │
│        with |E| ≤ 8                                            │
│                                                                 │
│ What we've shown:                                              │
│   ✓ E covers M-elements (as M-elements are in M)              │
│   ✓ E covers externals S_X (by Step 1-2)                       │
│   ✗ E covers bridges (no proof!)                               │
│   ✗ E is globally consistent (no coordination proof)           │
│                                                                 │
│ Gaps:                                                          │
│   1. Bridge coverage not shown                                 │
│   2. Spine edge selection not forced                           │
│   3. Independent E_X choices don't compose                     │
│   4. Missing cases (bridges avoiding spine vertices?)          │
│                                                                 │
│ OUTPUT: ✗ THEOREM UNPROVEN                                     │
└─────────────────────────────────────────────────────────────────┘
```

---

## The Three External Types Problem (Correct Analysis)

```
Setup: X = {a, b, c}, M-element with 3 edges

If all 3 external types exist:
  Type 1 on edge {a,b}: ∃ T₁ = {a,b,x₁}
  Type 2 on edge {a,c}: ∃ T₂ = {a,c,x₂}
  Type 3 on edge {b,c}: ∃ T₃ = {b,c,x₃}

Packing property:
  |T₁ ∩ T₂| = |{a}| = 1 ✓
  |T₁ ∩ T₃| = |{b}| = 1 ✓
  |T₂ ∩ T₃| = |{c}| = 1 ✓
  (requires x₁, x₂, x₃ all distinct)

External property:
  T_i external to X ⟹ ∀ Y ∈ M, Y ≠ X, (T_i ∩ Y).card ≤ 1

Combined:
  {T₁, T₂, T₃, M \ {X}} = 6-packing ⟹ ν ≥ 6 ✗

Conclusion:
  ¬(Type 1 ∧ Type 2 ∧ Type 3) ✓ PROVEN

What this means:
  At least one edge of X has NO externals
  ⟹ ∃ 2 edges that cover ALL externals ✓ PROVEN

What this does NOT mean:
  Those 2 edges cover X itself (needs 3 edges of X) ✗ FALSE
  Those 2 edges cover bridges (needs different edges) ✗ FALSE
  Those 2 edges are globally optimal (needs coordination) ✗ FALSE
```

---

## Edge Type Coverage Analysis

```
For M-element X = {a, b, c} with edges {e₁={a,b}, e₂={a,c}, e₃={b,c}}:

EXTERNALS (S_X):
  Type 1: Uses edge e₁ = {a,b}
  Type 2: Uses edge e₂ = {a,c}
  Type 3: Uses edge e₃ = {b,c}
  ν ≤ 4 prevents all 3 types

BRIDGES (X-to-Y triangles):
  Type B1: Uses edges from both X and Y (not independent)
  Type B2: May avoid some spine vertices
  Type B3: Can be edge-disjoint from external covers

COVERAGE REQUIREMENT:
  Must cover all types with edges from:
    E_X ⊆ X.edges (up to 2 edges)
    E_Y ⊆ Y.edges (up to 2 edges)
  Problem: Bridges use edges from BOTH, but we choose independently!
```

---

## Counterexample: Why 2 Edges per Element Fails

```
Concrete PATH_4:
  A = {v₁, a, a'}   edges: {v₁,a}, {v₁,a'}, {a,a'}
  B = {v₁, v₂, b}   edges: {v₁,v₂}, {v₁,b}, {v₂,b}
  C = {v₂, v₃, c}   edges: {v₂,v₃}, {v₂,c}, {v₃,c}
  D = {v₃, d, d'}   edges: {v₃,d}, {v₃,d'}, {d,d'}

Externals of A (example):
  S_A might have:
    T₁ = {v₁, a, x₁} on edge {v₁,a}
    T₂ = {a, a', x₂} on edge {a,a'}
  Not all 3 edges used (ν ≤ 4 prevents it)

Choice: E_A = {{v₁,a}, {a,a'}} (covers S_A and A itself)

Bridges between A and B:
  B_AB = {a, v₁, v₂}  (a ∈ A, v₁,v₂ ∈ B, and v₁ ∈ A)
  Edges: {a,v₁} ⊆ A, {a,v₂} not in either, {v₁,v₂} ⊆ B

Coverage check:
  {a,v₁} ∈ E_A? Yes (E_A includes {v₁,a}) ✓

But consider:
  B_AB' = {a', v₁, v₂}  (a' ∈ A, v₁,v₂ ∈ B, v₁ ∈ A)
  Edges: {a',v₁}, {a',v₂}, {v₁,v₂}

Coverage check:
  {a',v₁} ∈ E_A? Only if E_A = {{v₁,a'}, ...}
  But E_A = {{v₁,a}, {a,a'}} (chosen to cover external S_A)
  Is {v₁,a'} ∈ E_A? NO ✗

  {v₁,v₂} ∈ E_B? Depends on B's choice
  But E_B was chosen to cover S_B, not necessarily to include {v₁,v₂}

PROBLEM: Different bridge B_AB needs edge {a,v₁}
         Different bridge B_AB' needs edge {a',v₁}
         But E_A = 2 edges can't cover both!
         And we haven't proven E_B includes {v₁,v₂}!

Result: Bridges may not be covered ✗
```

---

## Why Spine Edges Alone Fail

```
B = {v_ab, v_bc, b_priv}
Edges of B:
  s₁ = {v_ab, v_bc}  (spine edge)
  s₂ = {v_ab, b_priv}  (spoke from v_ab)
  s₃ = {v_bc, b_priv}  (spoke from v_bc)

Claim: "If E_B includes spine edge s₁, all bridges hit"

Bridge T_AB_1 = {a, v_ab, b_priv}
  Edges: {a,v_ab}, {a,b_priv}, {v_ab,b_priv}=s₂
  Spine s₁ = {v_ab,v_bc} not in T ✗
  But s₂ ∈ T! So if E_B includes s₂ (not s₁), still covered.

Bridge T_AB_2 = {a, v_ab, z} where z ≠ b_priv
  Edges: {a,v_ab}, {a,z}, {v_ab,z}
  Spine s₁ = {v_ab,v_bc} includes v_ab but z ≠ v_bc, so not in T ✗

Bridge T_AB_3 = {a', v_ab, v_bc} where a' ∈ A
  Edges: {a',v_ab}, {a',v_bc}, {v_ab,v_bc}=s₁
  Spine s₁ ∈ T! ✓
  But this assumes:
    - {a',v_ab} ⊆ T ⟹ a' ∈ A, v_ab ∈ A ∩ B ✓
    - {v_ab,v_bc} ⊆ T ⟹ v_ab, v_bc ∈ T ✓
    - But T = {a', v_ab, v_bc}, so need all 3 to be in G as clique!
    - Only if G contains full PATH_4 structure AND external vertices

ISSUE: Even if spine edge is in E_B, not all bridges contain it!
```

---

## Summary of Mathematical Structure

| Triangle Type | Containment | Edges | Coverage by E_X | Coverage by E_Y | Problem |
|---------------|-------------|-------|-----------------|-----------------|---------|
| **M-element A** | X={a,b,c} | 3 edges | ✓ (trivial) | - | None |
| **External S_A** | Shares 1 edge with A | 1+ edges | ✓ (proven) | - | None |
| **Bridge A-B** | 2 vertices from A, 2 from B | 3 edges | Partial (depends) | Partial (depends) | ✗ No coordination |
| **Non-M triangle** | Doesn't share 2+ with any M | ? | ? | ? | ✗ Undefined |

---

## Conclusion

The adaptive selection proof **breaks down at the bridge coordination stage**. While the ν ≤ 4 constraint successfully limits externals to use ≤ 2 edges per M-element, extending this to global 8-edge coverage requires proving that:

1. **Independent edge choices compose** (they don't automatically)
2. **Bridges are forced into a specific structure** (they're not)
3. **Spine edges suffice for all cases** (they don't)

Without these proofs, the theorem remains incomplete.
