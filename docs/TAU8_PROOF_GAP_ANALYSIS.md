# τ ≤ 8 for PATH_4: Proof Gap Analysis

## Date: January 13, 2026

## Executive Summary

The τ ≤ 8 bound for PATH_4 (Tuza's conjecture ν=4) remains **OPEN**. The primary approach using `tau_S_union_X_le_2` is **BLOCKED** by a counterexample.

## What's Proven (Aristotle-verified)

| Theorem | Source | Lines | Status |
|---------|--------|-------|--------|
| `tau_S_le_2` | slot257 | 200+ | ✅ PROVEN |
| `tau_X_le_2` | slot257 | 100+ | ✅ PROVEN |
| `tau_union_le_sum` | slot257 | 50+ | ✅ PROVEN |
| `path4_triangle_decomposition` | slot387 | exact? | ✅ PROVEN |
| `triangle_helly_vertex` | slot371 | 10+ | ✅ PROVEN |
| τ ≤ 12 for PATH_4 | slot139 | - | ✅ PROVEN |

## What's BLOCKED

### 1. `tau_S_union_X_le_2` is FALSE (Pattern #28)

**Claimed:** τ(S_e ∪ X_{e,f}) ≤ 2 for adjacent e, f in M

**Counterexample:**
- A = {v₁, a₁, a₂} with S_A containing base triangle {a₁, a₂, x}
- X_{A,B} bridges require spokes {v₁, a₁}, {v₁, a₂}
- S_A base triangle requires edge {a₁, a₂}
- **Total: 3 edges, not 2**

### 2. `common_vertex_propagation` is FALSE (slot371)

**Claimed:** If all pairs in a set share vertex with fixed pair, they share common vertex

**Counterexample (Aristotle-found on Fin 4):**
```lean
-- T₁ = {0, 1, 2}, T₂ = {1, 2, 3}
-- externals = {{0, 1, 3}, {0, 2, 3}}
-- T₁ ∩ T₂ = {1, 2}
-- But no common vertex in all externals!
-- {0,1,3} ∩ {0,2,3} = {0, 3}, neither is in T₁ ∩ T₂
```

## The Mathematical Gap

### PATH_4 Structure: A —v₁— B —v₂— C —v₃— D

**Decomposition (PROVEN):**
```
G.cliqueFinset 3 = S_A ∪ S_B ∪ S_C ∪ S_D ∪ X_{A,B} ∪ X_{B,C} ∪ X_{C,D}
```

**Naive Bound:**
- 7 disjoint sets × 2 edges each = 14 edges
- Way too high!

**Hoped-for Bound:**
- S covers: 4 × 2 = 8 edges
- X covers: absorbed by S covers
- **Total: 8 edges**

**The Gap:**
X covers are NOT absorbed by S covers. The S_e cover might use base edges that don't hit bridges.

## Attempted Approaches

### Approach 1: Spoke Cover Strategy
- Pick 2 edges per M-element through shared vertices
- Works for most triangles
- **FAILS** for S_e "base triangles" avoiding shared vertex

### Approach 2: Bridge Absorption (slot387)
- Prove τ(S_e ∪ X_{e,f}) ≤ 2
- **BLOCKED** by counterexample

### Approach 3: Fan Apex Propagation (slot371)
- Prove all X-externals share common vertex
- **BLOCKED** by negation

### Approach 4: Global Construction
- Choose covers globally to maximize overlap
- **Complex optimization problem**
- No clean formalization yet

## Possible Paths Forward

### Option A: Prove Weaker Bound (τ ≤ 10)
- Intermediate between τ ≤ 8 and τ ≤ 12
- Add 2 extra edges for base triangle coverage
- More likely achievable

### Option B: Case Analysis on S_e_structure
- If S_e uses spoke edges, τ(T_e) ≤ 2
- If S_e uses base edge, count how many base triangles exist
- Prove base triangles are globally bounded

### Option C: LP/Counting Approach
- Formulate covering as ILP
- Prove LP relaxation ≤ 8
- Rounding argument?

### Option D: Pivot to Other Cases
- Focus on STAR, CYCLE_4, or other ν=4 cases
- PATH_4 might be the hardest case

## Recommendation

**Focus on Option B** (Case Analysis):
1. Prove: In PATH_4, at most 2 M-elements can have "base structure" S_e
2. Interior elements B, C have 2 shared vertices, making base structure less likely
3. Even if 2 endpoints have base structure, total is 4×2 + 2×1 = 10 edges

This would give τ ≤ 10, with potential to strengthen to τ ≤ 8 with more analysis.

## Files

- `/Users/patrickkavanagh/math/submissions/nu4_final/slot388_direct_8cover_construction.lean`
- `/Users/patrickkavanagh/Downloads/f5cfc9ac-2c32-4c0b-a652-fd5b724c41fe-output.lean` (slot257)
- `/Users/patrickkavanagh/Downloads/abcb9ff3-c5e6-4420-a2db-7e1ebf064582-output.lean` (slot387)
- `/Users/patrickkavanagh/Downloads/c36f268b-ac37-47b4-bbee-9e6b1fb15027-output.lean` (slot371)
