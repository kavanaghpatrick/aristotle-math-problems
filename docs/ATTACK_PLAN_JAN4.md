# Tuza ν=4 Attack Plan - January 4, 2026

## Executive Summary

**Goal**: Prove τ ≤ 8 for ν=4 cases (Tuza's conjecture τ ≤ 2ν)

**Current State**:
- τ ≤ 12 PROVEN for all cases (slot139)
- scattered case: τ = 12 is TIGHT (Propeller counterexample)
- 23 false lemma patterns documented

**Key Insight from Debate**: All externals of a single M-element share a common "apex" vertex x.

---

## What's PROVEN (0 sorry)

| Lemma | Slot | Implication |
|-------|------|-------------|
| tau_le_12_cycle4 | slot139 | Baseline bound for all ν=4 |
| two_externals_share_edge | slot182 | Any 2 externals of A share an edge |
| different_edges_share_external_vertex | slot224f | Externals using different A-edges share apex |
| tau_union_le_sum | slot133 | Subadditivity |

---

## The Strategy for τ ≤ 8

### Step 1: Prove all externals share common apex (slot250)
- If T₁, T₂ are externals of A, they share external vertex x (proven via slot182 + slot224f)
- This means ALL externals of A form a "fan" around apex x

### Step 2: Prove τ per M-element ≤ 2 (slot251)
- For A = {a, b, c} with apex x:
  - Edge {a, b} covers A and externals using edge {a, b}
  - Edge {c, x} covers externals using edges {a, c} or {b, c}
- Total: 2 edges per M-element

### Step 3: Combine for τ ≤ 8
- 4 M-elements × 2 edges = 8 total
- This gives τ ≤ 8 for star/cycle/path cases

---

## Submitted to Aristotle

| Slot | UUID | Target | Status |
|------|------|--------|--------|
| slot250 | 4eff0fc9-8d7e-4d72-b438-59c811689a24 | same_edge_share_external_vertex | **LIKELY FALSE** |
| slot251 | blocked | tau_per_M_element_le_2 | DEAD (depends on #250) |
| slot227 | 7857bb62-83c5-41d6-8f1a-0e4a3de97767 | bridge_externals_share_apex | **DISPROVED** |

**CRITICAL**: slot227 found a COUNTEREXAMPLE! Bridge externals do NOT share apex.

### Counterexample (CE_G, 13 vertices):
```
M = {A, B, C, D}
A = {0, 1, 2}
B = {0, 3, 4}  ← shares vertex 0 with A
C = {7, 8, 9}  ← disjoint
D = {10, 11, 12} ← disjoint

T₁ = {0, 1, 5}  ← external of A, vertex 5 outside
T₂ = {0, 3, 6}  ← external of B, vertex 6 outside

5 ≠ 6 → NO shared apex between T₁ and T₂!
```

**Implication**: The 4+4 approach (2 edges × 4 M-elements = 8) does NOT work for cycle/path cases.

### Counterexample for slot250 (same_edge externals):
```
V = 16 vertices
A = {0, 1, 2}
B = {7, 8, 9}, C = {10, 11, 12}, D = {13, 14, 15}  ← all disjoint

T₁ = {0, 1, 5}  ← external of A, uses edge {0,1}, external vertex = 5
T₂ = {0, 1, 6}  ← external of A, uses edge {0,1}, external vertex = 6

T₁ ∩ A = T₂ ∩ A = {0, 1}  (SAME edge!)
But 5 ≠ 6 → NO shared external vertex!

ν = 4 is maintained: any 5 triangles share edge {0,1}
```

**THE ENTIRE "APEX APPROACH" IS DEAD.**

---

## Cases Breakdown

| Case | τ ≤ 8 Feasible? | Notes |
|------|-----------------|-------|
| **scattered** | ❌ NO | Propeller proves τ = 12 tight |
| **star_all_4** | ✅ YES | All share v, fan structure applies |
| **three_share_v** | ✅ YES | 3-star + 1 isolated |
| **cycle_4** | ❌ UNLIKELY | CE_G counterexample is cycle structure! |
| **path_4** | ❌ UNLIKELY | Same issue as cycle - bridge externals independent |
| **matching_2** | ❓ POSSIBLE | Two independent pairs, no bridges |

---

## False Lemma Patterns to AVOID

1. **Pattern 7**: external_share_common_vertex across M-elements (FALSE)
2. **Pattern 22**: bridge_externals_share_apex (FALSE)
3. **Pattern 23**: tau_le_8_scattered (FALSE - Propeller counterexample)
4. **Patterns 1-6**: Various vertex-local covering lemmas (FALSE)
5. **Pattern 20-21**: Link graph + König (FALSE - incomplete coverage)

---

## Next Actions

1. Monitor slot250, slot251, slot227 results
2. If slot250 proves, build slot252 (tau_le_8_star_all_4) using it
3. If slot251 proves, generalize to other cases
4. Focus on star_all_4 first (most constrained structure)

---

## Debate Consensus (Grok, Gemini, Codex)

All agents agreed on:
1. ❌ Scattered case: τ = 12 is TIGHT
2. ❌ K₄-free hypothesis: DEAD
3. ✅ Star case: Most promising for τ ≤ 8
4. ✅ Fan/apex structure: Key insight for covering
5. ⚠️ Need synergy at shared vertices for cycle_4

---

**Document created**: January 4, 2026
**Status**: ACTIVE - Submissions running
