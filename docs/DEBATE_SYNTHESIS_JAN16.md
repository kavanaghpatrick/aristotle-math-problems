# Multi-Agent Debate Synthesis: τ ≤ 8 for PATH_4

**Date**: January 16, 2026
**Agents**: Claude (moderator), Grok-style, Gemini-style, Codex-style
**Rounds**: 3

## Executive Summary

**CONSENSUS**: τ ≤ 8 is **ACHIEVABLE** for PATH_4 with an **ADAPTIVE** cover construction.

The key insight resolving Pattern 30's gap: **bridges are automatically covered by any 2-edge selection from a triangle** because 2 edges cover all 3 vertices (pigeonhole), and bridges contain the shared vertex (slot441).

---

## The Problem

Pattern 30 identified that "2 edges per middle element" fails because:
- The 6-packing constraint only applies to S_e externals
- Bridges (triangles with |T ∩ A| ≥ 2) are EXCLUDED from 6-packing
- Dropping an edge type for B may leave A-B bridges uncovered

## The Solution

### Key Insight 1: Bridge Containment (slot441)
Any A-B bridge contains v₁ (the shared vertex of A and B).

### Key Insight 2: Pigeonhole on 2-edge Selection
Any 2 edges from triangle B = {v₁, v₂, b} cover all 3 vertices.
- At least one edge contains v₁ (hits A-B bridges)
- At least one edge contains v₂ (hits B-C bridges)

### Key Insight 3: 6-Packing Guarantees Existence
slot412 proves at most 2 of 3 S_e external types exist, so 2 edges suffice for externals.

---

## Final 8-Edge Cover Construction

```
PATH_4: A —v₁— B —v₂— C —v₃— D
```

### Cover Selection (Adaptive)

For each M-element X, select 2 edges based on which external types exist:

| Element | Role | Edge Selection | Covers |
|---------|------|----------------|--------|
| A = {v₁, a₁, a₂} | Endpoint | 2 edges covering populated types | A, S_e(A), A-B bridges |
| B = {v₁, v₂, b} | Middle | 2 edges (any work!) | B, S_e(B), bridges auto-covered |
| C = {v₂, v₃, c} | Middle | 2 edges (any work!) | C, S_e(C), bridges auto-covered |
| D = {v₃, d₁, d₂} | Endpoint | 2 edges covering populated types | D, S_e(D), C-D bridges |

**Total: 8 edges**

### Why Middle Elements Are Automatic

For middle element B = {v₁, v₂, b}:
- ANY 2-edge selection covers v₁ and v₂ (pigeonhole)
- A-B bridges contain v₁ → automatically hit
- B-C bridges contain v₂ → automatically hit
- S_e(B) externals: at most 2 types by 6-packing → 2 edges suffice

The Round 2 disagreement was immaterial:
- {s(v₁,v₂), s(v₂,b)} ✓ works
- {s(v₁,v₂), s(v₁,b)} ✓ also works
- Both cover shared vertices v₁ and v₂

---

## Proven Components to Use

| Slot | Lemma | Status | Use |
|------|-------|--------|-----|
| 412 | `not_all_three_edge_types` | PROVEN | ≤2 S_e types exist |
| 422 | `exists_two_edges_cover_Se` | PROVEN | 2 edges cover S_e externals |
| 434 | `endpoint_two_edges_suffice` | PROVEN | Endpoint coverage |
| 441 | `bridge_contains_shared` | PROVEN | Bridges contain shared vertex |

---

## Remaining Work

### Lemma Needed: `all_triangles_hit_by_two_edges`

```lean
theorem all_triangles_hit_by_two_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hX : X ∈ G.cliqueFinset 3)
    (e₁ e₂ : Sym2 V) (he₁ : e₁ ∈ X.sym2 ∩ G.edgeFinset)
    (he₂ : e₂ ∈ X.sym2 ∩ G.edgeFinset) (hne : e₁ ≠ e₂)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTX : 2 ≤ (T ∩ X).card) :
    e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2 := by
  -- T shares edge with X
  -- Two edges from X cover all 3 vertices of X
  -- Therefore T shares at least one vertex pair (edge) with our selection
  sorry
```

### Main Theorem: `tau_le_8_path4`

```lean
theorem tau_le_8_path4
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, 2 ≤ (T ∩ E).card)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hPath : is_path4_structure M) :
    ∃ Cover : Finset (Sym2 V),
      Cover.card ≤ 8 ∧
      Cover ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ Cover, e ∈ T.sym2 := by
  -- Apply exists_two_edges_cover_Se to each M-element
  -- Union of 4 × 2-edge covers gives 8-edge cover
  -- Bridge coverage automatic by pigeonhole + slot441
  sorry
```

---

## Recommended Next Submission

**File**: `slot442_tau_le_8_path4.lean`

**Strategy**:
1. Import slot412, 422, 434, 441 as axioms/hypotheses
2. Define `is_path4_structure`
3. Prove `all_triangles_hit_by_two_edges` (pure combinatorics)
4. Assemble main theorem

**Expected Aristotle Tier**: 2 (medium - uses proven scaffolding)

---

## Agent Consensus Summary

| Agent | Position | Final Verdict |
|-------|----------|---------------|
| **Grok** | Middle edges need both shared vertices | τ ≤ 8 achievable |
| **Gemini** | Bridge absorption by neighbor | τ ≤ 8 achievable |
| **Codex** | Spine covers both directions | τ ≤ 8 achievable |

**All agents agree**: The 8-edge cover works because ANY 2-edge selection from a triangle automatically covers all three vertices, ensuring bridges (which contain shared vertices) are hit.

---

## Additional Gemini Confirmation (Post-Debate)

Gemini independently confirmed the **Component-wise Adaptive Assembly** strategy:

### Why "Universal" Fixed Selection Fails
- Endpoints with "Type 3" externals (on base edge {a₂,a₃}) aren't hit by "2 spokes"
- Middle elements with externals on BOTH legs aren't hit by "spine + 1 leg"

### The Rigorous Strategy
```
Cover = C_A ∪ C_B ∪ C_C ∪ C_D

where C_i = exists_two_edges_cover_Se(G, M, element_i)  -- from slot422
```

This adaptive approach:
1. **Handles all configurations**: slot422 adapts to which external types exist
2. **Guarantees cardinality**: |Cover| ≤ 2+2+2+2 = 8
3. **Covers bridges automatically**: Spine edges contain shared vertices

### Middle Element Special Case
For middle element B, the **spine edge s(v₁,v₂)** is incident to BOTH shared vertices:
- Covers A-B bridges (at v₁)
- Covers B-C bridges (at v₂)
- One edge handles both directions!
