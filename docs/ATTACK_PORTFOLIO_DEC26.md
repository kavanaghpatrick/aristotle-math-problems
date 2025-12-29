# Cycle_4 Attack Portfolio - December 26, 2025

> ## ⚠️ OBSOLETE (December 26, 2025 Evening)
>
> This document was written BEFORE Codex discovered `local_cover_le_2` is FALSE.
>
> **SEE INSTEAD**: `docs/ATTACK_PLAN_15_SLOTS.md` for the corrected strategy.

## Executive Summary

~~Based on synthesis from Grok-4, Gemini, Codex, and the AI debate, here is the strategic attack portfolio for proving τ ≤ 8 for the cycle_4 case.~~

**INVALIDATED** - the strategy below relies on a FALSE lemma.

## ~~The Winning Strategy~~ OBSOLETE

~~**VERTEX-CENTRIC via `local_cover_le_2`** (NOT S_e decomposition)~~

**`local_cover_le_2` is FALSE** - see `docs/FALSE_LEMMAS.md`

```
Core Insight: The diagonal constraint (A∩C).card = 0 is ESSENTIAL.
It guarantees h_only, enabling local_cover_le_2 at each shared vertex.
```

## Proof Structure (4 × 2 = 8)

```
STEP 1: Establish h_only at each shared vertex
  - v_ab ∈ A ∩ B, but v_ab ∉ C (since A∩C = ∅) and v_ab ∉ D (since B∩D = ∅)
  - Therefore: ∀ Z ∈ M, v_ab ∈ Z → Z = A ∨ Z = B ✓

STEP 2: Apply local_cover_le_2 at each vertex
  - E_ab with |E_ab| ≤ 2 covers supported triangles at v_ab
  - Similarly for E_bc, E_cd, E_da

STEP 3: Prove all triangles are covered
  - cycle4_all_triangles_contain_shared: every t contains some v_ij
  - cycle4_triangle_at_vertex_supported: t is "supported" at its v_ij
  - Therefore: t is covered by some E_v

STEP 4: Union bound
  - E = E_ab ∪ E_bc ∪ E_cd ∪ E_da
  - |E| ≤ 2 + 2 + 2 + 2 = 8 ✓
```

## Attack Portfolio (15 Submissions)

### TIER 1: CRITICAL PATH (Must Prove)

| Slot | Target | Strategy | Priority |
|------|--------|----------|----------|
| 80 | `tau_le_8_cycle4` | Full scaffolding, main theorem as target | 1 |
| 81 | `local_cover_le_2` | Standalone proof of core lemma | 1 |
| 82 | `cycle4_all_triangles_contain_shared` | Maximality argument | 1 |
| 83 | `cycle4_triangle_at_vertex_supported` | Support condition | 1 |
| 84 | `h_only_from_diagonal` | Diagonal → h_only derivation | 1 |

### TIER 2: SUPPORTING LEMMAS

| Slot | Target | Strategy | Priority |
|------|--------|----------|----------|
| 85 | `tau_le_8_cycle4` (inline) | Compact version with all lemmas inline | 2 |
| 86 | `tau_le_8_cycle4_Se` | Alternative S_e approach (backup) | 2 |
| 87 | `cycle4_vertex_only_in_adj` | Explicit h_only per vertex | 2 |
| 88 | `M_edges_at_card_bound` | Edges at v from 2 triangles ≤ 4 | 2 |
| 89 | `cycle4_no_loose_triangles` | All triangles share edge with M | 2 |

### TIER 3: ALTERNATIVE APPROACHES

| Slot | Target | Strategy | Priority |
|------|--------|----------|----------|
| 90 | `tau_le_8_cycle4` (informal) | Let Aristotle find approach | 3 |
| 91 | `union_of_local_covers` | Explicit union construction | 3 |
| 92 | `diagonal_bridges_empty` | No bridges between opposite elements | 3 |
| 93 | `cycle4_support_chain` | chain: all_middle → supported → covered | 3 |
| 94 | `tau_le_8_cycle4` (minimal) | Absolute minimum scaffolding | 3 |

## Key Debate Findings

### FALSE Approaches (Do NOT Use)

1. **S_e decomposition with bridge absorption** - Bridges are NOT absorbed by S_e covers
2. **Base-edge covers** - Miss bridges which require edges at shared vertex
3. **T_pair decomposition** - Gives τ ≤ 12, not 8

### TRUE Insights

1. **Diagonal constraint guarantees h_only** - This is the key enabler
2. **Vertex-centric covers ALL triangles** - Including bridges
3. **Support condition IS satisfied** - Triangles sharing edge with A at v_ab have supporting edge

## Critical Questions Resolved

**Q: Is h_only satisfied in cycle_4?**
A: YES - diagonal constraint ensures v_ab ∉ C and v_ab ∉ D

**Q: Can triangles at v_ab share edge only with C/D (not A/B)?**
A: NO - would require v_ab ∈ C or v_ab ∈ D, contradicting diagonal

**Q: What about triangles containing multiple shared vertices?**
A: Covered by ANY of their shared vertices - no double-counting issue

## Scaffolding Requirements

Each submission MUST include:
1. Self-contained definitions (no imports from proven/)
2. `isTrianglePacking`, `isMaxPacking`, `trianglePackingNumber`
3. `triangleCoveringNumberOn`
4. `isCycle4` with diagonal constraint
5. `M_edges_at` definition
6. Clear comments explaining proof strategy

## Success Criteria

- At least ONE of Tier 1 submissions proves main theorem
- Supporting lemmas proven can be used as scaffolding for retry
- Alternative approaches provide fallback if vertex-centric fails

## Next Steps

1. Validate all files compile (syntax check)
2. Submit Tier 1 in parallel
3. Based on results, iterate with Tier 2/3
4. Incorporate proven lemmas as scaffolding
