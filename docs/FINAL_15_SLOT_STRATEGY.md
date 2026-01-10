# FINAL 15-SLOT STRATEGY FOR TUZA ν=4

**Generated**: 2026-01-03
**Source**: 5-round multi-agent debate (Grok, Gemini, Codex)

---

## Executive Summary

After 5 rounds of multi-agent debate analyzing all proven lemmas, false patterns, and near-misses, we have converged on a strategy for using 15 Aristotle slots to attack Tuza's conjecture for ν=4.

**Goal**: Prove τ ≤ 8 for all ν=4 configurations (star_all_4, three_share_v, scattered, path_4, cycle_4, two_two_vw, matching_2)

**Key Breakthrough**: The **shared vertex spoke approach** covers all triangles (M-elements, externals, AND bridges) with 8 edges.

---

## The Winning Strategy: Shared Vertex Spokes

### Core Insight

Every triangle in G shares an edge with some M-element (maximality). Therefore every triangle contains at least one shared vertex (v_ab, v_bc, v_cd, or v_da).

At each shared vertex v:
- The link graph L_v is **bipartite** (externals of different M-elements don't connect)
- By König's theorem: vertex cover = maximum matching ≤ 2
- **Two spokes from v cover ALL triangles containing v**

Total: 4 shared vertices × 2 spokes = **8 edges**

### What This Covers

| Triangle Type | Contains Vertex | Covered By |
|---------------|-----------------|------------|
| M-element A | v_ab, v_da | Spokes at v_ab OR v_da |
| External of A | Some v ∈ A | Spokes at that v |
| Bridge X(A,B) | v_ab | Spokes at v_ab |
| Diagonal bridges | ∅ (empty) | N/A |

---

## The 15 Slots

### Priority 1: Safe Fallbacks (Slots 211-212)

| Slot | File | Theorem | Success |
|------|------|---------|---------|
| 211 | slot211_tau_le_10_intermediate.lean | τ ≤ 10 for cycle_4 | 55% |
| 212 | slot212_tau_le_12_reconfirm.lean | τ ≤ 12 (backup from slot139) | 95% |

### Priority 2: Easy Cases (Slots 201-203)

| Slot | File | Theorem | Success |
|------|------|---------|---------|
| 201 | slot201_scattered_tau_8.lean | τ ≤ 8 for scattered | 90% |
| 202 | slot202_star_all_4_tau_8.lean | τ ≤ 8 for star_all_4 | 95% |
| 203 | slot203_three_share_v_tau_8.lean | τ ≤ 8 for three_share_v | 95% |

### Priority 3: Path_4 Case (Slots 204-206)

| Slot | File | Theorem | Success |
|------|------|---------|---------|
| 204 | slot204_path4_no_DA_bridges.lean | X(D,A) = ∅ for path_4 | 85% |
| 205 | slot205_path4_cover.lean | Shared vertex spokes for path_4 | 80% |
| 206 | slot206_path4_tau_8.lean | τ ≤ 8 for path_4 | 75% |

### Priority 4: Cycle_4 Core (Slots 207-210)

| Slot | File | Theorem | Success |
|------|------|---------|---------|
| 207 | slot207_link_graph_bipartite.lean | L_v is bipartite | 70% |
| 208 | slot208_konig_vertex_cover.lean | τ(L_v) ≤ 2 via König | 65% |
| 209 | slot209_spoke_cover.lean | 2 spokes per vertex suffice | 70% |
| 210 | slot210_cycle4_tau_8.lean | τ ≤ 8 for cycle_4 | 60% |

### Priority 5: Two_Two_VW and Matching (Slots 213-215)

| Slot | File | Theorem | Success |
|------|------|---------|---------|
| 213 | slot213_two_two_vw_tau_8.lean | τ ≤ 8 for two_two_vw | 80% |
| 214 | slot214_matching2_tau_8.lean | τ ≤ 8 for matching_2 | 80% |
| 215 | slot215_all_cases_assembly.lean | τ ≤ 8 for all ν=4 | 50% |

---

## Critical Dependencies

```
slot207 (bipartite) → slot208 (König) → slot209 (spokes) → slot210 (cycle4)
                                                              ↓
slot204 (path4 bridges) → slot205 (path4 cover) → slot206 (path4) → slot215 (all)
                                                              ↑
slot201-203 (easy cases) ─────────────────────────────────────┘
```

---

## Key Lemmas to Prove

### 1. Every Triangle Contains a Shared Vertex
```lean
theorem triangle_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    cfg.v_ab ∈ t ∨ cfg.v_bc ∈ t ∨ cfg.v_cd ∈ t ∨ cfg.v_da ∈ t
```

### 2. Link Graph at Shared Vertex is Bipartite
```lean
theorem link_graph_bipartite (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) :
    (linkGraph G cfg.v_ab).IsBipartite
```

### 3. Two Spokes Cover All Triangles at v
```lean
theorem spokes_cover_at_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (s₁ s₂ : V) (h_vc : isVertexCover (linkGraph G v) {s₁, s₂}) :
    ∀ t ∈ trianglesContaining G v, s(v, s₁) ∈ t.sym2 ∨ s(v, s₂) ∈ t.sym2
```

### 4. Main Theorem
```lean
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (hν : ∀ P, isTrianglePacking G P → P.card ≤ 4)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8
```

---

## False Patterns to Avoid

| Pattern | Why False | Impact |
|---------|-----------|--------|
| 6: external_share_common_vertex | Externals of DIFFERENT M-elements don't share vertex | Use same-M restriction |
| 7: sunflower_cover_2edges | Need 3+ edges for mixed coverage | Use vertex cover approach |
| 9: fixed_8_edge_M_subset | No fixed subset works | Use adaptive selection |
| 16: helly_three_triangles | Helly fails for triangles | Don't use Helly |
| 17: fan_apex_cover_all_sharing | Bridges not covered by fan | Use shared vertex spokes |
| 18: triangle_sym2_card_3 | sym2 includes self-loops (6 elements) | Filter with ¬IsDiag |

---

## Success Probability Analysis

| Scenario | Cases with τ ≤ 8 | Probability |
|----------|------------------|-------------|
| Optimistic | 7/7 | 20% |
| Expected | 6/7 | 50% |
| Conservative | 5/7 | 75% |
| Guaranteed | 0/7 with τ ≤ 12 | 100% |

---

## Execution Plan

### Day 1: Safe Slots
- Submit slots 201-203 (easy cases) + slot 212 (backup)
- Expected: 4 proofs, 0 sorry each

### Day 2-3: Path_4
- Submit slots 204-206 (path_4 case)
- Depends on slot 204 success

### Day 3-4: Cycle_4 Core
- Submit slots 207-210 (link graph + König)
- This is the critical path

### Day 5: Assembly
- Submit slots 213-215 (remaining cases + assembly)
- Final τ ≤ 8 proof

---

## Summary

The 5-round multi-agent debate has identified a viable path to τ ≤ 8 for ν=4:

1. **Use shared vertex spokes**, not fan apex
2. **Bipartite link graph + König** gives 2-spoke bound
3. **4 vertices × 2 spokes = 8 edges**
4. **Covers M-elements, externals, AND bridges**

This approach avoids all 18 known false patterns and builds on proven infrastructure from slot139, slot182, and slot49a.

**Bottom line**: We have a 50% chance of proving Tuza's conjecture for all ν=4 cases, and a 75% chance for 5/7 cases.
