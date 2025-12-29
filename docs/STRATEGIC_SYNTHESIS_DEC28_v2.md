# TUZA ν=4: STRATEGIC SYNTHESIS - December 28, 2025 (v2)

## Executive Summary

**Status**: 4 new submissions (slots 131-134) with **corrected approach**. Slot 133 (subadditivity) is **COMPLETE**.

**Critical Discovery**: `support_sunflower` with τ(T_v) ≤ 2 is **FALSE**. The correct approach separates M-coverage from external-coverage.

---

## Current Aristotle Submissions

| Slot | UUID | Purpose | Status |
|------|------|---------|--------|
| **131** | `ae553796-8ef2-4a6e-bf85-4c6aa7ba16f3` | external_share_common_vertex | ⏳ QUEUED |
| **132** | `87d3e442-c180-4164-b9b9-e8cf8ab34b1f` | cover_construction (8 edges) | ⏳ QUEUED |
| **133** | `a144d232-d801-457a-961a-2eb52daf35de` | subadditivity τ(S₁∪S₂) ≤ τ(S₁)+τ(S₂) | ✅ **COMPLETE** |
| **134** | `339e6a3b-6c5c-4cde-83de-500619778cbc` | tau_le_8_final assembly | ⏳ QUEUED |

---

## CORRECTED Proof Architecture (Dec 28, 2025)

```
┌─────────────────────────────────────────────────────────────────┐
│                    TAU_LE_8_CYCLE4 (slot134)                    │
│         τ(G) ≤ 8 via explicit 8-edge cover construction         │
└─────────────────────────────────────────────────────────────────┘
                                │
                    ┌───────────┴───────────┐
                    │                       │
                    ▼                       ▼
┌───────────────────────────┐   ┌───────────────────────────┐
│   M_COVER_EDGES (4)       │   │ EXTERNAL_COVER_EDGES (4)  │
│   {v_ab,v_da} covers A    │   │  {v_ab, x_ab} covers      │
│   {v_ab,v_bc} covers B    │   │   external at v_ab        │
│   {v_bc,v_cd} covers C    │   │  {v_bc, x_bc} covers      │
│   {v_cd,v_da} covers D    │   │   external at v_bc        │
└───────────────────────────┘   │  etc.                     │
                                └───────────────────────────┘
                                            │
                                            ▼
                    ┌───────────────────────────────────────┐
                    │ EXTERNAL_SHARE_COMMON_VERTEX (slot131)│
                    │   All external triangles at v share   │
                    │   a common external vertex x          │
                    │   **KEY NEW LEMMA**                   │
                    └───────────────────────────────────────┘
                                            │
                    ┌───────────┬───────────┴───────────┐
                    │           │                       │
                    ▼           ▼                       ▼
┌───────────────────────────┐   ┌───────────────────────────┐
│ CYCLE4_ALL_TRIANGLES_     │   │  TAU_UNION_LE_SUM         │
│ CONTAIN_SHARED (slot128)  │   │  (slot133) ✅ PROVEN      │
│   Every t has shared v    │   │  Subadditivity            │
│   ✅ PROVEN               │   │                           │
└───────────────────────────┘   └───────────────────────────┘
```

---

## False Lemmas Registry (UPDATED Dec 28)

| Lemma | Why False | Added |
|-------|-----------|-------|
| `local_cover_le_2` | 4 M-edges may be needed | Dec 26 |
| `tau_at_shared_vertex_le_2_general` | Needs cycle4 structure | Dec 26 |
| `avoiding_covered_by_spokes` | Spokes contain v, avoiding excludes v | Dec 25 |
| **`support_sunflower (τ ≤ 2)`** | **T_v includes M-elements A,B; need 3 edges** | **Dec 28** |

### NEW: Why support_sunflower (τ ≤ 2) is FALSE

At `v = v_ab`, `trianglesSharingMEdgeAt G M v` contains:
- A = {v_ab, v_da, a_priv} ← M-element
- B = {v_ab, v_bc, b_priv} ← M-element
- T1, T2, T3, T4 ← external triangles sharing {v_ab, x}

To cover all of {A, B, T1, T2, T3, T4}:
- `{v_ab, x}` covers T1-T4 ✓
- `{v_ab, x}` does NOT cover A (x ∉ A) ✗
- `{v_ab, x}` does NOT cover B (x ∉ B) ✗
- **Need 3 edges minimum**, not 2!

---

## The Corrected Approach

### Old (FALSE)
```
τ(T_v) ≤ 2 per shared vertex
→ 4 vertices × 2 edges = 8 total
```

### New (CORRECT)
```
1. Cover M with 4 edges (one from each element):
   - {v_ab, v_da} ∈ A
   - {v_ab, v_bc} ∈ B
   - {v_bc, v_cd} ∈ C
   - {v_cd, v_da} ∈ D

2. Cover external triangles at each v with 1 edge:
   - {v_ab, x_ab} covers all externals at v_ab
   - {v_bc, x_bc} covers all externals at v_bc
   - {v_cd, x_cd} covers all externals at v_cd
   - {v_da, x_da} covers all externals at v_da

Total: 4 + 4 = 8 edges ✓
```

### Why externals share common x (slot131)

If external triangles T1, T2 at v had DIFFERENT external vertices x1 ≠ x2:
- T1 = {v, m1, x1}, T2 = {v, m2, x2}
- If edge-disjoint: {T1, T2, C, D} might form packing of size 5
- Contradicts ν = 4

Therefore all external triangles at v share a common external vertex x.

---

## Proven Theorems Inventory

### ✅ COMPLETE (0 sorry)

| Slot | Theorem | Statement |
|------|---------|-----------|
| 128 | `cycle4_all_triangles_contain_shared` | Every triangle contains v_ab ∨ v_bc ∨ v_cd ∨ v_da |
| 128 | `cycle4_element_contains_shared` | Every M-element contains 2 shared vertices |
| 128 | `triangle_shares_edge_with_packing` | Maximality: every t shares edge with M |
| **133** | **`tau_union_le_sum`** | **τ(S₁ ∪ S₂) ≤ τ(S₁) + τ(S₂)** |
| 133 | `cover_union` | Union of covers is cover of union |
| 133 | `triangleCoveringOn_empty` | τ(∅) = 0 |
| 133 | `triangleCoveringOn_singleton` | τ({t}) ≤ 1 |

### ⏳ PENDING (in Aristotle queue)

| Slot | Theorem | Purpose |
|------|---------|---------|
| 131 | `external_share_common_vertex` | Key lemma: externals share x |
| 132 | `full_cover_covers_all` | 8-edge cover construction |
| 134 | `tau_le_8_cycle4` | Final assembly |

---

## Dependency Graph (Updated)

```
                    ┌─────────────────┐
                    │   tau_le_8_     │
                    │   cycle4        │
                    │   (slot134)     │
                    └────────┬────────┘
                             │
         ┌───────────────────┼───────────────────┐
         │                   │                   │
         ▼                   ▼                   ▼
┌─────────────────┐ ┌─────────────────┐ ┌─────────────────┐
│ full_cover_     │ │ tau_union_      │ │ cycle4_all_     │
│ covers_all      │ │ le_sum          │ │ triangles_      │
│ (slot132)       │ │ (slot133)       │ │ contain_shared  │
└────────┬────────┘ │ ✅ PROVEN       │ │ (slot128)       │
         │          └─────────────────┘ │ ✅ PROVEN       │
         │                              └─────────────────┘
         ▼
┌─────────────────┐
│ external_share_ │
│ common_vertex   │
│ (slot131)       │
│ **KEY LEMMA**   │
└─────────────────┘
```

---

## Case Status Overview

| Case | Status | Bound | Notes |
|------|--------|-------|-------|
| **star_all_4** | ✅ PROVEN | τ ≤ 4 | 4 spokes |
| **three_share_v** | ✅ PROVEN | τ ≤ 5 | 3 spokes + 2 edges |
| **scattered** | ✅ PROVEN | τ = 8 | 4×2 edges |
| **cycle_4** | ⏳ SUBMITTED | τ ≤ 8 | Corrected approach (slots 131-134) |
| **path_4** | ⚠️ PARTIAL | τ ≤ 8 | Needs similar approach |
| **two_two_vw** | ⚠️ PARTIAL | τ ≤ 8 | Two independent pairs |
| **matching_2** | ⚠️ PARTIAL | τ ≤ 8 | Same as two_two_vw |

---

## Priority Actions

### Immediate
1. **Wait for slots 131, 132, 134 results** (slot 133 already COMPLETE)
2. **If 131 succeeds**: The key lemma is proven, rest should follow
3. **If 131 fails**: Analyze the gap in external_share_common_vertex proof

### On Results
- **If all 0 sorry**: 🎉 Cycle_4 PROVEN! Move to path_4
- **If sorry in 131**: The bipartite link graph argument needs refinement
- **If sorry in 132**: Cover construction details need work
- **If sorry in 134**: Assembly gaps, but pieces are there

### After Cycle_4
1. **path_4**: Endpoints have 2 private vertices each (base edges needed)
2. **two_two_vw**: Two independent pairs, simpler structure

---

## Files Reference

### Latest Submissions (Dec 28, 2025)
- `submissions/nu4_final/slot131_external_share_vertex.lean` → `.txt`
- `submissions/nu4_final/slot132_cover_construction.lean` → `.txt`
- `submissions/nu4_final/slot133_subadditivity.lean` → `.txt` ✅
- `submissions/nu4_final/slot134_tau_le_8_final.lean` → `.txt`

### Proven Output
- `proven/tuza/nu4/slot133_subadditivity_proven.lean` ✅

### False Lemmas Documentation
- `docs/FALSE_LEMMAS.md` (updated Dec 28 with support_sunflower)

---

## Metrics

| Metric | Value |
|--------|-------|
| Cases Proven | 3/7 (43%) |
| Cases Submitted | 1/7 (cycle_4) |
| Cases Remaining | 3/7 |
| Active Aristotle Jobs | 3 (slots 131, 132, 134) |
| Completed Jobs | 1 (slot 133 ✅) |
| Key Lemmas Proven | 7+ |
| False Lemmas Documented | 4 |

**North Star**: Complete all 7 cases → Tuza ν=4 PROVEN

---

*This synthesis supersedes STRATEGIC_SYNTHESIS_DEC28.md*
*Last updated: 2025-12-28 23:30 UTC*
