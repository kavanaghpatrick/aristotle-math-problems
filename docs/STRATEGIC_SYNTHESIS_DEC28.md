# TUZA ν=4: STRATEGIC SYNTHESIS - December 28, 2025

## Executive Summary

**Status**: 4 submissions in Aristotle queue (slots 127-130) implementing the **Sunflower-Partitioning** approach for Cycle_4.

**Key Breakthrough**: The "degenerate sunflower" insight - triangles at shared vertex v can be covered by ≤2 NON-M edges, bypassing the FALSE `local_cover_le_2` lemma.

**AI Consensus**: Proof chain is 85-90% complete. Critical gap is proving `support_sunflower` rigorously.

---

## AI Debate Summary (Dec 27-28, 2025)

### Grok-4 Assessment

**Rating**: 85-90% complete

**Strengths Identified**:
- Chain structure is progressively sound (127 → 128 → 129 → 130)
- Distinctness axioms derived cleanly from geometry
- Pigeonhole argument is crisp and correct
- Key insight validation via Codex counterexample

**Gaps Flagged**:
1. Sunflower degeneracy needs case analysis for dispersed structures (multiple x's)
2. Subadditivity needs explicit non-overlapping confirmation
3. Implicit assumptions on graph structure need bridging lemma

**Priority After Results**: Analyze feedback, resubmit fixes for gaps, validate against counterexamples

### Gemini Assessment

**Rating**: High-level logic valid, but critical sorry

**Strengths Identified**:
- Partition strategy is sound: G.K₃ ⊆ ∪T_v
- Local bound τ(T_v) ≤ 2 is correct target
- Aggregation 2+2+2+2=8 holds via subadditivity
- Pigeonhole (slot128) is verified and correct

**CRITICAL GAP IDENTIFIED**:
> The entire validity of the proof now rests on `slot129_support_sunflower.lean`.
> The lemma `support_sunflower` currently ends with `sorry`.
> Proving "at most 2 distinct external vertices appear" is the **hardest part of the problem**.

**Other Cases**: Claims path_4 and two_two_vw may already be proven (needs verification)

### Codex Assessment

**Exploration**: Verified file structure and dependencies
**Recommendation**: Focus on making `support_sunflower` sorry-free

---

## Current Aristotle Submissions (Dec 27, 2025)

| Slot | UUID | Purpose | Grok Review |
|------|------|---------|-------------|
| 127 | `6129b66a-9d45-4719-bd15-7bd2a467bacb` | Cycle4 distinctness axioms | APPROVED |
| 128 | `848d672f-ad1c-4c56-962d-ad4532653d21` | cycle4_element_contains_shared | APPROVED |
| 129 | `0d14bd8f-c5f6-443a-89a1-c028da839413` | support_sunflower | APPROVED |
| 130 | `9e577210-057b-4a86-9f05-cbc426221ef7` | tau_le_8_cycle4 assembly | APPROVED |

**Expected Results**: 6-24 hours (Aristotle processing time)

---

## Proof Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    TAU_LE_8_CYCLE4 (slot130)                    │
│         τ(G.cliqueFinset 3) ≤ 8 via partition + subadditivity   │
└─────────────────────────────────────────────────────────────────┘
                                │
                                │ depends on
                                ▼
┌─────────────────────────────────────────────────────────────────┐
│            TRIANGLES_PARTITION_BY_SHARED_VERTEX                 │
│   G.cliqueFinset 3 ⊆ T_vab ∪ T_vbc ∪ T_vcd ∪ T_vda             │
└─────────────────────────────────────────────────────────────────┘
                                │
                    ┌───────────┴───────────┐
                    │                       │
                    ▼                       ▼
┌───────────────────────────┐   ┌───────────────────────────┐
│ TAU_AT_SHARED_VERTEX_LE_2 │   │ CYCLE4_ALL_TRIANGLES_     │
│   τ(T_v) ≤ 2 for each v   │   │ CONTAIN_SHARED            │
│   (via support_sunflower) │   │   Every t has shared v    │
└───────────────────────────┘   └───────────────────────────┘
            │                               │
            │                               │
            ▼                               ▼
┌───────────────────────────┐   ┌───────────────────────────┐
│   SUPPORT_SUNFLOWER ⚠️    │   │ CYCLE4_ELEMENT_CONTAINS_  │
│   ≤2 edges cover T_v      │   │ SHARED (slot128)          │
│   **CRITICAL SORRY**      │   │   Pigeonhole argument     │
└───────────────────────────┘   └───────────────────────────┘
            │                               │
            │                               │
            ▼                               ▼
┌───────────────────────────┐   ┌───────────────────────────┐
│  EXTERNAL_VERTICES_       │   │ TRIANGLE_SHARES_EDGE_     │
│  BOUNDED ⚠️               │   │ WITH_PACKING (PROVEN)     │
│  "At most 2 x's appear"   │   │   Maximality argument     │
│  **NEEDS RIGOROUS PROOF** │   └───────────────────────────┘
└───────────────────────────┘
```

---

## The Critical Gap: support_sunflower

### What We Claim
Triangles at shared vertex v that share an M-edge can be covered by ≤2 edges.

### The "Degenerate Sunflower" Insight
From Codex counterexample analysis:
```
T1 = {v_ab, v_da, x}
T2 = {v_ab, a_priv, x}
T3 = {v_ab, v_bc, x}
T4 = {v_ab, b_priv, x}

All share edge {v_ab, x}! One edge covers all 4 triangles.
```

### Why This Might Be True
- At vertex v, triangles form a "sunflower" structure
- Core: vertex v
- Petals: {v, m, x} where m is M-neighbor, x is external
- If all petals share the same x, one edge suffices
- If petals split into 2 groups with x₁, x₂, two edges suffice

### What Must Be Proven
1. **External vertices are bounded**: At most 2 distinct x's appear in triangles at v
2. **Why bounded**: Too many x's would allow packing > 4 triangles, violating ν = 4

### Gemini's Warning
> "You are relying on the claim that 'at most 2 distinct external vertices appear'.
> Proving it generally for any max packing is the **hardest part of the problem**."

### Attack Strategies for sorry
1. **Pigeonhole on external vertices**: If 3+ x's exist, show ν > 4 contradiction
2. **Link graph analysis**: External vertices form a subgraph; bound its chromatic number
3. **Case exhaustion**: Enumerate possible external vertex configurations

---

## False Lemmas Registry (DO NOT USE)

| Lemma | Why False | Entry # |
|-------|-----------|---------|
| `local_cover_le_2` | 4 M-edges may be needed (Codex counterexample) | #24 |
| `tau_at_shared_vertex_le_2_general` | Needs cycle4 structure, not general | #26 |
| `avoiding_covered_by_spokes` | Spokes contain v, avoiding excludes v | #17 |
| `tau_pair_le_4` | Correct bound is ≤6 | - |

---

## Case Status Overview

| Case | Status | Bound | Approach |
|------|--------|-------|----------|
| **star_all_4** | ✅ PROVEN | τ ≤ 4 | 4 spokes |
| **three_share_v** | ✅ PROVEN | τ ≤ 5 | 3 spokes + 2 edges |
| **scattered** | ✅ PROVEN | τ = 8 | 4×2 edges |
| **cycle_4** | ⏳ SUBMITTED | τ ≤ 8 | Sunflower-partitioning |
| **path_4** | ⚠️ PARTIAL | τ ≤ 8 | Needs similar approach |
| **two_two_vw** | ⚠️ PARTIAL | τ ≤ 8 | Two independent pairs |
| **matching_2** | ⚠️ PARTIAL | τ ≤ 8 | Same as two_two_vw |

---

## Priority Actions

### Immediate (Today - Dec 28)
1. **Wait for Aristotle results** (6-24 hours expected)
2. **Prepare backup approach** for support_sunflower if it fails

### On Aristotle Results
- **If 0 sorry**: 🎉 Cycle_4 PROVEN! Move to path_4
- **If sorry in 129 (support_sunflower)**: Attack the external_vertices_bounded proof
- **If sorry in 128 (pigeonhole)**: Debug distinctness usage
- **If multiple sorry**: Analyze dependency chain

### After Cycle_4 Complete
1. **path_4**: Adapt sunflower approach
   - Endpoints A, D have 2 private vertices each
   - May need base edge cover for avoiding triangles
   - Middles B, C have All-Middle property

2. **two_two_vw**: Two independent pairs
   - No inter-pair bridges (A∩C = B∩D = ∅)
   - Each pair: τ(S_A) + τ(S_B) ≤ 2 + 2 = 4
   - Total: 4 + 4 = 8

---

## Key Insights from AI Debate

### Grok's Recommendation
> "Make the strategy doc a living document with version control.
> Tag as 'Cycle_4 v5: Sunflower-Partitioning Era' with changelog."

### Gemini's Key Point
> "The geometric constraint 'at most 2 external vertices' is the hardest part."

### Consensus Approach
1. Sunflower-partitioning is the right paradigm
2. Distinctness axioms are correctly derived
3. Pigeonhole argument is sound
4. The sorry in support_sunflower is the critical blocker
5. Path_4 and two_two_vw can follow similar template

---

## Metrics

| Metric | Value |
|--------|-------|
| Cases Proven | 3/7 (43%) |
| Cases Submitted | 1/7 (cycle_4 in queue) |
| Cases Remaining | 3/7 (path_4, two_two, matching) |
| Active Aristotle Jobs | 4 (slots 127-130) |
| Expected Completion | 6-24 hours |

**North Star**: Complete all 7 cases → Tuza ν=4 PROVEN

---

## Files Reference

### Latest Submissions
- `submissions/nu4_final/slot127_distinctness_axioms.lean`
- `submissions/nu4_final/slot128_element_contains_shared.lean`
- `submissions/nu4_final/slot129_support_sunflower.lean`
- `submissions/nu4_final/slot130_tau_le_8_assembly.lean`

### Proven Infrastructure
- `proven/tuza/nu4/slot69_*/output.lean` - tau_union_le_sum
- `proven/tuza/nu4/slot70_*/output.lean` - diagonal_bridges_empty
- `proven/tuza/nu4/slot71_*/output.lean` - S_e_structure

---

*This synthesis supersedes STRATEGIC_MAP_V2.md*
*Last updated: 2025-12-28 06:30 UTC*
*AI Review: Grok-4, Gemini, Codex*
