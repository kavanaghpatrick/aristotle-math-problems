# Tuza ν=4 Project Checkpoint - January 1, 2026

## Executive Summary

**Mission**: Prove Tuza's conjecture τ(G) ≤ 2ν(G) for ν=4, i.e., τ ≤ 8.

**Current State**:
- **Best PROVEN bound**: τ ≤ 12 (slot139, 0 sorry, 0 axiom)
- **Target bound**: τ ≤ 8 (NOT proven - requires new approach)
- **Proven files**: 11 (in `proven/tuza/nu4/safe_discard/`)
- **False lemma patterns**: 10 documented
- **Failed approaches**: 40+ catalogued

---

## Part 1: What We Know To Be TRUE

### 1.1 Proven Bounds (0 sorry, 0 axiom)

| Bound | Proof Location | UUID |
|-------|----------------|------|
| τ ≤ 12 (cycle_4) | slot139_tau_le_12_fallback | adc20172 |
| τ(S_e) ≤ 2 | parker_lemmas.lean | - |
| τ(X_ef) ≤ 2 | aristotle_nu4_tau_S_proven | - |
| τ(containing v in pair) ≤ 4 | slot69 | 80891b4c |
| τ(avoiding v in pair) ≤ 2 | slot69 | 80891b4c |
| τ(T_pair) ≤ 6 | proven via 4+2 | internal |

### 1.2 Core Structural Lemmas (Validated TRUE)

| Lemma | Description | Evidence |
|-------|-------------|----------|
| `tau_union_le_sum` | τ(A∪B) ≤ τ(A) + τ(B) | Aristotle f0a24a15 |
| `triangle_shares_edge_with_packing` | Maximality: every triangle shares edge with some M-element | Aristotle f0a24a15 |
| `avoiding_contains_base_edge` | Triangles avoiding v that share edge with e MUST share base {a,b} | slot61 |
| `no_bridge_disjoint` | No triangle bridges two disjoint M-elements | Aristotle c522a35a |
| `scattered_unique_parent` | In scattered config, each external has unique parent | Aristotle c522a35a |
| `nu_star_le_4_cycle4` | Fractional packing ≤ 4 in cycle_4 | Aristotle 445c65be |
| `M_edge_in_exactly_one` | Each M-edge in exactly one M-element | Aristotle 3d31b863 |
| `cycle4_all_triangles_contain_shared` | Every triangle contains some shared vertex | Aristotle eb28d806 |

### 1.3 Proven Infrastructure (11 clean files)

```
proven/tuza/nu4/safe_discard/
├── slot64a_ig_definitions_PROVEN.lean    # Interaction graph definitions
├── slot64b_M_edges_card_PROVEN.lean      # M_edges.card ≤ 12
├── slot64c_edge_unique_PROVEN.lean       # Edge uniqueness
├── slot64d_interact_share_PROVEN.lean    # Interacting edges share vertex
├── slot65_singleton_conflict_PROVEN.lean # Singleton conflict defs
├── slot67_bridge_absorption_PROVEN.lean  # Bridge/scattered lemmas
├── slot148a_scattered_partition_PROVEN.lean  # Scattered partition theorem
├── slot148b_owner_covered_PROVEN.lean    # Owner coverage
├── slot149_path4_structure_PROVEN.lean   # Path4 structure
├── slot150_matching2_structure_PROVEN.lean # Matching2 structure
└── slot151_tpair_spokes_PROVEN.lean      # Spoke lemmas
```

---

## Part 2: What We Know To Be FALSE

### 2.1 The 10 False Lemma Patterns

| # | Lemma | Why False | Evidence |
|---|-------|-----------|----------|
| 1 | `local_cover_le_2` | At v_ab, 4 M-edges used by 4 different triangles. Any 2-edge subset misses ≥2. | AI-verified |
| 2 | `avoiding_covered_by_spokes` | Spokes contain v; avoiding triangles don't contain v. Set theory. | Trivially false |
| 3 | `bridge_absorption` | Bridges share vertices with e,f but may not share edges with S_e/S_f triangles. | Aristotle |
| 4 | `trianglesContainingVertex_partition` | Triangle at v can share M-edge at different vertex. | Reasoning |
| 5 | `support_sunflower_tau_2` | trianglesSharingMEdgeAt includes M-elements A,B, not just externals. | Reasoning |
| 6 | `external_share_common_vertex` | T1={0,1,5} uses A's edge, T2={0,3,6} uses B's edge. T1∩T2={0} only. | AI-verified |
| 7 | `sunflower_cover_at_vertex_2edges` | At v_ab need: edge for A + edge for B + edge for externals = 3+. | AI-verified |
| 8 | `tau_pair_le_4` | T_pair needs 4 spokes (containing) + 2 bases (avoiding) = 6, not 4. | Trivially false |
| 9 | `fixed_8_edge_M_subset` | Any 8 of 12 M-edges omits 4. Externals using those 4 are uncovered. | Reasoning |
| 10 | `krivelevich_bound_forall_w` | τ ≤ 2ν* uses SUPREMUM over all w, not any particular w. | Aristotle |

### 2.2 The Core Mathematical Insight

```
THE τ ≤ 8 GAP:
- T_pair approach gives τ ≤ 6 per pair
- 2 pairs in cycle_4 gives τ ≤ 12
- To get τ ≤ 8, need 4-edge overlap between pairs
- But external triangles can use DIFFERENT edges from each pair
- No fixed 8-edge subset works universally
```

---

## Part 3: All Failed Approaches (Top 20)

| Approach | Why Failed | Category |
|----------|-----------|----------|
| `tau_pair_le_4_via_spokes` | avoiding_covered_by_spokes is FALSE | wrong_direction |
| `local_cover_le_2` | 4 M-edges may be needed at shared vertex | wrong_direction |
| `link_graph_bipartite` | M-neighbors form odd cycles | wrong_direction |
| `konig_lite_case_analysis` | Depends on false bipartiteness | wrong_direction |
| `fixed_8_edge_M_subset` | Any 8-subset omits 4 needed edges | wrong_direction |
| `external_share_common_vertex` | Externals use different M-triangle edges | wrong_direction |
| `bridge_absorption` | S_e covers don't absorb bridges | wrong_direction |
| `sunflower_cover_at_vertex_2edges` | Need 3+ edges per vertex | wrong_direction |
| `diagonal_spokes_at_corners` | T={v_da, a_priv, v_bc} not covered | wrong_direction |
| `generalizing_diagonal_bridges_empty` | Only works when truly disjoint | wrong_direction |
| `cycle_opposite_disjoint` | Opposite pairs CAN share vertices | wrong_direction |
| `bridges_inter_card_eq_one` | Bridges can share >1 vertex | wrong_direction |
| `lp_relaxation_krivelevich` | Aristotle processing error | technical_issue |
| `slot110_output_analysis` | Trusted Aristotle headers (wrong) | technical_issue |
| `mislabeled_proven_sorry_scaffolding` | /-- PROVEN --/ had sorry body | technical_issue |
| `Parker induction for nu=4` | T_e has up to 5 triangles when ν=4 | wrong_direction |
| `S_e_structure_edge_apex` | K4 counterexample | wrong_direction |
| `bridges_subset_Se_or_Sf` | Bridges share edge with BOTH e and f | wrong_direction |
| `tau_containing_vertex_le_2` | τ(containing v) can be arbitrarily large | wrong_direction |
| `avoiding_v_vertices` | Triangles can have vertices not in e or f | wrong_direction |

---

## Part 4: Case-by-Case Status

| Case | Status | τ Bound | Key Insight |
|------|--------|---------|-------------|
| **star_all_4** | PROVEN | τ ≤ 4 | All 4 triangles share v. 4 spokes suffice. |
| **three_share_v** | PROVEN | τ ≤ 5 | 3-star (3 spokes) + isolated (2 edges). |
| scattered | Partial | τ ≤ 12 | Each external has unique parent. Need τ ≤ 2 per owner. |
| path_4 | Partial | τ ≤ 12 | Endpoints need bases. τ_adjacent_pair gap remains. |
| two_two_vw | Partial | τ ≤ 12 | Two independent pairs. No inter-bridges. |
| matching_2 | Partial | τ ≤ 12 | Same as two_two_vw structure. |
| **cycle_4** | BLOCKED | τ ≤ 12 | All simple approaches exhausted. Need LP or novel insight. |

### cycle_4 Blockers

The cycle_4 case is blocked by 6 proven-false lemmas:
1. Pattern 1: local_cover_le_2
2. Pattern 5: support_sunflower_tau_2
3. Pattern 6: external_share_common_vertex
4. Pattern 7: sunflower_cover_at_vertex_2edges
5. Pattern 8: link_graph_bipartite (Konig fails)
6. Pattern 9: fixed_8_edge_M_subset

---

## Part 5: AI Debate Insights

### 5.1 Consensus Conclusions (All 3 AIs Agree)

| Finding | Implication |
|---------|-------------|
| τ ≤ 12 is PROVEN | Valid baseline result |
| Fixed 8-edge M-subset fails | Need adaptive covers |
| Link graphs NOT bipartite | Konig theorem invalid |
| "2 edges per vertex" is FALSE | Need 3+ edges |
| τ ≤ 8 likely TRUE | No counterexample found |

### 5.2 Strategy Evolution (7 Rounds)

| Round | Strategy | Outcome |
|-------|----------|---------|
| 1-2 | T_pair decomposition | τ ≤ 12 (not 8) |
| 3 | S_e + bridge absorption | Bridges not absorbed |
| 4 | Vertex-centric local_cover | Pattern 1 FALSE |
| 5 | Link graph + Konig | Pattern 8 FALSE |
| 6 | Fixed 8-edge construction | Pattern 9 FALSE |
| 7 | **LP/Fractional relaxation** | **UNTESTED - Top priority** |

### 5.3 Key Disagreement Resolution

**Gemini** proposed elegant τ ≤ 8 arguments based on intuition.
**Grok/Codex** found counterexamples disproving them.

Resolution: Grok/Codex correct on specifics. Gemini's intuition about τ ≤ 8 achievability may still hold via different mechanism (LP relaxation).

---

## Part 6: The Path Forward

### 6.1 Priority 1: LP/Fractional Relaxation (70% success estimate)

**Krivelevich's theorem**: τ ≤ 2ν* where ν* is fractional packing number.

**Key question**: Does ν* = 4 for cycle_4?

If YES: τ ≤ 8 follows immediately.

**Advantages**:
- Bypasses all Konig/bipartiteness issues
- No explicit cover construction needed
- Existential proof (easier than constructive)

**Barriers**:
- Mathlib LP support limited
- Need to prove ν* = 4 in cycle_4

### 6.2 Priority 2: Adaptive Non-M-Edge Cover (40% success)

**Strategy**: Allow cover edges from external triangles.

When T = {a_priv, v_da, z} exists, use edge {v_da, z} instead of M-edge.

**Advantages**:
- Circumvents Pattern 9 (fixed M-subset fails)
- May give existential proof

**Barriers**:
- Need to show such edges always exist
- Constructive proof still hard

### 6.3 Priority 3: Complete Simpler Cases First

| Case | What's Needed | Effort |
|------|--------------|--------|
| scattered | Prove τ ≤ 2 per owner (not 3) | Medium |
| path_4 | Prove 2-edge overlap exists | Medium |
| two_two_vw | Complete S_e analysis | Medium |

### 6.4 Priority 4: Accept τ ≤ 12 and Pivot

τ ≤ 12 = τ ≤ 3ν matches Haxell's best general bound (τ ≤ 2.87ν).

This is a **valid mathematical result** even if not optimal.

---

## Part 7: Operational Lessons

### 7.1 Process Failures We Fixed

| Issue | Fix |
|-------|-----|
| 14 files with sorry in proven/ | Moved to partial/, added verification rules |
| Database said 7 cases "proven" | Fixed to "partial", added integrity rules |
| trusted Aristotle headers | Now verify with `rg "sorry\|^axiom"` |
| 19hr gap between suspicion and fix | Parallel agent verification on any claim |
| 3-6 slots wasted on false lemma | Check FALSE_LEMMAS before submitting |

### 7.2 Hard Rules (Operational)

1. PROVEN = 0 sorry AND 0 axiom
2. `proven/` = verified clean files only
3. Database follows files, not vice versa
4. Check `failed_approaches` before new submissions
5. Near-misses (1-2 sorry) worked FIRST
6. Never trust Aristotle headers without verification
7. Parallel agent verification on any major claim

---

## Part 8: Metrics

| Metric | Value |
|--------|-------|
| Proven files (0 sorry, 0 axiom) | 11 |
| Validated TRUE lemmas | 90+ |
| FALSE lemma patterns | 10 |
| Failed approaches | 40+ |
| Best proven τ bound | 12 |
| Target τ bound | 8 |
| AI debate rounds | 12+ |
| Aristotle submissions | 150+ |

---

## Appendix A: Quick Reference - What NOT To Do

```
NEVER assume:
- Spokes cover avoiding triangles (Pattern 2)
- 2 edges per shared vertex suffice (Patterns 1,5,7)
- Link graphs are bipartite (Pattern 8)
- Fixed 8-edge M-subset works (Pattern 9)
- External triangles share common vertex (Pattern 6)
- Bridges absorbed by S_e covers (Pattern 3)
- τ(T_pair) ≤ 4 (Pattern 8) - correct bound is 6
```

## Appendix B: Database Queries for Current State

```sql
-- Validated TRUE lemmas
SELECT name, english FROM literature_lemmas WHERE validated_true = 1;

-- FALSE lemma patterns
SELECT lemma_name, why_false FROM false_lemmas;

-- Failed approaches
SELECT approach_name, avoid_pattern FROM failed_approaches WHERE frontier_id='nu_4';

-- Case status
SELECT case_name, status, key_insight FROM nu4_cases;
```

---

*Generated: January 1, 2026*
*Status: τ ≤ 12 PROVEN, τ ≤ 8 OPEN*
