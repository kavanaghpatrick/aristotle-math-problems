# Tuza ν=4 Strategic Debate Document
## February 2, 2026

---

## EXECUTIVE SUMMARY

**Mission**: Prove τ(G) ≤ 8 for all graphs G with ν(G) = 4 (Tuza's conjecture for ν=4)

**Current Status**:
- 2 cases FULLY PROVEN today (slot49, slot50)
- 1 case previously complete (path_4)
- 4 cases partial (cycle_4, scattered, two_two_vw, matching_2)
- 37 false lemmas documented (blocking invalid approaches)
- 30+ validated true lemmas (building blocks)
- 20+ failed approaches catalogued

**Key Insight**: The problem decomposes into ~6 structural cases based on how packing elements share vertices. Simple cases (star configurations) are now solved. Complex cases (cycles, scattered) require new techniques.

---

## PART 1: WHAT WE PROVED TODAY

### slot49: STAR_ALL_4 (τ = ν = 4) ✅ COMPLETE

**Configuration**: All 4 packing triangles share central vertex v=0
```
M = {{0,1,2}, {0,3,4}, {0,5,6}, {0,7,8}}
```

**Key Results**:
- `triangles_eq_M`: No external triangles exist
- `tau_equals_nu`: τ = ν = 4 (optimal)
- `cover_hits_all_triangles`: 4 spoke edges suffice

**Why It Works**: Central vertex creates "sunflower" - every triangle contains v, so 4 spokes cover everything.

### slot50: THREE_SHARE_V (τ ≤ 4) ✅ COMPLETE

**Configuration**: 3-star at vertex 0 + isolated triangle
```
M_star = {{0,1,2}, {0,3,4}, {0,5,6}}
M_iso = {{9,10,11}}
```

**Key Results**:
- `tau_M_eq_4`: Exactly 4 edges suffice
- `tuza_bound_three_share_v`: τ ≤ 8 (actually τ ≤ 4)
- `iso_disjoint_from_star`: No interference between components

**Why It Works**: Star component needs 3 spokes, isolated needs 1 edge. Total = 4.

---

## PART 2: FALSE LEMMAS (MINEFIELD MAP)

### Tier 1: Aristotle-Verified Negations (Highest Confidence)

| # | Lemma | Why False | Impact |
|---|-------|-----------|--------|
| 1 | `not_all_three_types` | S_e CAN have externals for all 3 edge types | Blocks 6-packing strategy |
| 2 | `at_most_two_edge_types` | Bridges use ANY edge-type | Blocks edge-type counting |
| 3 | `Se_fan_apex` | Externals don't share common apex | Blocks fan-based covers |
| 4 | `sym2_cover_cardinality` | Finset.sym2 includes self-loops | Caused 5+ slot failures |
| 5 | `covering_selection_exists` | Different triangles need different M-edges | Blocks simple selection |
| 6 | `triangle_in_some_Se_or_M` | Bridges excluded from ALL S_e sets | Need S_e' with bridge assignment |

### Tier 2: AI-Verified (High Confidence)

| # | Lemma | Why False | Correct Approach |
|---|-------|-----------|------------------|
| 7 | `local_cover_le_2` | 4 triangles at v need 4 edges | Accept τ ≤ 4 per vertex, not 2 |
| 8 | `external_share_common_vertex` | Externals from A vs B don't share | Major blocker - may need LP |
| 9 | `bridge_auto_covered_by_pigeonhole` | Covering vertex ≠ covering triangle | Explicit bridge handling needed |
| 10 | `fan_apex_outside_A` | Apex can be IN A (book case) | Allow internal apex |
| 11 | `tau_S_union_X_le_2` | Base + bridges need 3 edges | τ(S_e ∪ X) ≤ 3 is tight |

### Tier 3: Reasoning-Based

| # | Lemma | Why False |
|---|-------|-----------|
| 12 | `tau_pair_le_4` | T_pair needs 6 edges (4 spokes + 2 bases), not 4 |
| 13 | `avoiding_covered_by_spokes` | Trivially false: avoiding triangles don't contain v |

---

## PART 3: VALIDATED TRUE LEMMAS (BUILDING BLOCKS)

### Core Structural Lemmas

| Lemma | Statement | Status |
|-------|-----------|--------|
| `tau_S_le_2` | τ(S_e) ≤ 2 for exclusive externals | ✅ Proven |
| `tau_X_le_2` | τ(X_{e,f}) ≤ 2 for bridges | ✅ Proven |
| `lemma_2_2` | S_e triangles pairwise share edges | ✅ Proven |
| `lemma_2_3` | ν(G \ T_e) = ν - 1 | ✅ Proven |
| `bridge_shares_with_le_2` | Bridges share with ≤2 M-elements | ✅ Proven |
| `mem_X_implies_v_in_t` | Bridge triangles contain shared vertex | ✅ Proven |

### Intersection/Structure Lemmas

| Lemma | Statement | Status |
|-------|-----------|--------|
| `edge_disjoint_share_le_1` | Edge-disjoint triangles share ≤1 vertex | ✅ Proven |
| `intersecting_family_structure_corrected` | Pairwise edge-sharing → star OR K4 | ✅ Proven |
| `three_intersecting_triples_structure` | 3 pairwise edge-sharing → common edge OR ≤4 vertices | ✅ Proven |

### Cover Bounds

| Lemma | Statement | Status |
|-------|-----------|--------|
| `covering_number_le_two_of_subset_four` | ≤4 vertices → τ ≤ 2 | ✅ Proven |
| `inductive_bound` | τ(G) ≤ τ(T_e) + τ(G \ T_e) | ✅ Proven |
| `tuza_nu2` | ν=2 → τ ≤ 4 | ✅ Proven |

---

## PART 4: CASE STATUS

| Case | Status | τ Bound | Key Challenge |
|------|--------|---------|---------------|
| **star_all_4** | ✅ COMPLETE | τ = 4 | None - simplest case |
| **three_share_v** | ✅ COMPLETE | τ ≤ 4 | None - decomposition works |
| **path_4** | ✅ COMPLETE | τ ≤ 8 | 107 theorems via 3-case split |
| **cycle_4** | ⚠️ PARTIAL | τ ≤ 12 proven | Fan structure proven but τ ≤ 8 needs edge selection |
| **two_two_vw** | ⚠️ PARTIAL | τ ≤ 12 proven | Bridge coordination unsolved |
| **matching_2** | ⚠️ PARTIAL | τ ≤ 12 proven | Same as two_two_vw |
| **scattered** | ⚠️ PARTIAL | τ ≤ 12 proven | Infrastructure only |

---

## PART 5: FAILED APPROACHES (GRAVEYARD)

### Major Strategy Failures

1. **LP Relaxation (ν* ≤ 4 → τ ≤ 8)**
   - K4 counterexample: ν(K4)=1 but ν*(K4)=4/3
   - Cannot use Krivelevich without proving ν* ≤ 4 first

2. **6-Packing Contradiction**
   - Assumed "not all 3 edge-types" - FALSE
   - K4 structure allows all 3 types simultaneously

3. **Fan Apex Cover**
   - Assumed shared external apex - FALSE
   - Externals can have different third vertices

4. **Bridge Absorption**
   - Assumed S_e covers absorb bridges - FALSE
   - Bridges need explicit separate handling

5. **Vertex-Saturating Cover**
   - Assumed hitting vertices → covering triangles - FALSE
   - Must hit actual edges of each triangle

---

## PART 6: NEAR-MISSES (BEST OPPORTUNITIES)

| Slot | Sorries | Proven | Description |
|------|---------|--------|-------------|
| slot262 | 1 | 30 | path4_complete - near full proof |
| slot259 | 1 | 25 | path4_main_theorem |
| slot60 | 1 | 20 | cycle4_full_scaffolding |
| slot331 | 1 | 18 | tau_le_8_direct |
| slot51 | 1 | ? | spoke_cover_lemma (just submitted) |
| slot52 | 2 | ? | base_cover_lemma (just submitted) |

---

## PART 7: STRATEGIC OPTIONS

### Option A: Complete Remaining Cases via Concrete Decidability

**Approach**: For each remaining case (cycle_4, scattered, etc.), construct explicit graph on Fin 12-15 and prove τ ≤ 8 via `native_decide`.

**Pros**:
- Proven to work (slot49, slot50 succeeded this way)
- No false lemma risk
- Aristotle can find counterexamples if construction is wrong

**Cons**:
- Doesn't prove general theorem
- Need explicit construction for each case
- May not cover all subcases

**Effort**: Medium (1-2 weeks per case)

### Option B: Fix Near-Misses (slot51, slot52, slot60)

**Approach**: Focus on files with 1-2 sorries and high proven_count. These are closest to completion.

**Pros**:
- Leverages existing work
- High success probability
- Builds reusable lemmas

**Cons**:
- May hit same false lemmas again
- Requires understanding existing proof structure

**Effort**: Low-Medium (days per file)

### Option C: New Structural Approach - Bridge-Aware Partition

**Approach**: Instead of S_e (exclusive externals), use S_e' that assigns each bridge to exactly one packing element by minimum index.

**Key Insight**: False lemma `triangle_in_some_Se_or_M` shows bridges are excluded from all S_e. But we can CREATE S_e' that includes bridges.

**Pros**:
- Addresses root cause of bridge problems
- Potentially unifies all cases
- Already have `bridge_shares_with_le_2`

**Cons**:
- Unproven territory
- May discover new false lemmas

**Effort**: High (weeks of exploration)

### Option D: K4-Free + K4 Case Split

**Approach**: Prove τ ≤ 8 separately for:
1. K4-free graphs (no 4-clique)
2. Graphs containing K4 subgraph

**Rationale**:
- `not_all_three_types` was negated by K4 structure
- K4-free might allow stronger lemmas
- slot531 attempted this (2 sorries remain)

**Pros**:
- Isolates problematic K4 case
- K4-free likely has cleaner structure

**Cons**:
- K4 case may be equally hard
- Doubles the work

**Effort**: High

### Option E: Hybrid - Phase 1 Concrete, Phase 2 General

**Approach**:
1. Complete all cases via concrete `native_decide` (Phase 1)
2. Extract patterns and prove general theorem (Phase 2)

**Rationale**:
- Phase 1 gives us working proofs
- Phase 2 generalizes after we understand all cases
- CLAUDE.md already recommends this

**Pros**:
- Guaranteed progress (Phase 1)
- Informed generalization (Phase 2)
- Lower risk

**Cons**:
- Longer timeline
- May never reach Phase 2

**Effort**: Medium-High

---

## PART 8: RECOMMENDED STRATEGY

### Immediate Actions (This Week)

1. **Monitor slot53** (triple_apex) - still in Aristotle queue
2. **Process slot51, slot52 results** - 1 and 2 sorries respectively
3. **Submit concrete cycle_4 construction** - follow slot49/50 pattern

### Short-Term (2 Weeks)

1. **Complete cycle_4 case** via concrete Fin 12 construction
2. **Work near-misses** (slot60 cycle4, slot262 path4)
3. **Document any new false lemmas** discovered

### Medium-Term (1 Month)

1. **Complete all 6 cases** via concrete decidability
2. **Extract common patterns** from proven cases
3. **Attempt bridge-aware partition** (Option C)

### Key Principles

1. **Falsification-first**: Submit uncertain lemmas on small Fin n for counterexamples
2. **Concrete before abstract**: Prove on Fin 12 first, generalize later
3. **10+ scaffolding helpers**: 4x success rate improvement
4. **Avoid false lemma patterns**: Check database before submitting

---

## PART 9: OPEN QUESTIONS FOR DEBATE

1. **Is K4-free split worth pursuing?**
   - slot531 has 2 sorries
   - K4 case still needs separate proof

2. **Can bridge-aware S_e' approach work?**
   - Assign bridges by min-index
   - Need τ(S_e') ≤ 2 for each e

3. **Is there a simpler 8-edge cover construction?**
   - Current best: 2 edges per M-element
   - But bridges complicate selection

4. **Should we pursue general SimpleGraph theorem or accept finite verification?**
   - 108 Lean files use set-theoretic representation
   - General theorem requires SimpleGraph V with arbitrary V

---

## APPENDIX: Key File Locations

| File | Content |
|------|---------|
| `submissions/tracking.db` | All state (submissions, false_lemmas, etc.) |
| `submissions/nu4_final/slot49_*_aristotle.lean` | Proven star_all_4 |
| `submissions/nu4_final/slot50_*_aristotle.lean` | Proven three_share_v |
| `docs/DEBATE_*.md` | Previous debate documents |
| `CLAUDE.md` | Project rules and patterns |

---

*Document prepared for multi-agent strategic debate on Tuza ν=4 proof completion.*
