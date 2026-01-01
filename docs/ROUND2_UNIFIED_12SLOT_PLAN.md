# ROUND 2: UNIFIED 12-SLOT SUBMISSION PLAN
## Tuza's Conjecture ν=4 - Final Push
### January 1, 2026

---

## EXECUTIVE SUMMARY

After synthesizing proposals from Codex (15 slots), Gemini (12 slots), and Grok (12 slots), this document presents a refined 12-slot plan that:

1. **Leverages proven work**: Krivelevich bound (slots 59-60), τ ≤ 12 fallback (slot 139)
2. **Avoids known false lemmas**: Patterns 1-7 from failed_approaches
3. **Focuses on completion**: Near-miss files with 1-2 sorries get priority
4. **Respects dependencies**: Foundation → Cases → Synthesis

---

## CURRENT STATE (from database)

| Case | Status | Key Insight |
|------|--------|-------------|
| star_all_4 | PROVEN | 4 spokes |
| three_share_v | PROVEN | 3 spokes + 2 edges |
| scattered | PROVEN | 4×2 = 8 |
| path_4 | PROVEN | Krivelevich: τ ≤ 2ν* ≤ 8 |
| cycle_4 | PROVEN | Krivelevich: τ ≤ 2ν* ≤ 8 |
| matching_2 | PROVEN | Krivelevich: τ ≤ 2ν* ≤ 8 |
| two_two_vw | PROVEN | Krivelevich: τ ≤ 2ν* ≤ 8 |

**However**: The Krivelevich proofs use an axiom. We need to close the axiom gap.

---

## KRIVELEVICH APPROACH STATUS

### What's Proven (slots 59-60, 228)
- `nu_star_le_4`: ν*(G) ≤ 4 for ν=4 graphs
- `M_edge_in_exactly_one`: Each M-edge in exactly one packing element
- `triangle_shares_edge_with_packing`: Maximality
- `M_char_is_fractional`: M-characteristic is fractional packing
- `M_char_weight_eq_4`: Weight = 4

### What's Still Axiom/Sorry
- `krivelevich_bound`: τ(G) ≤ 2ν*(G) (Krivelevich 1995) - not in Mathlib
- `nu_star_le_4`: Still has a `sorry` in slot60_fixed.lean line 215

**Critical Gap**: The Krivelevich approach is sound but not fully machine-verified.
Two options:
1. Prove Krivelevich bound in Lean (hard - requires LP duality)
2. Close τ ≤ 8 via direct construction (avoid LP entirely)

---

## BLOCKED APPROACHES (DO NOT USE)

From failed_approaches table:

| Pattern | Why False | Impact |
|---------|-----------|--------|
| local_cover_le_2 | 4 M-edges may be needed at shared vertex | Blocks greedy spoke |
| external_share_common_vertex | Counterexample: T1∩T2 = {0} only | Blocks 4+4 |
| link_graph_bipartite | M-neighbors form odd cycles | Blocks König lite |
| diagonal_spokes_at_corners | T={v_da, a_priv, v_bc} not covered | Blocks 8-spoke |

---

## UNIFIED 12-SLOT PLAN

### Phase 1: Foundation (Slots 142-145)

| Slot | Name | Target | Deps | Diff | Rationale |
|------|------|--------|------|------|-----------|
| **142** | `M_edge_in_exactly_one_v2` | Prove M-edge uniqueness without axiom | None | 3 | Critical for LP approach |
| **143** | `nu_star_eq_4` | Prove ν*(G) = 4 exactly for ν=4 cycle | 142 | 4 | Removes Krivelevich axiom need |
| **144** | `tau_le_2nu_star_foundation` | Structural lemmas for τ ≤ 2ν* | 143 | 4 | Foundation for bound |
| **145** | `fractional_relaxation_tight` | M-characteristic achieves ν* = 4 | 142, 143 | 5 | Key LP lemma |

### Phase 2: Alternative Bounds (Slots 146-148)

| Slot | Name | Target | Deps | Diff | Rationale |
|------|------|--------|------|------|-----------|
| **146** | `tau_le_12_all_cases` | Generalize τ ≤ 12 to all ν=4 | None | 2 | Safe fallback |
| **147** | `tau_pair_direct` | τ(T_pair) ≤ 6 without false lemmas | None | 4 | Alternative to 4+4 |
| **148** | `bridge_free_bound` | τ ≤ 8 when bridges empty | 147 | 3 | Handles scattered/star |

### Phase 3: Cycle_4 Attack (Slots 149-151)

| Slot | Name | Target | Deps | Diff | Rationale |
|------|------|--------|------|------|-----------|
| **149** | `cycle4_all_middle` | Every triangle hits shared vertex | None | 3 | Key structural lemma |
| **150** | `cycle4_vertex_cover` | 2 edges suffice per shared vertex | 149 | 4 | Sunflower approach |
| **151** | `cycle4_tau_le_8_final` | Complete τ ≤ 8 proof | 149, 150 | 5 | Closes cycle_4 |

### Phase 4: Synthesis (Slots 152-153)

| Slot | Name | Target | Deps | Diff | Rationale |
|------|------|--------|------|------|-----------|
| **152** | `nu4_case_exhaustion` | All 7 cases enumerated | None | 3 | Case completeness |
| **153** | `tuza_nu4_complete` | ∀ G, ν(G)=4 → τ(G) ≤ 8 | All | 5 | Final theorem |

---

## DETAILED SLOT SPECIFICATIONS

### Slot 142: M_edge_in_exactly_one_v2
```lean
theorem M_edge_in_exactly_one_v2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    ∀ e ∈ M_edges G M, ∃! t, t ∈ M ∧ e ∈ t.sym2 := by
  -- Proof: If e in two M-elements, they share edge (contradiction with packing)
  sorry
```
**Strategy**: Use packing intersection bound (≤ 1 vertex shared).

### Slot 143: nu_star_eq_4
```lean
theorem nu_star_eq_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hcard : M.card = 4) :
    nu_star G = 4 := by
  -- Upper: ν* ≤ |M| = 4 (M-characteristic has weight 4)
  -- Lower: ν* ≥ 4 (M witnesses it)
  sorry
```
**Strategy**: Use M_char_is_fractional + M_char_weight_eq_4.

### Slot 144: tau_le_2nu_star_foundation
```lean
-- Structural lemmas needed for τ ≤ 2ν* result
-- This is the Krivelevich approach scaffolding
```
**Strategy**: Build towards the bound without assuming it as axiom.

### Slot 145: fractional_relaxation_tight
```lean
theorem fractional_relaxation_tight (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hcard : M.card = 4) :
    ∃ x : Finset V → ℚ, isFractionalPacking G x ∧ weight x = 4 := by
  -- Construct explicit fractional packing from M
  sorry
```
**Strategy**: M-characteristic function achieves this.

### Slot 146: tau_le_12_all_cases
```lean
theorem tau_le_12_all_cases (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hcard : M.card = 4) :
    triangleCoveringNumber G ≤ 12 := by
  -- Use all 12 M-edges as cover
  sorry
```
**Strategy**: Generalize slot139 result to all cases.

### Slot 147: tau_pair_direct
```lean
theorem tau_pair_direct (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (hshare : (e ∩ f).card = 1) :
    tau (T_pair G e f) ≤ 6 := by
  -- 4 spokes + 2 bases
  sorry
```
**Strategy**: Use proven tau_containing_v_in_pair_le_4 + tau_avoiding_v_in_pair_le_2.

### Slot 148: bridge_free_bound
```lean
theorem bridge_free_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hcard : M.card = 4)
    (hbf : bridges G M = ∅) :
    triangleCoveringNumber G ≤ 8 := by
  -- No bridges means T_pair decomposition suffices
  sorry
```
**Strategy**: When bridges empty, 4×2 local covers work.

### Slot 149: cycle4_all_middle
```lean
theorem cycle4_all_middle (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Cycle4 G M) :
    ∀ t ∈ G.cliqueFinset 3, ∃ v ∈ sharedVertices cfg, v ∈ t := by
  -- Pigeonhole: t uses ≥2 vertices from each M-element it shares edge with
  sorry
```
**Strategy**: Use card_sdiff + pigeonhole from Round 6 analysis.

### Slot 150: cycle4_vertex_cover
```lean
theorem cycle4_vertex_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ sharedVertices cfg) :
    ∃ C : Finset (Sym2 V), C.card ≤ 2 ∧ C ⊆ G.edgeFinset ∧
    ∀ t ∈ trianglesContaining G v, ∃ e ∈ C, e ∈ t.sym2 := by
  -- At each shared vertex, 2 edges suffice (sunflower)
  sorry
```
**Strategy**: The correct sunflower lemma (not the false one).

### Slot 151: cycle4_tau_le_8_final
```lean
theorem cycle4_tau_le_8_final (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hcard : M.card = 4)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- 4 shared vertices × 2 edges each
  sorry
```
**Strategy**: Combine cycle4_all_middle + cycle4_vertex_cover.

### Slot 152: nu4_case_exhaustion
```lean
theorem nu4_case_exhaustion (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hcard : M.card = 4) :
    isStar4 cfg ∨ isThreeShare cfg ∨ isScattered cfg ∨
    isPath4 cfg ∨ isCycle4 cfg ∨ isMatching2 cfg ∨ isTwoTwoVW cfg := by
  -- Sharing graph exhaustion
  sorry
```
**Strategy**: Analyze intersection patterns.

### Slot 153: tuza_nu4_complete
```lean
theorem tuza_nu4_complete (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hcard : M.card = 4) :
    triangleCoveringNumber G ≤ 8 := by
  -- Case split + proven bounds
  sorry
```
**Strategy**: Use case_exhaustion + each case's bound.

---

## DEPENDENCY GRAPH

```
          ┌─────────────────────────────────────────────────┐
          │                                                 │
          ▼                                                 │
       [142]─────┬──────────────────────────────────────────┤
         │       │                                          │
         ▼       ▼                                          │
       [143]   [146]──────────────────────────────┐         │
         │       │                                │         │
         ▼       ▼                                │         │
       [144]   [147]                              │         │
         │       │                                │         │
         ▼       ▼                                │         │
       [145]   [148]                              │         │
         │                                        │         │
         └────────────────────────────────────────┼─────────┤
                                                  │         │
       [149]──────────────────────────────────────┤         │
         │                                        │         │
         ▼                                        │         │
       [150]                                      │         │
         │                                        │         │
         ▼                                        │         │
       [151]──────────────────────────────────────┘         │
                                                            │
       [152]────────────────────────────────────────────────┤
                                                            │
                                                            ▼
                                                         [153]
```

---

## RISK ASSESSMENT

| Slot | Risk Level | Mitigation |
|------|------------|------------|
| 142-145 | MEDIUM | LP machinery complex; fallback to τ ≤ 12 |
| 146-148 | LOW | Uses proven lemmas only |
| 149-151 | HIGH | Sunflower approach may hit false lemma patterns |
| 152-153 | MEDIUM | Depends on prior slots |

---

## ALTERNATIVE STRATEGY IF BLOCKED

If cycle4_vertex_cover (slot 150) fails due to false lemma patterns:

1. **Accept τ ≤ 12** as final bound (still advances knowledge)
2. **Prove τ ≤ 10** via hybrid approach (4 cycle edges + 6 other)
3. **Document blocking pattern** in failed_approaches

---

## SUBMISSION ORDER

**Parallel batch 1** (no dependencies):
- 142, 146, 149, 152

**Parallel batch 2** (after batch 1):
- 143, 147, 150

**Parallel batch 3** (after batch 2):
- 144, 148, 151

**Sequential final**:
- 145, 153

---

## NEAR-MISS FILES TO COMPLETE FIRST

From database query (sorry_count ≤ 2, proven_count > 5):

| ID | File | Sorries | Proven | Status | Priority |
|----|------|---------|--------|--------|----------|
| 145 | cycle4_tau_le_8 | 1 | 20 | **BLOCKED** (contains FALSE lemma) | SKIP |
| 122 | tuza_nu4_slot39 | 1 | 16 | Review needed | HIGH |
| 146 | slot61_path4_corrected | 1 | 15 | Clean | **HIGH** |
| 229 | path4_adjacent_pair | 1 | 15 | Clean | **HIGH** |
| 218 | tau_adjacent_pair_le_4 | 1 | 14 | Review needed | MEDIUM |

**Warning**: ID 145 contains the FALSE lemma `avoiding_covered_by_spokes` - DO NOT attempt to close.

**Recommendation**: Prioritize ID 146 and 229 (both have clean proven lemmas).

---

## CONSENSUS POINTS (All Three AIs Agree)

1. **safe_discard soundness** is needed before reduction strategies
2. **bridge_absorption** is critical for matching_2/two_two_vw
3. **cycle_4 is hardest** (all rate difficulty 5)
4. **τ ≤ 12 is safe fallback** with 95%+ success
5. **Don't repeat failed patterns** - check failed_approaches first

---

## FINAL RECOMMENDATION

1. **Complete near-miss ID 146 or 229** (path4 with clean proofs, 1 sorry, 15 proven)
2. **Submit slots 142, 146, 149 in parallel** (foundation + fallback + structural)
3. **Monitor for false lemma patterns** - stop if hitting Pattern 5-7
4. **Accept τ ≤ 12 if τ ≤ 8 blocked** - still publishable result

---

## IMMEDIATE ACTION ITEMS

### Priority 1: Verify Krivelevich Proof Status
```sql
SELECT notes FROM submissions WHERE id IN (227, 228);
```
If Krivelevich bound is proven without axiom, ALL CASES ARE CLOSED.

### Priority 2: Submit Safe Fallback
Submit slot 146 (τ ≤ 12 generalization) immediately for guaranteed progress.

### Priority 3: Parallel Foundation Attack
Submit slots 142, 149 in parallel:
- 142: M_edge_in_exactly_one_v2 (LP foundation)
- 149: cycle4_all_middle (structural)

### Priority 4: Close Near-Misses
```bash
# Check ID 146 and 229 for completability
sqlite3 submissions/tracking.db "SELECT notes FROM submissions WHERE id IN (146, 229);"
```

---

## SUCCESS CRITERIA

- **Minimum**: τ ≤ 12 proven for all ν=4 (slot 146)
- **Target**: τ ≤ 8 proven for all ν=4 (slot 153)
- **Stretch**: Krivelevich bound proven in Lean (closes axiom gap)

---

## DOCUMENT HISTORY

- **v1.0** (Jan 1, 2026): Initial synthesis from Codex/Gemini/Grok proposals
- Gemini synthesized foundation; Claude refined based on database state
