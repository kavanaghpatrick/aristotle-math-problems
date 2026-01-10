# Strategy Synthesis: Post-Crisis Recovery Plan
## After 13 False Lemmas - Jan 1, 2026

---

## CRITICAL SITUATION SUMMARY

**Both main LP approaches for τ ≤ 8 have been DISPROVEN by Aristotle:**

| Pattern # | Lemma | Status | Impact |
|-----------|-------|--------|--------|
| 12 | `externals_sum_le_totalSlack` | FALSE (Aristotle G6) | Exchange argument fails |
| 13 | `covering_selection_exists` | FALSE (Aristotle G_ex) | CoveringSelection fails |

**Current REAL proven bound:** τ ≤ 12 (slot113, slot139)
**Claimed τ ≤ 8:** Uses FALSE lemmas or AXIOMS (Krivelevich bound unproven)

---

## MULTI-AGENT CONSENSUS (Grok + Gemini + Codex)

### Areas of Agreement

1. **Previous τ ≤ 8 "proofs" are INVALID** - They used false lemmas:
   - `avoiding_covered_by_spokes` (Pattern #2)
   - `external_share_common_vertex` (Pattern #6)
   - `tau_pair_le_4` (Pattern #8)

2. **τ ≤ 12 is the current REAL ceiling** - Proven via all 12 M-edges covering

3. **Two viable paths remain:**
   - **Path A:** LP/Krivelevich (prove ν* = 4 ⟹ τ ≤ 2ν* = 8)
   - **Path B:** Direct case-by-case construction

4. **Cycle_4 is fundamentally different** - All 4+4 decomposition approaches fail

### Agent-Specific Insights

| Agent | Key Insight | Recommendation |
|-------|-------------|----------------|
| **Grok** | Scattered: 2 edges per M-element | Start with scattered_tau_le_8 |
| **Gemini** | Is τ ≤ 8 even TRUE? Core question | Focus on ν* = 4 proof |
| **Codex** | Krivelevich is AXIOM not proof | Build tau_tpair_disjoint_pair_le_4 first |

---

## RECOMMENDED STRATEGY: Hybrid Approach

### Phase 1: Secure Easy Cases (SCATTERED, MATCHING_2)

These cases have NO external_share_common_vertex dependency:

**Theorem 1: scattered_tau_le_8**
```lean
theorem scattered_tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_scattered : ∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B) :
    triangleCoveringNumber G ≤ 8
```

**Why it works:**
- 4 disjoint triangles, each needs ≤2 edges to cover owned triangles
- Total: 4 × 2 = 8

**Theorem 2: matching2_tau_le_8**
```lean
theorem matching2_tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Matching2Config G) :
    triangleCoveringNumber G ≤ 8
```

**Why it works:**
- Two isolated pairs (A,B) and (C,D)
- Each pair needs ≤4 edges (spokes from shared vertex)
- No overlap by matching2_independent_pairs (slot150)
- Total: 4 + 4 = 8

### Phase 2: PATH_4 via Endpoint Analysis

**Theorem 3: path4_tau_le_8**
```lean
theorem path4_tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4Config G) :
    triangleCoveringNumber G ≤ 8
```

**Decomposition:**
- Endpoint A: 2 edges (base, private triangles only)
- Endpoint D: 2 edges (base, private triangles only)
- Middle B-C: 4 edges (spokes from v_bc)
- Total: 2 + 4 + 2 = 8

**Key insight:** path4_no_AC_bridge and path4_no_BD_bridge isolate endpoints

### Phase 3: CYCLE_4 - New Approach Required

**All previous approaches are INVALID:**
- 4+4 via T_pair: FALSE (avoiding triangles not empty)
- 4+4 via externals sharing: FALSE (Pattern #6)
- Exchange argument: FALSE (Pattern #12)
- CoveringSelection: FALSE (Pattern #13)

**New approaches to explore:**

1. **Vertex cover duality**:
   - 8 shared vertices in cycle_4
   - Each triangle contains ≥2 shared vertices
   - König-style bound possible?

2. **Degree counting**:
   - Total degree in link graphs bounded
   - Average covering cost ≤ 2 per vertex

3. **Fractional relaxation**:
   - Prove ν*(cycle_4) = 4 directly
   - Use LP duality for τ ≤ 8

4. **External triangle counting**:
   - At most 4 external triangles total? (ν constraint)
   - 4 M-triangles + 4 externals = 8 edges?

---

## SUBMISSION PRIORITY ORDER

| Priority | Target | File | Likelihood |
|----------|--------|------|------------|
| 1 | `matching2_tau_le_8` | slot175 | HIGH (uses slot150) |
| 2 | `scattered_tau_le_8` | slot176 | HIGH (uses slot148a,b) |
| 3 | `path4_tau_le_8` | slot177 | MEDIUM (uses slot149) |
| 4 | `nu_star_eq_4` | slot178 | MEDIUM (LP approach) |
| 5 | `cycle4_tau_le_8_new` | slot179 | LOW (needs new strategy) |

---

## SUCCESS CRITERIA

For each submission:
1. ✅ Zero sorries expected (include FULL proven scaffolding)
2. ✅ No false lemma patterns (check against docs/FALSE_LEMMAS.md)
3. ✅ Scaffolding count ≥7 (correlates with 40.7% success)
4. ✅ Focused scope (1 main theorem, supporting lemmas only)

---

## MATHEMATICAL QUESTIONS TO RESOLVE

1. **Is τ ≤ 8 even TRUE for all ν=4 graphs?**
   - No counterexample known, but not proven either
   - Gemini suggests constructing potential counterexamples

2. **Can we prove ν* = 4 for ν = 4?**
   - Gap between fractional and integer packing can be large in general
   - But for ν = 4, specific structure may force equality

3. **What is the correct bound for T_pair?**
   - τ_pair_le_4: FALSE in general
   - τ_pair_le_6: PROVEN (4 spokes + 2 base edges)
   - τ_pair_le_4 with isolation condition: OPEN (Codex's suggestion)

---

## NEXT ACTIONS

1. ☐ Create slot175_matching2_tau_le_8.lean using slot150 scaffolding
2. ☐ Create slot176_scattered_tau_le_8.lean using slot148 scaffolding
3. ☐ Submit in parallel to maximize throughput
4. ☐ If both succeed: proceed to path4 and cycle4
5. ☐ If either fails: analyze counterexample, add to false_lemmas

---

*Generated from Grok + Gemini + Codex multi-agent debate on 2026-01-01*
