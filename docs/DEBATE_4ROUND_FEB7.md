# 4-Round Multi-Model Debate Summary
## Tuza ν=4 Proof Strategy
## February 7, 2026

---

## Participants

| Model | Focus Area | Rounds |
|-------|------------|--------|
| **Grok (xAI)** | Code correctness, Lean tactics | 4/4 |
| **Gemini (Google)** | Literature, proof strategy | 3/4 (R4 rate-limited) |
| **Codex (OpenAI)** | Architecture, formalization | 4/4 |

---

## Round-by-Round Summary

### Round 1: Initial Positions

**GROK:**
- Prioritize two_two_vw (adapts scattered strategy)
- Don't submit slot58 yet (6 sorries)
- Create slot60_exhaustiveness.lean (enumerate 11 patterns)
- Defer cycle_4 (1/10 success chance)

**GEMINI:**
- Intersection graph approach NOT standard in literature
- 11 patterns mathematically exhaustive, geometric realization fails
- For cycle_4: use fractional relaxation (ν* = 4)
- Pivot to LP or finite verification

**CODEX:**
- Found `subgraphFromTriangles` in slot30_disconnected.lean
- Key lemma: `triangleCoveringNumberOn ≤ triangleCoveringNumber(subgraph)`
- Lift Fin 12 via induced subgraph + isomorphism invariance

### Round 2: Cross-Responses

**GROK:**
- Fractional ν* formalization: sketched `def fractional_nu` with LP constraints
- "Non-standard" doesn't matter for correctness - only publishability
- Final assembly: case split with `obtain ⟨pat, h_pat⟩ := exists_exhaustive_pattern`
- MVP: Accept τ ≤ 12 for cycle_4, publish as "towards Tuza ν=4"

**GEMINI:**
- Enumerate 11 patterns (not 64) - use symmetry breaking
- LP is implementable: dual minimizes Σy_e s.t. Σ_{e∈T} y_e ≥ 1
- Agrees two_two_vw adapts scattered, BUT "5-packing lemma" is hidden blocker
- REJECTS partial result - cycle_4 is "most likely hiding spot for counterexample"

**CODEX:**
- Found slot462_fin12_main_theorem.lean with `all_patterns_tau_le_8`
- Found slot463_transfer_principle.lean for embedding into Fin 12
- cycle_4 still has 10+ sorries in slot145

### Round 3: Synthesis

**GROK ACTION PLAN:**
1. slot30_disconnected.lean (subgraph lifts) - Day 1-2
2. slot58.lean (5-packing lemma) - Day 2-3
3. slot60.lean (11 patterns) - Day 3-4
4. tuza_nu4_main.lean (assembly) - Day 4-5
- ACCEPTS τ ≤ 12 for cycle_4 as MVP

**GEMINI PIVOT:**
- Changed from "fight for τ ≤ 8" to "Green Build" strategy
- Priority: Housekeeping → slot58 → LP for cycle_4
- ACCEPTS τ ≤ 12 to clear the build

**CODEX FINDINGS:**
- slot462 has `all_patterns_tau_le_8` with native_decide
- slot463 transfer principle for Fin 12 embedding
- cycle_4 in slot145 has 10+ sorries

### Round 4: Final Consensus

**UNANIMOUS DECISION: Accept τ ≤ 12 for cycle_4**

| Model | Vote | Reasoning |
|-------|------|-----------|
| Grok | ✅ τ ≤ 12 | Pragmatic MVP, iterate later |
| Gemini | ✅ τ ≤ 12 | "Validity > Optimality" |
| Codex | ✅ τ ≤ 12 | Ship now, research τ ≤ 8 separately |

---

## Final Action Plan

### Immediate (This Week)

| Day | File | Action | Owner |
|-----|------|--------|-------|
| Mon | Math/Slot145.lean | Relax to τ ≤ 12 | Priority 1 |
| Tue | slot58_two_two_vw_general.lean | Fix 5-packing sorries | Priority 2 |
| Wed | slot60_exhaustiveness.lean | 11 pattern enumeration | Priority 3 |
| Thu | tuza_nu4_main.lean | Assembly theorem | Priority 4 |
| Fri | All | Testing + documentation | Cleanup |

### Minimal Victory Theorem

```lean
theorem tuza_nu4_mvp {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnu : trianglePackingNumber G = 4) :
    triangleCoveringNumber G ≤ 12
```

### Deferred to v2

- τ ≤ 8 for cycle_4 via fractional relaxation
- LP formalization (ν* = 4 → τ ≤ 8)
- Optimal cover construction

---

## Key Technical Insights

### From Grok
- Use `fin_cases` for pattern enumeration
- `add_le_add` for τ bounds
- Priority: correctness over publishability

### From Gemini
- Intersection graph approach hides geometric complexity
- 5-packing lemma is the hidden blocker
- LP dual: minimize Σy_e s.t. Σ_{e∈T} y_e ≥ 1

### From Codex
- `subgraphFromTriangles` enables lifting
- slot462 has working `native_decide` proofs
- Transfer principle: any 4-packing embeds in Fin 12

---

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| sym2 self-loop bug | Medium | High | Use explicit edge sets |
| 5-packing lemma blocked | High | Medium | Parallel LP track |
| Definition drift | Low | Medium | Audit before assembly |
| Mathlib version | Low | High | Pin versions |

---

## Files Referenced

| File | Purpose | Status |
|------|---------|--------|
| slot56_scattered_general_aristotle.lean | General scattered theorem | ✅ PROVEN |
| slot57_propeller_nu_verify_aristotle.lean | Propeller counterexample invalid | ✅ PROVEN |
| slot58_two_two_vw_general.lean | Two_two_vw general | 6 sorries |
| slot139_tau_le_12_fallback.lean | cycle_4 τ ≤ 12 | Ready |
| slot145_direct_cycle4_aristotle.lean | cycle_4 τ ≤ 8 attempt | 10+ sorries |
| slot462_fin12_main_theorem.lean | All patterns τ ≤ 8 | native_decide |
| slot463_transfer_principle.lean | Fin 12 embedding | Structure only |

---

## Debate Statistics

| Metric | Value |
|--------|-------|
| Total rounds | 4 |
| Models consulted | 3 |
| API calls | 12 |
| Consensus reached | ✅ Yes |
| Key decision | Accept τ ≤ 12 for MVP |

*Debate conducted February 7, 2026*
*Models: Grok-4 (xAI), Gemini-3-Pro (Google), GPT-5.2-Codex (OpenAI)*
