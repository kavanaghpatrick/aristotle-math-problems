# AI Debate: LP Relaxation PRD Review

**Date:** January 1, 2026
**Participants:** Grok-4, Gemini, Codex
**Subject:** PRD_LP_RELAXATION_TAU8.md

---

## Executive Summary

| Agent | Verdict | Key Finding |
|-------|---------|-------------|
| **Grok-4** | CONDITIONAL APPROVE | ν* ≤ 4 proof is incomplete |
| **Gemini** | INCOMPLETE | Only proves ν* ≥ 4, need dual |
| **Codex** | FEASIBLE | Use ℝ, fix Pattern 10 bug |

**Consensus:** The approach is **mathematically sound but incomplete**. The PRD proves ν* ≥ 4 (lower bound) but NOT ν* ≤ 4 (upper bound).

---

## Critical Gap Identified

### What the PRD Claims

> "Set w(A) = w(B) = w(C) = w(D) = 1, externals = 0. This achieves ν* = 4."

### What This Actually Proves

- **ν* ≥ 4**: There EXISTS a fractional packing with weight 4 ✓
- **ν* ≤ 4**: NO packing exceeds weight 4 ✗ (NOT PROVEN)

### Why This Matters

If ν* > 4 for some cycle_4 instance, Krivelevich gives τ ≤ 2ν* > 8.

---

## The Missing Proof: ν* ≤ 4

### Grok's Edge-Counting Argument

Sum edge constraints over all 12 M-edges:
1. Σ_{e ∈ M-edges} Σ{w(t) : e ∈ t} ≤ 12
2. Each M-triangle has 3 M-edges, contributing 3×w(M-element)
3. Therefore: 3(w(A)+w(B)+w(C)+w(D)) + external_contributions ≤ 12
4. Since external_contributions ≥ 0: w(A)+w(B)+w(C)+w(D) ≤ 4

### Key Insight

Externals share M-edges with M-elements. If w(M-element) = 1, externals on those edges get 0. To give externals positive weight, must reduce M-element weights, but net gain is 0 (trade-off).

### Formal Statement Needed

```lean
theorem fractional_packing_weight_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (h_cycle4 : isCycle4Config G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    (G.cliqueFinset 3).sum w ≤ 4 := by
  -- Edge-counting argument
  sorry
```

---

## Pattern 10 Bug Alert

### From Codex Review

The PRD's early drafts had Krivelevich stated as:
```lean
-- WRONG (Pattern 10):
axiom krivelevich_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    (τ G : ℝ) ≤ 2 * packingWeight G w
```

**This is FALSE!** Counterexample: K₃ with w=0 gives τ=1 > 0.

### Correct Formulation

```lean
-- CORRECT:
axiom krivelevich_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    (triangleCoveringNumber G : ℝ) ≤ 2 * fractionalPackingNumber G
```

Where `fractionalPackingNumber G = sSup {Σ w(t) | w valid packing}`.

---

## Lean Formalization Recommendations

### From Codex

| Aspect | Recommendation |
|--------|----------------|
| Number type | Use ℝ (not ℚ) |
| Definition style | Predicate-based |
| sSup handling | Prove nonemptiness + boundedness |
| Scaffolding | Import from slot64c, slot55 |

### Available Proven Lemmas

- `M_edge_in_exactly_one` (slot64c) - PROVEN
- `M_char_is_fractional` (slot55) - PROVEN
- `M_char_weight_eq_card` (slot55) - PROVEN

---

## Revised Submission Strategy

### Phase 1: Slot 153 (ν* ≥ 4)
**File:** `slot153_nu_star_ge_4.lean`
- Construct M_char weight function
- Prove it's a valid fractional packing
- Show it achieves weight 4
- **Expected:** 0 sorry (uses proven scaffolding)

### Phase 2: Slot 153b (ν* ≤ 4)
**File:** `slot153b_nu_star_le_4.lean`
- Edge-counting argument
- Sum over 12 M-edges
- Show no packing exceeds 4
- **Expected:** 1-2 sorry

### Phase 3: Slot 154 (τ ≤ 8)
**File:** `slot154_tau_le_8_krivelevich.lean`
- Krivelevich as axiom
- Combine ν* = 4 from Phases 1+2
- Derive τ ≤ 8
- **Expected:** 0 sorry (1 axiom)

---

## Risk Mitigation

### Risk 1: ν* > 4 for Some Cycle_4

**Mitigation (Gemini):** Verify ν* = 4 on concrete K₆ example before formalizing.

### Risk 2: Edge-Counting Proof Gaps

**Mitigation (Grok):** The argument is sound but needs careful Lean encoding. Split into small lemmas.

### Risk 3: sSup Complexity

**Mitigation (Codex):** Use predicate-based approach:
```lean
∀ w, IsFractionalPacking G w → packingWeight G w ≤ 4
```
This avoids sSup entirely for the upper bound.

---

## Updated Success Criteria

| Phase | File | Target Sorry | Target Axiom |
|-------|------|--------------|--------------|
| 1 | slot153 | 0 | 0 |
| 2 | slot153b | ≤ 2 | 0 |
| 3 | slot154 | 0 | 1 (Krivelevich) |

---

## Next Steps

1. ✅ PRD created
2. ✅ GitHub issue #42 created
3. ✅ AI debate completed
4. ⏳ Update PRD with edge-counting proof
5. ⏳ Draft slot153 (ν* ≥ 4)
6. ⏳ Draft slot153b (ν* ≤ 4)
7. ⏳ Submit to Aristotle

---

*Synthesis generated January 1, 2026*
