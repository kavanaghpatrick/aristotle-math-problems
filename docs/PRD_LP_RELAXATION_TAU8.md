# PRD: τ ≤ 8 via LP Relaxation (Krivelevich Bound)

**Date:** January 1, 2026
**Status:** REVISED - Post AI Debate (Grok, Gemini, Codex)
**Priority:** P0 (Only remaining path to τ ≤ 8)

---

## 1. Executive Summary

All combinatorial approaches to proving τ ≤ 8 for cycle_4 have failed due to 10 documented false lemma patterns. The LP relaxation approach (Krivelevich's theorem) bypasses these issues entirely.

**Goal:** Prove τ ≤ 8 for cycle_4 using:
1. Krivelevich's theorem: τ ≤ 2ν* (as axiom)
2. Prove: ν* = 4 for cycle_4 (the novel contribution)

---

## 2. Mathematical Background

### 2.1 Definitions

**Fractional Triangle Packing (ν*)**
- Assign weight w(T) ∈ [0,1] to each triangle T
- Constraint: For each edge e, Σ{w(T) : e ∈ T} ≤ 1
- ν* = max Σ w(T)

**LP Duality**
- ν* = τ* (fractional versions are equal)
- ν ≤ ν* = τ* ≤ τ (always)

**Krivelevich (1995)**
- τ ≤ 2ν* (published theorem, can be axiomatized)

### 2.2 Key Insight for Cycle_4

In cycle_4 configuration:
- 4 M-triangles: A, B, C, D
- 12 M-edges (3 per triangle)
- **Each M-edge is in exactly ONE M-triangle** (proven in slot64c)

**Optimal fractional packing:** Set w(A) = w(B) = w(C) = w(D) = 1

For any M-edge e in triangle X:
- Constraint: w(X) + Σ{w(T) : T external, e ∈ T} ≤ 1
- With w(X) = 1: No external using e can have positive weight
- Since every external shares an M-edge: All externals have w = 0

**Therefore:** ν* = 4 exactly (achieved by integral packing!)

---

## 3. Submission Strategies

### Strategy A: Direct ν* = 4 Proof

**File:** `slot153_nu_star_eq_4.lean`

**Approach:**
1. Define fractional packing as weight function
2. Prove M-edges are disjoint across M-elements (slot64c scaffolding)
3. Show w(A)=w(B)=w(C)=w(D)=1 is feasible
4. Show no packing can exceed 4 (all edge capacities saturated)

**Scaffolding needed:**
- `M_edge_in_exactly_one` (PROVEN in slot64c)
- `external_shares_M_edge` (PROVEN - maximality)

**Key lemma:**
```lean
lemma nu_star_le_4_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) :
    fractionalPackingNumber G ≤ 4 := by
  -- For each M-edge e, sum of weights over triangles containing e ≤ 1
  -- Each M-edge is in exactly one M-element (M_edge_in_exactly_one)
  -- So w(A) ≤ 1, w(B) ≤ 1, w(C) ≤ 1, w(D) ≤ 1
  -- Externals share M-edges, so constrained by M-element weights
  -- If w(A)=1, no external using A's edges can have positive weight
  -- Total: ν* ≤ w(A) + w(B) + w(C) + w(D) ≤ 4
  sorry
```

**Difficulty:** Medium (main logic is sound, needs Lean encoding)

---

### Strategy B: Axiom + Application

**File:** `slot154_krivelevich_axiom.lean`

**Approach:**
1. State Krivelevich as axiom: `axiom krivelevich : τ G ≤ 2 * ν* G`
2. Prove ν* = 4 for cycle_4 (from Strategy A)
3. Conclude τ ≤ 8

**Advantages:**
- Cleanly separates published theorem from novel contribution
- Aristotle only proves the novel part

**Key theorem:**
```lean
axiom krivelevich_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    (triangleCoveringNumber G : ℝ) ≤ 2 * fractionalPackingNumber G

theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  have h1 : fractionalPackingNumber G ≤ 4 := nu_star_le_4_cycle4 G M hM cfg
  have h2 : (triangleCoveringNumber G : ℝ) ≤ 2 * fractionalPackingNumber G := krivelevich_bound G
  -- Combine: τ ≤ 2 * 4 = 8
  sorry -- linarith after norm_cast
```

**Difficulty:** Low (if Strategy A succeeds)

---

### Strategy C: Constructive Weight Proof

**File:** `slot155_weight_construction.lean`

**Approach:**
1. Explicitly construct w: Triangles → ℚ
2. w(A) = w(B) = w(C) = w(D) = 1, w(external) = 0
3. Verify all edge constraints are satisfied
4. Show this achieves ν* = 4

**Advantages:**
- Most concrete/verifiable
- No abstract LP definitions needed

**Key structure:**
```lean
def optimalWeight (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4 G M)
    (t : Finset V) : ℚ :=
  if t ∈ M then 1 else 0

lemma optimalWeight_is_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M) :
    ∀ e ∈ G.edgeFinset,
      (G.cliqueFinset 3).sum (fun t => if e ∈ t.sym2 then optimalWeight G M cfg t else 0) ≤ 1 := by
  intro e he
  -- Case 1: e is an M-edge → exactly one M-element contains it (slot64c)
  -- Case 2: e is non-M-edge → no M-element contains it, sum = 0
  sorry
```

**Difficulty:** Medium-High (need to handle edge cases carefully)

---

### Strategy D: Dual LP (Edge Weights)

**File:** `slot156_dual_lp.lean`

**Approach:**
1. Define fractional edge cover
2. Construct y: Edges → ℚ with y(M-edge) = 1/2 for all 12 M-edges
3. Verify: Each triangle has Σ{y(e) : e ∈ T} ≥ 1
4. Total: Σ y(e) = 12 × 1/2 = 6 < 8

**Wait - this gives τ* ≤ 6, not τ ≤ 8!**

Actually, τ* = ν* = 4, so this doesn't give us τ ≤ 8 directly. We need τ ≤ 2ν*, not τ* ≤ ν*.

**Conclusion:** Dual LP doesn't help directly. Stick to Strategies A-C.

---

### Strategy E: Hybrid with Structural Lemmas

**File:** `slot157_hybrid_structural.lean`

**Approach:**
1. Combine ν* = 4 proof with structural lemmas
2. Use proven scaffolding extensively
3. Minimize sorry count by building on existing proofs

**Scaffolding to include:**
- `M_edge_in_exactly_one` (slot64c - PROVEN)
- `scattered_triangles_partition` (slot148a - PROVEN)
- `external_shares_edge_with_M` (slot148a - PROVEN)
- `triangle_contains_shared` (slot145 - needs fixing)

**Difficulty:** Medium

---

## 4. Definition Formalization

### 4.1 Fractional Packing Number

```lean
/-- A fractional triangle packing assigns weights to triangles
    such that each edge has total weight ≤ 1 -/
structure FractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj] where
  weight : Finset V → ℚ
  nonneg : ∀ t, 0 ≤ weight t
  bounded : ∀ t, weight t ≤ 1
  triangles_only : ∀ t, t ∉ G.cliqueFinset 3 → weight t = 0
  edge_constraint : ∀ e ∈ G.edgeFinset,
    (G.cliqueFinset 3).sum (fun t => if e ∈ t.sym2 then weight t else 0) ≤ 1

/-- The fractional packing number -/
noncomputable def fractionalPackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  sSup { (G.cliqueFinset 3).sum p.weight | p : FractionalPacking G }
```

### 4.2 Alternative (Simpler)

```lean
/-- Fractional packing as a predicate on weight functions -/
def IsFractionalPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℚ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
  (∀ t, t ∉ G.cliqueFinset 3 → w t = 0) ∧
  (∀ e ∈ G.edgeFinset,
    (G.cliqueFinset 3).filter (fun t => e ∈ t.sym2) |>.sum w ≤ 1)

/-- Upper bound on fractional packing value -/
lemma fractional_packing_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℚ) (hw : IsFractionalPacking G w) (bound : ℚ)
    (h : ∀ w', IsFractionalPacking G w' → (G.cliqueFinset 3).sum w' ≤ bound) :
    fractionalPackingNumber G ≤ bound := sorry
```

---

## 5. Proof Outline for ν* = 4 (REVISED per AI Debate)

### CRITICAL FIX (Jan 1, 2026 AI Debate)

The original proof was **incomplete**. It proved ν* ≥ 4 but NOT ν* ≤ 4.

### Part A: ν* ≥ 4 (Lower Bound) ✓

**Claim:** There exists a fractional packing achieving weight 4.

**Proof:**
1. M-edges partition by M-element (slot64c PROVEN)
2. Set w(A) = w(B) = w(C) = w(D) = 1, w(external) = 0
3. Check edge constraints: Each M-edge e is in exactly one M-element X, so Σ{w(t) : e ∈ t} = w(X) = 1 ≤ 1 ✓
4. Total weight = 4

### Part B: ν* ≤ 4 (Upper Bound) - THE MISSING PIECE

**Claim:** For ANY valid fractional packing w, Σ w(t) ≤ 4.

**Proof (Edge-Counting Argument from Grok):**

1. Sum edge constraints over all 12 M-edges:
   - Σ_{e ∈ M-edges} Σ{w(t) : e ∈ t} ≤ 12

2. Each M-triangle contributes 3 times (one per edge):
   - LHS ≥ 3·w(A) + 3·w(B) + 3·w(C) + 3·w(D) + external_contributions

3. Since external_contributions ≥ 0:
   - 3(w(A) + w(B) + w(C) + w(D)) ≤ 12
   - w(A) + w(B) + w(C) + w(D) ≤ 4

4. Externals share M-edges (by maximality), so they're bounded by residual capacity.

5. **Key insight:** Reducing M-element weights to give externals weight creates 1:1 trade-off. Maximum is achieved at w(M) = (1,1,1,1), w(external) = 0.

**Formal Lemma Needed:**
```lean
theorem fractional_packing_weight_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Cycle4 G M)
    (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    (G.cliqueFinset 3).sum w ≤ 4
```

### Part C: ν* = 4 (Combining A + B)

From Parts A and B: 4 ≤ ν* ≤ 4, therefore ν* = 4.

---

## 5.5 Pattern 10 Bug Warning (from Codex)

**CRITICAL:** The Krivelevich axiom must be stated correctly!

```lean
-- WRONG (Pattern 10 - FALSE):
axiom krivelevich_forall_w (G : SimpleGraph V) (w : Finset V → ℝ) (hw : IsFractionalPacking G w) :
    (τ G : ℝ) ≤ 2 * packingWeight G w
-- Counterexample: K₃ with w=0 gives τ=1 > 0

-- CORRECT:
axiom krivelevich_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    (triangleCoveringNumber G : ℝ) ≤ 2 * fractionalPackingNumber G
-- Uses SUPREMUM (ν*), not any particular packing
```

---

## 6. Risk Analysis

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Mathlib LP gaps | HIGH | Definition complexity | Use simpler predicate-based approach |
| sSup issues (emptiness) | MEDIUM | Proof complexity | Prove nonemptiness explicitly |
| Edge constraint encoding | MEDIUM | Many cases | Use slot64c scaffolding |
| Aristotle timeout | LOW | Lost attempt | Keep file focused, minimal sorry |

---

## 7. Success Criteria

| Criterion | Target |
|-----------|--------|
| Sorry count | ≤ 2 |
| New axioms | 1 (Krivelevich only) |
| Scaffolding reuse | ≥ 3 proven lemmas |
| AI pre-review | Grok + Gemini + Codex approve |

---

## 8. Submission Plan

### Phase 1: Slot 153 (ν* ≤ 4)
- Focus on proving ν* ≤ 4 only
- Use simple weight function definition
- Include slot64c scaffolding

### Phase 2: Slot 154 (τ ≤ 8)
- Add Krivelevich axiom
- Derive τ ≤ 8 from ν* ≤ 4
- Should be straightforward if Phase 1 succeeds

### Phase 3: Slot 155-157 (Alternatives)
- Only if Phase 1-2 fail
- Try constructive weight approach
- Try hybrid structural approach

---

## 9. Timeline

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| PRD Finalization | Today | This document + AI debate |
| Slot 153 Draft | Today | ν* ≤ 4 submission file |
| AI Review | Today | Grok/Gemini/Codex review |
| Submission | Today | Aristotle job |
| Phase 2 | After Phase 1 | τ ≤ 8 finalization |

---

## 10. Open Questions for AI Debate

1. **Is ν* = 4 actually TRUE for all cycle_4 graphs?**
   - The argument relies on M-edges being disjoint
   - What if the graph has additional non-M triangles creating fractional opportunities?

2. **Can we prove ν* ≤ 4 without Krivelevich?**
   - Direct edge counting might suffice
   - Each edge has capacity 1, total capacity = |E|
   - 4 triangles need 12 edge-slots, but edges overlap...

3. **What's the cleanest Lean encoding?**
   - Structure vs predicate for FractionalPacking
   - ℚ vs ℝ for weights
   - sSup vs explicit construction

4. **Should we try Chapuy et al. bound instead?**
   - τ ≤ 2ν* - ν*/√6 gives τ ≤ 7 for ν* = 4
   - Stronger but more complex

---

*PRD Version 1.0 - Ready for AI Debate*
