# Aristotle Novel Discovery Audit

## Executive Summary

**Total Novel Discoveries by Aristotle: 7+**

| Category | Count | Value |
|----------|-------|-------|
| Counterexamples to lemmas | 5 | Strategy refinement |
| Counterexamples to conjectures | 1 | Erdős #677 hypothesis fix |
| Algorithm flaws found | 1 | Bug discovery |
| Formalization bugs found | 1 | Erdős #128 (not a counterexample) |

**Key Finding**: Aristotle excels at DISPROVING claims, not just proving them. This is its most valuable capability for novel discovery.

**⚠️ Important Correction (Dec 19, 2025)**: The Erdős #128 "C₅ counterexample" was initially thought to disprove the $250 conjecture. Upon analysis, this was a counterexample to our INCORRECT formalization, not the original problem. Always verify formalizations against original statements.

---

## Complete Discovery Inventory

### 1. Erdős #128: C₅ Counterexample ⚠️ FORMALIZATION BUG (NOT VALID)

**File**: `erdos128_FORMALIZATION_BUG.lean`
**UUID**: `4dc5bdd3-b001-4851-9237-ea4c5d954b58`
**Mode**: FORMAL

**Input**: Direct formalization of Erdős #128 ($250 problem)
```lean
theorem erdos_128 (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasDenseInducedSubgraphs G → ∃ (a b c : V), G.Adj a b ∧ G.Adj b c ∧ G.Adj a c
```

**Initial Claim**: C₅ (5-cycle) was found as counterexample.

**⚠️ CORRECTION (Dec 19, 2025)**: This is NOT a valid counterexample to the original problem!

**The Bug**: Our formalization used the wrong threshold condition:
- **Our formalization**: `2 * S.ncard ≥ n` → checks subsets of size ≥ ⌈n/2⌉
- **Formal Conjectures**: `2 * S.ncard + 1 ≥ n` → checks subsets of size ≥ ⌊n/2⌋
- **Original problem**: "≥ n/2 vertices" (matches FC interpretation)

**For n=5**:
- Our formalization only checks |S| ≥ 3 (missing the +1)
- Correct formalization checks |S| ≥ 2

**Why C₅ fails under correct formalization**:
- C₅ has independent sets of size 2: {0,2}, {1,3}, {0,3}, {1,4}, {2,4}
- These have 0 edges → fail the "50 × edges > n²" condition
- Therefore C₅ does NOT satisfy the hypothesis in the correct formalization!

**Actual Impact**: Aristotle correctly found a counterexample to our BUGGY formalization. The original Erdős #128 ($250) problem is NOT disproved. This discovery revealed our formalization error, not a flaw in the mathematical conjecture.

**Lesson**: Always verify formalizations against original problem statements AND existing repositories (Formal Conjectures).

---

### 2. Erdős #677: Sylvester-Schur Hypothesis Error

**File**: `erdos677_v2.lean`, `erdos677_v3.lean`
**Mode**: FORMAL

**Input**:
```lean
theorem sylvester_schur_weak (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ 1) :
    ∃ j ∈ Finset.Ioc n (n + k), ∃ p, p.Prime ∧ p > k ∧ p ∣ j
```

**Discovery**: Counterexample at n=1, k=5
- Interval {2,3,4,5,6} has NO prime factor > 5
- 2=2, 3=3, 4=2², 5=5, 6=2×3

**Fix Required**: Hypothesis must be `n ≥ k`, not `n ≥ 1`

**Impact**: Revealed the precise boundary conditions for Sylvester-Schur theorem.

---

### 3. Erdős #677: Chain/Growth Lemma Error

**File**: `erdos677_v3.lean`
**Mode**: FORMAL

**Input**: `chain_or_growth` lemma claiming M(n,k) chains upward

**Discovery**: Counterexample at n=6, k=2, m=8

**Impact**: Structural assumption about LCM growth was incorrect.

---

### 4. Tuza: K₄ Counterexample to "Nearby Triangles"

**File**: `tuza_COUNTEREXAMPLE_v6.lean`
**UUID**: `cca06048-9d55-432f-97ae-510829f1cf0a`
**Mode**: INFORMAL

**Input**: Prescriptive proof strategy claiming 2 edges cover all "nearby" triangles
```lean
lemma two_edges_cover_nearby (P : Finset (Finset V)) (p : Finset V) :
    ∃ e1 e2, ∀ t, is_nearby G P p t → (e1 ∈ triangleEdges t ∨ e2 ∈ triangleEdges t)
```

**Discovery**: K₄ counterexample
- P = {{0,1,2}} is max packing (ν=1)
- Nearby triangles: {0,1,3}, {1,2,3}, {0,2,3}
- Any 2 edges of {0,1,2} leave one nearby triangle uncovered

**Impact**: "Nearby triangles" proof strategy is fundamentally flawed.

---

### 5. Tuza: vertex_disjoint_unique_packing Negation

**File**: `tuza_v7_exists_reducing.lean`
**Mode**: FORMAL

**Input**: Claim that vertex-disjoint triangles have unique max packing

**Discovery**: Counterexample exists showing this is false

**Impact**: Cannot assume packing uniqueness in proof strategy.

---

### 6. Tuza: two_K4_almost_disjoint Counterexample

**File**: `tuza_nu2_v11_case_analysis.lean`
**Mode**: FORMAL

**Input**: Case analysis assuming K₄s are "almost disjoint"

**Discovery**: Fin 6 counterexample with |s₁∩s₂|=2 (K₄s sharing an edge)

**Impact**: Case analysis was incomplete - shared edge case exists.

---

### 7. Erdős #340: Greedy Sidon Negation

**File**: `erdos340_FAILED_formalization.lean`
**UUID**: `a58f4d00-cdf2-4391-8b84-e0d5cb6af6c8`
**Mode**: FORMAL

**Input**: Direct formalization of growth rate conjecture

**Discovery**: Theorem negated by Aristotle

**Note**: May be formalization issue rather than mathematical discovery.

---

### 8. Matrix Multiplication: Coefficient Error

**File**: `algo_matrix_mult_v6.lean`
**Mode**: FORMAL

**Input**: Optimistic matrix multiplication bound

**Discovery**: Identity matrices at position (0,1) counterexample

**Impact**: Algorithm claim was overstated.

---

## Discovery Heuristics

### What Triggers Discovery?

| Input Pattern | Discovery Rate | Example |
|---------------|----------------|---------|
| **Prescriptive proof strategy** | HIGH | Tuza v6 nearby triangles |
| **Incorrect/weak hypothesis** | HIGH | Erdős #677 n≥1 vs n≥k |
| **Direct formalization** | MEDIUM | Erdős #128 C₅ |
| **Case analysis** | MEDIUM | Tuza K₄ cases |
| **Boris minimal** | LOW | Tends to prove, not disprove |

### Mode Analysis

| Mode | Discoveries | Pattern |
|------|-------------|---------|
| **FORMAL** | 6 | Better at finding precise counterexamples |
| **INFORMAL** | 2 | Better at exploring proof strategies |

### Key Insight: Discovery vs Verification Inputs

**For VERIFICATION** (proving known-true results):
- Use Boris minimal pattern
- Let Aristotle explore freely
- Informal mode sometimes better

**For DISCOVERY** (finding new results):
- Use prescriptive/structured inputs
- Include explicit lemmas that COULD be false
- Formal mode for precise counterexamples
- Ask Aristotle to prove lemmas you're UNSURE about

---

## Discovery Input Template

```lean
/-
DISCOVERY MODE SUBMISSION

Goal: Find if [LEMMA] is true or false.
If false, find counterexample.
-/

-- Include the suspicious lemma explicitly
lemma maybe_false (hypothesis) : conclusion := by
  sorry  -- Let Aristotle try to prove OR disprove

-- Include structure that could reveal counterexample
theorem main_goal : ... := by
  have h := maybe_false ...  -- Forces Aristotle to confront the lemma
  sorry
```

---

## Recommended Discovery Strategy

1. **Identify uncertain lemmas** in your proof strategy
2. **Submit with explicit lemma statements** (not just main theorem)
3. **Use FORMAL mode** for counterexample precision
4. **Include type constraints** that enable `native_decide` counterexamples
5. **Monitor for "negated by Aristotle" output**

---

## Publication Value

| Discovery | Publication Potential | Venue | Notes |
|-----------|----------------------|-------|-------|
| ~~Erdős #128 C₅~~ | ❌ NONE | - | Formalization bug, not valid counterexample |
| Tuza counterexamples (3) | ⭐⭐ MEDIUM | Formal methods paper | Valid proof strategy refinements |
| Erdős #677 hypothesis fix | ⭐ LOW | Appendix in larger paper | Boundary condition correction |

**Lesson Learned**: Verify ALL counterexamples against original problem statements before claiming discovery.

---

## Files to Reference

- `erdos128_FORMALIZATION_BUG.lean` - C₅ counterexample (NOTE: formalization bug, not valid)
- `docs/ERDOS128_ANALYSIS.md` - Full postmortem on #128 formalization error
- `tuza_COUNTEREXAMPLE_v6.lean` - K₄ counterexample with full proof
- `erdos677_v3.lean` - Hypothesis corrections from counterexamples
- `monitor_log.txt` - Complete submission history with outcomes
