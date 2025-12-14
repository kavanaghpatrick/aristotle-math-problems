# Aristotle Lessons Learned - December 2025

## The Big Discovery: Path of Least Resistance

**Aristotle optimizes for PROVABILITY, not FAITHFULNESS to intent.**

When given an ambiguous problem, Aristotle will solve the easiest valid interpretation, even if that's not what the problem actually asks.

### Case Study: Erdős #153

| Aspect | What Problem Asked | What Aristotle Proved |
|--------|-------------------|----------------------|
| Claim | Universal (∀ Sidon sets) | Existential (∃ some family) |
| Difficulty | Hard (open problem) | Trivial (powers of 2) |
| Quantifiers | ∀M, ∃N, ∀A, ... | ∀M, ∀N, ∃A, ... |
| Result | Would solve #153 | Proves nothing new |

The proof compiled with 0 sorries. The math was correct. But it answered the wrong question.

## New Verification Protocol

### OLD: "0 sorries + compiles = solved"
### NEW: "0 sorries + compiles + MATCHES ORIGINAL = solved"

After any Aristotle "success":
1. ✓ Verify it compiles
2. ✓ Verify zero sorries
3. ✓ **Verify quantifier structure matches original**
4. ✓ **Run multi-model verification (Grok/Gemini)**
5. ✓ **Check definitions match standard usage**

## Refined Boris Pattern

Boris = Minimal INTERVENTION, not minimal PRECISION

| DO | DON'T |
|----|-------|
| ✓ Provide exact formal statement | ✗ Prescribe proof strategy |
| ✓ Specify quantifier structure explicitly | ✗ Specify which lemmas to use |
| ✓ Use Lean syntax for the theorem | ✗ Provide partial proofs |

### Example: Good vs Bad Submission

**BAD** (what we did):
```
Prove: avg_sq_gap → ∞ as |A| → ∞ for Sidon sets
```

**GOOD** (what we should have done):
```lean
theorem erdos_153 : ∀ M : ℚ, ∃ N : ℕ, ∀ A : Finset ℕ,
  (IsSidonSet A ∧ A.card > N) → averageSquaredGap A > M
```

## Other Key Insights

### 1. Timeouts Produce Building Blocks
Many "failed" runs contain valuable intermediate lemmas. Always extract and reuse.

### 2. Multi-Model Debate Essential
Grok caught the formalization error we missed. Always verify with external model.

### 3. Natural Language is Ambiguous
"f(A) → ∞ as |A| → ∞" can mean:
- ∃ family where this holds (easy)
- ∀ objects, this holds (hard)

Aristotle picks the easy one. Specify explicitly.

## Updated CLAUDE.md Rules

Add to Aristotle workflow:

```
## Post-Aristotle Verification (MANDATORY)

After any Aristotle success, before claiming solved:
1. Extract the main theorem statement
2. Compare quantifier-by-quantifier with original problem
3. Run Grok: "Does this theorem exactly match [original problem]?"
4. If mismatch: resubmit with explicit formal statement
```

## The Quantifier Trap

| Natural Language | Could Mean | Aristotle Prefers |
|-----------------|------------|-------------------|
| "X → ∞ as n → ∞" | ∀ or ∃ | ∃ (easier) |
| "For large n, P holds" | ∀ or ∃ | ∃ (easier) |
| "P(n) is unbounded" | ∀ or ∃ | ∃ (easier) |

Always write explicit quantifiers:
```
∀ M, ∃ N, ∀ n > N, P(n) > M    -- Universal (hard)
∀ M, ∀ N, ∃ n > N, P(n) > M    -- Existential (easy)
```

## The Hypothesis Restriction Trap (NEW - Dec 14, 2025)

### Case Study: Erdős #149

| Aspect | What Problem Asked | What Aristotle Proved |
|--------|-------------------|----------------------|
| Claim | For ALL graphs | Only for Δ ≤ 2 |
| Theorem | `theorem erdos_149 (G : SimpleGraph V) ...` | `theorem erdos_149_delta_le_2 (G) (h : G.maxDegree ≤ 2) ...` |
| Difficulty | Hard (open conjecture) | Trivial (small case) |
| Result | Would prove conjecture | Proves nothing new |

**What happened**: Aristotle added `h : G.maxDegree ≤ 2` hypothesis that wasn't in the original problem.

### The Pattern

Aristotle will ADD restrictive hypotheses to make proofs tractable:

| Type | Example Added Hypothesis |
|------|--------------------------|
| Degree bounds | `h : G.maxDegree ≤ k` |
| Size bounds | `h : A.card ≤ n` |
| Structural | `h : G.isTree` or `h : G.isConnected` |
| Special cases | `h : p.IsPrime` when problem is about all n |

### Prevention Strategy

1. **Explicit "NO ADDITIONAL HYPOTHESES" instruction**
2. **State theorem in exact Lean syntax with no sorry-able hypotheses**
3. **Compare output theorem signature character-by-character**

### Example: Fixed Submission

**Before (allows trap)**:
```
Prove the strong chromatic index conjecture: χ'_s(G) ≤ (5/4)Δ²
```

**After (prevents trap)**:
```lean
-- PROVE EXACTLY AS STATED, NO ADDITIONAL HYPOTHESES
theorem erdos_149 (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.strongChromaticIndex : ℚ) ≤ (5/4) * (G.maxDegree : ℚ)^2 := by
  sorry
```

## Both Traps Combined: The False Positive Checklist

After ANY Aristotle success, verify:

| Check | Quantifier Trap | Hypothesis Trap |
|-------|-----------------|-----------------|
| 1. Main theorem name | Does it match? | Is it renamed (e.g., `_delta_le_2`)? |
| 2. Quantifier order | ∀∃∀ vs ∀∀∃? | N/A |
| 3. Theorem arguments | N/A | Any new `h : ...` parameters? |
| 4. Scope | Universal or existential? | Full generality or restricted? |

**If ANY check fails**: FALSE POSITIVE. Do not claim solved.

## Summary

1. Aristotle takes path of least resistance
2. "0 sorries" ≠ "correct answer"
3. Quantifier order is everything (TRAP #1)
4. Hypothesis restrictions invalidate proofs (TRAP #2)
5. Explicit Lean theorem statements > natural language
6. Multi-model verification catches errors
7. Boris = precise formulation + autonomous proof
8. ALWAYS compare output theorem signature to original
