# Tuza Strategic Decision - Dec 18, 2025

## Executive Summary

**DECISION: Modified Pivot (Option D)**
- Document what we proved (quick win)
- Archive failed strategies (prevent regression)
- Pivot to tractable problems

## What We Achieved

### Proven Theorems
| Theorem | Source | Significance |
|---------|--------|--------------|
| τ(G) ≤ 3ν(G) | v7 minimal | First Lean 4 formalization |
| τ(K₄) = 2ν(K₄) | v7 minimal | Tight example verified |
| τ(K₅) = 2ν(K₅) | v7 minimal | Tight example verified |
| tuza_case_nu_1 | v5 output | ν=1 case complete |
| Conditional theorem | v5 output | "If reduction property, then Tuza" |

### Counterexamples Found
| Approach | Why It Fails |
|----------|--------------|
| TuzaReductionProperty | Removing 2 edges from packing triangle doesn't always decrease ν |
| NearbyTriangles | In K₄, nearby triangles each share only ONE edge with packing |

### Why Not Continue?

1. **Gap is massive**: Going from τ ≤ 3ν to τ ≤ 2ν requires probabilistic methods or complex weighting schemes
2. **Natural approaches exhausted**: Counterexamples show inductive strategies don't work
3. **Infrastructure trap**: Planar Tuza requires formalizing planarity, embeddings, Euler's formula
4. **Low expected value**: Continuing has ~0% chance of breakthrough

## Recommended Actions

### Immediate (Today)
1. ✅ Saved `tuza_PROVEN_weak_bound.lean` with full proofs
2. ✅ Saved `tuza_COUNTEREXAMPLE_v6.lean` documenting failure
3. ✅ Updated monitor_log.txt with results
4. ✅ Committed and pushed to GitHub

### Short-term (This Week)
1. Create `proven/` directory for verified results
2. Create `archive/tuza_failed_strategies.md`
3. Write brief README for Tuza results

### Pivot Targets

**High Priority (Similar to Weak Tuza):**
| Problem | Why Good Target |
|---------|-----------------|
| Mantel's Theorem | ex(n, K₃) = ⌊n²/4⌋ - exact result, similar logic |
| Small Ramsey bounds | R(3,4) ≤ 9 - finite, good for search |
| Turán bounds | ex(n, H) for small H - induction + edge counting |

**Medium Priority:**
| Problem | Notes |
|---------|-------|
| Erdős-Szekeres | Monotone subsequences, purely combinatorial |
| Triangle-free independence | Related to Ramsey theory |

**Skip for Now:**
- Planar Tuza (infrastructure trap)
- Asymptotic bounds (need probabilistic methods)
- Problems requiring heavy analytic machinery

## Key Lessons Learned

### Boris Pattern Vindicated
- v7 minimal (47 lines) produced MORE than v6 prescriptive (160 lines)
- Minimal approach lets Aristotle prove what it CAN prove
- Prescriptive approaches led to finding counterexamples (still valuable!)

### What Works for Aristotle
1. Local structure reasoning (triangles, cliques)
2. Induction on graph size/parameter
3. Case analysis on small configurations
4. Finding counterexamples to false claims

### What Doesn't Work
1. Probabilistic arguments
2. Complex weighting schemes
3. Global optimization
4. Arguments requiring "insight leaps"

## Files Created
- `submissions/tuza_PROVEN_weak_bound.lean` - Full τ ≤ 3ν proof
- `submissions/tuza_COUNTEREXAMPLE_v6.lean` - K₄ counterexample
- `docs/TUZA_STRATEGIC_DECISION.md` - This document

## Conclusion

We got real, verifiable mathematical value from Tuza:
- First Lean 4 formalization of τ ≤ 3ν
- Two formally proven counterexamples to natural approaches
- 10+ helper lemmas with complete proofs

Now pivot to problems where Aristotle can achieve complete solutions.
