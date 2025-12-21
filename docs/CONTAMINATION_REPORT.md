# Tuza Formalization Contamination Report

**Date**: December 20, 2025
**Severity**: CRITICAL

## Summary

Two formalization bugs were discovered that invalidate multiple "proven" theorems:

1. **Bug 1 (coveringNumberOn)**: Definition allows edges not in G
2. **Bug 2 (sym2 self-loops)**: `Finset.sym2` includes self-loops, allowing invalid covering

## Bug 1: Unrestricted Edge Sets

### Buggy Definition
```lean
def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ...}
  -- E can be ANY Sym2 set, not restricted to G.edgeFinset
```

### Correct Definition
```lean
def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (...) |>.image Finset.card |>.min |>.getD 0
  -- E must be a subset of G.edgeFinset
```

## Bug 2: Self-Loops in sym2

### Discovery
```lean
#eval ({1, 2, 3} : Finset ℕ).sym2
-- Output: {s(1, 1), s(1, 2), s(1, 3), s(2, 2), s(2, 3), s(3, 3)}
-- INCLUDES self-loops s(1,1), s(2,2), s(3,3)!
```

### Impact on Proofs
In `aristotle_tuza_nu2_PROVEN.lean`, line 122:
```lean
refine' ⟨ { Sym2.mk ( v, v ) }, _, _ ⟩  -- Uses self-loop to "cover"!
```

This claims a single self-loop can cover all triangles containing vertex v. But self-loops are NOT valid edges in SimpleGraph!

## Affected Files

### CONTAMINATED (Invalid Proofs)
| File | Bug(s) | What's Wrong |
|------|--------|--------------|
| `aristotle_tuza_nu2_PROVEN.lean` | Both | Uses self-loop at line 122 |
| `aristotle_tau_Te_cases.lean` | Bug 1 | Missing edge restriction |
| `aristotle_tuza_nu_le_3_COMPLETE.lean` | Bug 1 | Missing edge restriction |
| `tuza_nu3_*.lean` (recent) | Bug 1 | Missing edge restriction |

### CLEAN (Valid Proofs)
| File | Why Clean |
|------|-----------|
| `aristotle_tuza_nu1_PROVEN.lean` | Uses `F ⊆ G.edgeFinset` |
| `aristotle_parker_proven.lean` | Uses `G.edgeFinset.powerset` |
| `aristotle_tuza_infrastructure_COMPLETE.lean` | Correct restriction |
| `aristotle_tuza_base_cases.lean` | Correct restriction |

## Correct Approach

### For Triangle Covering
```lean
def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) : Prop :=
  E ⊆ G.edgeFinset ∧  -- MUST be actual graph edges
  ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2

def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0
```

### For Covering on Subset (T_e)
```lean
def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E =>
    ∀ t ∈ S, ∃ e ∈ E, e ∈ t.sym2
  ) |>.image Finset.card |>.min |>.getD 0
```

## Action Items

1. ✅ Create `tuza_nu3_FIXED.lean` with correct definitions
2. ⏳ Submit `tuza_nu3_pessimist_FIXED.lean` when slot opens
3. ❌ Do NOT trust any theorem from contaminated files
4. ⚠️ Re-prove ν=2 case with correct definitions

## Lessons Learned

1. **Always verify definitions match mathematical intent**
2. **Mathlib's `Finset.sym2` includes diagonals - be careful**
3. **Existential definitions (sInf over arbitrary sets) are dangerous**
4. **Use `G.edgeFinset.powerset` to restrict to valid edges**
