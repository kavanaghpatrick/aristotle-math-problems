# ROUND 3 DEBATE: Complete Analysis Index

## The Central Question

**Can middle-element externals through private vertices exist in PATH_4?**

## Documents in This Analysis

### 1. Executive Summary
**File:** `DEBATE_ROUND3_EXECUTIVE_SUMMARY.md`

**Quick answer:** YES, they exist. Critic A's cover is invalid. τ ≤ 8 depends on a false lemma.

**Key findings:**
- Middle-element externals CAN exist
- False lemma: tau_pair_le_4 (claims ≤ 4, actually needs ≤ 6)
- Proven bound: τ ≤ 12 for PATH_4
- Open question: τ ≤ 8 for PATH_4

### 2. Concrete Example
**File:** `DEBATE_ROUND3_CONCRETE_EXAMPLE.md`

**Explicit construction:**
- Graph on 10 vertices with PATH_4 packing
- Triangle T = {v1, b, x} using private vertex b
- Proof that Critic A's cover fails
- Full 12-edge cover enumeration

### 3. Detailed Verdict
**File:** `DEBATE_ROUND3_VERDICT.md`

**Complete analysis:**
- Proof that such triangles can exist
- Classification (B-external, in T_pair(A,B))
- Coverage requirements
- Database evidence for false lemma
- Recommendations for next steps

### 4. Full Technical Analysis
**File:** `DEBATE_ROUND3_ANALYSIS.md`

**Deep dive:**
- Lean definitions from slot51_path4_PROVEN.lean
- Decomposition approach (containing v vs avoiding v)
- Why 6 edges are needed, not 4
- Edge-by-edge coverage analysis
- Historical context from database

## Quick Reference

### The Answer

**YES** - Triangle T = {v1, b, x} can exist where:
- B = {v1, v2, b} is a middle element
- b is B's private vertex
- x is any vertex with edges to v1 and b

### Why It Matters

Such triangles:
- Are valid B-externals
- Must be covered by spoke edge {v1,b}
- Invalidate any cover that omits this spoke
- Prove Critic A's 7-edge cover is WRONG

### Current State

| Statement | Status | Source |
|-----------|--------|--------|
| T = {v1, b, x} can exist | ✅ PROVEN | Structural argument |
| Critic A's cover is valid | ❌ FALSE | Missing {v1,b} |
| τ(T_pair) ≤ 4 | ❌ FALSE | Database: false_lemmas |
| τ(T_pair) ≤ 6 | ✅ TRUE | Decomposition: 4 spokes + 2 bases |
| PATH_4: τ ≤ 12 | ✅ PROVEN | slot290_tau_le_12_fixed.lean |
| PATH_4: τ ≤ 8 | ❓ OPEN | Blocked by false lemma |

### Database References

**False lemma entry:**
```sql
SELECT * FROM false_lemmas WHERE lemma_name = 'tau_pair_le_4';
```

**Proven submission:**
```sql
SELECT * FROM submissions WHERE filename = 'slot290_tau_le_12_fixed.lean';
```

**Case knowledge:**
```sql
SELECT * FROM nu4_cases WHERE case_name = 'path_4';
```

## Mathematical Core

### The Decomposition

For e ∩ f = {v}:

**T_pair(e,f) = trianglesContaining(v) ∪ trianglesAvoiding(v)**

**Containing v:**
- Needs 4 spokes: edges from v to other vertices in e and f
- Example: {v,a1}, {v,a2}, {v,b1}, {v,b2}

**Avoiding v:**
- Needs base edges from e and f
- Example: {a1,a2}, {b1,b2}

**Total: 6 edges, NOT 4**

### Why Private Vertices Matter

Private vertex b in B = {v1, v2, b}:
- Creates potential for triangle {v1, b, x}
- This triangle contains v1 (shared vertex)
- Must be covered by spoke {v1,b}
- Cannot be ignored in coverage analysis

### The Gap from 12 to 8

**Current bound:** τ ≤ 12
- T_pair(A,B) ≤ 6
- T_pair(C,D) ≤ 6
- Total ≤ 12

**Target:** τ ≤ 8
- Need to eliminate 4 edges
- Possible via overlaps/bridges?
- No proof exists either way

## Next Steps

### Option 1: Prove τ = 9 or 10
- Construct explicit counterexample
- Show 8 edges insufficient
- Close the question with upper bound > 8

### Option 2: Find τ ≤ 8 via new approach
- Abandon T_pair decomposition
- Use PATH_4-specific structure
- Target actual edge overlaps

### Option 3: Automated search
- Enumerate small graphs
- Check τ for each PATH_4 instance
- Find maximum τ empirically

## Files to Update

1. **Move to partial/:** `slot51_path4_PROVEN.lean` (contains false lemma)
2. **Database:** Mark tau_pair_le_4 dependencies
3. **Documentation:** Update nu4_cases.path_4 with these findings

## Key Insight

**The existence of middle-element externals through private vertices is STRUCTURAL, not coincidental.**

Every middle element with a private vertex can generate such externals. Any cover that omits the corresponding spoke edges is necessarily incomplete.

This is a fundamental feature of PATH_4, not a corner case.
