# Executive Summary: Adaptive Selection Proof Gap

## The Question

**User asked**: For the PATH_4 τ ≤ 8 proof (slot335), where is the mathematical gap if all 3 external types exist?

**Context**: Aristotle proved two adaptive lemmas, both with the same sorry: `¬(type1 ∧ type2 ∧ type3)` — the claim that not all 3 external types can coexist.

---

## Answer: There Are FIVE Critical Gaps

### Gap 1: Confusing External Triangles (S_X) with All Sharing Triangles (T_X)

**Location**: slot335:143-144

**The Claim**: "If our 2 edges for X cover all S_X triangles, bridges are covered too."

**The Problem**:
- S_X = externals to X only (share edge with X, no other M-element)
- T_X = ALL triangles sharing edge with X (includes M-element X, externals, bridges)
- 2 edges of X cannot cover all 3 edges of X

**Example**: X = {a,b,c}, E_X = {{a,b}, {a,c}}
- T = {b,c,w} shares edge {b,c} with X
- But {b,c} ∉ E_X, and neither {a,b} nor {a,c} covers T
- **Triangle T is uncovered** ✗

### Gap 2: Bridge Coordination Is Unproven

**Location**: slot335:155-171 ("STEP 5 refined")

**The Claim**: "If we include ONE spine edge in our selection for B or C, all bridges are covered."

**The Problem**:
- Bridges T = {x_A, x_B, z} have edges using elements from BOTH A and B
- Edges of T are NOT necessarily in A.edges ∪ B.edges
- Independently chosen E_A and E_B do not globally coordinate to cover all bridges
- No proof that spine edges in E_B hit all bridges involving B

**Example**:
- T = {a, v₁, b} shares {a, v₁} with A, shares {v₁, b} with B
- If E_A = {{a, a'}, {a, v₁}} and E_B = {{v₁, v₂}, {v₂, b}}, then:
  - {a, v₁} ∉ E_B (not in B's edge set)
  - {v₁, b} ∉ E_A (not in A's edge set)
  - **Bridge T is uncovered** ✗

### Gap 3: External Definition Ambiguity

**Location**: slot335:49-52

**The Definition**:
```lean
def isExternalOf G M X t :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y
```

**The Issue**:
- An "external" is a triangle NOT in M
- But the covering problem requires covering M-elements too (they're triangles!)
- The proof treats "2 edges per X" as covering both X and S_X, but:
  - X has 3 edges (it's a triangle)
  - 2 edges cannot form a complete cover of a 3-edge triangle

**Question**: Are M-elements assumed separately covered, or must they be in E?

### Gap 4: Missing Bridge Classification

**Location**: The proof doesn't distinguish between:

1. **Externals to X only** (S_X): share edge with X, not with other M-elements
2. **Bridges between X and Y** (X_XY): share edge with both X and Y
3. **M-elements themselves** (X ∈ M): triangles in the packing

**The argument for S_X**:
- If S_X uses all 3 edges of X, form {T₁, T₂, T₃} ∪ (M \ {X}) = 6-packing → contradiction
- Therefore S_X uses ≤ 2 edges ✓

**But for bridges**:
- Can they use all 3 edges of both parent M-elements simultaneously?
- Can a bridge exist without sharing spine vertices?
- **The proof doesn't analyze this**

### Gap 5: The Main Sorry

**Location**: slot335:175-181

```lean
theorem tau_le_8_path4 ... :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ isTriangleCover G E := by
  sorry
```

This single `sorry` hides the entire bridge coverage argument. The proof structure is:

```
✓ Step 1: externals_on_at_most_two_edges (ν ≤ 4 argument works)
✓ Step 2: two_edges_per_X_cover_externals (follows from Step 1)
? Step 3-5: bridges_covered_by_adaptive_selection (NO PROOF)
? Final: 4 × 2 = 8 edges suffice (depends on Step 3-5)
```

---

## Root Cause: The Three External Types

**User's observation**: If all 3 external types exist, we get a 6-packing contradiction.

**Correct inference**:
- Type 1: externals on edge {a,b} of X
- Type 2: externals on edge {a,c} of X
- Type 3: externals on edge {b,c} of X
- {T₁, T₂, T₃, M\{X}} = 6-packing contradicts ν ≤ 4
- **Therefore, not all 3 types can coexist**

**This proves**:
- At least one of the 3 edges of X has NO externals
- So ∃ 2 edges that cover all S_X externals ✓

**This DOES NOT prove**:
- Those 2 edges cover M-element X itself ✗
- Those 2 edges globally coordinate with other M-elements' edges ✗
- Those 2 edges cover bridges ✗

The proof correctly identifies that externals are constrained, but incorrectly extends this to claim 8 edges total suffice.

---

## Key Missing Hypothesis

**What the proof assumes but doesn't state**:

For PATH_4 (A — B — C — D), there exist edge selections E_A, E_B, E_C, E_D such that:
1. |E_X| ≤ 2 for each X
2. **All triangles in G are covered**

This requires:
- M-elements to be individually covered (or stated as pre-covered)
- Bridges to be covered by the union of edge selections
- Global coordination of edge choices

**None of these are proven**.

---

## What IS Proven

| Statement | Status | Why |
|-----------|--------|-----|
| ν ≤ 4 ⟹ S_X uses ≤ 2 edges | ✅ | 5-packing argument is solid |
| ∃ 2 edges covering S_X | ✅ | Follows from above |
| ∃ 2 edges covering S_X ∪ {X} | ❌ | X has 3 edges; 2 can't cover all 3 |
| ∃ 2 edges covering T_X (all sharing) | ❌ | Counterexample: T={b,c,w} using edge {b,c} ∉ E_X |
| Bridges covered by spine edges | ❌ | Bridges can avoid spine vertices |
| 8 edges global cover | ❌ | Depends on all above |

---

## Recommended Actions

### Option A: Complete the Proof (2-8 hours)
Prove `bridges_covered_by_adaptive_selection` explicitly:
```lean
lemma bridges_covered_by_spine_coordination
    (hν : ν ≤ 4)
    (hpath : isPath4 M A B C D)
    (E_A E_B E_C E_D : chosen adaptively)
    (h_externals : ∀ X, externals_of X covered by E_X)
    (h_spine : B.choice includes edge {v_ab, *} OR {v_bc, *})
             (C.choice includes edge {v_bc, *} OR {v_cd, *}) :
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E_A ∪ E_B ∪ E_C ∪ E_D, e ∈ t.sym2
```

**Difficulty**: Medium-Hard. Requires careful case analysis of bridge types and spine coverage.

### Option B: Accept τ ≤ 12 (30 minutes)
The fallback proof (slot139) is already proven, 0 sorry, 0 axiom:
```
Each M-element: 3 edges
4 M-elements: 4 × 3 = 12 edges
τ ≤ 12 is PROVEN ✓
```

Cost: τ ≤ 12 instead of τ ≤ 8, but solid.

### Option C: Try LP Fractional Relaxation (4-6 hours)
Use duality instead of combinatorial argument:
```
Fractional packing number ν* ≤ 4 (by constraint)
By LP duality: τ* ≤ 2 × ν* ≤ 8
Integer cover: τ ≤ ⌈τ*⌉ ≤ 8
```

Requires constructing explicit dual certificate.

### Option D: Submit as Open Problem (2 hours)
Document the gap and submit:
```
PARTIAL RESULT:
- Prove τ ≤ 12 via all-edges approach (slot139)
- Identify gaps in τ ≤ 8 via adaptive approach
- Open: Can adaptive selection achieve τ ≤ 8?
```

---

## Timeline Estimate

| Approach | Time | Confidence | Files |
|----------|------|------------|-------|
| Complete proof | 2-8h | 40% (unsolved problem?) | slot335 + new lemmas |
| Accept τ ≤ 12 | 0.5h | 100% | use slot139 |
| LP fractional | 4-6h | 50% | new slot file |
| Open problem | 2h | 100% | documentation |

**Recommendation**: Start with Option B (τ ≤ 12 submission), then explore Option A (bridge coordination) as a separate research task.

---

## Verification

Run Aristotle on a minimal bridge counterexample to verify the gap:

```lean
-- Minimal PATH_4 with edge selection that misses a bridge
def bad_choice : ∃ G M E_A E_B E_C E_D,
  isMaxPacking G M ∧ isPath4 M A B C D ∧
  (∀ X ∈ {A,B,C,D}, E_X covers externals to X) ∧
  (E_A ∪ E_B ∪ E_C ∪ E_D does NOT cover all triangles in G)
```

This would formally disprove the current adaptive approach and confirm the gap.

---

## Files Referenced

1. **Main proof**: `/Users/patrickkavanagh/math/submissions/nu4_final/slot335_adaptive_1sorry.lean`
2. **Scaffolding**: `/Users/patrickkavanagh/math/submissions/nu4_final/slot334_adaptive_cover.lean`
3. **Fallback proof**: `/Users/patrickkavanagh/math/submissions/nu4_final/slot139_*.lean` (τ ≤ 12, proven)
4. **False lemmas database**: `/Users/patrickkavanagh/math/submissions/tracking.db` (patterns #6, #7, #17, #22, #27, #28)

---

## Conclusion

The adaptive selection approach for τ ≤ 8 is **mathematically incomplete**. The key insight (ν ≤ 4 bounds externals) is valid, but the extension to cover all triangles (including M-elements and bridges) is unproven and likely requires additional structural arguments or weaker bounds.

**Safest path forward**: Submit τ ≤ 12 (proven), document τ ≤ 8 gaps for future work.
