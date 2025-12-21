# Tuza Formalization Audit Report

Date: 2025-12-20

## Critical Findings

### 1. T_e DOES include e itself (VERIFIED)

**Status**: CORRECT BEHAVIOR

The definition:
```lean
def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))
```

**Does include e** because:
- `triangleEdges e` contains all 3 edges of triangle e
- `triangleEdges e ∩ triangleEdges e = triangleEdges e ≠ ∅`
- Therefore `¬Disjoint (triangleEdges e) (triangleEdges e)` is TRUE
- So `e ∈ T_e(e)` holds

**Mathematical correctness**: This is CORRECT. T_e should include e itself since e shares all its edges with itself.

**Proof**: See `test_T_e_inclusion.lean` - compiles successfully.

---

### 2. coveringNumberOn allows edges NOT in G (POTENTIAL BUG)

**Status**: CRITICAL ISSUE

There are TWO different definitions in use:

#### Definition A (sInf version - ALLOWS NON-GRAPH EDGES):
```lean
def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E}
```

**Problem**: `E : Finset (Sym2 V)` is ANY set of Sym2 pairs, not restricted to `G.edgeFinset`.

This means you could "cover" triangles with edges that DON'T EXIST in the graph!

**Example counterexample**:
- Graph G = K₄ - {one edge}
- Triangle t = {a,b,c} where edge {a,b} is MISSING
- Definition A would allow E = {{a,b}} to "cover" t
- But {a,b} ∉ G.edgeFinset!

#### Definition B (powerset version - CORRECT):
```lean
noncomputable def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : ℕ :=
  (G.edgeFinset.powerset.filter (fun C =>
    ∀ t ∈ S, ¬Disjoint (triangleEdges t) C)).image Finset.card |>.min |>.getD 0
```

**This is CORRECT** because `G.edgeFinset.powerset` restricts to actual edges in G.

#### Files Using Which Definition:

**Definition A (BUGGY - unrestricted E)**:
- `tuza_nu3_case_by_case.lean`
- `tuza_nu3_counterexample_finite.lean`
- `tuza_nu3_pessimist.lean`
- `tuza_tau_Te_lemma.lean`
- `tuza_nu3_flower_exclusion.lean`
- `tuza_nu3_key_insight.lean`
- `tuza_nu3_final_fixed.lean`
- `aristotle_tau_Te_cases.lean`
- `aristotle_tuza_nu_le_3_COMPLETE.lean`

**Definition B (CORRECT - restricted to G.edgeFinset)**:
- `tuza_tau_Te_packing_SCAFFOLDED.lean`
- `tuza_tau_Te_packing_CORRECTED.lean`

**Recommendation**: Use Definition B everywhere. Definition A is mathematically incorrect for the Tuza problem.

---

### 3. The "False Flag" was CORRECT (e must be in M)

**Status**: CORRECT CONSTRAINT

Previous analysis showed that `τ(T_e) ≤ 2` fails for arbitrary triangles e not in the packing.

**Example** (flower graph):
- Central triangle {0,1,2} has τ(T_e) = 3
- But {0,1,2} is NOT in the maximum packing M
- For actual packing elements, τ(T_e) ≤ 2 holds

**The constraint `e ∈ M` is ESSENTIAL** and was correctly identified in:
- `tuza_tau_Te_packing_CORRECTED.lean`

This matches Parker's paper - the lemma applies to **packing elements**, not arbitrary triangles.

---

### 4. Two different T_e definitions (BOTH VALID, but different)

**Status**: SEMANTIC DIFFERENCE

#### Edge-based:
```lean
def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))
```

#### Vertex-based:
```lean
def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)
```

**Are they equivalent?**

For triangles in a simple graph, these SHOULD be equivalent:
- Share an edge ⟺ share ≥2 vertices
- But need to verify this formally

However, if e is NOT a valid triangle (e.card ≠ 3), they differ:
- Edge-based: looks at edges of e
- Vertex-based: looks at vertices of e

**Recommendation**: Use edge-based definition for clarity, since it directly captures "shares an edge".

---

## Summary of Recommendations

### Critical Fixes Needed:

1. **Replace all uses of Definition A (sInf unrestricted) with Definition B (powerset restricted)**
   - This is a mathematical correctness bug
   - Could lead to incorrect proofs

2. **Ensure all submissions include the constraint `e ∈ M`**
   - The lemma `τ(T_e) ≤ 2` only holds for packing elements
   - Not for arbitrary triangles

3. **Verify T_e includes e itself**
   - This is correct behavior (proven)
   - Don't try to "fix" this

### Non-Critical Improvements:

1. **Standardize on edge-based T_e definition**
   - More direct semantic match to "shares an edge"
   - Vertex-based works but requires proving equivalence

2. **Add explicit comments**
   - "T_e includes e itself"
   - "E must be edges from G, not arbitrary Sym2 pairs"

---

## Files to Review/Fix Priority:

**HIGH PRIORITY** (using buggy coveringNumberOn):
- `aristotle_tuza_nu_le_3_COMPLETE.lean`
- All ν=4 submissions using Definition A

**MEDIUM PRIORITY**:
- Verify all submissions have `e ∈ M` constraint
- Check Parker lemma formalizations

**LOW PRIORITY**:
- Standardize T_e definition across files
- Prove equivalence of T_e definitions
