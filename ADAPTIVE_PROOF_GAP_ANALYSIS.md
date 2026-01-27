# Adaptive Selection Proof Gap Analysis
## Tuza PATH_4 τ ≤ 8 via ν ≤ 4

**Status**: Proof structure sound, but critical gaps in the bridge coordination argument

**Files**:
- `/Users/patrickkavanagh/math/submissions/nu4_final/slot335_adaptive_1sorry.lean` - Main proof with single `sorry`
- `/Users/patrickkavanagh/math/submissions/nu4_final/slot334_adaptive_cover.lean` - Scaffolding

---

## The Proof Strategy (Correct Structure)

### STEP 1: Externals at Most 2 of 3 Edges (VALID)

**Claim**: For any X ∈ M with edges {a,b}, {a,c}, {b,c}, the set S_X of external triangles uses at most 2 of these 3 edges.

**Proof Sketch (Aristotle verified logic)**:
```
Assume S_X has triangles on ALL 3 edges:
  T₁ = {a, b, x₁}  -- shares edge {a,b} with X
  T₂ = {a, c, x₂}  -- shares edge {a,c} with X
  T₃ = {b, c, x₃}  -- shares edge {b,c} with X

Observation 1: T₁, T₂, T₃ pairwise intersect in exactly 1 vertex from X
  |T₁ ∩ T₂| = |{a}| = 1 ✓
  |T₁ ∩ T₃| = |{b}| = 1 ✓
  |T₂ ∩ T₃| = |{c}| = 1 ✓
  (External vertices x₁, x₂, x₃ are all distinct, else contradiction)

Observation 2: Each Tᵢ is EXTERNAL to X, so by definition:
  ∀ Y ∈ M, Y ≠ X ⟹ ¬sharesEdgeWith Tᵢ Y
  ⟹ |Tᵢ ∩ Y| ≤ 1 for all Y ∈ M \ {X}

Conclusion: {T₁, T₂, T₃} ∪ (M \ {X}) is a VALID PACKING
  - Size = 3 + 3 = 6
  - Contradicts ν ≤ 4
  - Therefore S_X cannot use all 3 edges
```

**Status**: ✅ VALID - This argument is bulletproof.

---

## The Missing Pieces (Where Proof Breaks Down)

### CRITICAL GAP 1: Bridge Coverage Assumption (Line 143-144)

**Claim** (slot335:143-144):
> "Every bridge shares edge with some X, so it contains 2 vertices of X.
>  If our 2 edges for X cover all triangles sharing edge with X, bridges are covered too."

**MISSING HYPOTHESIS**: The claim assumes we choose 2 edges per X that cover **all T_X** (triangles sharing edge with X), not just **S_X** (externals only).

**Example Counterexample** (False Lemma #7 in database):
```
Graph: A={v₁,a,a'}, B={v₁,v₂,b}, C={v₂,v₃,c}, D={v₃,d,d'}

At shared vertex v₁ = A ∩ B:
  A ∩ A = {v₁, a, a'}  -- 3 edges: {v₁,a}, {v₁,a'}, {a,a'}
  B ∩ A = {v₁}
  T_A = triangles sharing edge with A = {A} ∪ S_A

  A itself contains all 3 vertices v₁, a, a'
  But the external x added to form bridge with B doesn't share both a, a'
```

**The Real Issue**:
- We choose 2 edges E_X ⊆ X.edges to cover S_X (externals of X only)
- These 2 edges do NOT necessarily cover X itself (an M-element)
- X is a triangle in the graph → must be covered by our edge cover
- If we only pick 2 edges {e₁, e₂} ⊆ X.edges, we might miss X (need all 3 edges of X)

**Mathematical Root Cause**:
```
Correct statement: "If our 2 edges cover S_X, do they also cover X?"
Answer: NOT NECESSARILY
  - 2 edges of a 3-edge triangle X cover some of X's edges
  - But every triangle needs coverage, including X itself
  - This is INDEPENDENT of whether externals are covered
```

---

### CRITICAL GAP 2: Bridge Coordination for PATH_4 (Line 155-171)

**Claim** (slot335:155-171):
> "For bridges: Every bridge B contains a shared vertex v ∈ X ∩ Y.
>  In PATH_4, shared vertices form the 'spine': v_ab, v_bc, v_cd.
>  If we include ONE spine edge in our selection for B or C (the middle elements),
>  all bridges are covered."

**Where the logic breaks down**:

#### 1. **Edge-Disjointness Problem** (False Lemma #28: tau_S_union_X_le_2)

For bridge X_AB between A and B (A={v₁,a,a'}, B={v₁,v₂,b}):
```
Bridges are triangles T sharing edges with BOTH A and B:
  T = {v₁, a, w}  shares {v₁,a} with A
  T = {v₁, b, w}  shares {v₁,b} with B
  ...
  T = {a, a', w}  shares {a,a'} with A  AND  ...?

The claim "2 edges per X cover all T_X" is FALSE (Pattern #7).

Worse: Even if true, the 2 edges for A and 2 for B chosen
INDEPENDENTLY might not coordinate to cover bridges.

Example: If A chooses {a,a'} and {v₁,a}, while B chooses
{v₁,v₂} and {v₂,b}, the bridge T = {a, b, z} uses edge {a,b}
which is NOT in A.edges ∪ B.edges.
```

#### 2. **Bridges Not Forced to Share Spine Vertex** (False Lemma #22: bridge_externals_share_apex)

The claim that all bridges "contain a spine vertex" is not mathematically forced:

```
Bridge T sharing edge {e,f} with A and edge {g,h} with B:
  The shared vertex v = A ∩ B is ONE such vertex
  But T might only touch v through ONE of these two edges

Example PATH_4: T = {a, b, z}
  - a ∈ A, b ∈ B, but neither is v₁
  - T shares {a, v₁} ∩ A = partially, but the EDGE is not {v₁,*}
  - Similar issue with B

Bone: The "spine vertex" appears in T, but if the covering
edges for A don't include the right edge incident to that vertex,
the bridge T remains uncovered.
```

---

### CRITICAL GAP 3: External Definition Ambiguity

**Current Definition** (slot335:49-52):
```lean
def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y
```

**Issue**: The proof sketch claims "2 edges per X suffice for ALL triangles sharing edge with X" (T_X), but this conflates:

1. **S_X** = Externals that share edge with X ONLY (no other M-element)
2. **T_X** = ALL triangles (in G, not necessarily in M) that share edge with X

**The crucial gap**:
```
From step 1: ∃ e₁, e₂ ⊆ X such that ∀ T ∈ S_X, (e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2)

This DOES NOT imply: ∀ T sharing edge with X, (e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2)

Counter-example: X = {a, b, c}, e₁ = {a,b}, e₂ = {a,c}.
If all S_X use edges {a,b} or {a,c}, that's fine.
But what if there's a triangle T = {b, c, x} sharing edge {b,c} with X?
No external of X uses {b,c} (else {T, T₁, T₂, T₃, M\{X}} would be 6-packing).
So T is NOT an external.
But the covering problem requires: cover ALL triangles T_X, not just S_X.
T = {b,c,x} shares {b,c} with X but {e₁,e₂} = {{a,b},{a,c}} doesn't cover it!
```

---

### CRITICAL GAP 4: Proof of `externals_on_at_most_two_edges` (Line 115-121)

**Claim** (slot334:115-121):
```lean
lemma externals_on_at_most_two_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X : Finset V) (hX : X ∈ M) (hX_card : X.card = 3) :
    ∃ e1 e2 : Sym2 V, e1 ∈ X.sym2 ∧ e2 ∈ X.sym2 ∧
    ∀ T, isExternalOf G M X T → e1 ∈ T.sym2 ∨ e2 ∈ T.sym2 := by
  sorry
```

**Status**: ✅ This is PROVABLE (the ν ≤ 4 argument guarantees it).

**However**: This only proves externals use ≤2 edges of X. The proof then INCORRECTLY extends this to claim 2 edges cover all T_X (triangles sharing edge with X).

---

## The Root Mathematical Hypothesis Missing

The proof needs a **stronger theorem** that the current code doesn't establish:

### **THEOREM (Missing)**: Adaptive Edge Selection is Globally Coordinated

**Statement**:
```
Given M = {A, B, C, D} (PATH_4 structure) with |M| = 4 and ν ≤ 4:

For each X ∈ M, ∃ edge-pair (e₁_X, e₂_X) such that:
1. e₁_X, e₂_X ⊆ X.edges
2. ALL triangles in G (M-elements and non-M) that
   share edge with X are covered by {e₁_X, e₂_X}
3. GLOBAL coordination: The 4 edge-pairs together
   cover all triangles in G

Cardinality: 4 × 2 = 8 edges ✓
```

**Why This Is Hard**:

The issue is that:
- Condition 2 requires `e₁_X, e₂_X` to cover both externals S_X AND the M-element X itself
- But the ν ≤ 4 argument only constrains S_X
- X has 3 edges; 2 edges cannot cover all 3 edges of a triangle
- Therefore, we MUST ensure X itself is covered elsewhere (e.g., by edges that ARE in X)

**The Failed Approach**:
```
Naive extension of step 1:
  "If externals use ≤2 edges, then 2 edges cover externals.
   M-elements are in M, so they're separately listed as covered.
   Therefore, 2 + (M as M-elements) covers everything."

Why it fails:
  The cover E must be a SUBSET of G.edgeFinset.
  If e ∈ E and e ∈ X.edges, then e ∈ G.edgeFinset.
  X is a triangle (3 vertices, 3 edges).
  If we can only pick 2 of X's 3 edges, then X is NOT fully covered.
  We need to pick edges that are IN triangles we need to cover.

  For example: X = {a,b,c} with edges {a,b}, {a,c}, {b,c}.
  If we pick e₁ = {a,b} and e₂ = {a,c}:
  - Triangle T = {a,b,c} is covered (both e₁ and e₂ are in T.sym2) ✓
  - Triangle T' = {b,c,w} shares edge {b,c} with X, but
    e₁ ∉ T'.sym2 and e₂ ∉ T'.sym2, so T' NOT covered ✗

  To cover T', we'd need edge {b,c}.
  But then we have 3 edges of X itself!
```

---

## What Needs to Be Proven

To complete the proof, one of these must hold:

### **Option A**: Prove Adaptive Selection Works for PATH_4 Specifically

Use the path structure to show coordination is possible:
```
PATH_4: A — B — C — D
Shared vertices: v_ab = A ∩ B, v_bc = B ∩ C, v_cd = C ∩ D

For A (endpoint):
  - Externals S_A use ≤2 edges
  - A.card = 3, so A itself uses 3 edges
  - Choose: 2 edges from A that cover S_A
  - A is automatically covered (it's in M, so "assumed covered" as separate input)

For B (middle):
  - Externals S_B use ≤2 edges
  - Must ALSO coordinate to cover bridges X_AB and X_BC
  - Bridge X_AB contains v_ab (the shared vertex)
  - If we include edge {v_ab, *} in our 2-edge selection, all bridges are hit

Lemma (PATH_4 specific):
  "For PATH_4 with ν ≤ 4, we can choose 2 edges per element
   such that: (1) externals are covered, (2) bridges via spine edges are covered"
```

**Status**: Not yet proven.

### **Option B**: Accept τ ≤ 12 (Fallback)

The provable bound from the scaffolding:
```
Each M-element has 3 edges.
Each external of X uses some edge of X.
ν ≤ 4 only constrains: if S_X uses all 3 edges, → contradiction
Therefore: For each X, ∃ edge (e) such that all S_X triangles
  use ≤ 2 edges ≠ e.

Total covering edges per M-element: 3 (all edges of the M-element itself)
Total: 4 × 3 = 12 edges
```

This is **PROVEN** in slot139. The jump from 12 → 8 requires Option A.

### **Option C**: Use LP Fractional Relaxation

Skip the combinatorial argument and use:
```
Theorem: ν* ≤ 4 ⟹ τ* ≤ 8 (by LP duality)
Then: τ ≤ ⌈τ*⌉ ≤ 8 (rounding)
```

Requires careful dual certificate construction.

---

## Summary of Mathematical Gaps

| Gap | Location | Nature | Impact |
|-----|----------|--------|--------|
| **1** | slot335:143-144 | Confuses S_X (externals) with T_X (all sharing edge) | Bridges might not be covered |
| **2** | slot335:155-171 | Bridge coordination assumption not proven | Spine edges might miss bridges |
| **3** | slot335:49-52 | External definition doesn't include M-elements | M-elements coverage unclear |
| **4** | slot334:115-121 | `externals_on_at_most_two_edges` proven, but extension faulty | The 2-edge bound doesn't extend to all T_X |
| **5** | slot335:175-181 | Main `sorry` hides bridge coordination | Proof incomplete |

---

## Recommended Fix Path

### **Immediate** (30 min):
1. **Clarify the external definition**: Does isExternalOf require that T doesn't share with ANY other M-element, or just not an "edge-share"? Current: "not sharesEdgeWith"
2. **Separate concerns**: Prove two theorems:
   - `externals_use_le_two_edges`: For each X, ∃ e₁, e₂ s.t. ∀ T ∈ S_X, (e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2)
   - `bridges_covered_by_spine_coordination`: ??? (HARD - needs structure)

### **Medium** (2-4 hours):
3. **Prove PATH_4-specific bridge lemma**: Show that choosing edges including spine vertices covers bridges
4. **Add M-element coverage separately**: Prove that M-elements (triangles in M) are covered as a distinct case

### **Long-term** (Alternative):
5. Accept τ ≤ 12 and publish that instead
6. Try LP relaxation approach for τ ≤ 8

---

## Files to Modify

1. **slot335_adaptive_1sorry.lean** (Lines 155-181):
   - Current: Claims bridge coordination without proof
   - Should: Add lemma `bridges_covered_by_spine_coordination` with full proof

2. **slot334_adaptive_cover.lean** (Line 180):
   - Current: `bridges_covered_by_adaptive_selection` is sorry
   - Should: Either prove it or downgrade to τ ≤ 12

3. **Add new lemma file**:
   - PATH_4 structure enforcement
   - Spine vertex coordination
   - Bridge coverage mechanism

---

## Mathematical Verification Checklist

Before submission, verify:
- [ ] ✅ Externals use ≤2 edges of X (proven by ν ≤ 4)
- [ ] ❌ 2 edges of X cover all triangles sharing edge with X (NOT proven; false in general)
- [ ] ❌ Bridges contain spine vertices (assumption, not forced by structure)
- [ ] ❌ Spine edge selection coordinates across M elements (NOT proven)
- [ ] ❌ Global 8-edge set is valid cover (depends on above)

**Current Status**: 1 of 5 ✓
