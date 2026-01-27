# Adaptive Proof: Specific Counterexamples to Key Claims

## Overview

The adaptive selection proof (slot335/slot334) claims that for PATH_4 with ν ≤ 4, choosing 2 edges per M-element yields an 8-edge cover. Below are concrete counterexamples showing where this approach breaks down.

---

## Counterexample 1: Two Edges Cannot Cover a Triangle + Externals

### Setup

```
X = {a, b, c}  (a 3-clique)
Edges of X: e₁={a,b}, e₂={a,c}, e₃={b,c}

External triangles in S_X:
  T₁ = {a, b, x₁}  -- shares edge e₁={a,b}
  T₂ = {a, c, x₂}  -- shares edge e₂={a,c}
  T₃ = {b, c, x₃}  -- shares edge e₃={b,c}
```

### Proof Strategy (slot335:138-139)

**Claim**: "We can choose 2 edges of X that cover all S_X triangles."

**Proof**: "Simply pick one edge from each populated edge type."

**Analysis**:
- If only T₁ and T₂ exist (using edges e₁, e₂), then: Choose E_X = {e₁, e₂}
- T₁: e₁ ∈ T₁.sym2 ✓
- T₂: e₂ ∈ T₂.sym2 ✓
- S_X covered ✓

**But the problem comes from the next step:**

### Where It Breaks (slot335:143-149)

**Claim**: "If our 2 edges for X cover all S_X triangles, bridges are covered too."

**Reality**: The covering must also include the M-element X itself!

```
Triangles in G that need covering (assuming no bridges for now):
  X = {a, b, c}              (in M)
  T₁ = {a, b, x₁}            (external)
  T₂ = {a, c, x₂}            (external)
  T₃ = {b, c, x₃}            (external)
  (possibly) T₄ = {a, b, x₁'} (another external on e₁)
  ...

Cover chosen: E_X = {e₁={a,b}, e₂={a,c}}

Check coverage:
  X:  Both e₁ and e₂ are in X.sym2 ✓
  T₁: e₁ ∈ T₁.sym2 ✓
  T₂: e₂ ∈ T₂.sym2 ✓
  T₃: e₃ = {b,c} ∉ E_X, and e₁, e₂ ∉ T₃.sym2 ✗✗✗

Triangle T₃ is NOT covered!
```

### Why the Proof Sketch Is Wrong

The comment at slot335:145-149 admits the issue:

```lean
/- "But wait - we chose edges to cover EXTERNALS (S_X), not all T_X triangles.
   Key insight: A bridge B sharing edge with X and Y is NOT in S_X
   (it also shares with Y). However, B IS in T_X
   (triangles sharing edge with X)." -/
```

**The author recognized the gap but then failed to close it.**

The "fix" in STEP 5 (lines 155-171) claims spine edges will handle bridges, but provides no proof.

---

## Counterexample 2: Bridges Don't Always Contain Spine Vertices

### Setup (Detailed PATH_4)

```
M = {A, B, C, D} with PATH_4 structure:
  A = {v₁, a, a'}
  B = {v₁, v₂, b}
  C = {v₂, v₃, c}
  D = {v₃, d, d'}

Spine vertices: v₁, v₂, v₃
Shared vertices:
  v_ab = A ∩ B = {v₁}
  v_bc = B ∩ C = {v₂}
  v_cd = C ∩ D = {v₃}
```

### Bridge Triangle Issue

**Claim** (slot335:157-161): "Every bridge B contains a shared vertex v ∈ X ∩ Y."

**True**: By definition, a bridge shares edges with two M-elements.

**But**: The "spine edge" argument assumes that an edge **incident to v** is in our chosen E_X.

### Concrete Counterexample

```
Suppose:
  - A chooses edges E_A = {a,a'} (the base edge of A, not involving v₁)
  - B chooses edges E_B = {v₁,v₂} (the spine edge connecting B's shared vertices)
  - C chooses edges E_C = {v₂,v₃}
  - D chooses edges E_D = {d,d'}

Bridge T = {a, b, z} where:
  - {a, v₁} ⊆ A, so T shares the edge {a, v₁} with A?
    No! T = {a, b, z}, and A ∩ T = {a} (only 1 element)
    So T doesn't share an edge with A (needs 2 shared elements)

Let me reconsider: T = {a, v₁, z} where a ∈ A, v₁ ∈ B
  - T shares edge {a, v₁} ⊆ A ∩ T = {a, v₁} ✓ (2 elements)
  - T shares edge {v₁, z}? Only if z ∈ B. Say z = b ∈ B.
  - So T = {a, v₁, b} shares {a,v₁} with A and {v₁,b} with B (bridge)

Coverage:
  - Edge {a,v₁} ∈ T.sym2. Is {a,v₁} ∈ E_A?
    E_A = {a,a'}, so {a,v₁} ∉ E_A ✗
  - Is {a,v₁} ∈ E_B?
    E_B = {v₁,v₂}, so {a,v₁} ∉ E_B ✗
  - Other edges: {a,b} (not in M), {v₁,b} ∈ B.sym2
    Is {v₁,b} ∈ E_B? Only if we chose it.
    E_B = {v₁,v₂}, so {v₁,b} ∉ E_B ✗

Triangle T = {a, v₁, b} is NOT covered!
```

### Why This Happens

The issue is that:
1. **E_A ⊆ A.edges** (by design): E_A consists of edges within A only
2. **E_B ⊆ B.edges** (by design): E_B consists of edges within B only
3. **Bridge T = {a, v₁, b}** has edges:
   - {a, v₁}: one endpoint in A, one in B (NOT both in A, NOT both in B)
   - {a, b}: both outside both A's {v₁, a, a'} and B's {v₁, v₂, b}
   - {v₁, b}: one in A ∩ B = {v₁}, one in B only

**T.sym2 contains no edge in A.edges ∪ B.edges!**

The proof assumes {v₁, *} ∈ E_B will hit T, but T only has edge {v₁, b} incident to v₁, and if E_B = {v₁, v₂}, then {v₁, b} ∉ E_B.

---

## Counterexample 3: The Three Edge Types Problem (From False Lemma #6)

### Setup

```
M = {A={0,1,2}, B={0,3,4}, C={3,7,8}, D={7,1,9}}

At shared vertex v_ab = 0:
  A ∩ B = {0}
  Edges of A: {0,1}, {0,2}, {1,2}
  Edges of B: {0,3}, {0,4}, {3,4}

Edges containing 0 across A,B:
  From A: {0,1}, {0,2}  (the "spokes" from v_ab into A)
  From B: {0,3}, {0,4}  (the "spokes" from v_ab into B)
```

### The Claim (Disproven)

**Claim** (implicit in the adaptive proof): "External triangles at v_ab share a common external vertex x."

**Result** (False Lemma #6): Disproven by counterexample.

**What This Means**:
If externals T₁, T₂ at v_ab don't share a common external vertex, then:
- T₁ = {0, 1, 5}  (external to both A and B)
- T₂ = {0, 3, 6}  (external to both A and B)
- T₁ ∩ T₂ = {0} (only the shared vertex)

To cover both with 2 edges incident to 0:
- Edge {0, 5}: covers T₁ (since {0,5} ⊆ T₁ = {0,1,5}? No, {0,5} uses 0,5 but is that in the triangle? Yes if 5 ∈ T₁.)
- Wait, T₁ = {0, 1, 5} has sym2 = {{0,1}, {0,5}, {1,5}}
- If E_A = {{0,1}, {0,2}}, then {0,5} ∉ E_A

**The external vertex 5 ∉ A ∪ B, so no edge incident to 5 is in A.edges ∪ B.edges!**

---

## Counterexample 4: M-Elements Require Separate Coverage

### The Hidden Assumption

The proof at slot335 treats M-elements as "separately covered" (they're in M, so assumed given). But the **covering problem** asks: what is a **minimal edge set E ⊆ G.edgeFinset** such that **every triangle in G is covered**?

### Example

```
M = {A={a,b,c}}  (a single triangle for simplicity)
External: T₁ = {a,b,x}

Covering requirement:
  - Cover A = {a,b,c}: need edges from {a,b}, {a,c}, {b,c}
  - Cover T₁ = {a,b,x}: need edges from {a,b}, {a,x}, {b,x}

If we choose E = {{a,b}, {a,c}} (covering A):
  - A: both edges in A.sym2 ✓
  - T₁: {a,b} ∈ T₁.sym2 ✓

If we choose E = {{a,b}} (to cover externals):
  - A: only one edge covered
    Remaining edges {a,c}, {b,c} not in E
    So A is NOT fully covered ✗
  - T₁: {a,b} ∈ T₁.sym2 ✓

For both to be covered, we need at least:
  - One edge in each "pair" that forms an edge of A: at least 2 edges
  - Potentially one edge for T₁ if it's not already covered

The adaptive proof claims "2 per M-element" but:
  - 2 edges might not cover the M-element itself
  - 2 edges might not cover externals if they use all 3 edges
  - The ν≤4 constraint prevents all 3 edges being used by externals
  - But that doesn't mean 2 edges suffice!
```

---

## Counterexample 5: Why the Bridge Argument Fails

### PATH_4 Specific Issue

```
PATH_4: A — B — C — D
Bridge X_AB shares edge with both A and B

If we independently choose:
  E_A = {edge₁_A, edge₂_A}  (chosen to cover S_A)
  E_B = {edge₁_B, edge₂_B}  (chosen to cover S_B)

Bridge T = {x_A, x_B, z} where:
  - x_A ∈ A (not a spine vertex), x_B ∈ B (not a spine vertex)
  - T shares edge {x_A, v_ab} with A? Only if x_A is in T and v_ab is in T
  - But we can construct T such that:
    - {x_A, x_B} ⊆ T (bridge uses both private elements)
    - {v_ab, z} ⊆ T (uses spine and external)

Then T.sym2 ∩ (A.edges ∪ B.edges) = ∅ (no edge of T is within A or B)
```

### The Coordination Problem

The proof fails because:
1. **Independently chosen E_A and E_B don't coordinate** to cover bridges
2. **Spine edges are not guaranteed to be in E_B** (Aristotle only proved externals use ≤2 edges, not which 2)
3. **Bridge triangles can avoid spine vertices** by using private elements

---

## Mathematical Lessons

### What's Provable
- ✅ ν ≤ 4 ⟹ externals at X use ≤ 2 of X's 3 edges
- ✅ This contradicts all 3 edges being used (5-packing argument)

### What's NOT Provable (and counterexampled)
- ❌ 2 edges per X suffice to cover ALL T_X (need 3 edges for X itself)
- ❌ Bridges always contain spine vertices (can use private + external)
- ❌ Spine edges alone cover all bridges (need coordination)
- ❌ Independent 2-edge selections per X compose into global cover

### The Real Question
**Can we choose 2 edges per X such that globally they form an 8-edge cover?**

Answer: **UNKNOWN** - requires structured proof that the adaptive choices coordinate.

The false lemma database (pattern #7, #17, #22) collectively show that naive approaches fail.

---

## Recommendation

The adaptive proof is **not ready for submission**. Before claiming τ ≤ 8, you must:

1. **Prove the bridge coordination lemma explicitly**:
   ```lean
   lemma bridges_covered_by_adaptive_selection
       (M : Finset (Finset V))
       (hpath : isPath4 M A B C D)
       (E_A E_B E_C E_D : Finset (Sym2 V))
       (h : ∀ X ∈ M, ∃ E ⊆ X.edges, |E| = 2 ∧
            ∀ T ∈ G.cliqueFinset 3 sharing edge with X,
            ∃ e ∈ E, e ∈ T.sym2) :
       -- Then 8 edges total suffice
   ```

2. **Or accept τ ≤ 12** (which is proven in slot139, 0 sorry, 0 axiom)

3. **Or pivot to LP fractional method** (more robust but requires dual certificate)
