# Lemma 4: fan_apex_exists - Concrete Mathematical Examples

## Example 1: Complete Graph K₃ (Vacuous)

### Setup
```
G = K₃: vertices {0, 1, 2}
Edges: {0,1}, {1,2}, {2,0} (complete triangle)

Maximum packings: M = {{0,1,2}} (only one triangle possible)
```

### Analysis
```
A = {0,1,2}
Externals of A: None (no other triangles exist in K₃)

hExt_nonempty: False → theorem vacuously true
```

### Verdict
✓ Vacuous case, theorem satisfied

---

## Example 2: Complete Graph K₄

### Setup
```
G = K₄: vertices {0, 1, 2, 3}
Edges: All pairs (complete)

K₄ contains 4 triangles:
  T1 = {0, 1, 2}
  T2 = {0, 1, 3}
  T3 = {0, 2, 3}
  T4 = {1, 2, 3}

Maximum packing size: ν(K₄) = 1 (any two triangles share edge)
Actually: Any two distinct triangles in K₄ intersect in ≥2 vertices
So maximum packing M.card ≤ 1

But ν = 4 problem requires M.card = 4, so K₄ is NOT relevant for ν=4 case.
```

### Why K₄ doesn't apply
For the ν=4 case, we need graphs where ν(G) = 4. K₄ has ν = 1, so it doesn't appear.

---

## Example 3: K₅ (The Interesting Case)

### Setup
```
G = K₅: vertices {0, 1, 2, 3, 4}

Total triangles: C(5,3) = 10
  {0,1,2}, {0,1,3}, {0,1,4}, {0,2,3}, {0,2,4}, {0,3,4},
  {1,2,3}, {1,2,4}, {1,3,4}, {2,3,4}

Maximum packing: ν(K₅) = 2
Example: M = {{0,1,2}, {0,3,4}} (disjoint triangles)
```

### Applying Lemma 4
```
M = {{0,1,2}, {0,3,4}}
A = {0,1,2}

Edges of A: {0,1}, {1,2}, {2,0}

Externals of A (triangles sharing edge with A, not in M, not sharing edge with other M):
  Check {0,1,3}:
    - Shares edge {0,1} with A ✓
    - Shares vertex 0 with B={0,3,4}, but edge {0,3} or {0,4}?
    - {0,1,3} ∩ {0,3,4}: vertices {0,3}, edges {0,3} ✓ (shares edge with B ✗)
    - So {0,1,3} is NOT an external (shares edge with both A and B)

  Check {1,2,3}:
    - Shares edge {1,2} with A ✓
    - Shares vertices with B={0,3,4}: only vertex 3
    - {1,2,3} ∩ {0,3,4} = {3} (only 1 vertex, no edge) ✓
    - So {1,2,3} IS an external of A

  Check {0,2,3}:
    - Shares edge {0,2} with A ✓
    - Shares vertices with B={0,3,4}: vertices {0,3}
    - Edges {0,3}: edge of B? B = {0,3,4} has edges {0,3}, {0,4}, {3,4}
    - {0,3} is edge of B ✗
    - So {0,2,3} is NOT an external

  Check {2,3,4}:
    - Shares vertices with A={0,1,2}: only vertex 2 (no edge) ✓
    - Shares vertices with B={0,3,4}: vertices {3,4}
    - Edges {3,4}: edge of B ✓
    - So {2,3,4} is NOT an external (doesn't share edge with A)
```

### Problem: K₅ with 2-packing doesn't have externals!

For lemma to apply, we need M.card = 4, but K₅ has ν = 2.

---

## Example 4: Cycle_4 Graph (The Actual Case)

### Hypothetical Construction

Let me construct a graph G where:
- ν(G) = 4 (maximum packing has 4 elements)
- M = {A, B, C, D} is a maximal packing

One such construction: Petersen-like graph or circulant.

For simplicity, consider an abstract graph with:
```
Vertices: {v_ab, v_bc, v_cd, v_da, a_priv, b_priv, c_priv, d_priv}

M-elements (disjoint triangles):
  A = {v_ab, v_da, a_priv}
  B = {v_bc, v_ab, b_priv}
  C = {v_cd, v_bc, c_priv}
  D = {v_da, v_cd, d_priv}

Shared vertices:
  v_ab = A ∩ B
  v_bc = B ∩ C
  v_cd = C ∩ D
  v_da = D ∩ A

These form a cycle: A ↔ B ↔ C ↔ D ↔ A
```

### Applying Lemma 4 to Element A

```
A = {v_ab, v_da, a_priv}
Edges of A: {v_ab, v_da}, {v_da, a_priv}, {a_priv, v_ab}

Now: What are the externals of A?
(Triangles sharing an edge with A, but not in M and not sharing edge with B, C, D)

Candidates:
1. {v_ab, v_da, x} for some external x
   - Shares edge {v_ab, v_da} with A ✓
   - Need x ≠ a_priv and T doesn't share edge with B, C, D
   - B shares vertex v_ab with A. If T = {v_ab, v_da, x}:
     - T ∩ B ⊇ {v_ab}
     - If x ∈ B, then T might share edge with B
     - B = {v_bc, v_ab, b_priv}
     - For T to share edge with B: need 2 vertices of T in B
     - T shares {v_ab} with B. Need another: x ∈ {v_bc, b_priv}?
     - If x = v_bc or x = b_priv, then shares edge
     - So x ∉ {v_bc, b_priv}
   - Similarly, D shares vertex v_da with A
     - D = {v_da, v_cd, d_priv}
     - T ∩ D ⊇ {v_da}
     - If T = {v_ab, v_da, x}, for shared edge need x ∈ {v_cd, d_priv}
     - So x ∉ {v_cd, d_priv}

   So external of form {v_ab, v_da, x} requires x ∉ {a_priv, v_bc, b_priv, v_cd, d_priv}

2. {v_da, a_priv, x} for some external x
   - Shares edge {v_da, a_priv} with A
   - Constraint: x avoids shared vertices with B, C, D

3. {a_priv, v_ab, x} for some external x
   - Shares edge {a_priv, v_ab} with A
   - Similar constraints

### Applying Fan Apex Theorem

If externals exist, they pairwise share edges (by slot182).

Consider T₁ = {v_ab, v_da, x₁} and T₂ = {v_da, a_priv, x₂}
- Both externals of A
- Both contain v_da (common to two edges of A)
- T₁ ∩ T₂ ⊇ {v_da}
- They share an edge (by slot182)
- Edge must include v_da, so edge is {v_da, u} for u ∈ T₁ ∩ T₂
- T₁ ∩ T₂ = {v_da} ∪ (other shared vertices)
- If T₁ = {v_ab, v_da, x₁} and T₂ = {v_da, a_priv, x₂}
- Shared vertices: {v_da, ...}
- If x₁ = x₂, then shared edge could be {v_da, x₁}
- If x₁ ≠ x₂, then for shared edge we need another common vertex
  - T₁ has {v_ab, v_da, x₁}
  - T₂ has {v_da, a_priv, x₂}
  - Common: {v_da} + possibly others
  - For 2 shared vertices: need {v_da, u} where u ∈ {v_ab, x₁} ∩ {a_priv, x₂}
  - u = v_ab: but v_ab ∉ {a_priv, x₂} (external condition)
  - u = a_priv: but a_priv ∉ {v_ab, x₁} (since T₁ doesn't contain A's private vertex from that edge)
  - u = x₁ = x₂: must be equal

So x₁ = x₂!

By similar reasoning with other externals, all contain same x.

### Conclusion

All externals of A share a common external vertex x (the fan apex).
Spoke edges {v_ab, x}, {v_da, x}, {a_priv, x} cover all externals.
τ(externals of A) ≤ 3 ✓
```

---

## Example 5: The Helly Counterexample (Pattern 16)

### Setup
```
Triangles T₁, T₂, T₃ with pairwise edge-sharing but NO common edge
```

### The Counterexample
```
T₁ = {a, b, x}
T₂ = {b, c, x}
T₃ = {a, c, x}

Edges:
  T₁: {a,b}, {b,x}, {a,x}
  T₂: {b,c}, {c,x}, {b,x}
  T₃: {a,c}, {a,x}, {c,x}

Pairwise edges:
  T₁ ∩ T₂: {b, x} → share edge {b,x} ✓
  T₂ ∩ T₃: {c, x} → share edge {c,x} ✓
  T₃ ∩ T₁: {a, x} → share edge {a,x} ✓

Common to all: T₁ ∩ T₂ ∩ T₃ = {x}
Common EDGE: None! (Each pair uses different edge of x)

This DISPROVES Pattern 16: Pairwise edge-sharing ≠> common edge
```

### But Lemma 4 is Different

```
For Lemma 4: T₁, T₂, T₃ are all externals of SAME A = {a, b, c}
  - T₁ shares edge {a, b}
  - T₂ shares edge {b, c}
  - T₃ shares edge {a, c}

All three contain x = common fan apex

Lemma 4 claims: x exists (vertex) ✓
Lemma 4 does NOT claim: common edge exists ✓

So Lemma 4 AVOIDS Pattern 16 trap by claiming vertex, not edge.
```

---

## Example 6: Same Fan Apex for Different A-Edges

### Setup
```
A = {a, b, c}
Edges: {a,b}, {b,c}, {c,a}

Three externals using different edges but same apex x:
  T₁ = {a, b, x}  (uses edge {a,b})
  T₂ = {b, c, x}  (uses edge {b,c})
  T₃ = {c, a, x}  (uses edge {c,a})

Note: This is the fan structure!
```

### Verification by Slot182

```
T₁ and T₂ share edge {b,x}?
  T₁ ∩ T₂ = {b, x} (cardinality 2) → potential edge
  Need: b and x both in T₁ (✓) and both in T₂ (✓)
  So yes, they share edge {b,x} ✓

T₂ and T₃ share edge {c,x}?
  T₂ ∩ T₃ = {c, x} → yes, share {c,x} ✓

T₃ and T₁ share edge {a,x}?
  T₃ ∩ T₁ = {a, x} → yes, share {a,x} ✓

Pairwise edge-sharing verified! (consistent with slot182)
All contain x! (consistent with Lemma 4) ✓
```

### Why Slot182 is Satisfied

Slot182 says: Two externals of A share an edge.
Here: All pairs share edges through x ✓

This is the natural structure where externals of A are spread around using different edges of A, but all pass through a common external vertex x.

---

## Example 7: Non-Fan Structure (Slot182 Violation)

### Hypothetical Counterexample Attempt

```
Can we construct externals T₁, T₂ of A that DON'T share an edge?
Suppose:
  A = {a, b, c}
  T₁ = {a, b, x₁} (shares edge {a,b})
  T₂ = {b, c, x₂} (shares edge {b,c})
  x₁ ≠ x₂

Do T₁ and T₂ share an edge?
  T₁ ∩ T₂ = ?
  T₁ has {a, b, x₁}
  T₂ has {b, c, x₂}
  Common: {b}
  Cardinality 1!

NO shared edge → This violates slot182!
```

### Why Slot182 Prevents This

If T₁, T₂ don't share an edge:
- Then {T₁, T₂} ∪ (M \ {A}) is a 5-packing
- But ν = 4, so maximum packing is size 4
- Contradiction!

Therefore: T₁ and T₂ MUST share an edge.

### The Only Way to Satisfy Slot182

```
For T₁ = {a, b, x₁} and T₂ = {b, c, x₂} to share an edge:
  - Shared edge must have 2 vertices in both T₁ and T₂
  - Common vertices: b + either (a or x₁) and (c or x₂)
  - Possibilities:
    1. {b, c}: needs c ∈ T₁, but T₁ = {a, b, x₁}
       → requires x₁ = c, but c ∉ A private vertices
       → NOT possible in external context

    2. {b, a}: needs a ∈ T₂, but T₂ = {b, c, x₂}
       → requires x₂ = a, contradicts x₂ ∉ A
       → NOT possible

    3. {b, x₁}: needs x₁ ∈ T₂
       → x₁ ∈ {b, c, x₂}
       → x₁ = x₂ (since x₁ ≠ b, x₁ ≠ c)
       → FORCED: x₁ = x₂

    4. {b, x₂}: needs x₂ ∈ T₁
       → x₂ ∈ {a, b, x₁}
       → x₂ = x₁ (since x₂ ≠ a, x₂ ≠ b)
       → FORCED: x₁ = x₂

CONCLUSION: Slot182 + triangle structure FORCES x₁ = x₂
This is the algebraic content of Lemma 4!
```

---

## Example 8: Multiple Externals, All Forced to Same Apex

### Setup
```
A = {0, 1, 2}
M-element B = {1, 2, 3} (shares edge {1,2} with A)

Externals of A (avoid sharing with B):
  E₁ = {0, 1, x}  (uses edge {0,1} of A)
      Avoids B: Need x ∉ {1,2,3}, so x ∉ {3}

  E₂ = {1, 2, y}  (uses edge {1,2} of A)
      But B = {1, 2, 3} shares edge {1,2}
      E₂ would share edge {1,2} with B → NOT external ✗

  E₃ = {0, 2, z}  (uses edge {0,2} of A)
      Avoids B: Need z ∉ {1,2,3}

So: Only externals using edges {0,1} and {0,2} are possible.
```

### Case: x = z (Same apex for all externals)

```
E₁ = {0, 1, x}
E₃ = {0, 2, x}

Slot182: Do E₁ and E₃ share an edge?
  E₁ ∩ E₃ = {0, x}
  If x ≠ 0: cardinality 2 → share edge {0,x} ✓

Lemma 4: Both contain x ✓
Corollary: τ(E₁, E₃) ≤ 2 (edges {0,x}, {1,x}, {2,x}, but need only {0,x}, {1,x}, {2,x})
Wait: E₁ = {0,1,x}, E₃ = {0,2,x}
  Cover E₁: need edge with both 0,1 → {0,1}
  Cover E₃: need edge with both 0,2 → {0,2}
  But {0,1}, {0,2} are edges of A, not external!

Better: Use spoke edges {0,x}, {1,x}, {2,x}
  E₁ = {0,1,x} covered by {0,x} or {1,x}
  E₃ = {0,2,x} covered by {0,x} or {2,x}
  Total 2 edges {0,x}, {1,x}, {2,x} = 3 edges max
```

---

## Summary of Examples

| Example | Case | Fan Apex | Status |
|---------|------|----------|--------|
| K₃ | Vacuous (no externals) | N/A | ✓ Theorem satisfied |
| K₄ | Not ν=4 | N/A | ✗ Doesn't apply |
| K₅ with 2-packing | Not enough elements | N/A | ✗ Doesn't apply |
| Cycle_4 abstract | Lemma applies | x ∉ A | ✓ Sound |
| Pattern 16 counterexample | Shows Helly fails | (still x exists) | ✓ Lemma claims vertex ✓ |
| Same apex for 3 externals | Explicit fan | x = apex | ✓ Sound |
| Slot182 violation attempt | Forced to same x | x | ✓ Algebra forces it |
| Multiple externals, constrained | Practical case | x | ✓ Works |

---

## Key Insight from Examples

The examples show that:

1. **Slot182 is the KEY**: Forces pairwise edge-sharing
2. **Triangle structure does the REST**: Only one way to satisfy edge-sharing is to have common vertex
3. **Fan apex is INEVITABLE**: Once you have pairwise edge-sharing and triangle constraint, common vertex must exist
4. **Avoids Helly by design**: Doesn't claim common edge, just common vertex

---

**Conclusion**: Lemma 4 is the natural algebraic consequence of slot182 + triangle geometry. The examples make the proof strategy concrete and verifiable.
