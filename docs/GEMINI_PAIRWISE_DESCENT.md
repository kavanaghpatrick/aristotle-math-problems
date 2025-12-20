# Gemini Analysis: Pairwise Descent Strategy

## Context

After Aristotle proved `tau_X_le_2'` and `mem_X_implies_v_in_t`, we asked Gemini for the most promising approach to ν=4.

## Gemini's Key Insight

> The standard "Parker" approach fails because it attempts a **local descent of 1** (ν → ν-1) which requires finding a single e with τ(T_e) ≤ 2. The K_6 obstruction proves such an e does not always exist.
>
> However, the K_6 obstruction has a weakness: it is a small, dense cluster.

### The Winning Strategy: Pairwise Descent (Induction by 2)

Instead of searching for one edge e to remove, we should search for a **pair of intersecting triangles** {e, f} to remove simultaneously.

If we remove two triangles {e, f}, the packing number drops by at least 2 (ν' ≤ ν - 2).
We allow ourselves a cost of 2 × 2 = 4 edges.

Thus, the condition to satisfy Tuza becomes:
```
τ(T_e ∪ T_f) ≤ 4
```

## Mathematical Proof Strategy

### Step 1: The "Disjoint or Share" Dichotomy

Prove that in any maximum packing P with ν ≥ 2:

1. **Case A:** There exists an e that is vertex-disjoint from all other f ∈ P.
   - Result: T_e = S_e (no overlaps). We have τ(S_e) ≤ 2, so standard induction works.

2. **Case B:** Every e shares a vertex with at least one other f.
   - Result: We can always find a pair {e, f} with |e ∩ f| = 1.

### Step 2: The Pairwise Union Bound (The Core Lemma)

**Lemma: tau_union_le_4**

Given disjoint triangles e, f sharing exactly one vertex v:
```
τ(T_e ∪ T_f) ≤ 4
```

**Proof Sketch using proven lemmas:**

Decompose T_e ∪ T_f into three sets:
1. S_e (Private to e)
2. S_f (Private to f)
3. X(e,f) (The overlap)

We know from `mem_X_implies_v_in_t` that every triangle in X(e,f) contains v.
We know from `tau_S_le_2` that S_e can be covered by 2 edges, and S_f by 2 edges.

The key insight: covering X(e,f) using edges incident to v may overlap with covers for S_e and S_f.

- Let E_v(e) be the two edges of e touching v.
- Picking E_v(e) covers X(e,f) AND covers "half" of S_e.
- We can complete the cover of S_e and S_f without exceeding 4 edges total.

### Step 3: Density Compensation

If τ(S_e) = 2, S_e is "heavy" (triangles on all sides).
If S_e is heavy, it limits how many triangles can be in X(e,f) without violating maximum packing.

Possible lemma: "If S_e is complex (needs 2 edges), X(e,f) is simple."

### Step 4: The Algorithm

1. **Check for Isolated e:** If found, remove e (τ ≤ 2).
2. **Check for Pair {e,f}:** If found, remove both (τ ≤ 4).
3. **Residual:** Apply induction.

## Why This Works for K_6

In K_6 with 4 edge-disjoint triangles:
- Every e shares vertices with ALL other triangles
- Pick any pair {e₁, e₂} sharing vertex v
- τ(T_{e₁} ∪ T_{e₂}) ≤ 4
- Residual has ν ≤ 2
- τ(residual) ≤ 4 (by known ν ≤ 2 result)
- Total: 4 + 4 = 8 ✓

## Submissions Created

1. `tuza_nu4_pairwise_descent.lean` - Full strategy with all cases (submitted b0891cdd)
2. `tuza_tau_union_minimal.lean` - Focused on just tau_union_le_4 lemma (ready)
3. `tuza_pairwise_informal.md` - Informal proof sketch (ready)
