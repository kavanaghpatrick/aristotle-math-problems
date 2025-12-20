# Tuza ν≤3: Gap Analysis

## What We Have (All Proven, 0 Sorry)

### Definitions
```
T_e = trianglesSharingEdge G e = triangles sharing ≥2 vertices with e
S_e = S G e M = triangles in T_e that DON'T share ≥2 vertices with any OTHER m ∈ M

Relationship: S_e ⊆ T_e
Difference: T_e \ S_e = triangles sharing edge with e AND with some other m ∈ M
```

### Key Lemmas

| Lemma | Statement | Use |
|-------|-----------|-----|
| `lemma_2_2` | Triangles in S_e pairwise share edges | S_e is pairwise intersecting |
| `lemma_2_3` | ν(rest) = ν - 1 | Induction hypothesis applies |
| `inductive_bound` | τ(G) ≤ τ(T_e) + τ(rest) | Main decomposition |
| `intersecting_family_structure` | Pairwise intersecting → star OR K4 | Structure of S_e |
| `tau_star` | τ(star) ≤ 1 | Cover star with one edge |
| `covering_number_on_le_two_of_subset_four` | τ(K4 triangles) ≤ 2 | Cover K4 with two edges |
| `tau_S_le_2` | τ(S_e) ≤ 2 | **Key result for S_e** |
| `tuza_case_nu_0` | ν=0 → τ=0 | Base case |

## The Gap

### What We Need
```
τ(G) ≤ 2ν for ν ≤ 3
```

### Proof Attempt (Why It Fails)
```
1. Pick max packing M, pick e ∈ M
2. By inductive_bound: τ(G) ≤ τ(T_e) + τ(rest)
3. By lemma_2_3: ν(rest) = ν - 1
4. By IH: τ(rest) ≤ 2(ν-1)
5. NEED: τ(T_e) ≤ 2
6. HAVE: τ(S_e) ≤ 2 (but S_e ⊆ T_e, so this doesn't help directly!)
```

### The Missing Piece
We need: **τ(T_e) ≤ 2** (or equivalent)

Options:
1. Show T_e = S_e for some choice of e when ν ≤ 3
2. Show τ(T_e) ≤ 2 directly via different argument
3. Use different decomposition that uses S_e instead of T_e

## Why ν ≤ 3 Matters

### Case ν = 1
- M = {e}, no other elements
- S_e = T_e (nothing to exclude)
- τ(T_e) = τ(S_e) ≤ 2 ✓

### Case ν = 2
- M = {e, f}
- S_e = triangles sharing edge with e but NOT with f
- T_e \ S_e = triangles sharing edge with BOTH e and f
- Question: Can τ(T_e) > 2?

### Case ν = 3
- M = {e, f, g}
- S_e = triangles sharing edge with e but not with f or g
- T_e \ S_e = triangles sharing edge with e AND (f or g)
- More complex structure

## Parker's Approach (from paper)

Parker proves: For ν ≤ 3, **there exists** e ∈ M such that τ(T_e) ≤ 2.

Key insight: Not ALL e work, but we can CHOOSE e wisely.

The choice involves analyzing the structure of how triangles overlap with M elements.

## What's Needed to Complete

### Option A: Prove τ(T_e) ≤ 2 for some e
Need lemma:
```lean
lemma exists_e_with_tau_Te_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hnu : M.card ≤ 3) :
    ∃ e ∈ M, triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2
```

### Option B: Different decomposition
Reformulate inductive_bound to use S_e instead of T_e, with careful handling of T_e \ S_e.

### Option C: Direct case analysis
Prove ν=1, ν=2, ν=3 separately without general induction.
- ν=1: Done (S_e = T_e)
- ν=2: Direct analysis of two packing triangles
- ν=3: Direct analysis of three packing triangles

## Recommendation

Submit to Aristotle with explicit request to prove:
1. `τ(T_e) ≤ 2` when ν ≤ 3, OR
2. Case-by-case proofs for ν = 1, 2, 3

The formalized lemmas provide the infrastructure; we just need the final connection.
