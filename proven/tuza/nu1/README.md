# Tuza ν=1: Two Edges Suffice

## Theorem

```lean
lemma nu_eq_1_implies_tau_le_2 (h : trianglePackingNumber G = 1) :
    triangleCoveringNumber G ≤ 2
```

## Statement

If a graph has packing number ν = 1 (i.e., any two triangles share an edge), then at most 2 edges are needed to cover all triangles.

## Proof Strategy

When ν(G) = 1, any two triangles must share an edge (otherwise we'd have a packing of size 2).

This means all triangles form a "pairwise edge-sharing" family. Such families have a special structure:

**Case 1**: All triangles share a common edge {u, v}
- Cover with just 1 edge: {u, v}

**Case 2**: No common edge exists
- By `pairwise_edge_sharing_no_common_edge_implies_subset_K4`:
- All triangles are contained in a set of ≤ 4 vertices
- By `subset_K4_implies_cover_le_2_restricted`:
- Any set of triangles on ≤ 4 vertices can be covered by ≤ 2 edges

## Key Lemmas

```lean
-- Any two triangles share an edge when ν=1
lemma nu_eq_1_implies_pairwise_edge_sharing (h : trianglePackingNumber G = 1) :
    ∀ t₁ t₂, t₁ ∈ G.cliqueFinset 3 → t₂ ∈ G.cliqueFinset 3 → (t₁ ∩ t₂).card ≥ 2

-- Pairwise edge-sharing without common edge → ≤4 vertices
lemma pairwise_edge_sharing_no_common_edge_implies_subset_K4 ...

-- Triangles on ≤4 vertices → covered by ≤2 edges
lemma subset_K4_implies_cover_le_2_restricted ...
```

## Verification

```bash
lake env lean proven/tuza/nu1/tuza_nu1_PROVEN.lean
```

## Aristotle Details

- **UUID**: 2b21c426-552d-4eb4-831e-b797545758e2
- **Date**: December 19, 2025
- **Lean version**: leanprover/lean4:v4.24.0
- **Mathlib**: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
