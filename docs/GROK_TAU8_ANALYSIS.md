# Grok-4 Analysis: τ ≤ 8 for ν = 4

## Problem
Aristotle proves ALL helper lemmas but FAILS on main `tau_le_8` theorem.

## Key Insight
The gap is that Aristotle can't synthesize the cover construction because there's no explicit case split.

## Case Analysis by "Supported Edges"
Supported edge = edge of X ∈ M that has ≥1 X-external.

| # Supported | Structure | Common Vertex | Cover Construction |
|-------------|-----------|---------------|-------------------|
| 0 | No externals | Any v ∈ X | {s(v,u), s(v,w)} for any v ∈ X = {v,u,w} |
| 1 | All externals share edge e = {u,w} | Both u and w | {e, any other X-edge} |
| 2 | Exactly 1 per edge, same t ∉ X | Shared endpoint v | {s(v,t), opposite edge} |
| 3 | Exactly 1 per edge, same t ∉ X | NONE in X | {s(a,t), s(b,c)} for any a ∈ X |

## Why Case 3 is Special
For X = {a,b,c} with externals on all 3 edges:
- {a,b} ∩ {a,c} ∩ {b,c} = ∅
- No vertex of X is in all externals
- But by `common_external_vertex`, all externals share t ∉ X
- Cover {s(a,t), s(b,c)} works

## Recommended Lemmas for Aristotle

### Structural Lemmas
1. `if_ge_two_supported_then_unique_t`: If ≥2 supported edges, all externals use same t ∉ X
2. `common_vertex_in_X_for_le_two`: If ≤2 supported edges, ∃ v ∈ X in all externals
3. `one_external_per_supported_edge`: If ≥2 supported, exactly 1 external per edge

### Covering Lemmas (one per case)
1. `cover_zero_supported`: Explicit 2-edge cover when no externals
2. `cover_one_supported`: Explicit 2-edge cover when 1 supported edge
3. `cover_two_supported`: Explicit 2-edge cover when 2 supported edges
4. `cover_three_supported`: Explicit 2-edge cover when 3 supported edges

## Main Theorem Structure
```lean
theorem two_edges_cover_X (X : Finset V) (hX : X ∈ M) :
    ∃ e₁ e₂, covers_X_and_externals X e₁ e₂ := by
  let n := num_supported_edges X
  interval_cases n
  · exact cover_zero_supported ...
  · exact cover_one_supported ...
  · exact cover_two_supported ...
  · exact cover_three_supported ...
```

## Current Submissions
- slot319: 12 helpers proven, main failed
- slot321: 7 helpers proven (incl. common_external_vertex), main failed
- slot322: Running (2 sorries)
- slot323: Running (1 sorry with combined approach)
