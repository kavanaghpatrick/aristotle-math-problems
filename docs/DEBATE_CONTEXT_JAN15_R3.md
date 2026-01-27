# Multi-Agent Debate: τ ≤ 8 for PATH_4 - Round 3

## Rounds 1-2 Consensus
- **τ ≤ 4 is FALSE**: Bridge T = {v₁, a₂, b₃} proves it
- **τ ≤ 8 is achievable**: 2 edges from each of 4 packing elements
- **Endpoints**: Adaptive selection works (proven in slot426)
- **Middles**: Spine edge required for both-direction bridges

## Fresh Aristotle Evidence (Jan 15)

### slot430 Result (UUID 582bf365)
Main theorem `tau_le_8_path4` has **1 sorry** at line 566:
```lean
-- Case analysis on which pair (E, F) is
-- Adjacent pairs: (A,B), (B,C), (C,D)
-- Non-adjacent pairs can't have bridges (would share edge with middle element)
sorry
```

**PROVEN in slot430:**
- `exists_two_edges_cover_Se` (lines 337-349)
- `bridge_contains_shared` (lines 290-299)
- `middle_no_base_externals` (lines 301-309)
- `triangle_classification` (lines 321-334)
- `active_triangle_disjoint_from_disjoint_member` (lines 351-380)
- `bridge_in_active_contains_shared` (lines 418-430)

### slot427 Gap Confirmed (Lines 891-895)
```lean
· -- x = b₃, we have v₂, b₃ ∈ T but not necessarily v₁
  -- Our selection is {s(v₁,v₂), s(v₁,b₃)} - neither directly covers {v₂, b₃}
  -- This is the gap! We need to use s(v₂, b₃) instead of s(v₁, b₃) in some cases
  sorry
```

## The Remaining Gap

**Problem**: Middle B = {v₁, v₂, b₃} with selection {s(v₁,v₂), s(v₁,b₃)}
- A-B bridges: Contain v₁ (shared with A) → covered by s(v₁,v₂) or s(v₁,b₃) ✓
- B-C bridges of form {v₂, v₁, z}: Covered by s(v₁,v₂) ✓
- B-C bridges of form {v₂, b₃, z}: **NOT COVERED** by either edge!

**Potential Solutions:**

1. **Adaptive selection for middles**: Choose {s(v₁,v₂), s(v₂,b₃)} when Type {v₂,b₃} externals exist
   - But then A-B bridges of form {v₁, b₃, a} are not covered!

2. **Prove mutual exclusion**: Show {v₁,b₃}-type bridges and {v₂,b₃}-type bridges can't both exist
   - Would require proving some structural constraint

3. **Cross-coverage**: A-B bridges covered by A's selection, B-C bridges covered by C's selection
   - Works if we can prove coordination between adjacent elements

4. **Three-edge selection for middles**: Accept τ ≤ 10 instead of τ ≤ 8
   - Fallback if 2 edges truly insufficient

## Round 3 Question

**Given the Aristotle-proven scaffolding, which solution path closes the gap?**

Focus on:
1. Is there a mutual exclusion principle for {v₁,b₃} vs {v₂,b₃} bridge types?
2. Can cross-coverage from adjacent elements work?
3. What structural constraint makes adaptive selection valid?

Provide your definitive recommendation with Lean proof sketch.
