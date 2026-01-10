# PATH_4 CRITICAL FINDING: The External Triangle Problem

## The Problem

We've been trying to prove τ ≤ 8 for PATH_4, but exhaustive search proves:

**NO 8-EDGE COVER EXISTS FOR PATH_4 IF WE MUST COVER ALL EXTERNAL TYPES**

## What We Discovered

### PATH_4 Structure
- A = {v1, a1, a2} - 3 edges
- B = {v1, v2, b} - 3 edges
- C = {v2, v3, c} - 3 edges
- D = {v3, d1, d2} - 3 edges

**Total: 12 M-edges**

### The External Triangle Constraint

The problem states: "any external triangle shares an edge with some M-element"

We interpreted this as: **each of the 12 edges defines an external triangle TYPE**

If this interpretation is correct, then:
- A-externals come in 3 types (one per A edge)
- B-externals come in 3 types (one per B edge)
- C-externals come in 3 types (one per C edge)
- D-externals come in 3 types (one per D edge)

**To cover all 12 external types, we need all 12 edges!**

## What slot300 Actually Proves

slot300 proves τ ≤ 10 using this cover:
```
A: 3 edges {v1,a1}, {v1,a2}, {a1,a2}
B: 2 edges {v1,v2}, {v2,b}
C: 2 edges {v2,v3}, {v3,c}
D: 3 edges {v3,d1}, {v3,d2}, {d1,d2}
```

But wait - this is only 10 edges, not 12!

**Key question: Does this 10-edge cover actually cover all triangles?**

## Two Possible Resolutions

### Possibility 1: Not all edges have external triangles

Maybe some edges (like {v1,b} or {v2,b}) don't actually have external triangles in the graph.

If the graph only has certain edges, then:
- Some external triangle types might not exist
- A 10-edge cover could work

### Possibility 2: Externals can share edges

Maybe multiple external triangles of the SAME type can exist, but we only need to cover the shared edge once.

For example:
- External {x, a1, a2} shares edge {a1,a2} with A
- Another external {y, a1, a2} also shares edge {a1,a2} with A
- Covering {a1,a2} once covers BOTH externals

This is what slot300 assumes!

## The Key Insight

Looking at slot300's proof structure:
```lean
by_cases ht_M : t ∈ M
· -- t ∈ M: use its own edge
· -- t ∉ M: shares edge with M (max_packing_shares_edge)
```

The proof says:
1. If triangle t is in M, cover it with one of its edges
2. If triangle t is NOT in M, it shares an edge with some m ∈ M (by maximality)
3. That shared edge is already in our cover (from step 1)

**This works because the cover includes at least one edge from EACH M-element!**

## The 10-Edge Cover Works Because:

- A: All 3 edges included → covers A + all A-externals ✓
- B: 2 edges {v1,v2}, {v2,b} → covers B + externals sharing these edges
  - Missing: externals sharing {v1,b} ONLY ❌
- C: 2 edges {v2,v3}, {v3,c} → covers C + externals sharing these edges
  - Missing: externals sharing {v2,c} ONLY ❌
- D: All 3 edges included → covers D + all D-externals ✓

**Wait, this still doesn't work if there are externals using {v1,b} or {v2,c}!**

## The Resolution: Graph Constraints

The only way slot300's proof works is if:

**THE GRAPH STRUCTURE PREVENTS CERTAIN EXTERNAL TRIANGLES FROM EXISTING**

Specifically:
- No external triangle uses ONLY edge {v1,b} from B
- No external triangle uses ONLY edge {v2,c} from C

Why might this be true?
- If creating such an external would violate the packing maximality
- If the vertex set is constrained (only 9 vertices)
- If the graph edges are constrained

## What We Need to Check

1. Does slot300's proof actually verify that the 10 edges cover all triangles?
2. Or does it assume a specific graph structure?
3. Are there additional constraints we're missing?

## The Fan Apex Strategy Revisited

If externals of an endpoint share a common apex:
- A-externals all contain some vertex x_A ∈ A
- Then covering the 2 spokes from x_A covers ALL A-externals
- This reduces from 3 edges to 2 edges

But the exhaustive search shows this doesn't give us 8 edges total!

**Even with fan apex, we get at most 2+2+2+2 = 8 edges**

And this ONLY works if:
- All 4 M-elements have fan apex structure
- No other constraints apply

## Conclusion

One of the following must be true:

1. **τ ≤ 8 is FALSE for PATH_4** - we can only achieve τ ≤ 10 or τ ≤ 12
2. **We're missing a constraint** - the graph or packing has additional structure
3. **The external triangle definition is wrong** - not every edge has external triangles

We need to:
- Carefully review slot300's proof
- Check if there are graph constraints we missed
- Possibly ABANDON the τ ≤ 8 goal for PATH_4
