# Tuza Strategy: The Structural Approach

## The Key Insight

Instead of attacking Tuza's conjecture directly, we attack the **structure of triangle packings**.

The reduction lemma (`exists_two_edge_reduction`) requires:
> For any G with ν > 0, ∃ 2 edges that hit EVERY maximum packing

This is a **hitting set problem** for the family of all max packings.

## The New Concept: Blocking Number

Define: `blockingNumber(G)` = minimum edges to hit ALL maximum packings

**The reduction lemma is equivalent to: blockingNumber(G) ≤ 2**

## Why This Reframing Helps

Instead of asking "do 2 edges reduce ν?", we ask:
1. How many maximum packings can exist?
2. What structure do they share?
3. Can we always find 2 edges that intersect all of them?

## The ν=2 Case Analysis

For ν=2, we have two edge-disjoint triangles t1, t2. Cases:

### Case 1: Vertex-Disjoint (t1 ∩ t2 = ∅)

**Claim**: Only ONE max packing exists.

**Why**: Any other triangle t must share edge with t1 or t2 (else ν ≥ 3).
So any alternative packing would need triangles sharing edges with t1, t2.
But then those triangles share edges with t1 or t2, not edge-disjoint.

**Blocking**: Any 2 edges, one from each triangle, suffice.

### Case 2: Bowtie (t1 ∩ t2 = {v}, one shared vertex)

```
    a---b
     \ /
      v
     / \
    c---d

t1 = {a,b,v}, t2 = {c,d,v}
```

**Alternative packings exist IFF** there's a "crossing" edge (a-c, a-d, b-c, or b-d).

**Blocking**: Two edges incident to center v always work:
- {v-a, v-c} hits t1 and t2
- Any alternative packing must use v (since ν=2 forces structure)

### Case 3: Share 2+ Vertices

Impossible (would share an edge, not edge-disjoint).

## The Submission: tuza_nu2_packing_structure.lean

This submission defines:
1. `maxPackings G` - the family of all maximum packings
2. `BlocksAllMaxPackings G S` - S hits every max packing
3. `blockingNumber G` - minimum blocking set size
4. `Bowtie` - explicit structure for shared-vertex case

Then proves:
1. `vertex_disjoint_unique_packing` - Case 1 has unique packing
2. `bowtie_alternatives` - Characterizes when Case 2 has alternatives
3. `blocking_number_le_2_when_nu_2` - **THE KEY THEOREM**
4. `exists_two_edge_reduction_nu_2` - Implies ν decreases

## Why This Might Work

1. **Finite case analysis** - ν=2 has limited structure
2. **Explicit construction** - We specify which 2 edges work
3. **Structural lemmas** - Each case has clear characterization
4. **Clean separation** - Blocking ≠ covering, easier to reason about

## Current Submissions

| UUID | Approach | Status |
|------|----------|--------|
| f62d4c0a | v5 - original scaffolding | Running |
| 44189eca | FULL v3 - induction attempt | Running |
| **7bbcd387** | **Packing structure** | **NEW** |

## What Success Looks Like

If `blocking_number_le_2_when_nu_2` is proven:
→ `exists_two_edge_reduction_nu_2` follows
→ ν=2 case is complete
→ Pattern may generalize to ν=3

## Literature Support

Per Grok's analysis:
- Haxell (1999): "the full 2-edge reduction holds for ν=2 via case analysis"
- This approach aligns with known proof strategies
- No counterexamples found up to n=20 via SAT solvers
