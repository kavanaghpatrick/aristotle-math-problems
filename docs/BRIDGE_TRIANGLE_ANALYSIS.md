# Bridge Triangle Gap Analysis

## The Gap (Confirmed by Gemini)

A **bridge triangle** is a triangle T that shares edges with MULTIPLE packing elements.

Example:
- M = {X={a,b,c}, Y={c,d,e}} where X∩Y = {c}
- Bridge triangle T = {b,c,d}
- T shares edge {b,c} with X
- T shares edge {c,d} with Y
- T is NOT external to X (fails "only shares with X" requirement)
- T is NOT external to Y (fails "only shares with Y" requirement)

The `two_edges_cover_all_externals` theorem only covers:
- T = X (element itself)
- T external to X (shares edge ONLY with X)

Bridge triangles are NOT covered by this theorem!

## When Are Bridge Triangles Uncovered?

For T = {x, c, y} where c is the shared vertex of X and Y:
- T's edges: {x,c}, {c,y}, {x,y}
- X contributes 2 edges incident to common vertex v of X's externals
- Y contributes 2 edges incident to common vertex w of Y's externals

T is covered if ANY of these hold:
- v = c → X contributes {c, ?}, which includes {c, x}
- v = x → X contributes {x, c} among its edges
- w = c → Y contributes {c, y} among its edges
- w = y → Y contributes {y, c} among its edges

T is UNCOVERED only if:
- v ∉ {x, c} (so v is the "other" vertex of X)
- w ∉ {c, y} (so w is the "other" vertex of Y)

## Key Question

Can we prove that for any bridge triangle T = {x, c, y}, at least one of:
1. X's common vertex is x or c
2. Y's common vertex is c or y

If yes, τ ≤ 8 is rescued.

## Possible Approaches

### Approach 1: Bridge Triangles Force Common Vertex

Conjecture: If bridge triangle T = {x, c, y} exists, then c must be the common vertex for at least one of X or Y.

Why this might be true:
- T passes through c
- If there's an X-external containing c, then c could be the common vertex
- But T itself is NOT an X-external, so T doesn't force this

### Approach 2: Count Bridge Triangles

For PATH_4 with consecutive sharing:
- At most 3 pairs share a vertex: (A,B), (B,C), (C,D)
- Each pair can have multiple bridge triangles

However, bridge triangles all pass through the shared vertex. So adding edges incident to the 3 shared vertices would cover ALL bridge triangles.

Cost: At most 6 extra edges (2 per shared vertex)
But: Some of these might already be in our 8-edge cover

### Approach 3: Global Optimization

Instead of 2 edges per element independently, choose 8 edges globally to minimize uncovered triangles.

This is more complex but might be necessary.

## Resolution for Aristotle Submission

For now, we:
1. Include the proven scaffolding from slot306
2. Add a lemma specifically for bridge triangle coverage
3. Let Aristotle attempt to prove or find counterexample

If Aristotle finds a counterexample to bridge triangle coverage, we know τ ≤ 8 needs a different approach.
If Aristotle proves it, we have a complete proof.
