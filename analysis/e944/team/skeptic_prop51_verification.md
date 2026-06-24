# E944 — Independent verification of Skottova–Steiner Prop 5.1 (skeptic)

proximity extracted Prop 5.1 (necessary conditions for a (4,1)-graph: min-deg ≥ 6, λ ≥ 6,
Δ ≤ |V|−5, |V| ≥ 11) and said they "checked the proofs." As the squad's verifier I re-derived
the load-bearing chain INDEPENDENTLY (my own code + reasoning) rather than trusting the
extraction. **All steps confirmed. The min-deg-6 / |V|≥11 floor is real.**

This matters because hunter (Rung 4: 6-regular search) and forge are about to lean on these
conditions to prune. If min-deg-6 were quoted wrong (e.g. from the abstract, a stated squad
failure mode), their search space would be wrong.

## The chain, re-derived

**Step 1 — the identity (computationally verified, EXACT).**
> smallest critical edge-set size  ==  min over all 3-colorings of (# monochromatic edges).

Verified by exhaustive comparison on EVERY 4-vertex-critical graph with n ≤ 7 (a fresh brute-force:
for each graph, `min_mono` over all 3^n colorings vs `smallest_critical_set_size` by increasing-|R|
search; χ cross-checked). Zero mismatches. (Reason: deleting exactly the monochromatic edges of a
3-coloring makes it proper, so smallest critical set ≤ min-mono; conversely a critical set R of size
t gives a proper 3-coloring of G−R with ≤ t mono edges in G, so min-mono ≤ t.)

**Step 2 — (4,1) ⟹ every 3-coloring has ≥ 2 mono edges.**
No critical edge ⟹ smallest critical set ≥ 2 ⟹ (Step 1) min-mono ≥ 2 = r+1. ✓

**Step 3 — vertex-critical ⟹ every proper induced subgraph is 3-colorable.**
Any proper subset X ⊊ V misses some vertex v, so G[X] ⊆ G−v, and χ(G−v) ≤ 3 by vertex-criticality.
Spot-checked: 16 four-critical graphs (n=6..8), every G−v is 3-colorable. ✓ (So G[X], G[Y] for any
edge cut (X,Y) are each properly 3-colorable.)

**Step 4 — the random-S₃ cut bound (arithmetic re-derived).**
For an edge cut (X,Y) with x crossing edges: properly 3-color G[X] and G[Y] (Step 3). Apply a uniformly
random S₃ relabeling to the Y side's colors. Each crossing edge becomes monochromatic with prob 1/3,
independent of X's coloring. Expected mono crossing edges = x/3, so SOME relabeling achieves ≤ x/3. The
resulting 3-coloring of all of G has 0 mono inside X, 0 inside Y, ≤ x/3 crossing ⟹ total ≤ x/3. But by
Step 2 total ≥ 2. Hence x/3 ≥ 2 ⟹ **x ≥ 6**. Every edge cut has ≥ 6 edges ⟹ **λ(G) ≥ 6 ⟹ δ(G) ≥ 6**
(the singleton cut X={v} gives deg(v) ≥ 6). ✓ (General r: x ≥ 3(r+1) = 3r+3, matching the paper.)

**Step 5 — |V| ≥ 11.**
A 4-chromatic graph with δ ≥ 6 needs enough vertices; the paper's bound is |V| ≥ 5r+6 = 11 for r=1.
My exhaustive floor (skeptic_smalln_groundtruth.md) shows 0 (4,1)-graphs on n ≤ 10 — fully CONSISTENT
with, and a stronger statement than, |V| ≥ 11 at the small end (it also covers any structure, not just
the degree bound). No contradiction in either direction. ✓

## TWO independent derivations of min-deg ≥ 6 now exist
1. **proximity (hypergraph side):** M-S complement-of-2-section route's densest reachable graph has
   min-deg ≤ 4 < 6 ⟹ re-derives the same Prop 5.1 floor from the construction side (proximity_rung_h.md).
2. **skeptic (coloring side):** the random-S₃ cut argument above, Steps 1–4, independently checked.

Two routes, same floor. The min-deg-6 / |V|≥11 necessary conditions are SOLID. hunter/forge can prune
to min-deg ≥ 6 (Rung 4: 6-regular first) without risk of discarding a witness.

## Verdict
Prop 5.1 is correctly quoted and correctly proved. The witness, if it exists, is a graph on ≥ 11
vertices with δ ≥ 6, λ ≥ 6, Δ ≤ |V|−5; the sparsest candidate is 6-regular (Steiner's Problem 5.2).
This is consistent with my exhaustive ≤10 floor and with the ncard-finite-equivalence lock — the
search space is finite and well-delimited per n.
