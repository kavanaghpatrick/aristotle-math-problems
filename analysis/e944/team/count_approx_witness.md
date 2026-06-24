# E944 — The best small approximate witness: C_7(1,2) = complement(C7) (count)

**Verification:** `python3 analysis/e944/team/dissect_n7.py`; circulant check inline.
Engine `critedge.py` self-tested (exact chi vs brute force).

## The graph
Among ALL 4-vertex-critical graphs on ≤7 vertices, the one with the FEWEST
critical edges is the **circulant C₇(1,2)** = **complement of C₇**:
- n=7, m=14, **4-regular**, vertex-transitive (Z₇ rotation).
- χ = 4, every vertex critical (4-vertex-critical). ✓
- **7 of its 14 edges are NON-critical; 7 are critical.** Min over all n≤7.

## The mechanism (this is the key structural finding)
The edge set splits into two Z₇-orbits by circulant difference:
| edge orbit | difference | count | critical? | #triangles through edge |
|---|---|---|---|---|
| outer 7-cycle | ±1 | 7 | **ALL critical**     | 2 |
| inner 7-cycle | ±2 | 7 | **ALL non-critical** | 1 |

Because the graph is vertex-transitive, **criticality is constant on each edge
orbit**. An entire orbit of 7 edges can be deleted-one-at-a-time without dropping
χ — i.e. χ(G − e) = 4 for every difference-2 edge e, while the graph remains
4-vertex-critical.

**This is precisely the lever an E944 witness needs.** A witness is a graph where
EVERY edge is non-critical. C₇(1,2) achieves it for one full orbit (half the
edges). The question becomes: is there a (vertex-transitive or not) 4-vertex-
critical graph in which **every** edge-orbit is non-critical?

## Why "more triangles ⇒ more critical" here, and the caution
In this graph the critical edges sit in 2 triangles, the non-critical in 1. But
this correlation is NOT a law: in the n=7 graph 3 (the 4-regular-free one) edges
in 0 triangles were critical. Triangle count is not the discriminant. The real
discriminant is whether some 3-coloring of G "uses" the edge — an edge e=uv is
NON-critical iff G−e is still 4-chromatic, iff there is NO proper 3-coloring of
G−e (equivalently every 3-coloring attempt of G that would be unlocked by
removing uv still fails). For C₇(1,2), removing a difference-2 edge leaves a
graph still forcing 4 colors.

## Construction-search implication (what I'll do next)
The witness, if it exists, is plausibly **vertex-transitive** (so we don't have to
kill each edge individually — kill one per orbit). Strategy:
1. Search circulants C_n(S) for 4-vertex-critical instances where EVERY connection
   difference yields a non-critical edge. C₇(1,2) fails only on difference 1.
   Look for C_n(S) with χ=4, vertex-critical, and 0 critical edges.
2. More generally, search Cayley graphs / vertex-transitive 4-chromatic graphs.
3. Cross-check against archivist's account of the Brown k=5 witness — is it
   vertex-transitive? If Brown's k=5 graph is a circulant/Cayley graph, the k=4
   analogue search space is well-defined.

## Honest caveat
Vertex-transitivity is a heuristic, not a theorem — the k=4 witness need not be
vertex-transitive. But it is the cheapest large search space that contains the
known mechanism, and C₇(1,2) proves the mechanism is real at n=7.
