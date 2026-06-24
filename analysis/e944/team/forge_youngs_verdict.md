# forge — Youngs / projective-quadrangulation seed: VERIFIED then REFUTED

Invention-mandate lead seed (from team-lead): non-bipartite quadrangulations of
the projective plane are 4-chromatic by a global ℤ₂ parity invariant (Youngs
1996). Candidate SECOND non-vertex-aligned redundancy mechanism.

## VERIFIED (the theorem is real and global)
Youngs' theorem (J. Graph Theory 21, 1996): every non-bipartite quadrangulation
of RP² has χ EXACTLY 4 — it jumps 2→4, skipping 3. The obstruction is a genuine
global ℤ₂ invariant (the quadrangulation is "odd"), not any local odd cycle or
clique. K4 is the minimal example (quadrangulates RP²: V−E+F = 4−6+3 = 1, 3 quad
faces). This IS a global, non-local χ=4 mechanism — qualitatively what the mandate
wants.

## REFUTED as a witness family (clean, via forge's degree-3 theorem)
A quadrangulation of RP² satisfies Euler V−E+F=1 with 2E=4F (every face a quad,
every edge on 2 faces) ⟹ **E = 2V − 2** exactly. Hence average degree
= 2E/V = 4 − 4/V < 4 for all V. So EVERY projective quadrangulation has a vertex
of degree ≤ 3; since a 4-vertex-critical graph has δ≥3 (Gallai), some vertex has
degree EXACTLY 3.

By **forge's theorem** (deg-3 vertex in a 4-vertex-critical graph ⟹ all 3 of its
edges critical), every such quadrangulation has ≥3 critical edges. So:

> **No non-bipartite projective-planar quadrangulation is an Erdős-944 witness.**

The global parity obstruction is real but lives on graphs that are TOO SPARSE
(m = 2n−2, forced degree-3 vertices), conflicting with forge's δ≥4 and SkSt's
δ≥6 witness conditions.

## Computational confirmation
Exhaustive over ALL χ=4 graphs with the quadrangulation edge-count m=2n−2 that
are 4-vertex-critical (nauty geng + exact χ + count's checkers):
| n | m=2n−2 | #χ=4 | #4-vertex-critical | min |E*| |
|---|---|---|---|---|
| 6 | 10 | 8 | 1 | 10 (all) |
| 7 | 12 | 64 | 3 | 10 |
| 8 | 14 | 762 | 5 | 13 |
| 9 | 16 | 12203 | 40 | 14 |
At most 2 edges are ever redundant — these sparse graphs are critical-edge
dominated, exactly as the degree-3 theorem predicts.

## The PAYOFF for the invention mandate (sharpens the spec)
The same theorem that killed the seed tells us what the SECOND mechanism MUST
satisfy: it must live on a DENSE graph. A witness has δ≥6 ⟹ m ≥ 3n. So the
global mechanism cannot be a sparse topological structure (quadrangulation,
triangulation: m=3n−3 borderline, still has low-degree vertices on most
surfaces). **The second mechanism must be a DENSE global obstruction** — e.g. a
parity/flow structure on a graph of average degree ≥ 6. This rules out the whole
"sparse surface quadrangulation" family and redirects toward dense ℤ₂/flow
structures (handed to algebra: signed graphs, nowhere-zero tensions on dense
graphs; and to jensen: re-express J-S transfer as a dense parity obstruction).

## Status
Seed adjudication: REFUTED (clean proof + exhaustive confirmation). The mandate
continues toward DENSE global mechanisms. The degree-3 theorem is now doing real
work as a filter on candidate mechanisms.
