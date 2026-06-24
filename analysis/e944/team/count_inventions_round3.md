# E944 — count INVENTIONS Round 3 (coloring-space / inverse objects)

(Detail for INVENTIONS.md count-lane Round 3. Written to own file to avoid the
concurrent-edit race on INVENTIONS.md. Pointer added there.)

## CNT-7 — Blame distribution (coloring-space inverse object) — STRONG NEW RESULT

**Definition (the inverse reframing).** Work in COLORING space, not graph space.
For a 4-chromatic G, every 3-coloring has ≥1 monochromatic ("conflict") edge.
Define blame(e) = #{3-colorings whose ONLY monochromatic edge is e}
                = #{proper 3-colorings of G−e}.
Then **e is critical ⟺ blame(e) > 0**. Hence the witness condition translates to:
**"no critical edge" ⟺ blame(e)=0 ∀e ⟺ min over all 3-colorings of (#monochromatic
edges) ≥ 2** — i.e. NO 1-conflict 3-coloring exists.

This is the FIRST coloring-space / inverse object in the squad — every other search
object (mine and teammates') is forward (build graph → compute χ). CNT-7 inverts it:
characterize the witness by the structure of near-3-colorings.

**Computed result — full enumeration of all 531,441 three-colorings of C₁₃(1,2,5)
(vertex 0 fixed by symmetry), exact:**
- conflict histogram, low end: {1 conflict: 26 colorings, 2 conflicts: 26, 3: 182, …}
- min-conflict = 1 (1-conflict colorings exist ⟹ critical edges exist; consistent).
- **every one of the 13 critical edges has blame EXACTLY 2** — perfectly uniform
  (26 = 13 × 2).

**The sharp new mechanism (why the circulant is rigid, in coloring-space terms):**
blame is perfectly uniform — each critical edge is the unique conflict of exactly 2
of the 26 one-conflict colorings, tied together by the Z₁₃ symmetry. There is NO
concentrated, killable target: an edit that destroys the 2 colorings blaming one
edge, by symmetry, creates 1-conflict colorings blaming another. Kill-one-revive-
another, now seen at the level of the coloring-incidence structure rather than the
graph. This is a cleaner explanation than "the difference-1 orbit is critical."

**The crisp witness target in this language:** a 4-chromatic, vertex-critical graph
whose minimum number of monochromatic edges over ALL 3-colorings is ≥ 2 (no 1-conflict
coloring). That is a direct, computable coloring-space objective — same as 0 critical
edges, but the blame STRUCTURE tells you why descent stalls and what to attack
(eliminate 1-conflict colorings, not edges).

**Search test:** SA minimizing (#1-conflict-colorings + vertex-crit debt) over
degree-preserving swaps from C₁₃(1,2,5). STOPPED as REDUNDANT: #1-conflict-colorings
> 0 ⟺ critical edges exist ⟺ min-conflict = 1, and my earlier degree-preserving
6-regular annealing + basin-hopping ALREADY proved the critical-edge count plateaus
at 13 on the 6-regular manifold and is robust to local + large-step moves. So
"push min-conflict to ≥ 2" is exactly the same plateau, already established
unreachable by 6-regular search. The full-enumeration version (531k colorings/iter)
was too slow to justify re-deriving a known result; killed to free CPU. The VALUE of
CNT-7 is the blame STRUCTURE (uniform blame = 2), not a new search outcome — the
search would confirm the plateau, which we have.

## CNT-8 — Hajós-join criticality walk — DEFERRED
Canonical generator of all 4-critical graphs as an SA move-set scored by critical-edge
fraction. Deferred this round in favor of the CNT-7 lead; queued for round 4.

## CNT-9 — Blame-bipartite decoupling — PARKED (subsumed by CNT-7)
The bipartite blame graph (critical-edges × damaged-vertices) is dense and symmetric
(CNT-5: ~7-10 damage/edge; CNT-7: exactly 2 blame/edge, uniform). No sparse cover ⟹
no single edit decouples. Parked.

## Net Round 3
The CNT-7 inverse/blame object is the genuinely new contribution: it recasts the
witness as a coloring-space condition (min-conflict ≥ 2) and exposes the circulant's
rigidity as perfectly-uniform blame. This is a fresh lens that complements the
impossibility side (wall/gallai's "global 3-coloring CSP") with an exact, computed
incidence structure. No witness; the uniform-blame finding is mild impossibility intel
for the symmetric regime and a concrete target objective for asymmetric search.
