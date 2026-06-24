# E944 — Steiner's Problem 5.2 at the floor (skeptic)

Skottova–Steiner 2025 (arXiv:2508.08703) **Problem 5.2**: *Does there exist a 6-regular
(4,1)-graph?* This is the literature-sanctioned first computational target, because Prop 5.1
(independently verified in skeptic_prop51_verification.md) forces any (4,1)-graph to have
min-degree ≥ 6, and 6-regular is the sparsest allowed.

I exhaustively tested ALL connected 6-regular graphs (nauty `geng -c -d6 -D6 n`) for the
(4,1)-property, with both χ-checkers (backtrack + SAT) required to agree on every decision.

## Results

| n | connected 6-regular graphs | 4-vertex-critical among them | **6-regular (4,1)-WITNESSES** |
|---|---|---|---|
| 11 | 266 | 0 | 0 |
| 12 | 7,849 | 0 | 0 |
| 13 | 367,860 | 1 | 0 |
| 14 | 21,609,300 | 0 | 0 |
| 15 | NOT COMPLETED (~200M+ graphs, infeasible in-session) | — | — |

**n=15 note:** the 6-regular set at n=15 is ~200M+ connected graphs (geng generation rate ~40k/8s of
generation alone, with the per-graph dual-checker screen as the real bottleneck) — not completable in a
session. A successor wanting it should shard geng output across workers. CAVEAT on prior: the n≡1 mod 3
necessary condition (wall, skeptic-verified to n≤32) is for 4-vc 6-regular CIRCULANTS only — it does NOT
constrain general (non-circulant) 6-regular graphs, so a general 6-reg 4-vc graph at n=15 (≡0 mod 3) is
NOT ruled out a priori. Empirically the general 6-reg 4-vc graphs are rare (none at n=11,12,14; one at
n=13) but that pattern is not a theorem. So n=15 6-regular is genuinely unresolved, just infeasible here.

**n=11, 12, 14: NOT A SINGLE 6-regular graph is even 4-vertex-critical**, let alone a witness.
**n=13: exactly ONE 6-regular graph is 4-vertex-critical (the iso class of count's C₁₃(1,2,5)), and
it HAS a critical edge.** So **Steiner's Problem 5.2 = NO at n=11, 12, 13, AND 14.** (n=14 exhausted
all 21,609,300 connected 6-regular graphs, χ cross-checked.)

The first 6-regular 4-vertex-critical graph in existence appears at n=13, and it is exactly count's
circulant C₁₃(1,2,5) — independently verified by me (6-regular, χ=4, vertex-critical, critical only
on the difference-1 orbit, 26/39 non-critical edges). It misses being a witness by a single orbit.
(Note: 367,860 is the authoritative `geng -c -d6 -D6 13` stream count consumed by the sweep; an
earlier truncated count command reported ~341,879 before timing out — use the sweep figure.)

## Why n=11,12 have no 6-regular 4-vertex-critical graph (observation)
A 6-regular graph on 11 or 12 vertices is fairly dense (33 / 36 edges). For it to be
4-vertex-critical with χ=4, every vertex deletion must drop χ to 3 — a strong global symmetry
of the chromatic obstruction. Empirically the dense 6-regular graphs at these small orders are
either 3-colorable (χ=3) or, if χ=4, NOT vertex-critical (some vertex is "redundant"). The first
6-regular 4-vertex-critical graphs appear at n=13.

## Relationship to the rest of the squad
- This is the FINITE, decidable form of Steiner's Problem 5.2 — a publishable computational result
  regardless of the YES/NO verdict (Steiner posed it as open).
- Confirms / extends the witness floor: combined with the exhaustive ≤10 floor
  (skeptic_smalln_groundtruth.md + hunter), there is no (4,1)-graph on ≤10 vertices of ANY degree,
  AND no 6-regular (4,1)-graph on n=11 or 12.
- Does NOT resolve k=4: a witness could be non-6-regular (min-deg 6 but irregular, Δ ≤ |V|−5) or
  6-regular on n ≥ 13. The search continues; hunter owns the broader min-deg-6 (non-regular) sweep.

## Verification integrity
- Every χ decision cross-checked by two independent algorithms; zero disagreements.
- Enumeration by nauty (canonical, each iso class once) — no hand-rolled subset enumeration.
- Counts of the geng output (266 at n=11, 7849 at n=12) match independent geng -c -d6 -D6 counts.
