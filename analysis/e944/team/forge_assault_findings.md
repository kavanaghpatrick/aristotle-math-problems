# forge ASSAULT findings (2026-06-10) — the redundancy/criticality tension is a HARD wall

Assault target: drive min-critical-edge count 7→0 on a 4-vertex-critical graph.
Four construction lines run, all dual-verified (forge_verify.py + count's checkers.py).

## Line (a): C₁₃(1,2,5) orbit surgery — FAILED, manifold rigid
`forge_assault_c13.py`. Degree-preserving 2-swaps on the seed (6-regular, χ=4,
vertex-critical, 13 critical edges on the diff-1 Hamilton-cycle orbit).
**Result: ZERO accepted moves across 12k attempts.** Every 2-swap breaks
vertex-criticality. The 6-regular 4-vertex-critical manifold is even more rigid
than the general one — local edge surgery cannot navigate it.

## Line (b): voltage / double covers — 0 CRITICAL EDGES but NOT vertex-critical
`forge_assault_covers.py`. Z₂ and Z₃ voltage covers of C₁₃(1,2,5) over its 3
edge-orbits. **Every nontrivial cover is χ=4 with 0 critical edges (100%
redundant)** — e.g. Z₂cover voltage (0,0,1): n=26, m=78, χ=4, ALL 78 edges
redundant. BUT all are NOT vertex-critical: every vertex is removable, because a
cover gives each vertex a "twin" copy that carries the obstruction when its
partner is deleted.

## Line (c): trim covers/biwheels to the vertex-critical boundary — TENSION CONFIRMED
`forge_assault_trim.py`. Take the 0-critical-edge covers/biwheels and delete
removable vertices (preserve-zero / min-critical / random orders) until
vertex-critical. **Every path collapses the redundancy:** the boundary is reached
with critical_edges ≈ (#remaining vertices) — e.g. Z₂cover(0,0,1) trims to n=13,
13 critical edges; Z₂cover(1,0,0) trims to n=19, 19 critical edges. The
preserve-zero heuristic CANNOT keep critical edges at 0 down to vertex-criticality.

## Line (d): random 6-regular n≥15 — NEGATIVE, and it teaches us something
`forge_assault_walls_sat.py`. skeptic already exhausted CONNECTED 6-regular
n≤14 (first 6-reg 4-vc graph = C₁₃(1,2,5) at n=13, has critical edges; no witness
≤14). I sampled random 6-regular at n=15,16,17,18,20 — **0 of 30000 trials at
EVERY n was even 4-vertex-critical.** Random regular graphs are too well-connected
to be vertex-critical at χ=4 (lots of removable vertices). **Vertex-critical
6-regular graphs are a rare, structured set — not findable by random sampling.**
So a 6-regular witness (if any) is a specific structured graph; random search is
futile. Reinforces: use structured constructions or exhaustive/CEGAR (hunter).

## Line (e): partial-cover twin-merge interpolation — NO SWEET SPOT
`forge_assault_partial_cover.py`. Interpolate between the fat cover (0 critical
edges, not VC) and the lean base (VC, critical edges) by merging twin pairs
(i,0)≡(i,1) for a subset M of base vertices. **To reach vertex-criticality the
greedy must merge ALL twins (|M|=13), collapsing back to the base C₁₃(1,2,5) with
13 critical edges.** Partial merges either stay non-VC or, once VC, have the full
critical count. No intermediate sweet spot — another face of the same wall.

## THE STRUCTURAL WALL (the gold)

Across FOUR independent generators (local surgery, covers, biwheel trim, plus the
earlier annealing/directed-growth), the SAME phenomenon:

> **Edge-redundancy and vertex-criticality are antagonistic.** Adding redundancy
> (covers, fat biwheels, extra obstructions) kills critical edges but ALSO makes
> vertices removable (a deleted vertex's obstruction survives via a parallel
> copy). Restoring vertex-criticality (trimming) destroys exactly the parallel
> copies that provided edge-redundancy. The witness must occupy a knife-edge
> where every vertex is load-bearing for χ=4 YET every edge has a backup
> obstruction — and no construction I have reaches it.

This is the existence-side mirror of wall's impossibility analysis. It does NOT
prove non-existence (the global edge-count squeeze doesn't close, per wall), but
it shows WHY every natural construction fails: the two requirements pull the graph
in opposite topological directions.

## Score ledger (min critical edges achieved at vertex-criticality)
- Global min (any method): **8** — the n=10 exhaustive champion `ICpdbY{]_`.
- C₁₃(1,2,5): 13. Covers trimmed: 13–19. None beats the exhaustive 8.
- The assault did NOT drive below 8, and did NOT reach 0.

## PROVEN theorem extracted from the assault (the real deliverable)
> **If v has degree 3 in a 4-vertex-critical graph, all 3 edges at v are critical.**
> ⟹ a (4,1)-witness has min degree ≥ 4.
Elementary proof + the per-vertex lemma in `forge_vertex_spanning.md`. Verified
exactly on all 139 four-vertex-critical graphs n=7,8,9. This is a self-contained
cousin of SkSt's δ≥6 and explains WHY Jensen–Siggers cannot reach E*=∅: their
H(m) is built from degree-3 transfer-path vertices (44/67 at m=3), each forcing 3
critical edges. The "vertex-spanning E*" fact (every vertex touches a critical
edge, in all tested graphs) is PROVEN-EQUIVALENT to wall's criterion / "no
witness" — an honest reformulation, not new leverage; the easy strengthening
"every vertex ≥2 critical edges" is FALSE (counterexample n=9 `HCp\`fr]`).

## Honest verdict
The construction lines confirm the tension is a real wall, consistent with k=4
being the lone holdout that has resisted Steiner et al. The reportable advances
are: (1) the PROVEN degree-3 theorem + witness δ≥4 corollary; (2) the per-vertex
criticality lemma tying construction-failure to wall's criterion; (3) the
dual-verified J-S reconstruction with spanning E*; (4) five dual-verified
negative construction lines mapping the antagonism. NOT a witness. Best concrete
object remains the n=10 exhaustive champion (8 critical edges) and C₁₃(1,2,5)
(the unique 6-regular near-miss, one bad orbit). Assault did not drive |E*| below
8 or reach 0; the evidence increasingly favors "no k=4 witness," though that
remains unproven (wall: global density squeeze does not close).
