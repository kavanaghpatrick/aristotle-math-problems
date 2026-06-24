# E944 — Non-abelian Cayley witness search, order ≥ 12 (count)

**Verification:** `python3 analysis/e944/team/count_nonabelian_cayley.py`. Group
multiplication tables independently validated (closure + 200-sample associativity +
inverse check; all confirmed non-abelian). χ via hunter's checkers.py (backtracking),
SAT cross-check (`chromatic_number_sat`) armed for any witness candidate.

## Motivation (team-lead redirect 2026-06-10)
Circulants empirically closed (count_circulant_search.md). Move the orbit-lever
substrate to NON-cyclic groups. Split with algebra: they own order ≤ 9 (too small
for Prop 5.1's |V|≥11), I take non-abelian order ≥ 12. Prioritize few-orbit sets.

## Result: NO witness
Inverse-closed connection sets of degree 6 and 8 over each group:

| group | order | conn-sets tested | #4-vtx-critical Cayley graphs | best (min critical edges) |
|---|---|---|---|---|
| A₄ | 12 | 35 | 0 | — |
| D₆ | 12 | 147 | 0 | — |
| Dic₃ (Q₁₂) | 12 | 15 | 0 | — |
| D₃×Z₂ | 12 | 147 | 0 | — |
| D₇ | 14 | 322 | 0 | — |
| D₈ | 16 | 1235 | **48** | 16 critical edges (m=48, 5 orbits) |
| D₉ | 18 | 2049 | 0 | — |
| D₁₀ | 20 | 6275 | 0 | — |
| Dic₄ | 16 | 67 | 0 | — |
| Dic₅ | 20 | 205 | 0 | — |
| D₃×Z₃ | 18 | 233 | 0 | — |

**Zero (4,1)-witnesses.** Most non-abelian groups in this range yield NO
4-vertex-critical Cayley graph at all (same double-bind I found for abelian Cayley
graphs: symmetry kills vertex-criticality). Only D₈ (order 16) produced 48
four-vertex-critical Cayley graphs, and the best still has 16 critical edges out of
48 — far from a witness (1/3 critical, no better than circulants).

## Reading
- The vertex-transitive route is now mapped across cyclic (circulants), abelian
  (Z_a×Z_b), and non-abelian (dihedral/dicyclic/alternating) substrates, orders
  up to 20. **No witness, and the best symmetric approximations plateau at ~1/3
  critical edges (C₁₃(1,2,5) circulant is still the overall champion).**
- This is fully consistent with archivist's literature intel: the only known k=5
  witness (Brown, 17 vertices) is ASYMMETRIC / ad-hoc, NOT a Cayley graph; Jensen's
  symmetric k≥5 family is circulant and provably degenerates to χ=3 at k=4
  (jensen + Skottová–Steiner §5). So the symmetric route was always the long shot.
- **Verdict on the symmetric substrate: empirically exhausted at small order.** A
  k=4 witness, if it exists, is most likely asymmetric (Brown-style). Hand off to
  forge (gadget/asymmetric surgery) and hunter (asymmetric 6-regular CEGAR above the
  geng floor).

## Honest caveat
This does NOT rule out larger non-abelian groups or non-vertex-transitive graphs.
It is a bounded, well-defined negative over the natural symmetric families ≤ order 20,
confirming Steiner's lean extends beyond circulants to other Cayley substrates at
small order.
