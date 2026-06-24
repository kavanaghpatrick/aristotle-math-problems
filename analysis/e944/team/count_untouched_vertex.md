# E944 — forge's discriminating test: untouched-by-E* vertices (count + forge)

**Verification:** `python3 analysis/e944/team/untouched_vertex_test.py`. Exact χ.

## The test (forge's discriminant, resolving our interpretation difference)
I had read fragmented E* (critical-edge subgraph splitting into components) as
existence-leaning. forge correctly pointed out: fragmentation is NOT existence-leaning
if E* still SPANS all vertices (every vertex has a critical edge ⟹ not a witness).
The real discriminant: a 4-vertex-critical graph with a vertex UNTOUCHED by E* (no
incident critical edge) = a "wall-balanced" vertex = a LOCAL instance of the witness
condition. **A witness is a graph where ALL vertices are untouched.** So: can even ONE
vertex be untouched, and if so, at what degree?

## Result — untouched vertices do NOT appear in the feasible regime
| regime | 4-vtx-critical graphs with an untouched vertex? |
|---|---|
| census n≤7 (EXHAUSTIVE, atlas) | **NONE** — E* always spans |
| dense n=11, δ≥6 (2000 samples) | **NONE** |
| dense n=12, δ≥6 (2000 samples) | **NONE** |

The ONLY place an untouched vertex was ever observed: my n=13 SA near-witness at
critE=9, which had **min-degree 4 (infeasible — Prop 5.1 needs δ≥6)**. So:
- forge's champion: E* fragmented {5,5} but SPANS all 10 vertices (0 untouched) — not
  a witness, confirmed.
- Untouched vertices are rare and, where seen, tied to LOW-DEGREE (δ=4) structure.
- **No untouched vertex appears at δ≥6 in anything tested**, and none at all on n≤7.

## Interpretation (concession + the sharpened impossibility constraint)
I concede forge's point: fragmentation alone is not existence-leaning; spanning E* is
the discriminant, and forge's champion's E* spans. The discriminating test resolves
toward IMPOSSIBILITY: even a SINGLE wall-balanced vertex (the local witness condition)
does not occur in feasible (δ≥6) 4-vertex-critical graphs. A witness needs ALL vertices
wall-balanced; the data says you can't get even one at δ≥6.

This adds a new, sharp constraint to the impossibility picture:
**"untouched-by-E* ⟹ low-degree"** empirically — a vertex with no critical edge in a
4-vertex-critical graph appears only at low degree, never at the δ≥6 a witness requires.
Combined with the absorber-suppression result (f≥2 ⟹ near-zero absorbers in the dense
regime), both the EDGE side (E* spanning) and the COCYCLE side (absorber suppression)
say the witness conditions evaporate exactly in the feasible regime.

## Honest caveat
Sampled (no nauty for n≥8 exhaustive) — but census n≤7 is exhaustive and dense n=11,12
sampling is substantial. NOT a proof. The discriminating lead forge proposed (untouched
vertex at δ≥6) was not found; if anyone produces one, that IS the existence lead and
gets triple-verified. As stands, it's another impossibility constraint, and I was
over-reading fragmentation — forge's spanning-E* framing is the correct one.
