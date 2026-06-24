# E944 — ENC-11 roomy asymmetric search (count + proximity): the wall held

**Verification:** `python3 analysis/e944/team/enc11_roomy.py`. Exact χ. The decisive
test of proximity's hypothesis that the over-full corner is a cramming+symmetry artifact.

## proximity's hypothesis (the artifact theory)
The over-full corner (δ≥6 ⟹ all vertices non-critical) that every prior search hit
might be an ARTIFACT of (a) cramming δ=6 onto too few vertices (forge n=10 ⟹ near-K
density) and (b) symmetry/regularity. The test: search at n=13/14 (where δ=6 = 39/56
of edges, SPARSE, room to spare) with an ANTI-REGULARITY bias (reward degree variance,
keep |Aut| low, degrees mixed) — the ENC-7 asymmetric corner. If a witness exists in
the "easy" regime, this is where it should appear.

## Result — the wall HELD (decisive negative)
Both seeds (asymmetric, degrees 3-7, anti-regular SA toward δ≥6):
| n | best feasible-δ≥6 state reached |
|---|---|
| 13 | (χ=4, **5 non-critical vertices**, 9 critical edges, δ=6) |
| 14 | (χ=4, **2 non-critical vertices**, 13 critical edges, δ=6) — walks the trade curve; also hit (4, 9 ncV, 5 critE, 6) earlier |

The n=14 chain VISIBLY walks the trade curve: at it=2500 it was at (9 non-critical
vertices, 5 critical edges); by it=7500 at (2 non-critical vertices, 13 critical
edges). It trades one debt for the other along a continuum, never reaching (0,0).
**With room AND asymmetry, the search STILL cannot reach (critE=0, δ≥6, vertex-
critical).** Closest in the vertex-criticality dimension: n=14 with only 2 non-
critical vertices, but then 13 critical edges (= n, the plateau).

## Why this is the cleanest impossibility signal in the whole assault+blitz
It removes BOTH artifacts proximity flagged:
- NOT cramming: n=13/14 has ample room for δ=6 (sparse, ≤50% density).
- NOT symmetry: explicitly asymmetric (anti-regularity reward, mixed degrees 3-7→6+).
And the wall STILL holds — the search lands on the (critE, ncV) trade curve and
cannot reach its (0,0) intersection. Combined with everything prior, the obstruction
is now confirmed independent of:
- basin (circulant / Mycielski / random / forge-champion / asymmetric-seeded)
- granularity (single / multi-edge / degree-lifting)
- density regime (cramped n=10 / roomy n=13-14)
- symmetry (vertex-transitive circulants / anti-regular asymmetric)

## Honest status
No witness. This is heuristic, NOT a proof — SA can miss a needle. But the
artifact-free negative is the strongest empirical statement the search side can make:
the three conditions {δ≥6, vertex-critical, critical-edge-free} appear to lie on
mutually exclusive regions across every controlled variation. This is precisely the
empirical content of the conjectured impossibility lemma. The actual resolution needs
the structural proof (wall's f-invariant / a min-conflict≥2 argument); the search side
is now saturated and consistently negative across all controls.
