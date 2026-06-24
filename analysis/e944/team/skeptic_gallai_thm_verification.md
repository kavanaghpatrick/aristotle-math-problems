# E944 — Independent re-derivation of gallai Theorem 2 & Theorem 4 (skeptic)

gallai asked me to adversarially re-derive their two load-bearing local results on my OWN census,
with my OWN from-scratch code (NOT importing gallai_crit.py's edge_noncritical_local). Done.

## Method (independent)
- My own `proper_3cols_minus_u(G,u)`: brute-force enumerate EVERY proper 3-coloring of G−u.
- My own `rainbow_forced(u,v)`: True iff in every such coloring, N(u)∖{v} uses all 3 colors.
- Cross-checked against my own `crit_edge` (= χ(G−e) < χ(G), via chi_A) over ALL 4-vertex-critical
  graphs n≤9 (geng enumeration, 141 graphs, 2303 edges).

## THEOREM 2 (rainbow-forcing characterization) — CONFIRMED
> uv critical ⟺ NOT (in every proper 3-coloring of G−u, N(u)∖{v} uses all 3 colors).

Result: **2303 edges checked across all 141 four-vertex-critical graphs n≤9, ZERO mismatches.**
Every edge's directly-computed criticality matched the rainbow-forcing prediction exactly. This
extends gallai's own verification (n≤7, 103 edges) to n=8 and n=9 with an INDEPENDENT implementation.
The proof in gallai_local_structure.md is sound; the characterization is correct. ★ This is the
load-bearing local non-criticality certificate — now independently confirmed.

## THEOREM 4 (forced 2-2-2 balance at a deg-6 all-non-critical vertex) — VACUOUSLY confirmed n≤9
> If u has degree 6 and ALL incident edges are non-critical, then N(u) is colored exactly 2-2-2
> in every proper 3-coloring of G−u.

Result: **0 such vertices exist in any 4-vertex-critical graph n≤9** (checked, 0 mismatches among 0
instances). HONEST CAVEAT: the theorem's HYPOTHESIS (deg-6 vertex with all incident edges
non-critical) is NEVER satisfied at n≤9 — consistent with my Problem 5.2 finding that no 6-regular
4-vertex-critical graph exists below n=13, and the lone n=13 one (C₁₃(1,2,5)) HAS critical edges.
So my census cannot empirically distinguish Theorem 4 from any vacuously-true statement at small n;
the support for it is the PROOF (gallai derives it from Theorem 3's argument), not the census.
Theorem 4 will only get a non-vacuous empirical test once a deg-6 all-non-critical vertex appears —
which by definition only happens at/near an actual witness. Its logical content is sound regardless.

## Verdict
- Theorem 2: independently CONFIRMED, n≤9, 2303 edges, 0 mismatches. Solid, usable as the O(1)-per-edge
  local prune for hunter/forge.
- Theorem 4: proof sound; empirically vacuous at small n (hypothesis never met). Not a defect — just
  means it's a witness-regime statement, untestable by census until a witness-like vertex exists.
