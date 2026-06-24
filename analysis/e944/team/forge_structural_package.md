# forge — STRUCTURAL DATA PACKAGE for the fresh-toolkit levers (2026-06-11)

My role (team-lead): structural-data supplier for the fresh levers. This is the
CANONICAL set of discriminating test graphs. Every lever (wall hom-complex, count
entropy, algebra flow-duality) should test against THESE, not convenient examples.
Verified data (g6 + properties) in `forge_structural_package.json`. All χ /
vertex-criticality / |E*| dual-checkable via checkers.py.

## The discriminating graphs (and WHY each matters)

| name | n | m | χ | vtx-crit | |E*| | E* span | E* comp | the discriminating role |
|------|---|---|---|---|---|---|---|---|
| **n10_champion** ICpdbY{]_ | 10 | 22 | 4 | YES | 8 | yes | 2 | the min-|E*| 4vc graph; irregular (|Aut|=4); E* in 2 comps. The "redundancy record" — closest VERTEX-CRITICAL graph to a witness. |
| **C13(1,2,5)** | 13 | 39 | 4 | YES | 13 | yes | 1 | unique 6-regular 4vc graph at n=13; |E*|=one full diff-orbit; the SYMMETRIC near-miss. |
| **C14(1,2,5)** | 14 | 42 | 4 | NO | 0 | — | — | 6-regular, χ=4, |E*|=0 — the DENSE no-critical-edge case, but NOT vertex-critical. Closest on the |E*|-axis; fails the vertex axis. |
| **cocktail K_{2,2,2,2}** | 8 | 24 | 4 | NO | 0 | — | — | smallest |E*|=0 χ=4 graph; the canonical ALMOST-WITNESS (|E*|=0 but every vertex removable, partition-robust). |
| **K(6,2) Kneser** | 15 | 45 | 4 | NO | 0 | — | — | 6-regular, |E*|=0, passes ALL SkSt filters (δ≥6, edge-conn≥6, n≥11) BUT vertex-transitive |Aut|=720 — dense almost-witness, dead by symmetry. |
| **GQyurg** | 8 | 16 | 4 | NO | 0 | — | — | K₄-FREE (ω=3) |E*|=0 χ=4 — refutes "|E*|=0 ⟹ contains K₄". Forces the proof to be COLORING-structural, not clique-based. |
| **G_5,2,2** (Z17) | 17 | 68 | 5 | YES | 0 | — | — | k=5 WITNESS, 8-regular. CONTROL #1 — every lemma's claim must FAIL here (it's a genuine (5,1)-witness). |
| **G_5,2,4** (Z33) | 33 | 198 | 5 | YES | 0 | — | — | k=5 WITNESS, 12-regular. CONTROL #2 (archivist) — second independent k=5 escape; robustness check. |

## How to USE these per lever (test the RIGHT example, not the convenient one)

**The discriminating axis.** A witness needs BOTH (vertex-critical) AND (|E*|=0).
The almost-witnesses each have exactly ONE:
- VERTEX-CRITICAL but |E*|>0: n10_champion (|E*|=8), C13 (|E*|=13). [the "vertex axis is satisfied" examples]
- |E*|=0 but NOT vertex-critical: cocktail, K(6,2), C14(1,2,5), GQyurg. [the "edge axis is satisfied" examples]
- BOTH (the witness) at k=4: NONE exists (exhaustive n≤12). At k=5: G_5,2,2, G_5,2,4.

**So any lever's candidate invariant Φ must:**
1. SEPARATE vertex-critical-with-|E*|>0 from |E*|=0-not-vertex-critical at k=4
   (test on n10_champion / C13 vs cocktail / K(6,2) / C14 / GQyurg).
2. Be NONZERO/obstructing on a real witness at k=5 in the WRONG way — i.e. Φ must
   NOT obstruct G_5,2,2 and G_5,2,4 (else Φ would "prove" k=5 impossible, which is
   false). This is wall's k=5 tripwire, MANDATORY.
3. For impossibility: Φ must obstruct EVERY k=4 graph that is vertex-critical
   (forcing |E*|>0) — test it kills n10_champion's path to |E*|=0.

**Lever-specific pointers:**
- wall (hom-complex/topology): compute the obstruction on the CONCRETE complexes of
  these graphs. The cocktail K_{2,2,2,2} is the cleanest |E*|=0 topological object
  (complete multipartite = join structure, simple hom-complex). GQyurg is the
  K₄-free stress test (no simplicial-clique shortcut). G_5,2,2 must come out
  obstruction-FREE (it's a witness).
- count (entropy): the n10_champion (min |E*|, irregular) and C13 (regular, |E*|=n)
  are the entropy-extreme pair. The |E*|=0 set (cocktail/K(6,2)/C14) are the
  "zero-entropy-on-E*" cases that must be shown non-vertex-critical.
- algebra (flow-duality): C13/C14 are the cleanest ℤ₃-tension pair (n=13 critical
  orbit vs n=14 |E*|=0). G_5,2,2 (k=5, |E*|=0) is the ℤ₄-tension control — the flow
  obstruction must distinguish ℤ₃ (k=4) from ℤ₄ (k=5).

## Companion proven facts (the structural backbone)
- E*-degree SLOPE LEMMA (forge, proven): E*-deg(v) ≥ max(0, 6−deg(v)). Local, tight,
  k=4-specific. (forge_extremal_findings.md)
- B₁ = ½Σ_v cnt(v) localization (forge). (forge_B1_localization.md)
- vertex-spanning / |E*|≥⌈n/2⌉; no witness n≤12 (all degrees); ~556K |E*|=0 graphs
  all non-vertex-critical; K₄-route refuted.
- The irreducible core: "every deg-6 vertex 2-2-2-balanced in every G−v 3-coloring
  simultaneously" (gallai Thm 4 / q=3 CSP). NOT to be ground directly (team-lead).
