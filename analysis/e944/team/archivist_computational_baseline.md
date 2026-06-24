# E944 — Prior computational searches (baseline for hunter)

Verified via Grok live web+X search (June 2026) + the two 2025 ETH papers. Calibration per squad protocol: stated as published-or-not, not as nonexistence proofs.

## HEADLINE: No exhaustive search of the (4,1)-graph property has EVER been published.
No published work enumerates all (unrestricted) 4-vertex-critical graphs on n vertices and checks whether each has a critical edge. No SAT-based or nauty/geng-based search targeting Dirac k=4 is documented. Skottová–Steiner Problem 5.2 (6-regular (4,1)-graph?) has NO reported computational attempt. The erdosproblems.com/944 forum has NO mention of computer searches.
⟹ **hunter's exhaustive floor + targeted search would be genuinely NOVEL** — there is no prior baseline to beat, only to establish.

## What HAS been computed (restricted families — context, not the target)
- **P₆-free / P₇-free 4-critical & 4-vertex-critical** (Chudnovsky et al., House of Graphs): exactly 2,608 4-critical and 62,126 4-vertex-critical P₇-free graphs on ≤16 vertices; 24 4-critical and 80 4-vertex-critical P₆-free graphs; tables up to 15 vertices (e.g. 2,214 4-critical P-restricted graphs on ≤15 vertices). NONE of these enumerations checks the critical-edge property. Source: web.math.princeton.edu/~mchudnov/P6.pdf; houseofgraphs.org/meta-directory/critical-h-free.
- **Brinkmann / Royle-style catalogs** of small 3-/4-critical graphs exist for specific settings (even order, planar 4-valent, surface embeddings) — but not the unrestricted no-critical-edge check.
- **House of Graphs** (houseofgraphs.org) hosts 4-critical / 4-vertex-critical graphs mostly in restricted (H-free) classes; NO complete catalog of all small unrestricted 4-vertex-critical graphs.
- **Goedgebeur–Schaudt 2018**, "Exhaustive generation of k-critical H-free graphs", J. Graph Theory 87:188-207 (arXiv:1506.03647); program CriticalPfreeGraphs. ONLY generates H-FREE restricted classes, not the full enumeration. NOT useful for filtering the unrestricted search.

## VALIDATION of hunter's enumeration (counts of 4-vertex-critical graphs by order, ALL have a critical edge)
hunter's sequence: n4=1, n5=0, n6=1, n7=7, n8=8, n9=124, n10=2453 — zero (4,1)-witnesses through n=10.
Literature cross-check (archivist, June 2026):
- n=4 → 1 = K₄ (unique). CORRECT by definition.
- n=5 → 0. CORRECT (standard fact).
- n=6 → 1 = wheel W₅ = K₁+C₅ (the standard non-complete 4-critical graph). CORRECT.
- n=7 → 7. ★ MATCHES published computational claim (MathOverflow "number of vertices in k-critical graphs", 2017: "exactly seven 4-critical graphs on 7 vertices"). Independent verification of the checker.
- n=8,9,10 → 8, 124, 2453: NOT in any published table; NOVEL extensions, consistent with all known facts. No OEIS sequence exists for unrestricted 4-vertex-critical counts.
⟹ hunter's sequence is the most complete unrestricted enumeration by order in existence; record as a standalone result. No catalog to filter against ⟹ raw enumeration is the right approach.

## SCALE anchor (smallest known witness at the next case up)
**Brown's k=5 witness has 17 vertices** (confirmed June 2026). The smallest known no-critical-edge graph at the easiest neighboring case (k=5, k−1=4 composite) is order 17. Combined with the proven n≥11 floor: a k=4 witness, if it exists, is plausibly at n≥11 and could be substantially larger. Do not expect tiny.

## HARD constraints to seed the search (from Skottová–Steiner Prop 5.1, see archivist_master_toolkit.md)
Any (4,1)-graph G on n vertices:
- edge-connectivity ≥ 6, min degree δ ≥ 6
- max degree Δ ≤ n − 5
- n ≥ 11  (⟹ no (4,1)-graph on ≤10 vertices; PROVABLE skip, not just search)
- sparsest possible = 6-REGULAR. Open Problem 5.2: does a 6-regular (4,1)-graph exist? ← authors' recommended first search target.
- Circulants PROVABLY cannot be (4,1)-graphs (S–S §5) → exclude all circulants.

## Search strategy recommendation for hunter
1. Establish the verified FLOOR: confirm via exhaustive enumeration (geng/nauty) that no (4,1)-graph exists for n = 11, 12, 13, … as far as feasible. The δ≥6 + 6-regular constraint massively prunes (6-regular graphs on n vertices are far fewer than all graphs). For n=11..~16, enumerate 6-regular (or min-degree-6) graphs, compute χ (must be 4), test vertex-criticality, then test no-critical-edge.
2. Above the geng floor: SAT/CEGAR encoding of "(4,1)-graph on n vertices" restricted to 6-regular, with symmetry breaking. The no-critical-edge condition = for every edge e, G−e is NOT 3-colorable, i.e. G−e still needs 4 colors. Encode as: G is 4-chromatic ∧ G−v is 3-colorable ∀v ∧ G−e is 4-chromatic ∀e.
3. CALIBRATION (squad protocol): a "not found up to n=N" result is a VERIFIED LOWER BOUND on the smallest example, NOT evidence of nonexistence. The Jensen–Siggers construction shows (4,ε-fraction)-graphs exist at large n; a true (4,1)-graph, if it exists, may live at large n. Report any negative as "smallest (4,1)-graph, if any, has > N vertices."
