# E944 INVENTIONS — archivist lane (structural HYBRIDS: combine pieces no paper combined)

(Kept in a separate file from INVENTIONS.md to avoid write-contention with algebra's lane; pointer added there.)

I know every construction's boundary (Brown/Lattanzio/Jensen/Jensen-Siggers/MS/SkSt) + every wall. My lane: invent the GAPS BETWEEN them. The redundancy principle (rigid core + disagreement gadget) is the only route to no-critical-edge; the open problem is engineering it dense+asymmetric at k=4. All candidates respect Prop 5.1 (δ≥6, n≥11) and target 4-vertex-critical, 0 critical edges. χ dual-verified vs checkers.py.

## ROUND 1 (archivist)

### A1 — Triangulated/doubled Jensen–Siggers transfer gadget (kill the residual critical edges)
- **Def:** The verified J–S H(m) has a rigid K_{2m,2m,2m} core (0 critical edges) + a disagreement gadget G whose SPARSE path/leaf transfer subgadgets T(m),T'(m) (degree ≤3) carry ALL ~Θ(n) critical edges. HYBRID FIX: replace each sparse path transfer-gadget by a DENSER "doubled" version — two internally-disjoint parallel color-transfer paths sharing endpoints, so deleting one edge leaves the parallel obstruction intact (redundancy) while still forcing the χ=4 disagreement.
- **Why no paper did this:** J–S explicitly say "E* was connected/spanning, we cannot see how to avoid." Nobody thickened the transfer gadget into a 2-connected redundant version.
- **Kill-test:** build doubled-T variant at small m; check χ=4 vertex-critical and whether #critical edges drops vs the single-path version.

### A2 — Entangled Hajós sum (share a TRIANGLE, not identify+single-edge)
- **Def:** Standard Hajós join → edge-critical (wrong). HYBRID: ENTANGLE two copies of a 4-critical graph by identifying a whole shared TRIANGLE, so each shared edge is double-witnessed by both copies' criticality → conjecture shared-triangle edges become NON-critical while the graph stays vertex-critical.
- **Why no paper did this:** Hajós/Dirac sums are always PARALLEL (disjoint except the identified vertex/edge). Entangling on a shared dense substructure is the un-tried variant — deliberately creating the edge-redundancy standard Hajós avoids.
- **Kill-test:** entangle two W5 copies on a shared triangle; score χ/vertex-crit/critical edges.

### A3 — k=5 witness → k=4 by downward surgery (run the ladder backwards)
- **Def:** We HAVE a verified k=5 witness (G_{5,2,2}/Z₁₇, 0 critical edges). Everyone builds UP (k→k+1); nobody runs a no-critical-edge witness DOWNWARD. Delete a vertex (χ drops to 4, but those are critical) and check whether witness−v is vertex-critical with FEW critical edges — the witness's rare edge-redundancy might partially survive the χ-lowering.
- **Kill-test:** for each v in Z₁₇ witness, score witness−v: χ, vertex-critical?, #critical edges.

## RESULTS — see archivist_inventions_results.md (run this round)

## ROUND 2 (archivist) — design against the edge-local/vertex-local constraint

### B1 — Non-abelian Cayley graph (dihedral D_n) — escapes ABELIAN circulant degeneracy
- **Def:** Cayley graph on the dihedral group D_n (order 2n) with a symmetric generator set mixing rotations and reflections. Non-abelian ⟹ NOT a circulant ⟹ dodges W2's abelian distance-set degeneracy.
- **Why:** algebra showed the Z₃ wall is associativity/symmetry-induced; a non-abelian group breaks the global shift-symmetry while staying vertex-transitive and tunable in degree.
- **Kill-test + RESULT:** D₅ (order 10, deg 4): χ=4, VERTEX-CRITICAL, 10/20 critical edges (half non-critical — a real near-miss, but n=10<11 and deg 4<6, can't be a witness). D₆ (order 12, deg 6): χ=3 (degenerate). D₇,D₈ (deg 6, n=14,16): χ=4, δ=6 (meets Prop 5.1 floor!) but NOT vertex-critical. VERDICT: non-abelian Cayley reaches the δ≥6/n≥11 regime but loses vertex-criticality there — same Goldilocks gap as every dense construction. PARTIAL LEAD: D₅'s half-non-critical at the sparse end is worth a parameter sweep (other gen sets / groups A4, Q8) to find a vertex-critical point at deg≥6.
- **SWEEP DONE (full symmetric gen-set sweep over D₆…D₉, deg∈[6,8], n≥11):** NO vertex-critical graph found. DEAD. Independently re-confirms the density-freezing wall from a THIRD angle (non-abelian Cayley), after structural hybrids (A1/A2/A3) and algebra's quasigroup-circulants. The D₅ near-miss lives only at deg 4 / n=10, below the Prop 5.1 floor — the Goldilocks gap is real and robust across construction families.

### B2 — Asymmetric "ear-augmented" 4-critical graph (edge-local redundancy by design)
- **Def:** start from a sparse 4-critical graph (Hajós-built), then add EARS (paths through NEW vertices) so each original critical edge gets a second obstruction-path, BUT route ears so each new vertex lies on ≥2 ears (forcing it critical — fixes the A1-doubling failure where ear-vertices were non-critical).
- **Why dodge:** directly engineers "every edge in ≥2 obstructions" (edge-local) while "every vertex on ≥2 ears" keeps vertices critical (not vertex-local redundancy).
- **Kill-test:** [round-3 build — needs the ear-routing constructor]

### B3 — Johnson/Kneser-graph slice with tuned intersection threshold
- **Def:** vertices = k-subsets of [m]; adjacency by |intersection| in a chosen band. Pick (m,k,band) giving χ=4; these are dense, vertex-transitive, non-circulant, with rich automorphisms (NOT abelian-circulant).
- **Why dodge:** Kneser graphs have χ controlled by Lovász (χ(Kneser(m,k))=m−2k+2); a Johnson-band slice could land at χ=4 with high redundancy from the combinatorial symmetry.
- **Kill-test:** [round-3 — enumerate small (m,k,band) with χ=4, score]
