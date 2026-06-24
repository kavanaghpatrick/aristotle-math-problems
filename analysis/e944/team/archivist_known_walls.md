# E944 — KNOWN WALLS: every published obstruction to k=4 (canonical list)

Maintained by archivist. Integrates literature (Brown/Lattanzio/Jensen/Jensen–Siggers/Martinsson–Steiner/Skottová–Steiner) with squad computational/structural results. "Wall" = a reason a particular route to k=4 fails. NONE is a full impossibility proof; k=4 is genuinely open in BOTH directions.

## W1. Lattanzio tensor-product wall — k−1 must be composite
k−1 = 3 is prime ⟹ no nontrivial factorization ⟹ Lattanzio's product construction has no factors. Blocks the product route for k=4 (and k=6,8,…; but Jensen 2002 covers those via a different method). [La02; archivist_constructions_why_k4_fails.md]

## W2. Circulant / Cayley wall — provably χ=3 at k=4
Skottová–Steiner §5 (verbatim): for k=4 the circulant distance set degenerates (D₂=D₃=∅, only odd distances D₁ survive) ⟹ the circulant is essentially an odd cycle ⟹ χ=3, not 4. Jensen's color-pattern (the k≥5 engine) forbids distances >1 at k=4, leaving an odd cycle. AUTHORS BELIEVE no circulant (4,1)-graph exists. [S–S 2025 lines 1283-1292] CORROBORATED by squad: count's circulant/Cayley search (C_n(S), n≤22) — IN PROGRESS, expected empty per this wall.

**SYMMETRY of the known witnesses (count's question, answered June 2026):**
- **Brown 1992 (k=5): 17 vertices, AD-HOC / ASYMMETRIC.** NOT vertex-transitive, NOT circulant, NOT Cayley. The first-ever witness was hand-built, not symmetric.
- **Jensen 2002 (all k≥5): CIRCULANT** (vertex-transitive, Cayley on ℤ_N). The k≥5 family lives in the circulant world — but exactly that world collapses to χ=3 at k=4 (this wall).
- **Lattanzio 2002: circulant-adjacent** (block-circulant/matrix-like per secondary sources), transitivity not confirmed.
STRATEGIC IMPLICATION: the only symmetric route (circulant) is provably dead at k=4; the only working asymmetric example (Brown, 17 vtx) suggests a k=4 witness, if it exists, is more likely AD-HOC/ASYMMETRIC than a clean circulant. Search priority: bounded circulant sweep to empirically confirm/refute S–S's belief (publishable either way), then pivot to asymmetric / Brown-style / gadget (Jensen–Siggers) constructions.

## W3. Martinsson–Steiner hypergraph wall — arithmetic forces χ≤3 + degree too low
The complement-of-2-section construction gives χ=(n−1)/s+1 with α=s; at the unique admissible n it forces χ≤3 (archivist), and proximity proved (proximity_rung_h.md, VERIFIED two ways): (R1) the M-S sufficient condition is SAT-INFEASIBLE at the only admissible n=13 (property (i) forces ≥5 hyperedges but local-sparsity (ii) then fails); (R2) the densest graph the route can reach has min-degree ≤4 < 6 = the Prop 5.1 floor. So M-S graphs are structurally far too sparse to be (4,1)-graphs. The M-S route is EMPTY at k=4. [MS 2025; proximity]

## W4. Density / degree necessary conditions — any (4,1)-graph is forced dense
Skottová–Steiner Prop 5.1 (PROVEN necessary conditions, archivist_master_toolkit.md): any (4,1)-graph has edge-connectivity ≥6, δ≥6, Δ≤n−5, n≥11, sparsest possible = 6-regular. These RULE OUT all sparse candidates and tiny graphs. Independently re-derived from the hypergraph side by proximity. Used by wall to argue "a witness must be dense." [S–S 2025 Prop 5.1]

## W5. Small-n exhaustion wall — no witness exists for small graphs
Independent squad enumerations agree: skeptic (geng+backtrack+SAT, every χ cross-checked) and count (census) find ZERO (4,1)-graphs for n=4..9 (counts of 4-critical graphs: n=4..9 → 1,0,1,7,8,124, all have a critical edge). Combined with Prop 5.1's n≥11 (proven), the smallest possible (4,1)-graph has n≥11. hunter establishing the verified floor at n=11,12,13,…. CALIBRATION: this is a LOWER BOUND on the smallest example, NOT nonexistence — a true witness may live at large n (cf. J–S near-misses at large n). [skeptic, count, hunter]

## W6. Jensen–Siggers connected/spanning-E* wall (CONJECTURAL impossibility lever)
J–S 2012 built 4-vertex-critical graphs with only Θ(n) critical edges (of Θ(n²)) — but in EVERY example the critical-edge set E* is CONNECTED and SPANNING, and they "cannot see how to avoid this." CONJECTURE (theirs): if Dirac k=4 is FALSE, then E* may be forced connected/spanning. Proving "|E*|≥1 always" (with structure) would refute k=4. This is the sharpest IMPOSSIBILITY-direction target. [J–S 2012; archivist_jensen_siggers_2012.md] → wall/count own this.

## W7. k=3 degeneracy (why the problem starts at k=4)
3-vertex-critical = 3-critical = odd cycles, all edge-critical (E* = all edges). The vertex/edge-critical distinction is VOID at k=3 and first appears at k=4. So k=4 is intrinsically the hardest small case — no smaller case gives a pattern to extend. [J–S 2012; S–S 2025]

---
## What is NOT a wall (open in both directions)
- No published IMPOSSIBILITY proof for k=4 in general. All walls W1–W3 kill SPECIFIC construction templates, not all graphs.
- No exhaustive computational search of the (4,1) property was ever published before this squad (archivist_computational_baseline.md). hunter's floor is novel.
- The POSITIVE route remains open: Jensen–Siggers shows the construction is "Θ(n) critical edges away" from success; killing that linear core (W6 construction side) would resolve k=4 YES. Skottová–Steiner gluing (Lemma 2.1, k≥4) means ONE seed ⟹ infinitely many.

## VOCAB TRAP (gallai) — applies to W4/W6 usage
Kostochka–Yancey density (e≥(5n−2)/3) and Gallai low-vertex theorems are EDGE-critical theorems. The target is a vertex-critical graph that is NOT edge-critical. KY/Gallai do not directly bound it; track transfer carefully. [gallai_vocab_trap.md]
