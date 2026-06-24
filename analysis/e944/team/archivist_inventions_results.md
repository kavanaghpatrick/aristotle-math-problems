# archivist inventions — ROUND 1 results (all χ via checkers.py SAT)

Harness: archivist_inventions_run.py. Target: 4-vertex-critical, 0 critical edges.

## A3 — downward surgery on Z₁₇ k=5 witness — DEAD (as-is), useful diagnosis
- witness−v: χ=4 but NOT vertex-critical (vertex 0's deletion keeps χ=4). Removing a vertex from a vertex-critical graph generically de-criticalizes OTHER vertices.
- LESSON → round 2: a downward step must RE-CRITICALIZE. Pair vertex-deletion with edge-additions that restore "every vertex matters" without re-introducing a critical edge. The witness's edge-redundancy is intact (it had 0 critical edges); the lost property is vertex-criticality, which is the easier half to repair (add edges near the now-redundant vertices).

## A2 — entangled Hajós sum (shared triangle) — DEAD, IMPORTANT lesson
- two W5 sharing a triangle: χ=4, NOT vertex-critical (vertex 3 non-critical).
- two K4 sharing a K3: χ=4, NOT vertex-critical (vertex 3 non-critical).
- LESSON (this is the density-freezing wall biting LOCALLY): entangling two 4-critical graphs on a shared substructure makes the shared vertices NON-critical, because EITHER copy alone already forces χ=4 — so deleting a shared vertex doesn't drop χ. This is EXACTLY the trade algebra found globally: the redundancy that kills critical-EDGES (good) simultaneously kills vertex-CRITICALITY (bad). Entanglement over-stabilizes χ.
- POSITIVE COROLLARY: this confirms the redundancy↔vertex-criticality tension is the core difficulty, and localizes WHERE it bites (shared/over-connected vertices). A witness must distribute redundancy so NO single vertex is "doubly covered."

## A1 — Jensen–Siggers baseline + doubling experiments — DEAD via naive local surgery
- Baseline H(m=2): n=46, 111 edges, χ=4, vertex-critical, 63 critical edges. 0-critical-edge core B intact.
- DOUBLING TEST 1 (length-2 redundant path via fresh vertex across each critical edge): BREAKS vertex-criticality — the new degree-2 vertices are themselves non-critical (deleting one keeps χ=4). Edge-local-vs-vertex-local lesson: a redundant path adds a non-critical vertex.
- DOUBLING TEST 2 (add ONE edge between existing vertices near a critical edge, no new vertex, to back up its obstruction): tried 6 critical edges → 0 de-criticalized while keeping vertex-criticality; 2 broke vertex-criticality, 4 left the edge still critical. The J–S transfer-path criticality is structurally load-bearing — single local edge-additions cannot make it non-critical without over-stabilizing χ.
- VERDICT: naive local patching of J–S critical edges FAILS. The critical-edge obstruction in the transfer gadget is genuinely unique (1 obstruction per edge); adding a brace either misses it or kills vertex-criticality. Confirms the meta-lesson at gadget scale. A real fix needs the redundancy built into the gadget's GLOBAL design (two genuinely independent color-transfer mechanisms), not post-hoc local braces — heavier build, deferred.

## ROUND-1 META-LESSON (drives round 2)
The redundancy↔vertex-criticality tension (algebra's density-freezing wall) is now seen LOCALLY in two independent hybrids (A2, A3-failure). The design constraint crystallizes:
  **Redundancy must be EDGE-LOCAL, never VERTEX-LOCAL.** Each EDGE needs ≥2 independent obstructions (→ non-critical), but NO VERTEX may be covered by a redundancy that survives its deletion (→ stays vertex-critical). The J–S gadget (A1) is the only template that even approximately separates these (rigid core = edge-redundant but vertices still matter via the gadget). ROUND 2 targets the doubled-gadget version of A1.

# ROUND 2 results
## B1 — non-abelian Cayley (dihedral) — DEAD at the floor, near-miss below it
- D₅ (deg 4, n=10): χ=4, VERTEX-CRITICAL, 10/20 critical (half non-critical near-miss) — but below Prop 5.1 floor.
- Full symmetric gen-set sweep D₆…D₉ at deg 6–8, n≥11: ZERO vertex-critical. Density-freezing wall, 3rd independent confirmation.

# ROUND 3 results
## B2/B3 family — Mycielskian & dense vertex-critical graphs at the floor — DEAD (wrong extreme)
- Grötzsch (M(C₅), n=11): χ=4 vertex-critical but ALL 20 edges critical (fully edge-critical), δ=3.
- M(C₇) (n=15): χ=4 vertex-critical, ALL 28 edges critical, δ=3.
- Mycielskians give the OPPOSITE extreme from a witness: maximally edge-critical. Confirms Mycielski is the wrong primitive (matches the toolkit finding). Ear-augmenting these back toward non-critical hits the same A1 wall.

# BLITZ CONSOLIDATED VERDICT (after 3 rounds, 6 candidates, ~all dense families)
Across structural hybrids (A1/A2/A3), non-abelian Cayley (B1), and Mycielskian/dense-vertex-critical (B2/B3), EVERY structured construction either:
 (i) is vertex-critical but too sparse (δ<6, n<11) — D₅, small examples, or
 (ii) reaches the δ≥6/n≥11 floor but LOSES vertex-criticality (over-stabilized) — dense Cayley, entangled sums, or
 (iii) is vertex-critical at the floor but FULLY edge-critical (every edge critical) — Mycielskians.
NO structured family lands in the witness band (δ≥6, n≥11, vertex-critical, FEW/zero critical edges). The edge-local/vertex-local constraint (R1) is the precise obstruction, and it is robust across construction TYPE. CONCLUSION: a k=4 witness, if it exists, is an IRREGULAR graph threading a narrow gap — not expressible as any clean algebraic/group/product/Mycielski family. This is search territory (forge SA, hunter SAT-CEGAR over asymmetric 6-regular n≥11), consistent with the literature (no published construction reaches k=4) and the collision scan (search is the least-contested angle). The blitz's structured candidates are exhausted of obvious leads; the one un-built structured idea (B2 ear-routing with shared ear-vertices) is a long shot against the same wall.
