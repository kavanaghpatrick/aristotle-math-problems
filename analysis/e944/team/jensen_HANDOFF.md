# jensen — HANDOFF (e944 squad, 2026-06-10)

Snapshot for the successor "jensen". My lane: dissect-and-repair the known
constructions; now redirected by team-lead to the **Jensen–Siggers ASSAULT**.

## ASSAULT COMPLETE (added after handoff was first written) — see jensen_siggers_assault.md
Built + VERIFIED the Jensen–Siggers k=4 near-miss exactly (jensen_code/jensen_siggers.py;
matches archivist's independent build at m=3 n=67): χ=4, vertex-critical, core
B=K_{2m,2m,2m} has 0 critical edges, all critical edges in gadget G, E* connected+spanning.
Then PROVED the gadget-surgery route to a witness is dead:
- Naive 2nd-gadget overlay (js_surgery.py): χ=4 but NOT vertex-critical (each gadget
  independently sufficient with B → internal vertices of the other become non-critical).
- Refined jointly-necessary / double-cover (js_joint.py, js_shared_star.py): also NOT
  vertex-critical. Partial gadgets need ALL 3 chains to bite; double-covering a chain
  to make its edges redundant kills that chain's interior vertex-criticality.
- ROOT CAUSE (verified): transfer chains are PATHS with pendants → interior edges are
  BRIDGES → no within-chain reroute → edge-redundancy needs a parallel chain → parallel
  chain destroys vertex-criticality. The "rigid core + tree-like gadget" architecture
  provably cannot reach 0 critical edges.
- WITNESS SPEC (handed forge/wall): each edge's covering obstruction must be 2-EDGE-
  CONNECTED through that edge (within-obstruction reroute) AND killed by a vertex deletion.
  Density (gallai δ≥6) supplies this; bridges are fatal. Matches archivist's algebra-side
  R2 (density/redundancy wall) and wall's spanning-H_e tension — three independent routes
  to the same conclusion: a k=4 witness must be DENSE + ASYMMETRIC, not a structured gadget.

## 1. VERIFIED RESULTS + FILE POINTERS (all computationally checked)
- **Harness** `analysis/e944/team/jensen_code/harness.py`: exact χ via TWO
  independent engines (backtracking + DSATUR-exact) that MUST agree; vertex-crit,
  critical-edge, full E944 checker. Self-tests on K4/C5/Petersen/Grötzsch.
  **Cross-validated 3-ways** against count's `critedge.py` — all χ agree on a
  battery incl. the k=5 witness. TRUST THIS HARNESS.
- **Jensen'02 fully dissected** → `jensen_dissect_jensen2002.md`,
  `jensen_code/circulant_analysis.py` (build_Gkmq), `verify_circulants.py`,
  `why_k4_breaks.py`. VERIFIED genuine **k=5 witness G_{5,2,2} on N=17** (χ=5,
  vertex-crit, 0 critical edges); also G_{5,3,2} (N=25), G_{5,2,4} (N=33),
  k=6 G_{6,2,2} (N=41). **Exact k=4 death:** distance set D1∪D2∪D3; chromatic
  boost lives ONLY in D2 (width (k−5)m+2 odd / (k−6)m+3 even) and D3; at k=4
  |D2|=|D3| = 3−2m ≤ 0 ∀m≥2 → both EMPTY → only odd distances survive → χ≤3.
  Not even 4-chromatic. (gallai used build_Gkmq to validate δ≥2(k−1): G_{5,2,2}
  has δ=8 exactly — tight.)
- **Brown'92 + Lattanzio'02** → `jensen_dissect_brown_lattanzio.md`. Literal
  graphs UNAVAILABLE (paywalled; Jensen–Toft §5.14 has no adjacency; no citing
  paper reproduces them). DO NOT waste time chasing Brown's explicit graph, and
  DO NOT trust any LLM "Brown graph" (Grok hallucinated a 22-vertex one + falsely
  claimed Dirac settled k=4). Arithmetic role pinned: k−1=a·b composite gives a
  2D redundancy axis; k=4→k−1=3 prime→1D→no edge double-cover.
- **Circulant k=4 witness search** `jensen_code/circulant_k4_search.py`: ZERO
  witnesses for |S|≤4, N∈[5,26]. Corroborates count's larger circulant sweep.
- **SHARED FAILURE MODE (the synthesis):** no-critical-edge needs every edge
  covered by ≥2 INDEPENDENT 4-coloring obstructions; all 3 constructions source
  this from a k-scaling resource; at k=4 there's only ONE spare color class after
  a deletion, which can't host two obstructions. (This is the conjecture wall
  RESTATED, not proven — wall owns rigor.) Cross-corroborated by proximity
  (M-S route empty: 5-vs-15 + min-deg≤4<6) and count (0 circulant/abelian-Cayley
  witnesses).

## 2. WORK IN FLIGHT / WHERE I STOPPED
Team-lead issued ASSAULT MODE (Jensen–Siggers gadget surgery) THEN a SNAPSHOT
order (restart imminent → write handoff, go idle). So I STOPPED before building
the J–S graph. I answered forge's + gallai's blocking questions (see their
inboxes). The assault is UN-STARTED — it's your job.

## 3. NEXT STEPS FOR SUCCESSOR (execute the assault)
Source of truth: `archivist_jensen_siggers_2012.md` (full extract; PDF text in
/tmp/jensen_siggers.txt). The J–S k=4 graph is EXPLICIT and non-circulant:
- **B(m) = K_{2m,2m,2m}** (parts S₁,S₂,S₃): unique 3-coloring, **ZERO critical
  edges** (Lemma 1). Build it; verify 0 critical edges with the harness.
- **G(m)** (star v₀+v₁v₂v₃ glued to color-transfer gadgets T₁,T₂,T₃ + leafed
  T'₁,T'₂,T'₃; Sᵢ identified with B's parts): n=21m+4, holds ALL Θ(n) critical
  edges. Build via Constructions 2–4 in the extract.
- **H = 4-critical subgraph of B(m)∪G(m)**: χ=4, vertex-critical, critical edges
  ⊆ E(G), Θ(n) of them.
STEPS: (1) build B(m), G(m), H for m=3,4 in networkx; VERIFY with the harness
(`from harness import *`) that H is χ=4 vertex-critical and that critical edges
all sit in G. (2) For EACH gadget edge, characterize which 3-colorings die when
it's removed (the harness's critical_edges + a per-edge coloring diff). (3)
SURGERY: overlay a SECOND gadget G'(m) so each critical edge of G gains a
redundant obstruction avoiding it (team-lead's "two gadgets covering each other"
— this IS the missing 2nd independent obstruction from the shared-failure-mode
analysis). Verify after each mutation; check vertex-criticality isn't broken and
χ stays 4. Even cutting Θ(n)→O(1) critical edges is a major advance.

## 4. TRAPS
- **VERTEX-critical ≠ edge-critical** (the central E944 trap; see gallai's
  VOCAB WARNING in CLAIMS.md). KY/Gallai density theorems are for edge-critical;
  the density HALF transfers (e(G)≥(5n−2)/3), the Gallai-forest structural half
  does NOT. Target object has NO critical edge by definition.
- **ncard infinite trap** (skeptic): the Lean statement only admits FINITE-edge
  (hence finite) witnesses. Don't reason over infinite V.
- **LLM graph hallucination**: never trust an LLM's "explicit Brown/Jensen graph."
  Rebuild from the J–S extract (open-access, real) and VERIFY with the harness.
- Surgery that adds edges can silently destroy vertex-criticality (a vertex stops
  being critical) — re-check is_vertex_critical AFTER every mutation, not just χ.
- Don't conflate Jensen'02 (circulant, k≥5) with Jensen–Siggers'12 (gadget, k=4
  near-miss). The assault is on the latter.
