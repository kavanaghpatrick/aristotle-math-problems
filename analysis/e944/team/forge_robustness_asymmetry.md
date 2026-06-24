# forge — The robustness-asymmetry principle (why every global mechanism fails)

A unifying conceptual finding from the invention mandate, spanning ALL mechanisms
tested (J-S tripartite core, voltage covers, biwheels, Youngs quadrangulations,
Kneser/Schrijver). Candidate impossibility lever for wall/skeptic.

## The observation
A (4,1)-witness must simultaneously be:
- **EDGE-robust**: χ stays 4 after deleting ANY single edge (no critical edge).
- **VERTEX-fragile**: χ drops below 4 after deleting ANY single vertex (vertex-critical).

Every GLOBAL χ=4 mechanism I tested derives its edge-redundancy from a *robustness*
of the obstruction to LOCAL perturbation. But that same robustness makes the
obstruction survive VERTEX deletion too — because deleting a vertex is "less" than
the global obstruction can absorb. Concretely:

| mechanism | obstruction | why edge-robust (|E*|=0) | why ALSO vertex-robust (not vc) |
|---|---|---|---|
| Kneser K(6,2) | Borsuk-Ulam ℤ₂ | topological invariant survives 1 edge loss | survives 1 vertex loss too (K(5,2)-ish still obstructed) |
| voltage cover of C₁₃ | doubled odd structure | twin copy carries obstruction | twin copy carries it after vertex deletion too |
| biwheel (2 apexes) | two parallel apex-forcings | one apex backs up the other per edge | one apex backs up the other per vertex too |
| J-S tripartite core B | rigid unique 3-coloring | coloring forced by many edges | (B alone IS vertex-robust; J-S BOLTS ON the fragile gadget G to fix this — at the cost of degree-3 vertices ⟹ E*≠∅) |

## The principle (conjectural, unifying)
> A χ=4 obstruction that is robust enough to survive every single-EDGE deletion
> (giving E*=∅) is, by the same robustness, robust to every single-VERTEX
> deletion — so the graph is not vertex-critical. To FORCE vertex-criticality you
> must make the obstruction fragile, which reintroduces critical edges.

Jensen–Siggers is the ONE construction that breaks the symmetry: it keeps an
edge-robust core (B) and bolts on a SEPARATE vertex-fragile gadget (G) to force
vertex-criticality. But G must transmit a per-vertex disagreement, which (forge's
theorem) requires degree-3 transfer vertices, each contributing 3 critical edges.
So J-S pays for vertex-fragility with E* = Θ(n) ≠ ∅. The two requirements are
routed through DIFFERENT subgraphs, and the fragile one always leaks critical
edges.

## Status / honesty
This is a HEURISTIC unifying principle, NOT a proof — "robust to edges ⟹ robust
to vertices" is false in general (a single counterexample graph could decouple
them; that's exactly what a witness would be). But it explains, in ONE sentence,
why all five+ construction families and both invented global mechanisms fail the
same way, and it predicts the witness (if any) must DECOUPLE edge-robustness from
vertex-robustness — a property no natural mechanism supplies. For wall: a proof
that "edge-robust ⟹ vertex-robust" for χ=4 graphs would REFUTE Dirac k=4.
Combined with forge's degree-3 theorem (the fragile gadget needs low-degree
vertices ⟹ critical edges), this is the sharpest conceptual statement of the
obstruction the squad has.

## What would BREAK the principle (the witness signature)
A dense (δ≥6) graph whose χ=4 obstruction is robust to edge deletion but where
EVERY vertex is nonetheless load-bearing — i.e. the obstruction is "edge-spread"
but "vertex-concentrated." No mechanism supplies this; it is the precise target.

## jensen's death-mode arithmetic (2026-06-10) — sharpens the spec
jensen verified the exact k=4 failure of all 3 known constructions:
- Jensen'02 circulant: chromatic boost lives in distance intervals D2,D3 of width
  (k−5)m+2 / (k−6)m+3; at k=4 both = 3−2m ≤ 0 ⟹ empty ⟹ χ≤3. Needs k−1≥4 for a
  "long" distance.
- Lattanzio/Brown: need k−1 composite (2D redundancy axis); k−1=3 prime ⟹ 1D ⟹ no
  2nd axis.
- SHARED: no-critical-edge needs every edge covered by ≥2 INDEPENDENT 4-coloring
  obstructions. All 3 source this double-cover from a k-scaling resource. At k=4
  there are 3 color classes after a vertex deletion = ONE spare class, and one
  class can't host two independent obstructions.

jensen's CONSTRUCTIVE pointer (matches my entanglement spec): the missing "second
independent obstruction" = **two gadgets each covering the OTHER's critical edges**
(mutual cover), packed into δ≥6 with gallai's 2-2-2 balanced neighborhoods. This
is NOT my failed parallelization (which added a SEPARABLE redundant copy that
trims away) — it must be MUTUAL/entangled: gadget A's critical edges are redundant
because gadget B covers them and vice versa, with the two sharing vertices so
neither is vertex-removable. THIS is the precise target; testing next.

## Mutual-cover idea TESTED — fails for a deg-3 reason (2026-06-10)
jensen's "two gadgets covering each other's critical edges" — tested on the J-S
substrate (forge_mutual_cover.py) and resolved ANALYTICALLY by the deg-3 theorem:
adding a 2nd disagreement gadget on the same tripartite core gives 62 degree-3
vertices (vs 31 single, at m=2) — MORE, not fewer. Each gadget contributes its
OWN degree-3 transfer vertices; the other gadget does NOT raise their degree, so
by forge's theorem all those edges STAY critical. Mutual cover ADDS critical
edges, doesn't cancel them.

CRYSTALLIZED BARRIER: any gadget that transmits a PER-VERTEX disagreement (needed
for vertex-criticality) must use low-degree (degree-3) transfer vertices, and
those force critical edges. The ONLY way to make gadget A's critical edges
redundant is to RAISE the degree of A's degree-3 vertices to ≥4 — but raising
their degree means fusing structure at those vertices, which destroys the
transfer mechanism that made them carry the disagreement. This is the deg-3
theorem meeting jensen's spare-class arithmetic: vertex-criticality forces
low-degree transfer ⟹ critical edges; eliminating them destroys vertex-criticality.
The same antagonism, now pinned to the DEGREE of the transfer vertices.

## DIRECT TEST of the principle (forge-9 reverse-repair, 2026-06-10)
The robustness-asymmetry predicts: from a 0-critical-edge graph you CANNOT add
vertex-criticality without creating critical edges. Tested directly
(forge_reverse_repair.py): starting from K(6,2) (|E*|=0, 6-regular, all 15
vertices removable), NO edge addition reduces the number of removable vertices
without creating a critical edge — STUCK at round 0, all 4 restarts. This is the
principle confirmed by DIRECT ATTEMPT (not just observed failure): the
edge-robustness of K(6,2)'s Borsuk-Ulam obstruction makes every vertex removable,
and any local edit that would criticalize a vertex (drop χ(G−v) to 3) necessarily
creates an edge whose deletion also drops χ (a critical edge). The two are not
just empirically antagonistic — they are locally INSEPARABLE around K(6,2).

## jensen's BRIDGE refinement (2026-06-10) — sharpens the tension topologically
jensen proved the J-S architecture (rigid core + tree-like transfer gadgets) CANNOT
reach 0 critical edges: transfer chains are PATHS with pendants ⟹ interior edges are
BRIDGES ⟹ the only de-criticalization is a PARALLEL chain ⟹ a parallel chain creates
a non-critical vertex. SPEC: a witness needs every edge on a 2-EDGE-CONNECTED
sub-obstruction (within-itself reroute avoiding e); bridges are fatal; density
(δ≥6) supplies this.
NOTE (forge check): at the WHOLE-graph level all my |E*|=0 AND |E*|>0 4vc graphs are
already bridgeless (edge-conn ≥4). So the discriminating condition is jensen's FINER
one — 2-edge-connectivity WITHIN each per-edge sub-obstruction H_e — not whole-graph
bridgelessness. This is the same robustness-asymmetry made topological: edge-redundancy
needs each H_e 2-edge-connected through e (a within-obstruction reroute), but
vertex-criticality needs each H_e DESTROYED by some vertex deletion. The reroute (good
for edges) and the vertex-fragility (good for vertices) are the two antagonistic
requirements on the SAME family {H_e}. jensen's bridge analysis = the construction-side
proof that tree-like (bridge-ful) obstructions can't satisfy both; the impossibility
proof must show NO obstruction family (bridgeless or not) satisfies both at q=3.

## algebra's rung-doubling: TESTED, hits the wall (2026-06-10)
algebra's Youngs quadrangulation (odd_wheel_quad t=2): n=10, χ=4, vertex-critical,
|E*|=10 (cycles redundant, rungs critical). Proposed rung-doubling to close to 0.
I reproduced the baseline and TESTED 3 rung-doubling variants:
- diagonal rungs o_j-i_{j+2}: overshoots χ=5.
- 3-LAYER (add middle cycle, rungs o-k, k-i): n=15, χ=4, |E*|=0 BUT NOT vertex-
  critical (10 removable).
- twin inner layer per rung: n=15, χ=4, |E*|=0 BUT NOT vertex-critical (15 removable).
So rung-doubling DOES kill all critical edges (the parity mechanism works!) but
breaks vertex-criticality — EXACTLY the robustness-asymmetry. Doubling a rung makes
it redundant (parallel parity witness) but makes the rung-region vertices removable
(twin carries the obstruction). Same wall as covers/biwheels/Kneser/J-S. The
quadrangulation family confirms it from the parity side: the parity obstruction,
once made edge-robust by doubling, is also vertex-robust. No q=3 escape.

## jensen PARALLELISM-vs-ENTANGLEMENT dichotomy — my proxy FAILED (honest)
jensen's dichotomy (verified by jensen on G_5,2,2): edge-redundancy via separable
PARALLELISM (vertex-disjoint rails ⟹ non-critical rail vertices) vs ENTANGLEMENT
(reroutes share the edge's neighborhood ⟹ vertices stay critical). Witness needs
entanglement.
I tried to operationalize it (forge_entanglement_diag.py: avg common-neighbors +
"rail-fraction" = node-disjoint u-v paths whose interior avoids the common neighbors).
RESULT: my proxy does NOT separate the cases — it labels the k=5 witnesses G_5,2,2/
G_5,2,4 as "rail-like" (rail-frac 0.54/0.70) and the cocktail graph as "entangled,"
the OPPOSITE of jensen's correct verified classification. So my specific metric is
WRONG (the "avoid common neighbors" criterion mis-captures entanglement — G_5,2,2's
reroutes go through the broader N(u)∪N(v), not necessarily the common neighbors).
Do NOT use forge_entanglement_diag.py's labels. jensen has the correct working
criterion (verified on G_5,2,2: 7 internally-vertex-disjoint reroutes through the
dense common neighborhood) — defer to jensen's definition for the diagnostic.
