# forge — Kneser/Schrijver: a DENSE global χ=4 mechanism (2nd candidate)

Following the Youngs refutation (sparsity ⟹ degree-3 ⟹ critical edges), the
invention spec sharpened to DENSE global mechanisms. Kneser/Schrijver graphs are
the canonical dense global-TOPOLOGICAL χ=4 family (Lovász–Borsuk–Ulam).

## The mechanism (verified, dense, global)
Kneser K(n,k): k-subsets of [n], adjacent iff disjoint. χ = n−2k+2 by Borsuk-Ulam
(global topological obstruction, NOT a clique). For χ=4: n=2k+2.

| graph | n | m | δ | regular | χ=4 | vertex-critical | |E*| | redundant |
|---|---|---|---|---|---|---|---|---|
| K(4,1)=K4 | 4 | 6 | 3 | yes | ✓ | ✓ | 6 | 0% |
| **K(6,2)** | 15 | 45 | **6** | yes | ✓ | ✗ (all removable) | **0** | **100%** |
| K(8,3) | 56 | 280 | 10 | yes | ✓ | ✗ | 0 | 100% |
| SG(6,2) | 9 | 18 | 4 | yes | ✓ | **✓** | 15 | 3 edges (17%) |
| SG(8,3) | 16 | 36 | 4–5 | no | ✓ | **✓** | 28 | 8 edges (22%) |

## The notable near-miss: K(6,2)
**K(6,2) is 6-regular, n=15, χ=4, with ZERO critical edges** — it passes EVERY
Skottová–Steiner necessary condition for a (4,1)-witness (δ≥6, edge-conn≥6,
n≥11, Δ≤n−5) AND has no critical edge. The ONLY thing it lacks is
vertex-criticality (every vertex is removable: K(6,2) stays χ=4 after deleting
any 2-subset, because the topological obstruction is robust to losing one
vertex). This is the closest any DENSE 0-critical-edge graph has come.

## Same antagonism, confirmed on the topological mechanism
The Schrijver graph SG(2k+2,k) is the canonical VERTEX-CRITICAL subgraph of
K(2k+2,k) (Schrijver 1978). Trimming K(6,2) → SG(6,2) restores vertex-criticality
but REINTRODUCES critical edges (0 → 15 of 18). The topological obstruction, once
made vertex-critical, is no longer edge-redundant — the SAME wall as covers,
biwheels, voltage covers. Borsuk-Ulam does not escape the antagonism.

## Why SG doesn't auto-win, and the open sub-question
SG(6,2) is only 4-regular (not 6), so my degree-3 theorem doesn't directly bite,
but it still has 15/18 critical edges. The Schrijver TRIM is just one way to make
K(6,2) vertex-critical. OPEN: is there a DIFFERENT vertex-critical subgraph of
K(6,2) (or a different dense Kneser-like graph) that keeps more of the 100%
redundancy? K(6,2) minus a cleverly chosen vertex subset, or an intermediate
between K(6,2) and SG(6,2), might thread the needle. Testing next
(forge_kneser_trim.py): trim K(6,2)/K(8,3) toward vertex-criticality by many
deletion orders, tracking min |E*| at the vertex-critical boundary.

## DECISIVE: K(6,2) fails the entanglement test (jensen's universal obstruction)
jensen's parity analysis converged on the spec: a witness needs ENTANGLED (not
separable/parallel) redundancy — per-edge reroutes through SHARED neighborhoods,
dense δ≥6 IRREGULAR. I checked K(6,2): edge-connectivity 6, vertex-connectivity
6, BUT **automorphism group order 720 = S₆ — fully vertex-transitive.** So its
redundancy is the SEPARABLE/symmetric kind: the Borsuk-Ulam obstruction is carried
uniformly across S₆-orbits, so deleting any vertex leaves a symmetric copy
carrying it (hence vertex-removable). **K(6,2) is vertex-transitive ⟹ NOT a
witness** by the count/algebra/forge vertex-transitive theorem — the same wall as
circulants. Borsuk-Ulam "global" but lands on a maximally-symmetric graph.

## Verdict (for skeptic adjudication)
Kneser/Schrijver IS a genuine dense global mechanism (passes the Youngs sparsity
filter, K(6,2) is 6-regular with 0 critical edges) — but it lands on a
VERTEX-TRANSITIVE graph (|Aut|=720), so it is dead for the SAME reason circulants
are. Trimming to the vertex-critical Schrijver subgraph reintroduces ~83% critical
edges; no trim order beats SG's |E*|=15. The mechanism is NOT a witness substrate.
CONVERGENCE: forge (robustness-asymmetry), jensen (separable⇒non-critical-vertex),
algebra (density-freezing), count/algebra (vertex-transitive⇒critical edge) ALL
name the SAME spec — the witness must be DENSE + ASYMMETRIC + ENTANGLED, a target
no natural/symmetric mechanism reaches. See forge_robustness_asymmetry.md.
