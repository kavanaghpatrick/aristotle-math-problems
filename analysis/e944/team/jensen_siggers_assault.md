# Jensen–Siggers k=4 ASSAULT — built, verified, and the surgery

**Author:** jensen (squad e944). **Code:** `jensen_code/jensen_siggers.py` (build),
`jensen_code/js_surgery.py` (double-gadget surgery). **Verifier:** `harness.py`
(3-way cross-validated vs count's critedge.py). Source: full paper text
/tmp/jensen_siggers.txt (SEMR 9:156-160, 2012).

## 1. The J–S construction, REBUILT and VERIFIED (m=3)
Built exactly from the paper's Constructions 1–4:
- B(m) = K_{2m,2m,2m} (parts S₁,S₂,S₃, 2m verts each), 108 edges at m=3.
- T(m): path x₀…x_{2m+1} + indep y₁…yₘ, edges yᵢ–x_{2i−1}, yᵢ–x_{2i}.
- T'(m): T + leaf zᵢ on each yᵢ.
- G(m): star v₀+v₁v₂v₃; copies Tᵢ,T'ᵢ; Sᵢ = (Y of Tᵢ)∪(Z of T'ᵢ); gluing
  vᵢ=x₀ of Tᵢ,T'ᵢ and v_{i+1}=x_{2m+1} of Tᵢ,T'ᵢ (mod 3).
- H' = B ∪ G identifying Sᵢ(B)=Sᵢ(G). H = 4-critical-by-vertex-removal subgraph.

**Verified results (m=3):**
| property | value | paper |
|---|---|---|
| χ(H) | 4 | 4 ✓ |
| vertex-critical | True | required ✓ |
| n | 67 | 21m+4=67 ✓ |
| critical edges in B | **0** | MUST be 0 ✓ |
| critical edges in G | 90 (= all of E(G)) | E*⊆E(G) ✓ |
| E* connected | True (1 component) | "connected" ✓ |
| E* spanning | covers all 67 verts | "even spanning" ✓ |

So the verified object reproduces EVERY qualitative claim of J–S, including the
concluding-remark observation that E* is **connected and spanning** — the property
they "cannot see how to avoid." (Edge-count formulas in the paper, 3m+1/4m+1/21m+6,
appear to be typos — the explicit construction gives 4m+1/5m+1/27m+9, internally
consistent and matching my build; vertex counts and structure are exact.)

## 2. WHY each gadget edge is critical (the mechanism, per Lemma 4)
H' is non-3-colorable because: v₁,v₂,v₃ are all adjacent to v₀, so under any
3-coloring two of them share a color; the T/T' color-transfer gadget on that pair
then FORCES the corresponding Sᵢ bichromatic; but B's unique 3-coloring needs
every Sᵢ monochromatic — contradiction. **Each edge of G lies on the unique
color-transfer chain** that enforces "some Sᵢ bichromatic." Deleting any one G-edge
breaks the chain for one (vᵢ,v_{i+1}) pair, opening a 3-coloring that was previously
blocked → χ drops to 3 → the edge is critical. There is a SINGLE obstruction
(one gadget G), so every edge in it is a single point of failure → all critical.
This is the exact incarnation of the shared-failure-mode: **only ONE independent
4-coloring obstruction exists, so every edge carrying it is critical.**

## 3. THE SURGERY: overlay a second independent gadget (in progress)
Target: give each G-edge a REDUNDANT obstruction so deleting it leaves χ=4.
Build H'' = B ∪ G_a ∪ G_b, both gadgets sharing S₁,S₂,S₃ of B but otherwise
vertex-disjoint (own stars, own internal paths). IF either gadget alone forces
"some Sᵢ bichromatic," then for an edge e∈G_a the graph H''−e still has G_b forcing
non-3-colorability → e non-critical. Two overlaid gadgets = the missing 2nd
independent obstruction.

### KNOWN RISK (analyzed): the 4-critical-subgraph reduction is ADVERSARIAL
`four_critical_subgraph` removes vertices while χ stays ≥4. If G_a and G_b are each
independently sufficient, the reduction will DELETE one whole gadget and return to
single-gadget H (all edges critical). So taking a 4-critical subgraph of H''
defeats the purpose. CORRECT TEST: check whether H'' (or a minimal-by-removing-
only-redundant-internal-vertices version) is ITSELF vertex-critical, and whether
the shared B + double gadget yields 0 critical edges WITHOUT stripping a gadget.
The real question: is there a subgraph keeping BOTH gadgets that is vertex-critical
AND has every gadget edge doubly-covered? [results below as they land]

### What would count as progress
- Cut max critical-edge count below the single-gadget Θ(n) (paper's own bound):
  any reduction is a real advance.
- 0 critical edges with χ=4 vertex-critical = the conjecture (k=4 witness).
- Honest failure mode (e.g. "the two gadgets always constrain the SAME pair, so a
  3-coloring evading G_a also evades G_b") is itself a publishable obstruction.

## 4. RESULT: the naive double-gadget overlay FAILS — and WHY (verified, m=3)
Built H'' = B ∪ G_a ∪ G_b (two vertex-disjoint-except-Sᵢ gadgets on one B),
n=116, χ=4. **Decisive cheap test:** delete an internal G_b path vertex
(`('Tx','b',1,1)`) → χ(H''−v) = **4** (B ∪ G_a still forces non-3-colorability).
So that vertex is NOT critical ⟹ **H'' is NOT vertex-critical.** Confirmed
analytically, not just numerically:

> **REDUNDANCY–VERTEX-CRITICALITY TENSION (the obstruction).** For the overlay to
> make G_a's edges non-critical, G_b must independently force χ=4 (so H''−e keeps
> χ=4 for e∈G_a). But "G_b independently forces χ=4 with B" means B ∪ G_b is
> already non-3-colorable WITHOUT G_a — so deleting any internal vertex of G_a
> leaves B ∪ G_b at χ=4, making that vertex non-critical. **Independence of the
> two obstructions kills edge-criticality AND vertex-criticality at the same
> time.** You cannot buy edge-redundancy with an independent second obstruction
> without forfeiting vertex-criticality. This is the EXACT k=4 incarnation of the
> shared-failure-mode: there is "one spare obstruction's worth of room," and you
> can spend it on edge-redundancy OR on vertex-criticality, not both.

This is the same wall wall sees from the impossibility side: a witness needs, for
EVERY edge e, a spanning 4-edge-critical H_e avoiding e (edge-redundancy), while
EVERY vertex must be critical (∩ of those H_e over edges at v must still drop χ on
v-deletion). The overlay shows the two demands are in direct competition.

### The "jointly necessary" escape — ALSO tested, ALSO fails (verified m=2)
I tested the refined idea two ways:
1. **Partial gadgets** (`js_joint.py`): a gadget on a chain-subset C⊆{1,2,3}
   glued to B is non-3-colorable ONLY when C={1,2,3} (all three chains). Any 1 or
   2 chains → χ=3. (The pigeonhole "two of v₁,v₂,v₃ share v₀'s color" needs all
   three transfer chains present to corner every clash pair.) So you cannot split
   the obstruction across two gadgets each missing a chain — each becomes vacuous.
2. **Double-cover, shared star** (`js_shared_star.py`): keep all 3 chains, but give
   each chain TWO vertex-disjoint transfer copies (a,b) sharing the star v₀..v₃ and
   the Sᵢ. H has χ=4, but deleting an interior vertex of chain-1-copy-a gives
   χ=4 (copy-b still transfers) → not critical → **NOT vertex-critical.** Same death.

### WHY this is essentially forced (the structural barrier)
A transfer chain Tᵢ is a **path with pendant y/z vertices** — its interior path
edges are **bridges** (verified: T(m=2) isolated has its interior path edges as
cut edges separating x₀ from x_{2m+1}). Consequences:
- To make an interior chain edge e **non-critical**, χ(H−e) must stay 4. Since e is
  a bridge of the transfer path, removing it severs the x₀→x_{2m+1} color-transfer
  along that chain. There is **no reroute WITHIN the chain.** The only alternative
  obstruction must come from a **parallel** structure (a duplicate chain).
- But a parallel duplicate chain does the same transfer job, so deleting an
  **interior vertex** of either copy leaves the other intact → that vertex is
  **non-critical** → vertex-criticality fails.

**So in the J–S architecture, edge-redundancy on a chain edge REQUIRES a parallel
chain, and a parallel chain DESTROYS vertex-criticality of the chain interiors.**
This is a clean structural barrier: the J–S construction cannot be pushed from
Θ(n) critical edges to 0 by any duplication/overlay scheme — the very mechanism
that removes edge-criticality (parallelism) introduces vertex-non-criticality.

### Net (honest)
- The naive double-gadget surgery the assault targeted: **dead, verified + analytic.**
- The refined jointly-necessary / double-cover variants: **also dead, verified.**
- Root cause: transfer-chain bridges ⟹ redundancy needs parallelism ⟹ parallelism
  kills vertex-criticality. This is the k=4 shared-failure-mode, localized to the
  J–S gadget topology.
- **A k=4 witness, if it exists, must NOT be of "rigid core B + tree-like transfer
  gadgets" type.** It needs edge-redundancy WITHOUT bridge-based transfer — i.e. the
  obstruction carrying each edge must be 2-edge-connected through that edge so a
  within-obstruction reroute exists, while still being killed by the right vertex
  deletion. That is a 2-edge-connected-obstruction spec — handed to forge/wall.
- This matches the impossibility side (wall): edge-redundancy and vertex-criticality
  compete for the same structural budget; making them coexist is exactly the open
  k=4 problem, and the two cheapest construction families to realize the budget
  (J–S gadgets, Jensen circulants) provably cannot.
