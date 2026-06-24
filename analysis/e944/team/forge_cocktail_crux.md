# forge — the cocktail-party crux: the canonical "almost-witness" (proof-team, 2026-06-10)

Searching all χ=4 graphs that satisfy wall's balance criterion at EVERY vertex
(= |E*|=0, no critical edge) at small n, the SMALLEST is, exactly:

  **G]~v~w = K_{2,2,2,2}** — the cocktail-party graph (complete 4-partite, 4 parts
  of size 2). n=8, 6-regular (= K₈ minus a perfect matching), χ=4, |E*|=0.

It satisfies the ENTIRE (4,1)-witness predicate EXCEPT vertex-criticality (all 8
vertices removable). It is the cleanest illustration of the robustness-asymmetry.

## Why it has |E*|=0 AND is not vertex-critical (same cause)
χ(K_{2,2,2,2})=4 because it has 4 parts (ω=4). The 4-chromaticity is carried by
the PARTITION — a global structure.
- **No critical edge:** every edge joins two different parts. Deleting one edge
  uv (u∈P_i, v∈P_j) leaves the 4 parts still pairwise-joined (the OTHER vertices
  of P_i,P_j keep the cross-edges), so χ stays 4. |E*|=0.
- **Not vertex-critical:** deleting any vertex leaves K_{2,2,2,1} — still 4 parts,
  still ω=4, still χ=4. Every vertex removable.
The SAME partition-robustness gives both. To force vertex-criticality you'd shrink
parts to size 1 ⟹ K₄ ⟹ all 6 edges critical. The two requirements pull opposite.

## Why this is the proof crux (for gallai/wall/skeptic)
ANY proof of "χ=4 vertex-critical ⟹ B₁>0 (E*≠∅)" must EXPLAIN why the cocktail-
party route (|E*|=0) cannot be made vertex-critical. The localized statement
(forge_B1_localization.md): B₁=½Σ_v cnt(v), and cnt(v)=0 at every v ⟺ wall-balanced
⟺ |E*|=0. K_{2,2,2,2} achieves cnt(v)=0 everywhere but is not vertex-critical.

So the theorem is equivalent to: **a χ=4 graph that is wall-balanced at every
vertex (|E*|=0) always has a removable vertex.** K_{2,2,2,2} and the n=9 examples
(HFzf~z~, HFzvV~}) are all complete-multipartite-like / partition-robust.

CONJECTURE (forge, sharpened from the data): a χ=4 graph with |E*|=0 (no critical
edge) is "partition-robust" — its 4-chromaticity comes from a structure (e.g. a
homomorphism onto K₄ / a 4-partition with thick parts) that survives any single
vertex deletion ⟹ NOT vertex-critical. If every |E*|=0 χ=4 graph admits a
χ=4-preserving vertex deletion, Dirac k=4 is REFUTED.

## k=5 reality check (skeptic)
At k=5: K_{2,2,2,2,2} (cocktail party, 5 parts) is χ=5, |E*|=0, also not
vertex-critical — BUT the real (5,1)-witness G_{5,2,2} (gallai) IS vertex-critical
with |E*|=0. So "partition-robust |E*|=0 graphs aren't vertex-critical" is TRUE for
BOTH k=4 and k=5 on the cocktail-party family — the k=4-specific part is that at
k=4 the NON-cocktail |E*|=0 graphs (if any) also fail vertex-criticality, whereas
at k=5 G_{5,2,2} escapes. So the proof must show: at k=4, EVERY |E*|=0 χ=4 graph
is partition-robust-enough to have a removable vertex, while at k=5 the circulant
G_{5,2,2} is the escape. The q=3 lever: with only 3 colors, |E*|=0 forces a rigid
near-4-partite structure (thick parts) that k=5's extra color avoids.

## EXHAUSTIVE TEST RESULT (n=8,9) — conjecture HOLDS, but NOT via multipartite
Exhaustive over connected χ=4 |E*|=0 graphs (geng -d4):
- n=8: 130 such graphs, **0 vertex-critical** (0 witnesses). 129/130 are NOT
  complete-multipartite.
- n=9: 5681 such graphs, **0 vertex-critical** (0 witnesses). 5680/5681 NOT
  complete-multipartite.
So the cocktail-party graph is just the smallest example; the class of |E*|=0 χ=4
graphs is LARGE and DIVERSE (mostly non-multipartite), yet EVERY one has a
removable vertex (none vertex-critical). This is STRONGER evidence for the
conjecture and shows the obstruction is NOT a multipartite artifact — it is a
general property of "no critical edge ⟹ removable vertex exists" at k=4.

## Refined conjecture (the impossibility statement)
> **Conjecture (forge).** Every χ=4 graph with no critical edge (|E*|=0) has a
> removable vertex (is NOT vertex-critical). Equivalently: χ=4 ∧ vertex-critical
> ⟹ |E*| > 0 ⟹ B₁ > 0. = Dirac k=4 has answer NO.
Verified: ALL 130 (n=8) + 5681 (n=9) |E*|=0 χ=4 graphs are non-vertex-critical.
The mechanism is NOT multipartite-specific; it is the robustness-asymmetry in full
generality. This is the cleanest form of the impossibility target and the localized
B₁ statement (forge_B1_localization.md) is its dual.

## Next (proof attack)
- Extend the exhaustive |E*|=0 ⟹ removable-vertex check to n=10,11 (running).
- The PROOF must show: |E*|=0 (every G−v 3-coloring balanced on N(v)) provides
  enough "coloring freedom" that SOME vertex v has χ(G−v)=4 (removable). At k=5,
  G_{5,2,2} escapes because the extra color breaks the q=3 balance rigidity — the
  q=3 lever skeptic requires. Hand the diverse-but-uniform n=8,9 data to gallai
  (Potts) and wall (ℤ₃-tension) as the empirical base for the zero-free-region arg.

## EXHAUSTIVE BASE EXTENDED TO n=10 (decisive) + K4-conjecture REFUTED
| n | #(chi=4, |E*|=0) graphs | vertex-critical (= witnesses) | non-multipartite |
|---|---|---|---|
| 8 | 130 | 0 | 129 |
| 9 | 5,681 | 0 | 5,680 |
| 10 | 550,059 | 0 | 550,057 |
Conjecture "chi=4 & |E*|=0 => removable vertex (not vertex-critical)" holds over
~556,000 diverse graphs, ZERO exceptions. Robustness-asymmetry as near-certain k=4 theorem.

K4-anchoring conjecture REFUTED (saves a dead route): there ARE K4-free (omega=3) |E*|=0
chi=4 graphs (3 at n=8 e.g. GQyurg, 36 at n=9). So 4-chromaticity is NOT always clique-
anchored; the obstruction is the global coloring CSP, not cliques. A clique-based
impossibility proof is DEAD — the proof must be coloring-structural (gallai Potts / wall Z3-tension).

## STRENGTHENING: |E*|=0 forces MANY removable vertices (not just one)
In |E*|=0 χ=4 graphs at n=8, typically 7 of 8 vertices are removable (G−v still χ=4).
So no-critical-edge graphs are FAR from vertex-critical — the 4-obstruction is "thick"
(survives almost every single vertex deletion), mirroring how it survives every edge
deletion. This is the robustness-asymmetry at full strength: |E*|=0 ⟹ the obstruction
is BOTH edge-robust AND (heavily) vertex-robust. A vertex-critical graph needs the
obstruction vertex-FRAGILE at every vertex — the opposite extreme. The conjecture could
plausibly strengthen to: |E*|=0 χ=4 ⟹ at least (n − O(1)) removable vertices.
PROOF DIRECTION for gallai/wall: show no-critical-edge (B₁=0 / wall-balanced everywhere)
implies a coloring-count surplus that forces χ(G−v)=4 for some (many) v — the q=3
zero-free-region / Potts argument is the analytic vehicle; this is the structural target.
