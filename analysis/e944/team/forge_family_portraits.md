# forge — JOINT deleted-edge family portraits near x=q (proof-team, 2026-06-10)

For the LIVE impossibility lever (team-lead reframe): B₁ is NOT a function of P(G,x)
alone; the live question is the JOINT zero-free behavior of the FAMILY
{P(G−e,x) : e ∈ E} near x=q (q=3 for k=4). Computed via fast exact integer
evaluations P(G−e,k), k=0..6 (small graphs) + q-colorability for all sizes.
Code: forge_family_portrait.py.

## The clean reformulation (confirmed)
e is critical ⟺ G−e is q-colorable ⟺ P(G−e,q) > 0.
e is NON-critical ⟺ G−e is NOT q-colorable ⟺ P(G−e,q) = 0 ⟺ **x=q is a ROOT of
P(G−e,x)**.
Therefore: **|E*|=0 ⟺ x=q is a COMMON ROOT of the ENTIRE deleted-edge family
{P(G−e,x)}.** This is the exact polynomial-family statement of "no critical edge."

## Portraits (q=3 unless noted)
| host | n | χ | |E| | x=3 common root of whole family? | critical members P(G−e,3) |
|---|---|---|---|---|---|
| K_{2,2,2,2} cocktail (not-vc) | 8 | 4 | 24 | **YES** (24/24 root) | 0 |
| K(6,2) Kneser (not-vc) | 15 | 4 | 45 | **YES** (all root) | 0 |
| n8 GCZvv{ (not-vc) | 8 | 4 | 19 | **YES** (19/19 root) | 0 |
| n10 champion (VC, |E*|=8) | 10 | 4 | 22 | NO (14 root, 8 critical) | =6 each |
| C13(1,2,5) (VC, |E*|=13) | 13 | 4 | 39 | NO (26 root, 13 critical) | =6 each |
| **G_5,2,2 CONTROL (VC, |E*|=0, q=4)** | 17 | 5 | 68 | **YES** (all root) | 0 |

## Key observations for gallai/wall
1. **|E*|=0 ⟺ x=q common root of the family** — clean, holds across all examples
   incl. the non-multipartite GCZvv{ and the dense K(6,2). The joint lever is
   exactly: "can x=q be a common root of {P(G−e,x)} for ALL e, while G is
   (q+1)-chromatic AND vertex-critical?"
2. **CORRECTION (over-claim retracted):** the value P(G−e,3)=6 in the n=10 champion
   and C13 is NOT a universal invariant — it just reflects that THOSE hosts have a
   rigid (unique mod S_3) 3-coloring of G−e. Over all 4vc graphs n=7,8,9, critical-
   edge P(G−e,3) ∈ {6,12,18,24,30,36} = 6·{1..6} (multiples of 3! only because every
   3-coloring comes in 3!=6 permutations — a TRIVIAL divisibility, not a special
   invariant). So "critical ⟹ unique 3-coloring" is FALSE in general. Dropped as a
   lever. (Checked before handing to gallai — do not use.)
3. **Local rise:** for root-at-q members, P(q−1)=0 and P(q+1)−P(q) > 0 (the poly is
   flat-zero at and below q, rises above) — consistent with x=q being the
   chromatic root and the graph being exactly (q)-near.
4. **THE q=3 vs q=4 GAP (the tripwire):** G_5,2,2 (q=4) ALSO has x=4 as a common
   family root while VERTEX-CRITICAL — so "x=q common family root + vertex-critical"
   is REALIZABLE at q=4 (the k=5 witness). At q=3, the ~556K-graph exhaustive base
   shows it is NEVER realized (every |E*|=0 χ=4 graph is non-vertex-critical). So
   the impossibility theorem = "x=3 common family root ⟹ NOT vertex-critical" is
   q=3-SPECIFIC; the proof must use a q=3 fact that q=4 lacks. CANDIDATE q=3 lever
   (from obs 2): critical ⟹ unique 3-coloring (6 of them); the rigidity of the
   3-coloring space is much tighter than the 4-coloring space (q=4 has exponentially
   more colorings to redistribute), so the "common root" constraint over-determines
   the q=3 colorings in a way it doesn't at q=4.

## Hand-off
- gallai: the "x=q common root of the deleted-edge family" is your Potts B₁=0
  statement in family-polynomial form; the zero-free-region argument should target
  "this common-root configuration forces a removable vertex at q=3."
- wall: the family common-root ⟺ |E*|=0 framing should plug into the ℤ₃-tension;
  the q=3-vs-q=4 gap (obs 4) is the tripwire-respecting lever.
- NEXT (I can compute): confirm critical-value = q! at q=4 on G_5,2,2's critical-
  edge analogue (it has none, |E*|=0) — instead test a k=5 graph WITH critical edges;
  and compute, for the |E*|=0 hosts, the SECOND-nearest root of each P(G−e,x) to q
  (needs full poly for small n) to see if the common root at q is simple or has
  structure distinguishing vc from non-vc.

## SECOND k=5 CONTROL (archivist's G_5,2,4 on Z_33) — tripwire pattern robust
archivist built+verified a SECOND k=5 witness: G_5,2,4, circulant on Z_33,
D={1,3,4,5,12,13,21}, n=33, 12-regular, χ=5, vertex-critical, |E*|=0.
Family portrait at q=4: x=4 is a COMMON root of the whole deleted-edge family AND
the graph is vertex-critical — IDENTICAL pattern to G_5,2,2 (Z_17). So "common
family root + vertex-critical" is realized at q=4 by TWO independent witnesses,
confirming the tripwire pattern is robust (not a one-graph artifact). The
impossibility theorem must therefore explain why this configuration is realizable
at q=4 (≥2 witnesses) yet NEVER at q=3 (~556K exhaustive graphs, 0 witnesses) —
the q=3-specific lever. Both k=5 controls available for any lemma's k=5 check.
