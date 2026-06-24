# E944 — The mod-3 dichotomy in C_n(1,2,5): a crisp instance of the 3-way tension (count)

**Verification:** exact χ + vertex-criticality + critical-edge count on C_n(1,2,5),
n=13..19 (critedge.py / count_anneal engine, cross-checked vs hunter SAT). Reproduce
inline in the assault session; family = circulant with distances {1,2,5}.

## The dichotomy (exact computed data)
| n | n mod 3 | χ | vertex-critical? | #critical edges | which witness condition holds |
|---|---|---|---|---|---|
| 13 | 1 | 4 | **YES** | 13 (= n)  | (a) dense ✓ (b) vtx-crit ✓ (c) no-crit-edge ✗ |
| 14 | 2 | 4 | **NO** (ALL 14 vertices non-critical) | **0** | (a) ✓ (b) ✗ (c) ✓ |
| 15 | 0 | 3 | — | — | not even 4-chromatic |
| 16 | 1 | 4 | **YES** | 16 (= n)  | (a) ✓ (b) ✓ (c) ✗ |
| 17 | 2 | 4 | **NO** (all non-critical) | **0** | (a) ✓ (b) ✗ (c) ✓ |
| 18 | 0 | 3 | — | — | not 4-chromatic |
| 19 | 1 | 4 | **YES** | 19 (= n)  | (a) ✓ (b) ✓ (c) ✗ |

## What it shows
The single circulant family C_n(1,2,5) realizes BOTH near-miss corners of the
E944 obstruction, switched by n mod 3:

- **n ≡ 1 (mod 3):** 6-regular, χ=4, **vertex-critical**, but critical-edge count
  = n exactly (the entire difference-1 Hamilton cycle is critical, the other two
  orbits non-critical). Satisfies conditions (a) density + (b) vertex-criticality;
  FAILS (c) no-critical-edge, and fails it by the maximal "one whole orbit."

- **n ≡ 2 (mod 3):** 6-regular, χ=4, **ZERO critical edges** (satisfies the witness
  EDGE condition perfectly!), but **NOT vertex-critical — and not marginally:
  EVERY one of the n vertices is non-critical** (χ(G−v)=4 for all v). It is
  "over-full." Satisfies (a) + (c); FAILS (b) totally.

- **n ≡ 0 (mod 3):** χ collapses to 3 (not even 4-chromatic).

## The takeaway for the squad (the counting-side articulation of the obstruction)
The two non-trivial residues sit at OPPOSITE corners: one is vertex-critical with
a full Hamilton-cycle of critical edges; the other has no critical edge but is
maximally non-vertex-critical. **The family never lands in the middle (vertex-
critical AND 0 critical edges) — it overshoots from one side to the other as n
crosses a residue class.** This is the cleanest concrete picture of why the
witness is hard: the natural 6-regular family's tuning parameter (n mod 3) toggles
between violating (b) and violating (c), with no value hitting both.

A witness would need to interpolate between these corners — e.g. take the n≡2
"0-critical-edge" graph and repair vertex-criticality WITHOUT recreating critical
edges. But C₁₄(1,2,5) is far from that boundary (ALL vertices non-critical, not
just a few), so it is not a near-miss for local repair. The interpolation, if it
exists, is not within this circulant family — consistent with the squad verdict
that a witness is asymmetric / outside the circulant basin.

## Honest status
This is exact, verified, and a sharp illustration — NOT a proof of non-existence.
It explains the annealing plateau: chains from n≡1 seeds are pinned at ~n critical
edges (can't kill the Hamilton orbit without losing vertex-criticality, the n≡2
fate); chains constrained to stay feasible can't cross the gap.
