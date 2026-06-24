# E944 — Circulant / vertex-transitive route: NEGATIVE but informative (forge)

## Setup

For a circulant C_n(S) the automorphism group contains Z_n acting regularly, so:
- **Vertex-criticality is all-or-nothing**: if G−v₀ is 3-colorable for one v₀,
  it is for all v (transitivity). So a 4-chromatic circulant is automatically
  vertex-critical (every G−v 3-colorable) iff G−0 is 3-colorable.
- **Edges split into ≤|S| length-orbits**; all edges of a given connection
  length s are critical-or-redundant together. So a circulant is a witness iff
  it has **zero critical length-orbits** — only |S| conditions, not m.

This makes circulants the most economical place to *try* for a witness.

## Result: NO circulant witness for |S| ≤ 5, n ≤ 40 (exact).

Script `forge_circulants.py` (exact 3-/4-colorability via backtracking;
per-orbit criticality via one representative edge). Hundreds of 4-vertex-critical
circulants were found, but the minimum number of critical length-orbits is **1**,
never 0.

## The "exactly one critical orbit" phenomenon

Every near-miss has **exactly one** stubborn critical length-orbit; all others
are redundant. Examples:
- `C7(2,3)`: length-2 orbit critical (7 edges), length-3 redundant.
- `C22(7,8,9,10)`: length-7 orbit critical (22 edges), lengths 8,9,10 redundant.

Mechanism: the **redundant orbits alone form a 3-colorable graph**; the single
critical orbit is exactly what tips χ from 3 to 4. Concretely for C22(7,8,9,10),
C22(8,9,10) is 3-colorable, so every length-7 edge is critical. The whole graph's
4-chromaticity rests on ONE orbit, which is therefore globally load-bearing —
the opposite of what a witness needs (no edge load-bearing).

## Why this matters (hand-off to wall/gallai/skeptic)

This looks like a genuine obstruction for HIGH-symmetry graphs:

> **Conjecture (forge, empirical):** A vertex-transitive 4-chromatic graph
> always has a critical edge (cannot be an Erdős-944 witness).

Heuristic: in a vertex- and edge-orbit-transitive graph, 4-chromaticity is
"carried" by orbits uniformly; some minimal sub-union of orbits is the unique
χ=4 certificate, and any edge in the *smallest* such orbit is critical. A witness
must distribute the χ=4 obstruction so NO edge is in every certificate — which
requires **breaking symmetry** so different edges are covered by different
certificates.

**Construction consequence:** abandon high-symmetry substrates (circulants,
Cayley graphs, single-orbit designs). The exhaustive champions confirm this —
the n=10 record-redundancy graph (64% redundant) has automorphism group of order
only 4 and is irregular. **The witness is asymmetric.** Build by overlaying
several DIFFERENT odd-obstruction gadgets so each edge is redundant in at least
one of them, with deletions of distinct edges defended by distinct gadgets.

(Asking wall/gallai/skeptic: is "vertex-transitive ⇒ has a critical edge" a known
theorem or refutable? If true it cleanly explains why circulants fail and
redirects the whole construction effort to asymmetric overlays.)
