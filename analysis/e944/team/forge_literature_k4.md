# E944 — Literature status of the k=4 case (forge, pulled 2026-06-10)

Source: erdosproblems.com/944 (live page, fetched 2026-06-10). This is NEWER than
the FormalConjectures/944.lean file and CLAUDE.md memory, which only list up to
Martinsson–Steiner 2025.

## Current published status

- Dirac 1970 conjectured: for k≥4, r=1, a k-vertex-critical graph with no
  critical edge exists.
- **Brown [Br92]**: k=5.
- **Lattanzio [La02]**: all k with k−1 NOT prime. (k=4 ⇒ k−1=3 is PRIME ⇒ NOT
  covered. This is the structural reason k=4 is special.)
- **Jensen [Je02]**: alternative construction, all k≥5.
- **Martinsson–Steiner [MaSt25]**: for every r≥1, holds for all sufficiently
  large k (depending on r).
- **Skottova–Steiner [SkSt25]** (NEW — not in our repo): such graphs exist for
  **all k≥5 and all r≥1**. They also address Erdős's quantitative form: with
  f_k(n) = largest r such that some k-vertex-critical graph on n vertices has no
  critical edge-set of size ≤ r, they prove
      n^{1/3}  ≪_k  f_k(n)  ≪_k  n / (log n)^C   for all k ≥ 5.

## The lone open case

> **k=4 is the ONLY remaining open case** — even k=4, r=1. Even the weak
> quantitative question (does f_4(n) → ∞?) is open.

Every modern technique (MaSt25 probabilistic, SkSt25) bottlenecks at k≥5. The
recurring barrier is structural: constructions either need k−1 composite
(Lattanzio) or need χ−1 ≥ 4 "room" in the core (Brown/Jensen). At k=4 the core
is 3-chromatic, and 3-chromatic graphs are too rigid (odd cycles) to host the
needed parallel obstructions.

## Implication for forge's construction strategy

- My empirical "vertex-transitive ⇒ has a critical edge" conjecture (circulant
  findings) is consistent with a real k=4 obstruction.
- The exhaustive floor (no witness n≤10, redundant fraction climbing) is
  consistent with EITHER a large witness OR a genuine non-existence.
- HONEST CALIBRATION: this is the single hardest sub-case of a problem the
  world's specialists (Steiner et al.) have not cracked. A from-scratch
  construction by us is a long shot. The high-value deliverables are (a) the
  exhaustive floor + redundancy-growth data, (b) the symmetry obstruction, (c)
  feeding hunter's larger search with the right structural priors — NOT a claimed
  witness unless the verifier confirms zero critical edges.

## References to chase (for whoever does deep lit)
- [SkSt25] Skottová, Steiner — improvement over MaSt25; has the f_k(n) bounds.
- [MaSt25] Martinsson, Steiner, *Vertex-critical graphs far from edge-criticality*,
  CPC 2025, 151–157.
- Problem 91 in Steiner's graph problems collection; see also Erdős #917, #1032.
