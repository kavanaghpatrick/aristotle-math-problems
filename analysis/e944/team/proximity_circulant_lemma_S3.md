# §3 — The Circulant Lemma (proximity)

*Section 3 of the joint E944 impossibility document. Slots into forge's skeleton
(forge_B1_localization.md) after §2b (E*-degree slope lemma). All statements dual-checked via
checkers.py (backtracking χ + SAT χ agree) and, where noted, triple-checked with skeptic_adjudicate.*

## 3.0 Notation
Let `C_n(S)` be the circulant graph on vertices `ℤ_n` with connection set `S ⊆ {1,…,⌊n/2⌋}`: vertices
`i,j` adjacent iff the cyclic distance `d_n(i,j) ∈ S`. It is `2|S|`-regular (so `|S|=3` ⟹ 6-regular,
the Prop-5.1 sparsest witness class). `E*(G)` = the set of critical edges = `{e : χ(G−e) < χ(G)}`.
A *difference-orbit* is the set of all edges at a fixed cyclic distance `d ∈ S` (an orbit of the
`ℤ_n` rotation action, size `n` for `d < n/2`).

## 3.1 Statement

**Circulant Lemma (empirical, n ≤ 31).** *No 6-regular circulant is a (4,1)-graph.* Equivalently:
every 6-regular vertex-critical circulant `C_n(S)` (χ=4, every vertex critical) has `|E*| ≥ n > 0` —
it always has at least one critical edge. Verified exhaustively over all connection sets `S` for every
`n ≤ 21` (and the headline `|E*| > 0` confirmed to n = 31 via the triangle-free family + spot sets).

## 3.2 Mechanism (structural / coloring — NOT analytic)

The analytic zero-free levers (single chromatic polynomial + joint deleted-edge family) are CLOSED
(gallai/archivist). The circulant obstruction is a **ℤ₃-coloring** phenomenon:

By the `ℤ_n` rotation symmetry, the deleted-edge family `{G−e : e ∈ E(G)}` collapses to exactly `|S|`
isomorphism classes — one per difference-orbit. So `e` is critical iff its orbit's representative
deletion `G−e` is 3-colorable, i.e. iff some proper 3-coloring of `G` has its only monochromatic edge
in that orbit. Criticality is therefore an **orbit-level** property: each difference-orbit is either
entirely critical or entirely non-critical. `|E*| > 0` ⟺ ≥1 orbit is critical ⟺ the 3-coloring
structure of `G` cannot avoid leaving a singleton monochromatic edge in some orbit.

**Orbit-persistence (the core empirical fact, n ≤ 31, triple-verified incl. skeptic).** For every
6-regular vertex-critical circulant, at least one difference-orbit is critical. The critical orbit
RELOCATES with the connection set but never vanishes:
- `C₁₃(1,2,5)`: critical orbit = diff-1 (the Hamilton cycle), `|E*| = 13`.
- `C₁₃(1,3,5)`: critical orbit = diff-5, `|E*| = 13` (this set AVOIDS {1,2} — so the obstruction is
  NOT the {1,2}-triangle rigidity alone; relocation, not removal).

## 3.3 The orbit-count discriminant (fine structure, n = 31)

How MANY orbits are critical is governed by the ℤ₃-coloring structure, not merely its multiplicity.
Over all 60 triangle-free vertex-critical 6-regular circulants at n = 31 (essentially-distinct
3-colorings of `G−v₀` counted exactly = #proper-3-colorings / 6):

| #critical orbits | #essentially-distinct 3-colorings | count |
|---|---|---|
| 1 | 1 | 33 |
| 1 | 2 | 2 |
| 1 | 4 | 8 |
| 1 | 5 | 2 |
| 2 | 2 | 10 |
| 2 | 8 | 4 |
| 2 | 11 | 1 |

- **2 critical orbits ⟹ ≥2 essentially-distinct colorings AND triangle-free** (15/15; the 15
  two-orbit cases are exactly the triangle-free, ≥2-coloring ones). [Result 5 + the table.]
- **The converse FAILS**: 12 of the 45 one-orbit cases have ≥2 essentially-distinct colorings (up to
  5) yet all their singleton monochromatic edges land in the SAME orbit. So coloring-multiplicity is
  NECESSARY but NOT SUFFICIENT for two critical orbits.

**Discriminant.** `#critical orbits = #{distinct orbits hit by the singleton monochromatic edge across
the essentially-distinct ℤ₃-colorings of G−v}`. Triangle-freeness ENABLES multiple colorings;
whether those colorings' conflicts land in different orbits is the finer cocycle condition (feeds
wall's f(G) / §5 irreducible core).

## 3.4 q = 3 specificity (the k = 5 tripwire — §6)

The Lemma is `k=4` / `q=3`-SPECIFIC and must be, else it would contradict Brown/Jensen (who built
k≥5 circulant witnesses). VERIFIED: `C₁₇(1,3,4,5)` is an 8-regular **5-vertex-critical circulant with
`|E*| = 0`** (a genuine k=5 circulant witness; found by scanning circulants n ≤ 22, dual-checked). So
the orbit-persistence that forces `|E*| > 0` at k=4 BREAKS at k=5: it is a property of 3-colorings
(3 = q = k−1 nonempty color classes), not of circulants per se. The Lemma reads: *the ℤ₃-coloring
structure of a 6-regular vertex-critical circulant forces a critical difference-orbit* — and ℤ₃ is the
load-bearing arithmetic.

## 3.5 Status and scope
- Robust to n = 31 (exhaustive connection-set sweep n ≤ 21; triangle-free family + spot sets to n=31).
- HEURISTIC, not a proof — an n-uniform proof of orbit-persistence is the open piece (candidate route:
  show the ℤ₃-coloring CSP on `C_n(S)` always admits a singleton-conflict coloring; ties to wall's f(G)
  and §5). The empirical statement is the verified backbone.
- Verification instrument: `proximity_incremental_verifier.py` (independent SAT/activation-literal
  code path) re-confirms any candidate refinement; part of the quadruple-confidence gate.
- CAVEAT (squad standing rule): all circulant structural claims verified to n ≥ 31 — the "one-orbit /
  fraction-1/3" pattern was an n ≤ 21 artifact (it breaks at n=31: C₃₁(1,4,6), C₃₁(5,6,7) have TWO
  orbits, |E*|=2n). Only `|E*| > 0` (no witness) is the uniformly-true statement.
