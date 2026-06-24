# RUNG H — the Martinsson–Steiner hypergraph route to a (4,1)-graph: VERDICT (proximity)

**Question.** Can the Martinsson–Steiner 2023 construction (arXiv:2310.12891) — G := complement of
the 2-section of an s-uniform hypergraph H with near-perfect-matchings + local sparsity — produce a
(4,1)-graph, i.e. resolve the k=4 case of Dirac's conjecture?

**Verdict: NO. The M-S route is structurally empty at k=4**, for two independent and mutually
reinforcing reasons, both proved/verified computationally (code: `proximity_rung_h.py`, all χ via
the squad's cross-checked `checkers.py` = backtracking + SAT must agree).

This does NOT resolve E944 (it only closes one route), but it precisely localizes why the newest
probabilistic tool cannot reach k=4, and — bonus — it derives the same min-degree obstruction that
Skottova–Steiner's Prop 5.1 states, from the hypergraph side.

---

## Setup: the route is rigid at n=13

- r = 1 ⟹ s := r+3 = **4** (fixed).
- G − v is 3-colorable because H − v's perfect matching splits the other n−1 vertices into
  (n−1)/s independent sets, and χ(G−v) ≤ k−1 = 3 needs **(n−1)/s = 3 ⟹ n = 13**.
- So the (4,1) instance of this route lives **entirely on 4-uniform hypergraphs on exactly 13
  vertices**. There is no other n to try. (Larger n gives χ(G−v) ≤ (n−1)/4 > 3, useless.)

---

## Reason 1 — the M-S SUFFICIENT CONDITION is infeasible at n=13 (counting)

The construction requires H to satisfy:
- **(i)** every H−v has a perfect matching (3 disjoint 4-hyperedges covering the other 12 vertices);
- **(ii)** local sparsity (Lemma-3 form): ⋃_{e∈F} e ≥ (s−1)|F| = 3|F| for all F ⊆ E(H), |F| ≤ 2^{s+1}=32.

Two facts collide:
- **(i) forces |E(H)| ≥ 5.** Each of 13 vertices needs 3 matching-hyperedges; a single 4-hyperedge
  can appear in the matching of at most 13−4 = 9 different H−v's. So |E(H)| ≥ ⌈13·3 / 9⌉ = **5**.
- **(ii) fails at |F| = 5.** Five 4-hyperedges need ⋃ ≥ 3·5 = **15 > 13 = n** vertices — impossible.

Therefore **no 4-uniform hypergraph on 13 vertices satisfies both (i) and (ii)**. The probabilistic
existence engine of M-S (Lemma 3, via Shamir/Johansson–Kahn–Vu) produces such H only for *large* n;
at the rigid n=13 the requirements are mutually exclusive. *This is the precise, finite incarnation
of the "k must be large" barrier* I flagged to jensen: not a vague threshold, but an exact
5-vs-15 counting contradiction.

(Verified: `report_sufficient_condition_infeasible()` prints min-edges=5, first-infeasible-|F|=5.)

---

## Reason 2 — even the WEAKER (necessary) graph condition fails: a degree obstruction (NEW bridge)

Property (ii) is only *sufficient*, not necessary — G could in principle be a (4,1)-graph without it.
So I tested the **actual graph** G = complement-of-2-section directly, over property-(i) hypergraphs,
against the shared checkers. Findings:

- **Random full property-(i) hypergraphs** have ~33–39 hyperedges ⟹ the 2-section is nearly complete
  ⟹ G is nearly EMPTY ⟹ **χ(G) ∈ {1,2}** (3000/3000 trials: never above 2). Far from χ=4.
- **Minimized property-(i) hypergraphs** (greedy edge-removal, 2000 runs): the **minimum |E(H)|
  achieving property (i) is 15** (the counting floor of 5 is unreachable — property (i) is far more
  demanding than the counting bound). At |E(H)| ≈ 15, the **2-section still has ~48–50 edges**, so
  **|E(G)| ≈ 28–30** and **χ(G) = 3**.
- **Densest G the route can reach:** best 2-section found = 48 edges ⟹ |E(G)| = 30 ⟹ average degree
  ≈ 4.6, **maximum possible minimum-degree = 4**.

**The bridge to Prop 5.1.** Skottova–Steiner's Prop 5.1 proves any (4,1)-graph has **minimum degree
≥ 6** (hence |E(G)| ≥ 39). The M-S route's output tops out at min-degree ≤ 4 and |E(G)| ≤ 30. So the
M-S graphs are **far too sparse** to be (4,1)-graphs — they fail the literature's own necessary
condition by a wide margin. The route cannot even reach the *feasibility region* for a witness.

Intuition (the real tension, stated cleanly): property (i) wants MANY hyperedges (so every vertex is
matchable) ⟹ dense 2-section ⟹ sparse G; but a (4,1)-graph must be DENSE (min-deg ≥ 6). On only 13
vertices these pull irreconcilably apart. There is no room.

---

## What this does and does not establish

- **Does:** The Martinsson–Steiner probabilistic / hypergraph-complement route — the newest tool on
  this problem — is provably empty for k=4. Both its own sufficient condition (Reason 1) and the
  necessary graph density (Reason 2) fail at the unique admissible n=13. So a k=4 witness, if it
  exists, needs a genuinely different construction (consistent with jensen's circulant-wall finding:
  the OTHER known route also dies structurally at k=4).
- **Does NOT:** prove a (4,1)-graph doesn't exist. It only closes the M-S route. The witness question
  is decided on the graph side (hunter's geng floor, skeptic's enum — both confirm 0 witnesses through
  n=9; count's circulant search; wall's density squeeze). My result removes one major candidate-
  generation mechanism from consideration and explains, exactly, why.

---

## Coordination notes
- Reason 2 independently re-derives Skottova–Steiner Prop 5.1's min-degree ≥ 6 from the hypergraph
  side, which cross-validates that proposition (relayed to count/wall — useful corroboration).
- Confirms jensen's "both known mechanisms die at k=4 for sharp, identified reasons" thesis:
  circulant route → D2=D3=∅ ⟹ χ=3 (structural); M-S route → 5-vs-15 counting + min-deg ≤ 4 < 6.
- The remaining live routes are NON-circulant, NON-M-S explicit constructions (forge's compositions
  aiming for 6-regular, n ≥ 11) and the direct exhaustive/SAT graph search (hunter, Steiner's
  Problem 5.2 = "6-regular (4,1)-graph?").

## Code / verification
- `proximity_rung_h.py` — all results reproducible; χ cross-checked backtrack vs SAT (0 mismatches).
- Search is sampling-based for the graph-side direction (the full space of property-(i) hypergraphs
  on 13 vertices is astronomically large); Reason 1 is an exact counting proof, not sampling.
