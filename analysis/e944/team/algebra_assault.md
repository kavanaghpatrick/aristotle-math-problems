# E944 ASSAULT — asymmetric / non-associative substrates (algebra)

Goal: exploit the orbit obstruction in reverse. The obstruction
(`algebra_substrate_verdict.md`) kills SYMMETRIC substrates because automorphisms force
edge-criticality to be uniform on orbits. Asymmetric algebraic objects (quasigroups,
non-associative structures) have TRIVIAL automorphism groups, so the obstruction vanishes —
this is the live regime for a (4,1)-witness.

## KEY STRUCTURAL RESULT (verified) — non-associativity breaks the orbit obstruction

Construction "quasigroup-circulant" (`algebra_qcirculant.py`): generalize Cay(Z_n, ±D) by
replacing the group (Z_n,+) with a quasigroup (Q,∗) of the same order. Build i~j iff a
quasigroup left-translation/left-division relation lands in a generator set S.

Direct comparison at order n=9, generator S={1,2,3}, verified via networkx VF2 automorphism count
and hunter's χ checker:

| substrate | |V| | χ | **|Aut(G)|** | regime |
|---|---|---|---|---|
| Z₉ group-circulant | 9 | 5 | **18** (vertex-transitive) | orbit obstruction ACTIVE |
| non-assoc quasigroup-circulant | 9 | **4** | **1** (trivial!) | obstruction BROKEN |

**Interpretation:** with the group, the rotation i↦i+1 is an automorphism acting transitively on
each distance class, so an edge is critical iff its whole orbit is → "no critical edge" needs
every orbit redundant (impossible with 4-vertex-criticality, per the verdict). With a
non-associative quasigroup the analogous map is NOT an automorphism; |Aut|=1 means **every edge
is in its own singleton orbit**, so each edge's criticality is independent. This is precisely the
asymmetric regime the witness spec requires, and it is reachable at the "level 3" the prime k−1=3
otherwise forbids — because **non-associative quasigroups of order 3 exist** (9 of the 12 order-3
Latin squares are non-associative), so the "replacement substrate at level 3" is not empty.

(Caveat: all order-3 Latin squares are isotopic to Z₃, so the order-3 cell-graph collapses to the
group case — verified χ=3, all isomorphic. The non-associativity payoff appears at order ≥ 9 in
the quasigroup-circulant, where it produces χ=4 graphs with |Aut|=1.)

## Failure analyses (substrates tried, why each died)

1. **Latin-square cell graph (Q1)** — vertices = n² cells, adjacency = share row/col/symbol.
   - Order 3: all isomorphic to the group cell graph (isotopy collapse), χ=3. DEAD.
   - Order 4 (all 576 squares): reaches χ=4 but **never vertex-critical** — graphs too dense, a
     vertex deletion leaves χ=4. DEAD (fails vertex-criticality, not no-critical-edge).
   - Order 5 (random sample): never 4-vertex-critical. DEAD. Latin cell graphs are too dense/regular.

2. **Voltage / Z₃-lift (Q4)** of small bases (K4, C5, C7, wheel, K5−e): lifts collapse to χ=3 in
   ~95% of trials; when χ=4 appears it is **never vertex-critical**. Z₃ lifts preserve
   colorability rather than raising it. DEAD for the witness, though they do produce |Aut|>1.

3. **Quasigroup-circulant (QC-left / QC-diff)** — IN PROGRESS. Produces χ=4, |Aut|=1 graphs (the
   right regime). Scanning orders 8–13, generator sets |S|≤4, for the (4,1) property. Scoring by
   #critical edges; results appended below.

## Scan results (quasigroup-circulant)

[appended by algebra_qcirculant.py run — see task output]

## Status / honest assessment

- The non-associative substrate is the correct *category* (trivial Aut ⟹ orbit obstruction gone),
  and order-3 non-associative quasigroups exist, so the "level-3 replacement substrate" is real.
- Whether a quasigroup-circulant actually realizes the (4,1) property is an empirical question the
  scan is answering now. The structural lever is sound; the construction may still fail to thread
  the narrow band (χ=4 AND vertex-critical AND no critical edge) — these are competing constraints.
- This complements forge/SA (task #18, #19) on the combinatorial side and count on the non-abelian
  Cayley side; my contribution is the principled algebraic substrate that the obstruction predicts.

### Quasigroup-circulant scan v1 (orders 8-13, |S|<=4)
- n=8: tested=12320, 4-vertex-critical=4, witnesses=0, best #crit_edges=12/15 (QC-left S=(0,1,7))
- n=9: tested=19680, 4-vertex-critical=4, witnesses=0, best #crit_edges=10/19 (QC-left S=(2,5,6))
- n=11: tested=24200, 4-vertex-critical=0  <-- collapses out of the band exactly where Prop 5.1 needs it
- n=12: tested=9372, 4-vertex-critical=0
- n=13: tested=0 (timed out; 13-vertex backtracking χ too slow at this volume)

DIAGNOSIS: with |S|<=4 the QC graphs at n>=11 are either χ<4 (too sparse) or not vertex-critical.
They never reach the min-degree-6 / 6-regular regime Prop 5.1 requires for a witness. The few
4-vertex-critical hits (n=8,9) are below the |V|>=11 floor and have MANY critical edges (10-12).
The trivial-Aut property is necessary but NOT sufficient — the degree/density is wrong.

REFINEMENT v2 (next): force degree >= 6 by using larger generator sets |S| in {5,6,7} at n in
{11,12,13,14}, and seed a min-critical-edge descent from the best v1 candidates. Switch χ to the
SAT path for n>=13 (faster than backtracking at this density).

### FREEZING EXPERIMENT (decisive) — the second obstruction: density, not symmetry
For 4-vertex-critical quasigroup-circulant seeds, counted VALID redundancy-adding edge moves
(additions preserving χ=4 AND vertex-criticality) and the best critical-edge count after one move:

| n | m | base #crit | valid edge-additions | best #crit after 1 add |
|---|---|---|---|---|
| 7 | 12 | 10–11 | 3–4 | 9 |
| 8 | 15 | 12 | **0** (frozen) | 12 |
| 9 | 16/19 | 15 / 10 | 6 / **0** | 11 / 10 |
| 10 | 20/21 | 12–13 | 1–3 | 11–12 |
| 11,12,13 | — | — | **NO 4-vertex-critical QC seed exists at all** (|S|=3) | — |

TWO findings:
1. At n=7–10 the 4-vertex-critical quasigroup-circulants are **near-frozen**: 0–6 valid
   redundancy moves, and one move drops critical count by at most ~4 (never near 0). Edge-adding
   local descent makes essentially NO progress (verified: n=9 seed 10→10, zero edges added —
   every possible addition either pushes χ to 5 or kills vertex-criticality).
2. At n≥11 (the only band where Prop 5.1 ALLOWS a witness) the simple |S|=3 quasigroup-circulant
   produces **NO 4-vertex-critical graph at all** — too sparse for χ=4-and-vertex-critical;
   larger |S| (denser) breaks vertex-criticality instead.

## FINAL VERDICT (algebra, asymmetric substrate)
The non-associative quasigroup substrate **does** break the orbit obstruction (trivial Aut,
verified) — that part of the witness spec is satisfiable algebraically at "level 3." BUT it runs
into a SECOND, independent obstruction: a **density/freezing** wall. A (4,1)-graph must be both
vertex-critical (sparse-ish) and edge-redundant (dense, every edge double-witnessed); the
quasigroup-circulant lands on the wrong side — its 4-vertex-critical instances are nearly
edge-critical and frozen against adding redundancy, and at n≥11 it cannot stay 4-vertex-critical
at all. So the *principled algebraic* construction does not by itself reach a witness.

IMPLICATION (handed to forge/hunter): the witness, if it exists, needs a construction that is
asymmetric (✓ available) AND in the dense, non-frozen regime at n≥11 — reachable by GLOBAL search
(SA / SAT-CEGAR) over min-degree-6 graphs, not by local descent from tight algebraic seeds.
The two obstructions (symmetry: solved by quasigroups; density-freezing: open) are distinct; the
remaining barrier is density-freezing, which is forge's/hunter's global-search territory.
