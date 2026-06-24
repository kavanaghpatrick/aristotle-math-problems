# hunter — Validated Independent Checkers for e944

## Status: VERIFIER COMPLETE (cross-validated). Search in progress.

## The target predicate (locked to FormalConjectures source)

From `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring.lean`:

- `IsCriticalEdges G edges := χ(G.deleteEdges edges) < χ(G)`
- `IsCriticalEdge G e := IsCriticalEdges G {e}`
- `Subgraph.IsCriticalVertex G v := χ(G − v) < χ(G)`
- `IsCritical G k := χ(G) = k ∧ ∀ v, χ(G − v) < χ(G)`  (this is **vertex-critical**)

From `ErdosProblems/944.lean`:

- `IsErdos944 G k r := IsCritical G k ∧ (∀ edge-set S, IsCriticalEdges G S → r < |S|)`

### Target for k=4, r=1 (`erdos_944.dirac_conjecture.k_eq_four`)
A graph G with:
1. **χ(G) = 4**
2. **vertex-critical**: ∀v, χ(G−v) ≤ 3
3. **no critical single edge**: ∀ edge e, χ(G−e) = 4

**Key reduction**: "every critical edge-set has size > 1" ⟺ "no single edge is critical".
The empty set is never critical (deleteEdges ∅ = G, so χ < χ is false). Any 2+ edge-set that's
critical is fine. So the *only* binding constraint beyond vertex-criticality is: **no edge e has
χ(G−e) = 3**.

## Two INDEPENDENT χ implementations (squad-1 lesson: verifier before searcher)

`checkers.py`:
- **(A)** `chromatic_number_exact` — pure-python DSATUR-ordered backtracking with symmetry
  breaking. No external solver.
- **(B)** `chromatic_number_sat` — SAT encoding of k-colorability via python-sat / Cadical195.

Completely separate code paths. Cross-validated on every graph.

## Cross-validation results (`validate_checkers.py`) — ALL PASS

| Graph | n | m | χ (both agree) | vertex-crit (k=4) | no-crit-edge | IsErdos944(4,1) |
|---|---|---|---|---|---|---|
| K4 | 4 | 6 | 4 | True | **False** (all edges critical) | False |
| K3 | 3 | 3 | 3 | — | — | — |
| K5 | 5 | 10 | 5 | — | — | — |
| C5 | 5 | 5 | 3 | — | — | — |
| C6 | 6 | 6 | 2 | — | — | — |
| W5 (hub+C5) | 6 | 10 | 4 | True | **False** | False |
| Grötzsch | 11 | 20 | 4 | True | **False** | False |
| Petersen | 10 | 15 | 3 | — | — | — |
| K_{3,3} | 6 | 9 | 2 | — | — | — |

Both χ implementations agree on all 9; all known chromatic numbers correct. The three known
4-critical graphs (K4, W5, Grötzsch) are correctly flagged as having critical edges, i.e. NOT
witnesses — exactly the difficulty of k=4.

## Files
- `checkers.py` — the verified predicate library (importable by any squad member).
- `validate_checkers.py` — the cross-validation harness.
