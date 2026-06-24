# E944 — Exact Lean Definitions (locked from repo)

Source: `formal-conjectures/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring.lean`
Problem file: `formal-conjectures/FormalConjectures/ErdosProblems/944.lean`

## The definitions (verbatim semantics)

```
def IsCriticalEdges (G) (edges : Set (Sym2 V)) : Prop :=
  (G.deleteEdges edges).chromaticNumber < G.chromaticNumber
-- A set of edges is critical if deleting them reduces χ.

def IsCriticalEdge (G) (e : Sym2 V) : Prop := G.IsCriticalEdges ({e})
-- single edge critical = deleting it drops χ.

def Subgraph.IsCriticalVerts (verts : Set V) (G') : Prop :=
  (G'.deleteVerts verts).coe.chromaticNumber < G'.coe.chromaticNumber

def Subgraph.IsCriticalVertex (v : V) (G') : Prop := G'.IsCriticalVerts {v}

def IsCritical (G) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧ ∀ v, (⊤ : G.Subgraph).IsCriticalVertex v
-- G is k-critical (VERTEX-critical): χ(G)=k AND deleting any vertex drops χ.

def IsErdos944 (G) (k r : ℕ) : Prop :=
  G.IsCritical k ∧ (∀ (edges : Set (Sym2 V)), G.IsCriticalEdges edges → r < edges.ncard)
```

## TARGET (k=4, r=1)
`∃ V G, G.IsErdos944 4 1`
= ∃ a graph G with:
  (a) χ(G) = 4,
  (b) G is VERTEX-critical (every vertex deletion drops χ to 3),
  (c) for EVERY critical edge-set `edges`, `|edges| > 1`.

Condition (c) with r=1 ⟺ NO single edge is critical ⟺ G has NO critical edge
(equivalently: deleting any one edge keeps χ = 4).

## Definitional subtleties (matter for any proof / refutation)

1. **`IsCritical` = VERTEX-critical, not edge-critical.** This is the strong "vertex-critical without critical edges" object (Brown/Lattanzio/Jensen all build vertex-critical graphs). A vertex-critical graph need NOT be edge-critical. The whole point of Dirac's conjecture: a vertex-critical graph CAN lack critical edges. (Edge-critical ⟹ vertex-critical, so an edge-critical graph always HAS critical edges and is the wrong target.)

2. **`edges : Set (Sym2 V)` ranges over ALL sym2 sets,** not just G's edges. Deleting a non-edge of G does nothing to χ, so non-edges never help make an edge-set critical with smaller cardinality. The minimal critical edge-sets are necessarily subsets of G's edge set. r=1 condition is purely about: is any singleton edge critical?

3. **Empty edge-set is never critical** (χ unchanged), consistent. The "size > 1" really bites at singletons.

4. **`V : Type u` is ARBITRARY — but the Lean statement PROVABLY forces a FINITE-EDGE witness** (rigorous proof by skeptic, supersedes my earlier hand-wave). The mechanism (skeptic_statement_lock.md + CLAIMS.md SKEPTIC ALERT): `Set.ncard` of an INFINITE set = 0 in Mathlib (`Set.Infinite.ncard`). The clause `r < edges.ncard` is then FALSE for any infinite critical edge-set. If G is infinite with χ(G)=k finite, then `G.edgeSet` is an infinite critical edge-set (delete all edges → χ≤1<k), so `r < ncard = 0` FAILS ⟹ `IsErdos944 k r` is FALSE for that G. NET: `∃ V G, IsErdos944 4 1` can ONLY be witnessed by a graph with finitely many edges, hence finite (a χ=4 vertex-critical graph has no isolated vertices). So the Lean statement IS equivalent to the finite combinatorial question — but by this `ncard` argument, NOT by fiat. Nobody needs to handle infinite V; a finite witness is necessary AND sufficient. (de Bruijn–Erdős is the supporting compactness fact: χ≤k finite iff every finite subgraph is k-colorable.)

5. **r=1 is the WEAKEST nontrivial Dirac case.** The full erdos_944 asks for arbitrary r (no critical edge-set of size ≤ r); k_eq_four with r=1 just asks "no critical edge." Solving r=1 for k=4 is the gateway; larger r for k=4 is even harder and also open.

## Why this is the SOLE open case
- Brown 1992: k=5 (first vertex-critical graph w/o critical edges).
- Lattanzio 2002: all k with (k−1) NOT prime.
- Jensen 2002: all k ≥ 5.
- Martinsson–Steiner 2025: every r ≥ 1 for sufficiently large k.
- k=4: k−1 = 3 is prime; k < 5; so none of the above cover it. SOLE remaining open case of Dirac's 1970 conjecture.
