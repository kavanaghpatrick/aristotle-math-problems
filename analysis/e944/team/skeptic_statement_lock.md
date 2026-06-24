# E944 — DEFINITIVE STATEMENT LOCK (skeptic)

Supersedes the finiteness handling in `archivist_definitions.md` point 4 (which asserted
"the intended object is FINITE" by fiat). The Lean theorem quantifies over `V : Type u`
**arbitrary** — infinite included — so any impossibility proof or witness must contend with
what the statement *literally* says. This file proves the finite-equivalence rigorously.

Cite this file (not just intuition) whenever you (a) claim "WLOG G is finite", (b) prove
impossibility "for all 4-vertex-critical G", or (c) invoke de Bruijn–Erdős.

All Lean facts below were read directly from the pinned Mathlib in
`formal-conjectures/.lake/packages/mathlib` (line refs given) and from
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring.lean`.

---

## 0. The exact target

```
def IsErdos944 (G : SimpleGraph V) (k r : ℕ) : Prop :=
  G.IsCritical k ∧ (∀ (edges : Set (Sym2 V)), G.IsCriticalEdges edges → r < edges.ncard)

theorem erdos_944.dirac_conjecture.k_eq_four :
    answer(sorry) ↔ ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 4 1
```

Unfolded (k=4, r=1), `∃ V G, IsErdos944 4 1` asserts the existence of `(V, G)` with:

- **(A)** `G.chromaticNumber = 4`   (note: `chromaticNumber : ℕ∞`; `= 4` forces `G.Colorable 4`).
- **(B)** `∀ v : V, (⊤ : G.Subgraph).IsCriticalVertex v`, i.e. `χ(G − v) < χ(G) = 4` for every vertex.
       (`(⊤ : G.Subgraph).coe ≃g G` via `topEquiv`, Subgraph.lean:581, so this is literally
        "delete v from G, χ drops".)
- **(C)** `∀ edges : Set (Sym2 V), χ(G.deleteEdges edges) < χ(G) → 1 < edges.ncard`.

`IsCritical 4 = (A) ∧ (B)` is the standard **vertex-critical** notion (χ=4, every vertex critical).
(C) with r=1 is "no critical edge-set of size ≤ 1" ⟺ **no single edge is critical** ⟺ deleting any
one edge keeps χ = 4. This is the Dirac object: 4-vertex-critical with no critical edge.

---

## 1. THE ncard INFINITE TRAP — the load-bearing edge case

`Set.ncard : Set α → ℕ` returns the junk value **0 on infinite sets**:
> `Mathlib/Data/Set/Card.lean:573`  `theorem Set.Infinite.ncard (hs : s.Infinite) : s.ncard = 0`

So in clause (C), `1 < edges.ncard` is the proposition `1 < (a ℕ)`, and for an **infinite** critical
edge-set `edges` it reads `1 < 0`, which is **FALSE**. Therefore:

> **(C) is automatically VIOLATED if G admits even one infinite critical edge-set.**

This is not a curiosity — it forces finiteness of the witness, as follows.

### 1.1 Any G with χ(G)=k≥2 has its full edge set as a critical edge-set

`G.deleteEdges G.edgeSet = G \ G = ⊥` :
- `Mathlib/.../DeleteEdges.lean:53`  `deleteEdges_edgeSet : G.deleteEdges G'.edgeSet = G \ G'`,
  with `G' := G` gives `G \ G`.
- `SimpleGraph V` is a `CompleteAtomicBooleanAlgebra` (`Basic.lean:296`), so `G \ G = ⊥` (`sdiff_self`).

And `χ(⊥) ≤ 1`:
- `Mathlib/.../Coloring.lean:369`  `chromaticNumber_bot [Nonempty V] : (⊥).chromaticNumber = 1`.
  (G with χ=4 is Nonempty — an empty graph has χ=0.)

So `χ(G.deleteEdges G.edgeSet) = χ(⊥) = 1 < 4 = χ(G)` ⟹ `G.edgeSet` is a critical edge-set.

### 1.2 If G is INFINITE-edged, the witness FAILS

If `G.edgeSet` is **infinite**, then by §1.1 it is a critical edge-set, and by the ncard trap
`(G.edgeSet).ncard = 0`, so the (C)-clause instance `1 < 0` is false ⟹ (C) fails ⟹ `IsErdos944 4 1`
is FALSE for this G. 

> **NECESSARY CONDITION ON ANY WITNESS:** `G.edgeSet` must be FINITE.

### 1.3 Finite edges + vertex-critical at χ=4 ⟹ G is FINITE

In a vertex-critical graph with χ(G)=4≥2, **no vertex is isolated**:
- If `v` has empty neighborhood (degree 0), then `G − v ≅ G` on the colorability side: any proper
  coloring of `G − v` extends to `G` by giving `v` any color (it has no neighbors), and conversely.
  Hence `χ(G − v) = χ(G)`, contradicting (B) (`χ(G−v) < χ(G)`). So **every vertex has degree ≥ 1**.
- Every vertex is therefore an endpoint of some edge. With `G.edgeSet` finite, only finitely many
  vertices appear as endpoints ⟹ `V` is finite (up to the isolated vertices we just excluded; there
  are none). Formally: `V ⊆ ⋃_{e ∈ edgeSet} (endpoints e)`, a finite union of ≤2-element sets.

> **NET LOCK:** `∃ V G, IsErdos944 4 1` is witnessable **only** by a FINITE graph. And a finite
> 4-vertex-critical graph with no critical edge clearly satisfies (C) (all its critical edge-sets
> are finite; the minimal ones have size ≥ 2 by "no critical edge"). Therefore:

```
  (Lean) ∃ V G, IsErdos944 4 1   ⟺   (finite combinatorics)
  ∃ a FINITE simple graph G with χ(G)=4, vertex-critical, and no critical edge.
```

The equivalence holds **for a real reason** (the ncard trap kills infinite-edge witnesses), not by
declaring "we only care about finite graphs." Archivist's conclusion was right; the justification
was missing. This matters because:

- **Witness side (forge, algebra, jensen):** you may freely build a concrete `Fintype` graph. No need
  to worry that an infinite graph might be "the real witness." Good news.
- **Impossibility side (wall, count, gallai):** you must prove "every FINITE 4-vertex-critical graph
  has a critical edge." You do NOT need de Bruijn–Erdős and you do NOT need to handle infinite V as a
  separate case — the ncard trap already rules out infinite-edge G, and infinite-vertex/finite-edge G
  is impossible at χ=4 (§1.3). **Do not waste effort axiomatizing or invoking compactness.**

### 1.4 Caveat for a HOSTILE reading (does NOT change the lock, but know it)

Could a clever G have χ=4, be vertex-critical, have an infinite edge set, yet have NO infinite critical
edge-set OTHER than ones forced... no. §1.1 exhibits one specific infinite critical edge-set (the full
edgeSet) whenever edgeSet is infinite. There is no escape: infinite edgeSet ⟹ at least that one infinite
critical set exists ⟹ (C) fails. The argument is airtight. The ONLY witnesses are finite-edge, hence
finite, graphs. **Lock is hard.**

---

## 2. Secondary subtleties (verified, lower-stakes)

### 2.1 `edges` ranges over ALL of `Set (Sym2 V)`, not just `G.edgeSet`
`IsCriticalEdges edges := χ(G.deleteEdges edges) < χ(G)`. Deleting a non-edge of G does nothing:
`edgeSet_deleteEdges : (G.deleteEdges s).edgeSet = G.edgeSet \ s` (`DeleteEdges.lean:82`), so
`G.deleteEdges s = G.deleteEdges (s ∩ G.edgeSet)` (`:73`). Hence adding non-edges to a set never
changes whether it is critical, and never decreases ncard below a subset-of-edgeSet witness.
**Consequence:** the (C) condition is fully determined by edge-sets that are subsets of `G.edgeSet`.
For r=1 it reduces exactly to: **no singleton `{e}` with `e ∈ G.edgeSet` is critical.**
⚠️ A subtle trap for the IMPOSSIBILITY side: when you negate (C) you get "∃ edges, critical ∧ ncard ≤ 1".
ncard ≤ 1 means ncard ∈ {0,1}. ncard=0 ⟺ `edges` finite-and-empty OR infinite. Empty set is never
critical (χ unchanged). An *infinite* critical set has ncard 0 and DOES satisfy "ncard ≤ 1" — but that
is exactly the §1 mechanism, only possible for infinite-edge G which is already excluded. For the FINITE
witness we care about, ncard ≤ 1 ⟺ singleton ⟺ a genuine critical edge. So on finite graphs,
¬(C) ⟺ "∃ a critical edge". Clean.

### 2.2 `IsCritical` is VERTEX-critical, NOT edge-critical
Already flagged by gallai (vocab trap) and archivist. Re-confirmed: `IsCritical k := χ(G)=k ∧
∀v, IsCriticalVertex v`. The classical edge-criticality (χ(G−e)=k−1 for EVERY e) is a DIFFERENT,
stronger-on-edges class. The target is vertex-critical-but-not-edge-critical. Gallai/Kostochka–Yancey
density theorems are stated for EDGE-critical graphs and do NOT apply verbatim. (See gallai_vocab_trap.md.)
**My independent confirmation:** an edge-critical graph has EVERY edge critical, so it trivially has a
critical edge ⟹ it can NEVER be an E944 witness. The witness must be a vertex-critical graph whose
edge-critical "core" (the spanning subgraph of critical edges) is empty. Worth stating that bluntly.

### 2.3 χ uses `ℕ∞`; `= 4` is a genuine equality in `ℕ∞`
`chromaticNumber := ⨅ n ∈ {n | Colorable n}, (n:ℕ∞)` (`Coloring.lean:151`). `= 4` ⟹ `Colorable 4`
(finitely 4-colorable) and `¬Colorable 3`. No off-by-one: `IsCritical 4` is χ exactly 4, and (B) demands
each `χ(G−v) ≤ 3`. Standard.

### 2.4 The `r=1` here is the EASIEST nontrivial r for k=4
`erdos_944` (the umbrella) asks ∀r≥1; `k_eq_four` pins r=1. r=1 = "no critical edge". Larger r for k=4
is also open and strictly harder. Solve r=1 first.

---

## 3. ONE-LINE LOCK FOR THE SQUAD

> Prove/refute: **does a FINITE simple graph G exist with χ(G)=4, every vertex critical (χ(G−v)≤3 ∀v),
> and no critical edge (χ(G−e)=4 ∀e∈E)?** The Lean statement over arbitrary `V : Type u` is provably
> equivalent to this finite question (ncard-trap argument, §1). No infinite case to handle. No
> compactness needed. Edge-critical structural theorems do NOT apply (target is vertex-critical only).

---

## STATUS
- §1 (ncard trap + finite-equivalence): verified against Mathlib source line-by-line. HARD LOCK.
- §2: verified. §2.1 negation subtlety is the one place an impossibility proof could drift; flagged.
- Cross-check requested from: wall (impossibility uses §1.3 finiteness), forge/algebra (witness may be Fintype).
