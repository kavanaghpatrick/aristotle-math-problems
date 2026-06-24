# hunter — Completeness of the Exhaustive Floor (rigor documentation for the n_min lower bound)

This documents why the computational floor "no (4,1)-witness on ≤ N vertices" is a COMPLETE search,
i.e. a genuine theorem, not just "we didn't find one." Required for the publishable lower bound the
impossibility branch (wall) builds on.

## The object (locked to FormalConjectures source)
A **witness** = a finite simple graph G with:
- (V) χ(G) = 4,
- (C) vertex-critical: ∀ v, χ(G − v) ≤ 3,
- (E) no critical single edge: ∀ e ∈ E(G), χ(G − e) = 4.
This is exactly `∃ G, G.IsErdos944 4 1` (skeptic's statement-lock confirms the Lean ncard form is
finite-equivalent: a witness must have finitely many edges, hence is finite).

## Three reductions that make `geng -c -d3` a COMPLETE enumerator

### R1. Witness ⟹ connected.  (so `-c` loses nothing)
If G is disconnected, χ(G) = max over components χ(Cᵢ). For χ(G)=4 some component has χ=4. Removing
a vertex v from any OTHER component leaves a χ=4 component intact ⟹ χ(G−v) ≥ 4 ⟹ v non-critical ⟹
G not vertex-critical. (If two components both have χ=4, removing a vertex from one leaves the other
intact: same conclusion.) Hence every 4-vertex-critical graph is connected.
*Verified*: two disjoint K4's → χ=4 but vertex-critical=False.

### R2. Witness ⟹ minimum degree δ(G) ≥ 3.  (so `-d3` loses nothing)
A vertex v with deg(v) ≤ 2 in a 4-chromatic graph is non-critical: any proper 3-coloring of G−v
uses ≤ 2 colors on N(v), leaving a free color for v ⟹ χ(G−v) = χ(G) = 4 ⟹ v non-critical. So
vertex-criticality forces δ(G) ≥ 3.
(Conditional strengthening: by Skottová–Steiner Prop 5.1 / gallai THM 3 / proximity, a *witness*
additionally needs δ ≥ 6 — used by the `-d6` accelerated floor, marked CONDITIONAL.)

### R3. The predicate is isomorphism-invariant.  (so one representative per class suffices)
χ, vertex-criticality, and edge-criticality are all invariant under graph isomorphism. nauty's
`geng` outputs exactly one representative of each isomorphism class of connected δ≥3 graphs on n
vertices (canonical-form orderly generation — nauty's correctness is itself extensively verified and
relied on across combinatorics literature). Testing one representative per class is therefore
sufficient and complete.

## Conclusion (unconditional)
For each n ≤ 10, `geng -c -d3 n` enumerated EVERY isomorphism class of connected δ≥3 graphs; each was
tested for the full witness predicate (V)∧(C)∧(E) with an exact χ algorithm. Zero witnesses found.
By R1–R3 this covers ALL graphs on ≤ 10 vertices.

  **THEOREM (computational). Every 4-vertex-critical graph on at most 10 vertices has at least one
  critical edge. Equivalently: there is no (4,1)-witness (no graph resolving
  `erdos_944.dirac_conjecture.k_eq_four`) with ≤ 10 vertices. Any witness has ≥ 11 vertices.**

## Validation of the verifier (squad-1 lesson: verifier before searcher)
- TWO independent χ implementations: pure-python backtracking AND SAT (Cadical). Cross-validated on
  9 reference graphs (K4, K5, C5, W5, Grötzsch, Petersen, K₃,₃, …) — agree on every χ, all known
  chromatic numbers correct.
- During search, a sample of every n's near-misses re-verified by the SAT path: 0 disagreements.
- A SECOND completeness instrument (SAT/CEGAR, cegar_search.py) independently returns UNSAT at n=7,8.
- Independent re-enumerations by skeptic (#2: geng+backtrack+SAT) and count (#3: atlas) reproduce the
  4-vertex-critical counts exactly (1,0,1,7,8,124 for n=4..9; δ≥3 filter validated full-vs-d3 at n=8).

## Caveats stated honestly
- The δ≥6 (`-d6`) floor is CONDITIONAL on Prop 5.1 (δ≥6 for any witness). The δ≥3 floor is
  unconditional.
- "No witness ≤ N" is NOT evidence the answer is NO globally (squad-1 calibration: thresholds can be
  large; known constructions for k≥5 are themselves large). This is a LOWER BOUND on witness size,
  feeding the impossibility analysis — not a claim that no witness exists.
