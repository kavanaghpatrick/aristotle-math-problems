# hunter — Computational Assault on Erdős #944 (Dirac k=4): Consolidated Result

**Question.** Does a (4,1)-graph exist? = a finite graph G with χ(G)=4, vertex-critical
(∀v χ(G−v)≤3), and NO critical edge (∀e χ(G−e)=4). Existence resolves Dirac's 1970 conjecture for
k=4 (the sole open case). Verifier locked to FormalConjectures `IsCritical`/`IsCriticalEdges`.

## Verdict from the computational side: NO WITNESS found; none reachable at currently-feasible n.

### 1. Witness-size lower bounds (rigorous) — NO WITNESS ON ≤ 12 VERTICES
- **Unconditional, n ≤ 10:** exhaustive `geng -c -d3` (δ≥3 proven necessary), full predicate tested
  with exact χ; 4-vertex-critical counts 1,0,1,7,8,124,2453 (n=4..10), every one with a critical
  edge. Triple-sourced (hunter, skeptic, count); CEGAR confirms UNSAT n=7,8. Completeness proof:
  hunter_completeness_proof.md.
- **n = 11, within δ≥6 (Prop 5.1, proven necessary):** geng -c -d6 = 868,311 graphs, 0
  four-vertex-critical, 0 witnesses.
- **n = 12, COMPLETE within δ≥6:** since Δ≤n−5=7, the entire δ≥6 regime = degrees in {6,7}. Exhaustive
  `geng -c -d6 -D7 12` = **4,455,844 graphs, 0 four-vertex-critical, 0 witnesses** (8-shard parallel).
  Combined with skeptic's exhaustive 6-regular n=12, this CLOSES n=12: no (4,1)-witness on 12
  vertices (conditional only on the proven δ≥6 necessary condition).
- **n = 13: partial** — 6-regular slice exhaustively closed (skeptic: only C₁₃(1,2,5), has a critical
  edge). Full δ≥6 enumeration infeasible (degrees {6,7} alone time out at >120s for counting).

  **NET: no (4,1)-witness on ≤ 12 vertices. Any witness has ≥ 13 vertices** (δ≥3-unconditional ≤10;
  δ≥6-exhaustive 11–12).

### 2. Steiner's Problem 5.2 (6-regular witness): NO for n = 11,12,13,14 (with skeptic, exhaustive)
- n=11: 266, n=12: 7,849, n=14: 21,609,300 connected 6-regular graphs — NONE even 4-vertex-critical.
- n=13: exactly ONE 6-regular 4-vertex-critical graph (count's circulant C₁₃(1,2,5)); it HAS a
  critical edge but **26 of its 39 edges (2/3) are non-critical** — the closest approach found,
  missing a witness by a single difference-orbit.
- Every χ decision cross-checked by two independent algorithms (backtrack + SAT); zero disagreements.

### 3. The min-critical-edge floor (rigidity) — why local search cannot reach a witness
The minimum number of critical edges among vertex-critical δ≥6 graphs at n=13 is **13** (= the
C₁₃(1,2,5) value), and this is a hard plateau across every method tried:
- hunter annealer, two move sets (degree-preserving; full [6,n−5] add/remove): best 13.
- forge: three local-search methods, all stuck.
- count: 610 circulants n≤40, best leaves ~1/3 of edges critical.
At n≥14, random dense δ≥6 graphs rarely even reach the vertex-critical manifold (dense graphs carry
redundant 4-chromatic structure surviving vertex deletion). Conclusion: a witness, if it exists, is
an ISOLATED special structure, not reachable by incremental moves — consistent with gallai's proof
that the obstruction is GLOBAL, not local.

## Methods that DID NOT scale (exact bottleneck reports, for the successor / writeup)
1. **SAT-CEGAR** (existence_cegar.py): sound, and a valid completeness instrument at small n
   (UNSAT n=7,8). Does NOT scale: forcing SAT to *discover* non-3-colorability by blocking one
   3-coloring at a time never converges (n=11: 6000+ refinements, no progress). A lex-leader
   symmetry break (adjacent transpositions) was found UNSOUND — at n=4 it admits only 8 of 11
   isomorphism classes (drops C4, P4, diamond), so its UNSAT is untrustworthy and it can miss a
   witness. DISABLED. A complete static break (full lex-leader / canonical augmentation) would be
   needed to revive this path.
2. **geng δ≥6 enumeration**: infeasible past n=11 (n=12 produces 53M graphs in 20s, total in the
   billions; the Δ≤n−5 window does not help enough).
3. **Guided annealing** (witness_anneal.py): reaches the genuine optimum at n=13 (cross-validates
   skeptic) but the landscape rigidity blocks descent toward 0 critical edges.

## What would move the needle next
- An explicit CONSTRUCTION (forge/jensen/algebra lanes) — local search and enumeration are exhausted
  at reachable n; the witness is not a "nearby" object.
- A complete-symmetry-breaking SAT encoding (canonical augmentation) to make CEGAR a real search at
  n=12,13 for the IRREGULAR δ≥6 regime (the only slice not exhaustively closed).
- The IRREGULAR δ≥6 regime at n=13,14 is the sole computational gap (6-regular is closed ≤14, all
  degrees closed ≤10/≤11). A solo nice'd annealer is probing n=16 now; no witness expected.

## Files
checkers.py (locked verifier), floor_worker.py, floor_parallel.sh/_d6.sh, cegar_search.py,
existence_cegar.py, witness_anneal.py, hunter_completeness_proof.md, hunter_floor_results.md,
hunter_existence_campaign.md. Cross-squad: skeptic_problem52_floor.md, count_*, gallai_local_structure.md.
