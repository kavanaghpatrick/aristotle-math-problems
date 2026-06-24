# hunter — EXISTENCE CAMPAIGN (SAT-CEGAR witness search for e944, k=4)

## Goal
FIND a (4,1)-witness: a graph G with χ(G)=4, vertex-critical (∀v χ(G−v)≤3), and NO critical edge
(∀e χ(G−e)=4). A verified witness resolves Dirac's 1970 conjecture for k=4 (open 55 years).
The squad prior has shifted toward YES (no obstruction found anywhere; symmetric substrates
exhausted ≤ order 20 by count). The witness, if it exists, is ASYMMETRIC (Brown's k=5 witness is
17-vtx asymmetric; circulant/Cayley spaces are empirically closed for k=4).

## Encoder: `existence_cegar.py`
SAT over the graph (edge variables e[i][j]), incremental Cadical, with:
- STATIC necessary conditions (Skottová–Steiner Prop 5.1, proven; re-derived by gallai+proximity):
  min-degree ≥ 6, max-degree ≤ n−5. (These subsume KY e≥(5n−2)/3 and min-deg-3.)
- BAKED vertex-criticality: witnessing 3-coloring cV[v] of every G−v (forces ∀v χ(G−v)≤3 by
  construction — every returned model is automatically vertex-critical).
- BAKED 4-colorability: witnessing 4-coloring c4 (forces χ≤4).
- CEGAR (sound, lazy) for the two co-NP conditions: χ≠3 (G not 3-colorable) and no-critical-edge
  (every G−e not 3-colorable). Refinement clauses proven never to exclude a true witness.
- Every candidate witness re-verified on BOTH independent checkers (backtrack + SAT) before declaring.

## Soundness (why a returned WITNESS is real, and UNSAT is a real theorem)
- vertex-criticality + χ≤4 are baked → any model satisfies them.
- χ≠3 and no-critical-edge refinements only add clauses satisfied by every genuine witness (see
  module docstring proof). So the search NEVER excludes a witness.
- With symmetry-break OFF, the encoding ranges over ALL labeled graphs meeting the static conditions,
  so UNSAT at fixed n = "no (4,1)-witness on n vertices" (a completeness theorem, matching the geng
  floor as a second instrument).

## Validation gates (must pass before trusting big-n runs)
1. n=11 min-deg-6 → MUST be UNSAT (geng floor: 0 δ≥6 4-vtx-critical graphs at n=11). [running]
2. No FALSE_CANDIDATE ever (would mean a refinement bug; dual-checker catches it).

## Run plan (n=13 is first n where δ≥6 4-vtx-critical graphs exist at all)
- n=13, 14, 15, 16 — FIND mode (sym hint on for speed; still sound for existence).
- Parallelize across n (independent processes per n on the 14-core box).
- Bottleneck reports: refinement iteration count + elapsed per n; if a single n stalls (no UNSAT,
  no witness, refinements ballooning), report exact iter/sec and switch to batch-blocking (add
  gallai THM4 2-2-2 balanced-neighborhood static clauses to kill candidates wholesale).

## Status log

### SAT-CEGAR bottleneck (2026-06-10) — why it does NOT scale
- Validation n=11 min-deg-6: encoder did NOT reach UNSAT — ~6000 iterations all stuck on
  "chi3-refine" at degree [6,...,6]. Root cause: making SAT *discover* non-3-colorability by blocking
  one 3-coloring at a time cannot converge (astronomically many 3-colorable δ≥6 graphs).
- Tried lex-leader symmetry breaking (adjacent-transposition). FOUND UNSOUND: standalone n=4
  enumeration shows it admits only 8 of 11 isomorphism classes (drops C4, P4, diamond). So `--sym`
  UNSAT is untrustworthy AND it can miss a witness. DISABLED (raises now). Do not re-enable without a
  complete static break (full lex-leader or canonical-augmentation).
- geng -c -d6 enumeration: INFEASIBLE past n=11. n=12 produces 53M δ≥6 graphs in 20s and is nowhere
  near done (total in the billions). Degree window Δ≤n−5 does not help enough.

### Pivot to guided stochastic search (witness_anneal.py)
For the EXISTENCE goal, complete methods are out of reach at n≥12, so we use simulated annealing over
the δ≥6 / Δ≤n−5 regime, testing the FULL predicate with the fast exact checker. One verified witness
resolves the problem. Energy = #critical-edges among 4-vertex-critical graphs (staged penalty for
non-4-chromatic / non-vertex-critical). Witness = energy 0, verified on both checkers.

KEY DIAGNOSTIC: 99.8% of random 6-regular graphs on n=13 are ALREADY 4-chromatic (only 91/44661 are
3-colorable). So the difficulty is NOT 4-chromaticity — it is the joint tension between
VERTEX-CRITICALITY (needs every G−v to drop to χ=3, rare for dense graphs) and NO-CRITICAL-EDGE,
both in the dense δ≥6 regime. The witness is a dense graph that is *just barely* 4-chromatic at every
vertex yet has no single critical edge.

Campaign 1 (2026-06-10): 12 workers, n=13,14,15 × 4 seeds, 30 min. (results below)
- n=13 60s smoke: 142 seeds, best energy = 13 critical edges (4-vtx-critical but far from 0).

### RIGIDITY FINDING (convergent, multi-method) — local search cannot approach a witness
The minimum critical-edge count among vertex-critical δ≥6 graphs at n=13 plateaus at **~13** across:
- my annealer with degree-preserving moves (best 13),
- my annealer with the wider [6,n−5] add/remove move set (still 13),
- forge's three local-search methods (all stuck),
- count's 610 circulants n≤40 (best leaves ~1/3 of edges critical).
At n=14,15, random 6-regular seeds rarely even REACH the vertex-critical manifold in short budgets
(dense graphs have redundant 4-chromatic structure that survives vertex deletion). So: a witness, if
it exists, is an ISOLATED special structure, NOT reachable by incremental moves from typical δ≥6
graphs. This matches gallai's "obstruction is GLOBAL not local" and the asymmetry finding (count).
Implication: stochastic local search is the wrong instrument; the witness needs either a clever
explicit construction (forge/jensen/algebra) or a complete search at n where one is feasible
(skeptic's exhaustive 6-regular n=13 is the trustworthy slice). The honest existence verdict from the
computational side at reachable n is: NO witness found, and the search landscape is hostile to local
methods.


### DEFINITIVE root-cause finding (2026-06-10): why SAT-CEGAR cannot work here
Two experiments pin the failure precisely:
1. **THM4 static clauses make the base instance intractable.** Wired proximity's thm4_apply (sound,
   validated on fixed C₁₃(1,2,5)). At n=11 min-deg-6: WITHOUT THM4 the first solver.solve() returns
   in 0.00s; WITH THM4 (1848 clauses) it does NOT return in 90s. In the variable-edge search, THM4's
   per-(v,c) thm4y auxiliaries + seqcounter cardinality, layered on the n baked 3-colorings, build a
   cardinality network Cadical can't crack. So THM4-static trades one blowup for another.
2. **The real bottleneck is forcing χ≥4, which THM4 doesn't touch.** The original (no-THM4) n=11 CEGAR
   spent ALL ~6000 iterations in "chi3-refine" at degree [6,...,6] — i.e. the solver kept proposing
   δ≥6 graphs that are 3-COLORABLE, refined away one 3-coloring at a time, never reaching a
   vertex-critical candidate. THM4 acts only on vertex-critical-with-critical-edges graphs (the
   E-refine stage), which the search never reaches. So THM4 cannot help the dominant stall.

**CONCLUSION (firm):** SAT-CEGAR for this problem fails at forcing 4-chromaticity (χ≠3), a co-NP
condition that one-3-coloring-at-a-time blocking cannot converge on, and that no sound static
necessary-condition prune (degree, THM4, edge-connectivity) addresses. A complete static symmetry
break (canonical augmentation) would be required to even make UNSAT trustworthy, and the χ≥4 blowup
would remain. The SAT path is abandoned. The complete instruments are: geng enumeration (feasible to
n=12 full δ≥6, n=13 6-regular only) and proximity's structural SAT on the small K4-free-pruned n=13
|E|=40-41 corner. Beyond that, only explicit construction (forge/archivist) can produce a witness.

## GPU verification kernel (3^n enumeration) — built, VALIDATED, superseded by BHK (2026-06-11)
team-lead GPU directive: built gpu_verifier.py — full 3^n coloring enumeration on PyTorch MPS, one
pass yields chi<=3, f(G), B1 (min-conflict mass), per-edge AND per-vertex criticality.
VALIDATION (gpu_verifier_validate.py): EXACT match vs checkers.py on the full census — C13(1,2,5)
(vc, critE=13, f=1, B1=78), C14(1,2,5) (not-vc, critE=0, f=2), K_2,2,2,2 (not-vc, critE=0, f=4),
Grotzsch (vc, all 20 critical), K4, n=10 champion — ZERO mismatches, plus CPU brute-force f cross-check.
THROUGHPUT (the reason 3^n was rightly cancelled in favor of BHK 2^n): n=14 = 17 graphs/s best case
(colors tensor precomputed once + reused across graphs), n=16 = 0.3/s — vs CPU floor_worker 8800/s.
Root cause: exhaustive 3^n enumeration touches EVERY coloring; backtracking PRUNES the tree (proves
non-3-colorability after a tiny fraction). GPU parallelism cannot overcome the exponential work gap.
STATUS: superseded by gpu-smith's BHK 2^n inclusion-exclusion engine, but RETAINED as an INDEPENDENT
CROSS-CHECK ORACLE for BHK census validation (different algorithm = real verification). hunter owns
marathon v2 (CPU geng/anneal proposal + GPU BHK batch eval + exact CPU gate + skeptic adjudication).

## MARATHON v2 (2026-06-11) — hybrid, measured-optimal, multi-algorithm gate
gpu-smith delivered the BHK 2^n inclusion-exclusion engine (bhk_engine.py), VALIDATED vs checkers.py
(full census + 50 random, both prime moduli agree). CROSS-CHECK: my 3^n kernel + BHK + checkers (THREE
different algorithms) all agree on the census — strongest verification foundation.
gpu-smith's honest verdict (matches my 3^n finding): checkers backtracking beats BHK 200-3500x on the
full predicate; BHK pays full 2^n every time, backtracking short-circuits. So GPU engines are
CROSS-VERIFIERS, not the driver.
ARCHITECTURE (marathon_v2.py + marathon_v2_run.sh, PID launched nice -19):
  PROPOSE (annealer streams, since geng infeasible n>=14): witness_anneal irregular δ≥6 n=14-18 +
  count's min-conflict SA. CHECK: CPU floor_worker full predicate (8,800/s/core, ~100k/s on 14 cores).
  GATE on any 0-critical hit: triple_verify() = checkers(bt) + checkers(SAT) + 3^n GPU + BHK, ALL FOUR
  must agree -> skeptic_adjudicate.py -> ALERT team-lead+algebra+skeptic. (algebra exact gate +
  proximity verifier additional.) Gate tested end-to-end: synthetic C13(1,2,5) correctly REJECTED.
  Log: search_n14plus.log. Band n=14-18 primary. Early rounds: rigidity holds (plateau ~1002, no witness).
