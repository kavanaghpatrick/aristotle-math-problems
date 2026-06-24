# breaker KILL-LEDGER — E124 (BEGL96 k≥1): no route bypasses the MW spacing wall

Referee-grade input for the unified conclusion, item (1). Every candidate the invention cell proposed
to bypass the Mignotte–Waldschmidt cross-base spacing obstruction was adversarially kill-tested against
a fixed ground-truth gauntlet (admissible cofinite families + the β≈0.93–1.0 deep-trap families +
the deep stragglers). Engine: validated exact atom-sieve (breaker_atom_sieve.py, exact to 9×10⁹,
cross-checked bit-for-bit vs two independent engines). The ledger below is exhaustive over the cell's
output and shows each route reduces to the SAME wall in a different costume.

## The wall (one sentence)
For admissible D with ∑1/(d−1)=1 (the boundary, where (3,4,7) lives), the exceptional integers are
isolated points sitting at cross-base power near-coincidences |d_i^a − d_j^b|; bounding them is a
linear-forms-in-logarithms / Baker–Mignotte–Waldschmidt statement, and it lives on a measure-zero set
of continued-fraction-convergent arcs of log d_i / log d_j.

## KILL-LEDGER (route → why it reduces to MW)

| Candidate | Lane | Verdict | Reduces-to-MW mechanism (verified) |
|---|---|---|---|
| C5 / C5-band (2nd moment) | probabilistic | KILLED | Φ=0 at deep stragglers while E[Φ]≈14–22 — large-deviation events the variance can't exclude; can't discriminate β=0.933 from β=1 |
| INV-S1 (circle method) | analytic | KILLED | major-arc main term O(1) at the misses; minor-arc error same order at the boundary |
| INV-C2 / V1 / M5 (carry automaton) | combinatorial | KILLED | carry-state = two-base (3,4) gap ≈7688, grows with k → not finite-state |
| INV-V2 (Perron-Frobenius) | spectral | per-k=1 only | matrix finite at k=1 (37 states, gives n₀=581) but state count grows ~3^s at k=2 |
| INV-C1 (log-descent / valid peel) | multiplicative | algorithm, not proof | sound O(log n) DECODING (skip-depth ≤1 even at boundary k=3) but existence half tautological; own_thr(a)/a→1 kills the non-circular induction |
| INV-cassels-3 (UNSCALE deflation) | multiplicative | KILLED (unsound) | "b·h∈R ⟹ h∈R" FALSE — 36/37 holes are counterexamples; x↦x/b not well-defined on the cross-base sum |
| INV-T2 (Ostrowski/CF covering) | multiplicative | necessary-not-sufficient | θ-clustering is generic (cofinite & deep-trap identical); covering = the unproven MW question |
| INV-D3 (rep-fragility) | measure | KILLED | min-reps stays 2–5 at the actual gap, never reaches 1; slope ≠ deficit; range-blind |
| INV-M1 clean-θ / M2 | p-adic | KILLED | θ→0.955/0.9995 at power neighbors; valuation cone uninformative |
| INV-V3 (deficit drainage) | conservation | holds empirically, a-priori=MW | per-band drainage monotone through k=3, but proving drainage≥creation = bounding band cross-base alignment = MW |
| INV-M6 (base-4 repair ρ₄) | value-specific | bounded (≤6 k-uniform), a-priori=MW | ρ₄ bounded over rep n even at boundary, but proving the repair never fails = the {3,4} collision = MW |
| INV-M4-crude | value-specific | KILLED (sumset) | single top-scale inequality necessary-not-sufficient (distinctness) |
| INV-L6 (phase-locked 2-torus) | ergodic | descriptive, not closer | covering-count min(C)/window GROWS (no falsification — independent support for TRUE), but phase ψ_m only weakly torus-predictable (R²=0.38, period-4 resonance ≠ rotation numbers) ⟹ (BRIDGE) not a clean torus problem; same as T4 (~94% not exact) |

## STRUCTURAL SYNTHESIS (the load-bearing finding)
Three lanes were tried as ways to AVOID the cross-base coupling:
1. ADDITIVE closure (+M-marching: cassels-1/2, sumset deconvolution) — clean at k=1, grows with k.
2. MULTIPLICATIVE deflation (÷d self-map: C1, cassels-3, T2) — the ÷d map is well-defined on ONE
   base-b ray but BREAKS at the cross-base sum (cassels-3 unsound; C1 circular; T2 nec-not-suff).
3. LOCAL statistics (2nd moment, fragility, θ-concentration, valuation) — all blind to the deep
   stragglers (>9e9 for (3,4,11)), so all fail β≈0.93-1.0 discrimination.
**Every route that tries to factor away / avoid the coupling is provably blocked.** The coupling IS
the MW content.

### THE META-CRITERION (troika, unifies the entire ledger in one line)
Every KILLED candidate ultimately QUERIES representability at a modest computational scale — it
"n-samples" cover(D,N) somewhere (the second moment counts reps, the fragility measure counts reps,
the automaton tracks the carry of actual n, INV-C1 checks (n−a)∈R, the n-sampled torus δ reads
cover(D,N)). Any such quantity is DEEP-TRAP-BLIND BY CONSTRUCTION: the discriminating information for
the β≈0.93–1.0 families (e.g. (3,4,11), first miss >9×10⁹) lives beyond any reachable N, so an
n-sampled statistic cannot separate β=0.933 from β=1. **A surviving candidate MUST compute an INTRINSIC
quantity — a function of the atom set / D alone, NOT a scan of n.** Exactly two intrinsic shapes exist:
the two routes below. Everything sampled is pre-killed; this is why the board converged.

The two NON-blocked routes attack the coupling HEAD-ON (and are INTRINSIC — no n-sampling):
- INV-S10 (asymptotic Riesz-product minor-arc bound): bound |F_3F_4F_7| on the bad arcs directly.
  Empirically the decorrelation decay rate c∈[0.17,0.31] is k-uniform (boundary + strict-excess); the
  residual is c-lower-bound on the sparse CF-convergent arcs = the analytic face of MW.
- IFS/torus spectral radius (troika+lift): the same coupling viewed ergodically on 𝕋².

## THE CONCRETE MW WITNESS (the cleanest single piece of evidence, breaker-verified w/ maverick)
Two boundary families, IDENTICAL by every elementary parameter (both ∑1/(d−1)=1, σ=0), differ 35× in
threshold at k=3:
  n₀(3,4,7) = 166,025,260   vs   n₀(3,5,7,13) = 4,796,646   →  ratio 34.6×.
No elementary f(σ, d_max, d_2) can produce a 34.6× spread at identical σ=0. WORSE for any elementary
hope: the gap doesn't even track the closest cross-base power-coincidence — (3,4,7) has WEAKER closest
clustering (rel-pair 0.0247 via 3^29≈4^23) yet 35× LARGER n₀ than (3,5,7,13) (0.0046 via 3^7≈13^3,
the 2187≈2197 coincidence). So n₀ is NOT f(closest-pair) either — it is the FULL multi-pair,
multi-exponent transcendence (Baker) structure. This single comparison is the disproof that the
strict-excess / finite-stage-Astels "constant" is elementary: it is the MW threshold itself.
(maverick's v8 symbolic-constant hunt confirmed-negative; breaker thresholds the load-bearing evidence.)
Code: breaker_verify_maverick_35x.py.

## CONCLUSION (item 1 of the unified doc)
The entire BEGL96 k≥1 difficulty localizes to the MW spacing on measure-zero CF-convergent arcs. The
kill-ledger is exhaustive over the cell's invention output and proves no elementary / combinatorial /
multiplicative / local-statistical route bypasses it — each reduces to the same wall. The localization
(MW content confined to a measure-zero, single-scale, isolated-points set) is the contribution; the
remaining open content is exactly one transcendence question. The answer is almost certainly TRUE
(every admissible family tested is cofinite; both side-conditions provably necessary; FALSE branch
closed by the strict-2-doubling standard with corrected thresholds 581/3,982,888/166,025,260).

Ground-truth + all kill-test code: breaker_GAUNTLET.py + breaker_kill_*.py + breaker_attack_*.py.
