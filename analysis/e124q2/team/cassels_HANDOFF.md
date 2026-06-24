# cassels HANDOFF (≤1 page)

## Status
Owned the completeness-machinery angle. Delivered: **REDUCTION_THEOREM.md** (squad primary
deliverable, CHECKPOINT state — proven stack Thms 1–9 + open core + frontier + formalization table +
errata; TODOs marked at bottom). Plus my analysis files: cassels_completeness_lemma.md (Lemma C +
side-condition mapping), cassels_threshold_scaling_and_BEGL_constants.md, cassels_mass1_resolution.md,
cassels_completeness_machinery.md. Engines: code/reach.py (bitset), code/fast_engine.py (numpy, =breaker's).

## Key results (mine)
- **Lemma C** [ELEMENTARY]: R(D,k) cofinite ⟺ +M-closure failures finite (M=b^k). Threshold identity
  N₀ = v+M (v=last +M-failure), verified exact on 7 families.
- **Side-condition mapping** [COMPUTED, controls proved]: gcd=1 ⟺ residue coverage (cond a);
  β≥1 ⟺ +M-closure (cond b). Orthogonal. This is the keystone the lead built the commission around.
- **Resolved the lead's BLOCKING discrepancy** (lift vs maverick): `1/(d_max−1)` is the d_max-RAY-ALONE
  sum at x=d_max^J (verified 0.1667); the MERGED sum is β (lift's liminf correct). Cassels uses the
  merged sum ⟹ governed by β. maverick's "inf=1/(d_max−1)" was a single-ray measurement, NOT merged.
- **Corrected constants** (validated: engine reproduces BEGL (3,4,7) k=1=581 exactly):
  (3,4,7) N₀ = 581 / **3,982,888** / **166,025,260** for k=1/2/3 (k=3 stable at N=700M).
- **BEGL96 errata**: 3 of 4 printed s=1 constants off by +1 → use 79/112/17; (3,4,7)=581 ok.
  BEGL proves (3,4,7) k=1 ONLY ⟹ 124.lean ne_zero_three_four_seven is an over-claim (scholar filed report).

## Where I stopped (loose end now RESOLVED by breaker)
The (3,4,11) β=0.933<1 "cofinite" finding (N₀=1595, frozen N=40M→300M) is a **DEEP STRADDLER TRAP,
not a converse violation** — RESOLVED by breaker, no successor action needed. Pomerance's converse is
exact and safe: β<1 forces an infinite uncovered set, but at arbitrarily LOW density when β is barely
below 1, so the first exception lies beyond reach (breaker's atom-sieve: (3,4,11) k=0 clean to 9×10⁹,
the exception is real but > 9e9). Onset scale is wildly base-sensitive (transcendence): (3,5,7)
β=0.917, (3,4,10) β=0.944, (3,4,12) β=0.924 all look clean to 200M, while (3,4,9) β=0.958 shows misses
at 59048. So β≥1 IS necessary; my N₀=1595 was right as far as it went but is not the true threshold.
Lesson: even a 7.5× frozen window can be a straggler artifact when β is just below 1.

## Next steps (priority order)
1. Finish REDUCTION_THEOREM.md TODOs (Part 5 reconciliation list from lead: pull troika's mult-indep
   lemma, scholar's prime-tower bound, breaker's coverage-lag/threshold law, density's piece).
2. Get sumset+maverick to sign off the (finite +M-failures)≡(SEED)≡(★) equivalence (Part 2 TODO).
3. Get lift to confirm Theorem 9's margin closes the β>1 bulk (Part 3 strict-vs-boundary TODO).
   (The (3,4,11) puzzle is RESOLVED — see "Where I stopped"; β≥1 confirmed necessary.)

## Traps (learned the hard way)
- **Straggler trap**: local coverage hitting density 1.000 does NOT mean cofinite — stragglers persist
  far above. (3,4,7) k=2 looks done at 800k but last gap is 3.98M. A threshold is valid only if the
  window extends ≥3–4× past it with a verified gap-free tail. This bit the WHOLE team (785743, 57.7M
  were all truncations).
- Single-pass Cassels/Birch provably does NOT close E124 (maverick/troika/carry); cofiniteness is a
  multi-atom phenomenon; the surviving gaps are MW/Baker cross-base coincidences.
- Don't conflate the two "harmonic masses": conjecture β=∑1/(d−1) vs BEGL Claim-1 ∑1/(element−1).
- Lemma BG gives bounded gaps, NOT cofiniteness (maverick). "BG + residue coverage ⟹ done" is INVALID.
