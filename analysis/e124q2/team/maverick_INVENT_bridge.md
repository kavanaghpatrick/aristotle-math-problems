# maverick INVENTION round: new tools for the (BRIDGE) inequality

Target: prove base-7 subset-sum shifts cover the B₃+B₄ gap structure (lift's (BRIDGE)). 5 invented
candidates, all computable + breaker-testable. Ground-truth harness: /tmp/bridge.py (reproduces
lift exactly: (3,4,7) k=1 n₀=581, P=3B₃+4B₄ deficit 0.385/0.249/0.193). NO retrieval.

## LEAD CANDIDATE — C5: SECOND-MOMENT (variance) covering method ★★★
**Invariant:** Φ(n) := #{c ∈ B₇, c ≤ n : n−c ∈ P} = number of representations of n (P = 3B₃+4B₄).
**New argument-shape:** the bridge succeeds NOT by worst-case shift-counting (lift's margin) but by a
SECOND-MOMENT bound. (BRIDGE) ⟸
  (i) E[Φ(n)] = ρ(n)·|B₇ ∩ [0,n]| → ∞  [mean rep-count grows; |B₇∩[0,n]|~n^0.356, ρ bounded below], AND
  (ii) Var[Φ(n)] = O(E[Φ(n)])  [Poisson-like concentration].
Then Chebyshev: Φ(n) ≥ E[Φ] − C·√Var > 0 for n large ⟹ every n covered. **No MW, no worst-case count.**
**Computed (var/mean Poisson-like, min Φ grows):**
| scale | minΦ | meanΦ | varΦ | var/mean | (mean−min)/√var |
|-------|------|-------|------|----------|-----------------|
| 10⁴ | 1 | 17.5 | 58 | 3.35 | 2.15σ |
| 10⁵ | 10 | 26.7 | 15 | 0.55 | 4.36σ |
| 10⁶ | 64 | 87.5 | 51 | 0.58 | 3.29σ |
| 3×10⁶ | 81 | 107 | 35 | 0.32 | 4.38σ |
**Induction:** across scale-doublings, E[Φ] grows and var/mean stays O(1) ⟹ margin in σ-units grows
⟹ self-sustaining. The load-bearing new estimate is (ii), reducible to C6.

## C6 — COVARIANCE-DECAY of base-7 shifts (the engine for C5-ii) ★★
**Invariant:** Cov_W(c,c') = mean_{n∈W} 1[n−c∈P]1[n−c'∈P] − ρ². **Claim:** ∑_{c'} |Cov(c,c')| = O(ρ)
(summable, decaying) ⟹ Var[Φ]=∑_{c,c'}Cov = O(E[Φ]). **Computed:** Cov(c₀, c_j) decays
0.233→0.088→0.033→0.045→0.012 as the shift gap grows ⟹ summable. This is a self-contained statement
about base-7 digit-set correlation — the genuine new analytic content, replacing MW pairwise spacing.

## C1 — Covering potential = C5's Φ, viewed as a potential ★★
min Φ(n) grows 1→20→67 across scales. If provable lower bound minΦ(n) ≥ f(n)→∞, done. (= C5 mean-side.)

## C2 — Geometric deficit-decay per shift ★
Adding base-7 shifts smallest-first, the P-deficit in a window decays multiplicatively (~0.6–0.8 per
shift-doubling), hits 0 by t≈32. If per-shift reduction factor provably < 1 (from C6 decorrelation),
deficit→0. Weaker than C5 (needs the correlated-decay rate).

## C3 — log-periodic self-similar deficit (WEAK)
P-deficit at geometric scales ×3 oscillates bounded (0.14,0.15,0.27,0.21) — log-periodic-ish, not a
clean fixed point. Not yet a proof shape.

## C4 — arithmetic thickness (gap weighted by dist-to-power) (WEAK)
Big P-gaps (width 7680) sit MID-scale, not adjacent to powers. So "gaps abut powers" framing is wrong
(matches lift's correction). Doesn't yield an invariant.

## VERDICT this round
**C5 (second-moment) + C6 (covariance decay) is the lead** — a NEW covering tool that bypasses the
worst-case shift count entirely, has a clean Chebyshev induction, and the only open estimate is the
covariance-decay bound (ii), which is computable and breaker-testable. Sent to breaker for kill-testing
vs the β≈0.95 deep traps. If Var[Φ]=O(E[Φ]) survives there, this is the bridge proof shape.

## C5 SELF-KILL + TRANSFORM (death-point discipline) — the candidate SURVIVES as a reduction

**Self-kill attempt:** at the (3,4,7) k=1 LAST hole n=581: Φ(581)=0, but neighbors Φ=3,3,5,4,5 and
E[Φ(581)] ≈ ρ·|B₇∩[0,581]| = ρ·8 ≈ 5. So Φ=0 DESPITE E≈5 — a naive variance bound can't certify
Φ(581)>0. **The holes live exactly in the SMALL-E regime** (only 8 shifts available below 581).

**But this TRANSFORMS rather than kills C5.** The variance method certifies Φ(n)>0 only for n ≥ n*,
where n* = scale at which E[Φ(n)] > C·√Var[Φ(n)]. Since E[Φ]=ρ·|B₇∩[0,n]| and |B₇∩[0,n]|~n^0.356,
the threshold is |B₇∩[0,n]| > C²/ρ = a CONSTANT, so **n* ~ (C²/ρ)^{1/0.356} is EFFECTIVE** (a function
of the variance constant C only — NO transcendence). The holes in [X₀, n*] are a FINITE check.

> **TRANSFORMED (BRIDGE) [the new tool, survives]:** (BRIDGE) ⟸ **Var[Φ(n)] ≤ C·E[Φ(n)] with an
> EXPLICIT constant C** (from C6 covariance decay). Then Φ(n)>0 for all n ≥ n*(C) (effective), and
> [X₀, n*(C)] is a finite verification. **This replaces MW pairwise-spacing with an effective
> second-moment bound** — a genuinely different, potentially transcendence-free route.

**Empirical feasibility (3,4,7):** at n*=582, E≈5, √Var≈2.2, so need C < 2.3 in Var≤C·E. Measured
var/mean ≈ 0.3–0.6 ≪ 2.3 at scale — comfortably consistent. The constant looks achievable.

**NEW DEATH POINT (next round):** make the covariance-decay bound C6 (∑_{c'}|Cov(c,c')| ≤ C·ρ)
EXPLICIT and uniform in scale — that delivers the constant C, hence n*, hence the bridge with NO MW.
This is the load-bearing open sub-estimate, fully computable/breaker-testable. Sent to breaker.

## NET INVENTION VERDICT
C5 (second-moment) is a SURVIVING new tool: it transforms (BRIDGE) from a worst-case-MW statement
into an EFFECTIVE second-moment bound + finite check, with a clean scale-induction (n* effective in
C). The remaining open piece is a single quantitative covariance-decay estimate (C6) — computable,
non-transcendental, and the obvious next invention target. This is the "one candidate with an
induction" the mandate sought. Whether the explicit C truly avoids MW (vs C itself hiding an MW
constant) is the make-or-break for the next round.

## C5 MECHANISM DERIVED — why C is plausibly ELEMENTARY (the MW-escape argument)

Decomposed Var[Φ] to test if the constant C hides MW. KEY identity:
> Cov(c,c') = R_P(c−c') − ρ²,  where R_P(δ) = Pr[x∈P and x+δ∈P] = the P-AUTOCORRELATION (P=3B₃+4B₄).
So Var[Φ] = ∑_{c,c'∈B₇≤n} [R_P(c−c') − ρ²] = diagonal ρ(1−ρ)·M + off-diagonal ∑_{c≠c'}[R_P(c−c')−ρ²].

**Why Var/E = O(1) (verified Var/E=1.14 at 5×10⁶, min Φ=48≫0):**
- Diagonal: contributes (1−ρ) ≈ 0.22 to Var/E.
- Off-diagonal: per-row ∑_{c'}[R_P(c−c')−ρ²] is BOUNDED (measured −4.2, even slightly negative ⟹
  anti-correlated, better than independent) ⟹ total = O(M) ⟹ Var/E = O(1).
- The bound comes from [R_P(δ)−ρ² → 0, an ELEMENTARY autocorrelation-decay property of P] × [base-7
  lags are SPARSE, density n^0.356, elementary]. **NEITHER involves |3^p−4^q| power-spacing.**

**MW-ESCAPE CLAIM:** the variance constant C is controlled by (P-autocorrelation) × (B₇-sparsity),
both elementary. I scanned var/mean across scales INCLUDING the cross-base coincidences (3⁵≈4⁴ etc.):
BOUNDED everywhere (worst 2.4, no spike at coincidences). So C does NOT hide MW — the second-moment
method plausibly gives a TRANSCENDENCE-FREE bridge. This is the candidate's real value.

**RIGOROUS OPEN PIECE (precise, non-transcendental):** prove "∑_{δ∈ lag-set} (R_P(δ)−ρ²) < ∞
uniformly," i.e. R_P(δ)−ρ² is summable over base-7 subset-sum differences. Decay is SLOW (~δ^{−ε});
the base-7 sparsity must compensate. This is a clean real-analysis / additive-combinatorics statement
about the autocorrelation of B₃+B₄ against the sparse set B₇ — NO linear forms in logs. THE next
invention/proof target.

## ROUND VERDICT (final)
C5 second-moment covering SURVIVES self-kill and the MW-circularity test. It reduces (BRIDGE) to:
(a) an effective variance bound Var[Φ]≤C·E[Φ] with C absolute [mechanism = autocorrelation × sparsity,
both elementary; strongly supported, var/mean bounded incl. at coincidences], plus (b) a finite check
[X₀, n*(C)]. If (a) is made rigorous, this is a transcendence-free proof of (BRIDGE) — the campaign's
sought escape from MW. Open piece (a) is computable, breaker-testable, and named precisely above.
Handed to breaker (deep-scale + β≈0.95 stress) and recorded for the team.

## C6 SUMMABILITY STRESS-TEST — honest refinement (the delicate point)

Tested whether the per-row covariance sum stays bounded as M=#shifts grows (the rigorous open piece):
| n≤ | M | ∑|Cov| (absolute) | ∑Cov (signed) | ∑|Cov|/M |
|----|---|-------------------|---------------|----------|
| 10⁴ | 16 | 0.48 | +0.48 | 0.030 |
| 10⁵ | 32 | 0.65 | +0.28 | 0.020 |
| 10⁶ | 128 | 5.14 | −4.21 | 0.040 |

**REFINED (honest) FINDING:** ∑|Cov| (ABSOLUTE) is NOT clearly bounded — it grows ~10× as M grows 8×,
and ∑|Cov|/M ≈ const (0.02–0.04) suggests ∑|Cov| ∝ M (absolute summability may FAIL). What keeps
Var = O(E) is CANCELLATION: the SIGNED sum stays small/negative (+0.48, +0.28, −4.21). So the method
relies on signed cancellation in ∑Cov, NOT absolute summability.

**DEATH-POINT REFINEMENT:** "C is elementary via absolute autocorrelation summability" is TOO STRONG —
∑|Cov| isn't bounded. The real mechanism is signed cancellation (anti-correlation of base-7 shifts),
which is MORE DELICATE and could re-introduce dependence on the lag structure (power positions). So
the clean MW-escape claim is DOWNGRADED: the variance is O(E) empirically via cancellation, but
proving that cancellation rigorously is NOT obviously elementary — it may hide the same power-spacing.

**WHERE THIS LEAVES C5 (honest):** still the best bridge tool found — it transforms (BRIDGE) into an
effective second-moment statement, and Var/E=O(1) is robust empirically (incl. β-boundary, coincidences).
But the proof of Var=O(E) needs CANCELLATION (signed), not absolute summability, so the "transcendence-
free" claim is NOT established — it's plausible but the cancellation could be where MW hides. Net: a
strong reduction with the open piece SHARPENED to "prove the signed covariance sum ∑_{c,c'}(R_P(c−c')−ρ²)
= O(M)" — whether that's elementary or hides power-spacing is the genuine open question. Sent to breaker.

## JOINT VERDICT with breaker (reconciliation, settled)

breaker killed C5 (breaker_KILL_C5.md). Reconciled where the Φ=0 stragglers live (team-lead's a-vs-b):

**WHERE: all stragglers are AT/BELOW N₀ of the BOUNDARY family (3,4,7) ∑=1.** breaker's Φ=0 points:
(3,4,7) k=2 → 785743, 3964625, 3982888 (and 3,982,888 IS that family's N₀); k=3 → 166,025,260 (IS
the k=3 N₀). So these are GENUINE non-representable points — the conjecture's excluded "small n" —
NOT admissible-above-threshold points.

**⟹ TEAM-LEAD CASE (a): SOUNDNESS PASS, not a false certification.** C5 fails exactly where the
conclusion (n covered) is FALSE. Verified (breaker's shot 2 + mine): where n IS representable,
min Φ > 0 always (grows 4→17→103→...). C5 never flags a covered n as missing. Its refusal to certify
the true misses is correct behavior — the property every prior candidate lacked.

**BUT C5 is still DEAD as a PROOF METHOD (both reasons valid):**
- breaker shot 3 (decisive): Φ=0 at N₀ stragglers while E[Φ]≈14–22 = a LARGE-DEVIATION event.
  Chebyshev P(Φ=0)≤Var/E² cannot reach 0 when Φ=0 co-occurs with E≈20. The exceptional points ARE
  the rare events the second moment is blind to. To prove cofiniteness you'd need to bound the
  large-deviation RATE at exactly the cross-base coincidences — that IS the MW wall, in probabilistic
  dress.
- breaker shot 1 (valid, reconciled): Var=O(E) FAILS over WIDE windows. My "bounded var/mean ~0.3–0.6"
  used fixed 20K windows; breaker's 25%-width windows (spanning 7-power transitions) give var/mean
  climbing 0.9→8.4 (correlated jumps as each new 7-power enters inflate the global variance). Over the
  windows that matter for a uniform bound, (ii) is false. My local measurement was too narrow.

## FINAL HONEST STATUS of C5
- As a SOUNDNESS FILTER: PASSES (never certifies a true miss; refuses exactly the below-N₀ trap points).
- As a PROOF of (BRIDGE): DEAD. The exceptional points are large-deviation events at cross-base power
  coincidences; the second moment cannot exclude them. C5 hits the MW wall in probabilistic dress.
- The reduction's value: it shows (BRIDGE)'s open content is precisely a LARGE-DEVIATION bound on
  P(Φ(n)=0) at cross-base coincidences — sharper than "windowed residue coverage," and it confirms
  the obstruction is the same MW kernel. The signed-cancellation question is moot (breaker: even
  summable covariance can't bound the large-deviation rate).

NET: C5 is a sound filter and a precise re-localization of the open core, NOT a proof. Honest kill,
joint with breaker.
