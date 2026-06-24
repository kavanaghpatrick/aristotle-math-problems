# breaker: KILL of maverick's C5 (second-moment/Chebyshev bridge method)

C5 claim: Φ(n)=#{c∈B_{d_r},c≤n : n−c∈P}; (i) E[Φ]→∞ AND (ii) Var[Φ]=O(E[Φ]) ⟹ Chebyshev ⟹ Φ>0
⟹ (BRIDGE). Engine: breaker_kill_C5*.py (validated atom-sieve).

## KILL SHOT 3 (DECISIVE — C5 is UNSOUND): Φ=0 at deep stragglers while local E[Φ]≫1
At GENUINE non-representable n (true misses, triple-verified), Φ(n)=0 while local E[Φ] is large:
  (3,4,7) k=2: Φ(3964625)=0, Φ(3982888)=0, Φ(785743)=0 — local E[Φ] ≈ 14, 14, 11.5
  (3,4,7) k=3: Φ(166025260)=0 — local E[Φ] ≈ 22
These are verified LARGE-DEVIATION events: the expected number of covering 7-shifts is 14–22, but the
ACTUAL number is 0 (every 7-power shift dodges P — the 581-dodge mechanism at scale). A Chebyshev bound
P(Φ=0) ≤ Var/E[Φ]² CANNOT reach 0 when Φ=0 co-occurs with E[Φ]≈20. So C5 would PREDICT these stragglers
are covered; they are NOT. C5 is unsound — it cannot prove cofiniteness because the exceptional points
ARE precisely the rare events the second moment is blind to. (This is the MW wall in probabilistic dress:
the dodges happen at cross-base power coincidences, exactly where Φ concentrates to 0 vs its mean.)

## KILL SHOT 1 (assumption (ii) is FALSE at scale): Var ≠ O(E[Φ])
maverick measured var/mean=0.3–3.4 at SMALL scales (~10⁴). At larger scales it CLIMBS (local, 25%-width
windows, (3,4,7) k=1): center 30K→1.1, 300K→1.6, 1M→4.9, 10M→7.1, 25M→6.2 — trend upward (noisy because
it SPIKES just after each new 7-power enters: correlated jumps). Var grows super-linearly in E[Φ] ⟹
assumption (ii) Var=O(E[Φ]) is empirically false ⟹ even the Chebyshev STEP doesn't go through.

## KILL SHOT 2 result (the one place C5 is NOT wrong): minΦ stays ≥1 in covered regions
Where n is representable, minΦ>0 (grows: 4→17→103 for (3,4,7)). So C5 doesn't FALSELY flag covered n.
The failure is purely the converse: it can't EXCLUDE the true misses (shot 3).

## C6 (covariance decay) — moot
C6 (∑|Cov(c,c')|=O(ρ), summable) is the wrong target: even with summable covariance, shot 3 shows the
exceptional set is a large-deviation/concentration phenomenon, not a second-moment one. Bounding the
variance does not bound P(Φ=0) below the large-deviation rate, which is exactly where the misses live.

## VERDICT: C5 dies at the same MW wall, now as a large-deviation event (Φ=0 vs E[Φ]≈20). The deep
stragglers I found (the FALSE-branch artillery) are the explicit witnesses that kill the variance method.
