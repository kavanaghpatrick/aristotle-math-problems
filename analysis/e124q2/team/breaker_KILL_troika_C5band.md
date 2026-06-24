# breaker: KILL of troika's band/orbit-averaged C5 (band-local second-moment bridge)

Candidate: (BRIDGE) ⟸ band-local Var[Φ] ≤ C·E[Φ] (orbit-averaged density ρ̄), then band Chebyshev
⟹ Φ>0 past n*. troika's discrimination criterion: C5-band must show Var/E BLOW UP for β<1 (predict
NON-cofinite) and stay bounded for β≥1. Engine: breaker_kill_troika_C5band.py (validated atom-sieve).

## KILL: C5-band CANNOT discriminate β=0.933 from β=1 (fails troika's own criterion). N=200M, d_r=last base.
| D | β | cofinite? | max band Var/E | global minΦ | #Φ=0 in [N/10,N] |
|---|---|---|---|---|---|
| (3,4,7)  | 1.000 | YES | 16.60 | 80 | 0 |
| (3,4,11) | 0.933 | NO  | **12.31** | **4**  | 0 |
| (3,4,10) | 0.944 | NO  | 7.56  | 32 | 0 |
| (3,5,7)  | 0.917 | NO  | 18.60 | 38 | 24 (reachable) |

DECISIVE: (3,4,11) and (3,4,10) are NOT cofinite (β<1, Pomerance) yet up to 200M they show BOUNDED
band Var/E (12.3, 7.6 — LOWER than/comparable to the cofinite (3,4,7)'s 16.6) and minΦ>0, with ZERO
misses. C5-band is statistically INDISTINGUISHABLE between the cofinite (3,4,7) and the non-cofinite
(3,4,11)/(3,4,10). So the criterion "Var/E bounded ⟹ cofinite" FALSELY certifies (3,4,11) as cofinite.

## Why (structural, unfixable for any local statistic up to N):
(3,4,11)'s deep stragglers (first miss >9×10⁹, my FALSE-branch result) sit FAR beyond any reachable N.
Up to 200M, (3,4,11)'s Φ is positive everywhere with cofinite-looking band statistics — the
discriminating information simply isn't present below the straggler scale. A band-local second-moment
computed up to N CANNOT see misses that first appear at >9e9. (3,5,7) is the exception that proves the
rule: its threshold is reachable, so C5-band DOES see its 24 misses — but for the deep-trap families
(exactly the hard cases near β=1) it is blind.

## VERDICT: C5-band is TOO WEAK — it cannot distinguish near-threshold sub-critical families from the
boundary. Same root as the C5 kill (large-deviation events at deep stragglers invisible to 2nd moment),
now sharpened: the orbit-averaging fixed the global var artifact but did NOT add discriminating power,
because the discriminator lives beyond reach. No local statistic up to finite N can separate β=0.933
from β=1 — that separation IS the Pomerance/MW content, which is asymptotic.
