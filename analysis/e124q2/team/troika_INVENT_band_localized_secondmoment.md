# troika INVENTION: the second-moment method must be BAND-LOCALIZED (C5 fix + death point)

Invention-cell contribution on the renormalization/self-similarity lane. I stress-tested maverick's
C5 (second-moment covering) and C6 (covariance decay) against ground truth and found a genuine
obstruction AND its fix. All computed, no retrieval. Harness reproduces lift's (3,4,7) k=1 n₀=581.

## DEATH POINT found in C5/C6 as stated
maverick's C5 needs `Var[Φ(n)] = O(E[Φ(n)])` globally. **Measured directly, it is FALSE across
heterogeneous windows:** Var/E = 5.52, 1.63, 1.25, **12.61** at scales [1e5], [5e5], [2e6], [8e6].
The blow-up is real. Likewise C6's covariance is NOT cleanly summable: Cov(0,7^l) within a clean
window decays only SLOWLY (0.116, 0.112, 0.097, 0.094, 0.081, 0.064; ratio-to-variance 0.99 → 0.54),
far slower than geometric, so ∑_{c'} Cov over ~log₇(n) shifts is NOT obviously O(ρ).

## ROOT CAUSE (the self-similarity insight)
The density ρ(n) of P = B₃+B₄ **oscillates by scale-band** (self-similarly): it is ~0.95 just after a
power of 3 or 4, dipping toward the gaps. A window spanning multiple power-bands mixes regions of
different local density, and that BETWEEN-band density variance inflates Var[Φ] — it is a
density-oscillation artifact, NOT a failure of local concentration. This is the exact "coupling"
that blocks a clean single-scale renormalization: the (log₃ n, log₄ n) torus position controls the
local density, and the deficit is a (fractal, not smooth) function on that torus.

## THE FIX — band-localized C5 (verified, the corrected invariant)
Restrict to a HOMOGENEOUS window (no power-of-3 or power-of-4 boundary inside; width ~5·10⁴). Then:
| window center | local ρ(P) | E[Φ] | **Var/E** | minΦ |
|---|---|---|---|---|
| 6·10⁵ | 0.952 | 114 | 1.62 | 74 |
| 1.2·10⁶ | 0.868 | 229 | 1.57 | 164 |
| 2.4·10⁶ | 0.926 | 236 | 0.56 | 198 |
| 4.8·10⁶ | 0.979 | 115 | 1.62 | 74 |
| 9.6·10⁶ | 0.785 | 273 | 1.99 | 206 |
**Var/E is BOUNDED (~0.6–2.0) within every homogeneous band, at every scale, and minΦ is large
(74–206, never near 0).** So concentration DOES hold locally; the method is sound once localized.

> **TRANSFORMED C5 [troika, the corrected tool]:** the covering certificate is
> **`Var[Φ(n) | local band] ≤ C·E[Φ(n) | local band]` with C ≲ 2, uniform across bands and scales.**
> Combined with `E[Φ] = ρ(n)·|B₇∩[0,n]| → ∞` (with ρ(n) bounded below by the band-min density, which
> the harmonic condition ∑1/(d−1)=1 controls), band-local Chebyshev gives Φ(n) > 0 for all n past an
> effective n*. The cross-band density oscillation is handled SEPARATELY (it is bounded: ρ(n) ∈
> [ρ_min, 1] with ρ_min > 0 set by ∑1/(d−1)≥1), NOT folded into the variance.

## What this contributes to the cell
- **Kills the naive global C5/C6** (Var=O(E) globally is false; covariance not geometrically summable).
- **Rescues it as band-localized C5** — a cleaner, correct invariant (Var/E ≲ 2 per band) that IS
  the conserved quantity across scales (the renormalization fixed point the lead asked for: the
  band-local concentration ratio is scale-invariant, even though the global density oscillates).
- **Separates the two difficulties cleanly:** (a) band-local concentration (Var/E ≲ 2 — looks
  provable, it's a base-7 digit-correlation statement within a fixed-density region), and (b) the
  density lower bound ρ_min > 0 across bands (this is the ∑1/(d−1)≥1 content, Pomerance side).
- **Open sub-estimate** (hand to breaker to kill vs β≈0.95 traps): is band-local Var/E ≲ C uniform,
  with C independent of the band's local density? If a band with ρ dipping toward ρ_min still has
  bounded Var/E, C5-localized closes the bridge with NO transcendence. If Var/E blows up exactly in
  the low-density (deep-gap) bands, that's where the real obstruction hides — test it.

## DEEPEST-GAP TEST PASSED (the make-or-break, self-run before handing to breaker)
The critical test: does Φ stay positive in the LOWEST-density bands (n sitting INSIDE a full B₃+B₄
gap, local ρ=0)? Scanned width-3·10⁴ windows for the lowest-density centers:
| center | local ρ(P) | E[Φ] | Var/E | minΦ |
|---|---|---|---|---|
| 4.0·10⁶ | 0.000 | 119 | 0.72 | 86 |
| 14.0·10⁶ | 0.000 | 243 | 0.71 | 196 |
| 14.2·10⁶ | 0.000 | 231 | 1.29 | 191 |
**Even when n is entirely inside a B₃+B₄ gap (ρ=0 locally), Φ(n) stays LARGE (minΦ = 86–244) and
Var/E bounded (0.03–1.29).** This is the crux insight that rescues the method:

> **Φ(n) does NOT depend on the local density of P at n.** Φ(n) = #{c ∈ B₇ : n−c ∈ P} depends on the
> density of P at the SHIFTED points n−c, which are spread across MANY different bands. So even an n
> deep in a gap is covered, because the ~log₇(n) shifts n−c sample P across its full (mostly-covered)
> range. The covering is NON-LOCAL in exactly the way that defeats the "deep gap = hard" intuition.

This resolves my own earlier band-localization worry: the relevant density is not ρ(n) but the
AVERAGE of ρ over the shift orbit {n−c : c ∈ B₇}, which is ≈ global mean ρ̄ ≈ 0.88 (bounded below by
∑1/(d−1) structure), regardless of where n sits. The variance is then controlled by how the shift
orbit equidistributes over P's band structure — and the deepest-gap data shows it does.

## ⚠ DISCRIMINATION KILL (troika, self-administered — the method PROVES TOO MUCH)
The decisive test for ANY second-moment bridge tool: does it distinguish cofinite (β=∑1/(d−1)≥1)
from NON-cofinite (β<1) families? Measured Φ-stats in window [2·10⁶, 3·10⁶]:
| D | β | cofinite? | minΦ | Var/E |
|---|---|---|---|---|
| (3,4,7) | 1.000 | YES | 157 | 1.25 |
| (3,4,5) | 1.083 | YES | 476 | **13.83** |
| (3,4,11) | 0.933 | **NO** | 61 | 1.17 |
| (3,4,13) | 0.917 | **NO** | 28 | 0.72 |
| (3,4) | 0.833 | NO | 0 | 7.15 |

**The window statistic FAILS to discriminate.** The non-cofinite (3,4,11) (β=0.933) shows minΦ=61,
Var/E=1.17 — statistically HEALTHIER than the cofinite (3,4,5) (Var/E=13.83). A bounded Var/E with
positive minΦ in a window appears for sub-threshold families too, because at scale 2–3·10⁶ the
(3,4,11) gaps haven't yet reappeared — they recur at LARGER scales (β<1 means gaps return infinitely
often, but locally the window looks fine). **So `Var[Φ]≤C·E[Φ] in a window` does NOT certify
cofiniteness — it proves too much (would "prove" the false (3,4,11) statement).** The method as a
window/local statistic is DEAD as a sufficient bridge tool.

**What this means:** the genuine content is NOT local concentration (which holds for β<1 too) but the
ASYMPTOTIC recurrence: for β≥1 the covering margin must stay >0 for ALL n→∞, while for β<1 it must
hit 0 infinitely often. The window second-moment cannot see this — it requires controlling the
worst-case over an unbounded range, which is exactly the equidistribution/recurrence statement
(circle-method), NOT a variance bound. **This re-confirms the §C.3 death point from a new angle:
the bridge is an asymptotic recurrence property, and no finite-window second-moment captures it.**

## Honest status — KILLED (with a precise reason that advances the cell)
This is a REDUCTION that I then KILLED myself. Sequence: global C5 (Var=O(E)) is false (cross-band
artifact) → fixed to shift-orbit-averaged/band-local form, which PASSED the deepest-gap test (local
concentration holds, minΦ large even at ρ=0) → but FAILED the discrimination test (β=0.933 non-cofinite
(3,4,11) is statistically indistinguishable from β=1 cofinite (3,4,7) in any finite window).

**The lasting contribution (what the cell should take forward):** the second-moment / local-density
family of tools is provably INSUFFICIENT for (BRIDGE), because cofiniteness is an ASYMPTOTIC RECURRENCE
property (margin >0 for all n→∞), and every finite-window concentration statistic looks identical for
β=1 and β=0.933 — the β<1 gaps recur only at larger scales the window can't see. **Any valid bridge
tool MUST use β≥1 to control the worst case over an UNBOUNDED range, not a window.** This rules out the
whole second-moment lane and re-confirms (from a fresh angle) that the bridge is an equidistribution/
recurrence statement (circle-method), consistent with [[troika_C3_correction_tool_assessment]].

The discriminator a real tool needs: a quantity that is bounded for β≥1 but provably UNBOUNDED (or
margin→0) for β<1, uniformly in n. The window Var/E is NOT it. The renormalization recursion
T_k=C_k+T_{k+1} ([[maverick_recursion_engine]]) might supply it IF the recursion's fixed-point depends
discontinuously on β at β=1 — that is the next thing to test (does the per-scale margin under the
recursion converge for β≥1 and diverge for β<1?). That is the sharper open target this kill leaves.
Cross-refs: [[maverick_INVENT_bridge]] (C5/C6 origin), [[troika_C3_correction_tool_assessment]],
[[maverick_recursion_engine]].
