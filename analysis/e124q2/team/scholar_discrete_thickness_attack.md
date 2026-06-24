# Discrete-thickness transfer: the attack, the death point, and a surprising reversal

**Author:** scholar (4th attacker). **Builds on:** scholar_thickness_proofs.md. **Method:** port
Astels/Newhouse gap-induction to ℤ; find exactly where it breaks. All claims [COMP] (exact integer
computation) or [PROOF] (mechanism) unless tagged [SEC]. **Bottom line: the naive port SUCCEEDS in
the strictly-supercritical case and BREAKS exactly at the harmonic boundary ∑=1 — but in a
direction that HELPS us, because the discrete problem turns out EASIER than the continuum there.**

---

## 1. Discrete thickness matches the real one EXACTLY [COMP]

`B_d(L) = B_d(L−1) ∪ (d^{L−1} + B_d(L−1))`. Lower block `[0, (d^{L−1}−1)/(d−1)]`, upper block starts
at `d^{L−1}`. The first integer gap has width `g = d^{L−1} − (d^{L−1}−1)/(d−1) − 1`, the adjacent
bridge (lower block) has width `b = (d^{L−1}−1)/(d−1)`. Computed:

> **discrete bridge/gap width ratio = 1/(d−2)** — IDENTICAL to the real `τ(K_d)=1/(d−2)`. [COMP, d=3,4,5,7]

So the discrete thickness equals the continuous thickness; scaling by `d^k` (the level-k problem)
multiplies all gaps and bridges by `d^k`, leaving the RATIO invariant — hence the YES/NO answer is
k-invariant and only the SCALE (the floor `d^k`) carries k. This is the clean structural reason
behind troika's `N₀ ≍ d_max^k`.

## 2. The naive port: SUCCEEDS strictly-supercritical, FAILS at the boundary [COMP]

I ran the continuum sumset `K_{d_1}+…+K_{d_r}` at increasing resolution (depth L), tracking
max-gap / lattice-resolution in the interior:

| D | ∑1/(d−1) | continuum maxgap/res as depth→ | continuum verdict |
|---|---|---|---|
| (3,4,5) | 1.083 (>1) | 1.09→1.28→0.97→0.89 (shrinks to ~res) | **interval** ✓ |
| (3,4,7) | 1.000 (=1) | 7.7→11.7→17.4→16.3→30.7 (GROWS) | **NOT an interval** ✗ |
| (3,4) | 0.833 (<1) | ~20 (grows) | not an interval ✓(expected) |

So Astels' theorem, applied to the real `K_d`, gives an interval under the STRICT inequality
`∑1/(d−1) > 1`, and FAILS at exact equality `∑1/(d−1)=1`. (Astels' "≥" sharp-case must be the
strict version for the interval conclusion; equality yields a measure-full Cantor-like set with
gaps that shrink but never reach resolution.) **This is the death point of the naive port: the
continuous machinery does NOT cover the boundary triples (3,4,7), (3,5,7,13), (3,6,7,13,21) —
precisely the cases BEGL had to do by Mignotte–Waldschmidt.**

## 3. ★ THE SURPRISING REVERSAL: discrete is EASIER than continuum at the boundary [COMP]

Here is the key discovery of the attack. At the SAME boundary `∑=1`:
- **Continuum** `K_3+K_4+K_7` is NOT an interval (gaps grow with depth, §2).
- **Integer** `B_3 + 4·B_4-style` (≡ `Pow({3,4,7};1)`) IS cofinite — gap-free above 581 [COMP, verified].

> **The integer lattice floor supplies the slack the continuum lacks at ∑=1.** In the continuum
> there is no smallest scale, so at the exact thickness threshold the gap-filling induction runs
> forever and the residual gaps, though →0, never close to an interval. On ℤ the induction
> TERMINATES at the lattice floor (spacing 1 at k=0, `d^k` at level k): once gaps shrink below the
> floor there are no more gaps to fill, so a genuine interval (cofinite tail) appears. **Discreteness
> = a built-in strict-excess.**

This REVERSES the usual intuition (discrete problems harder than continuous) and explains the whole
landscape:
- It explains WHY BEGL needed Mignotte–Waldschmidt at the boundary: the thickness/Astels route
  genuinely fails at `∑=1` in the continuum, so the proof must instead use the ARITHMETIC spacing
  of the atoms — `|3^p − 4^q|` bounded below (MW) is exactly "the integer gaps near the floor don't
  conspire to stay open." The transcendence input is the discrete substitute for the missing
  continuum slack.
- It explains why strictly-supercritical D (`∑>1`, e.g. (3,4,5)) are EASY both ways (continuum
  already gives an interval, no transcendence needed) and have tiny thresholds.

## 4. The precise reduction the port yields (the proof skeleton for Q2)

Combining everything, Q2 reduces to:

> **(Port-Thm, strictly-supercritical).** If `∑1/(d−1) > 1` (strict) and gcd(D)=1, then `R(D,k)` is
> cofinite. PLAUSIBLE via a discrete Astels gap-induction: above the floor `d_max^k`, the bridge≥gap
> property holds (discrete thickness `>` threshold ⇒ strict bridge excess ⇒ every gap covered down
> to the floor), then residue coverage (team-proven R-half) handles classes, giving cofiniteness.
> [This is the achievable half — recommend cassels/maverick target the STRICT case first.]
>
> **(Boundary, ∑=1).** The hard core. Continuum thickness FAILS; needs the arithmetic atom-spacing.
> This is exactly the (3,4,7)-type case and exactly where Mignotte–Waldschmidt enters. The general
> boundary case is the genuine open problem; per my prior-art guardrail the MW route can't do it
> uniformly (height-growing constants), so it needs either a uniform lower bound on multi-base atom
> spacings or a new idea. [This is the irreducible (A)-core.]

So the team should SPLIT the proof: (i) prove the STRICT case by discrete-thickness (a clean,
likely-formalizable theorem — a genuine new result), (ii) isolate the boundary `∑=1` case as the
residual hard core (where (3,4,7) lives), and note BEGL only did (3,4,7) there by MW.

## 4a. CORRECTION (maverick immune-check): the dichotomy is 3-WAY, not strict-vs-boundary [COMP]

My §2 binary claim "strict ∑>1 ⟹ continuum interval; fails only at boundary ∑=1" is WRONG.
maverick found `{3,4,6}` (∑=1.033, STRICT excess) whose continuum gaps GROW (maxgap/res ≈3.6 at
depth 7, like the boundary), with integer n₀(1)=986 EXCEEDING the boundary (3,4,7)'s 581. Verified:
(3,4,5) coprime → ~1.0 (interval); (3,4,6) → ~3.6 (grows); (3,4,7) → ~17 (grows).

ROOT CAUSE (verified): `6 = 2·3` shares a prime with BOTH 3 and 4 (=2²), so pairs (3,6),(4,6) are
multiplicatively dependent and cluster via small |2^a−3^b| spacings. Pairwise-coprime D have no
such clustering. **Discriminator is NOT strict-vs-boundary but: margin δ = ∑1/(d−1)−1 VS the worst
cross-base multiplicative clustering (|p^a−q^b| for prime-sharing/close pairs).** The lattice floor
supplies a FIXED slack; whether it closes the gap depends on δ beating the clustering.

Correct 3-WAY picture:
1. EASY — δ>0 and pairwise mult-independent enough that δ dominates clustering ((3,4,5)): interval, no MW.
2. MW-HARD-BOUNDARY — δ=0 ((3,4,7),(3,5,7,13)): clustering at the margin; needs MW.
3. MW-HARD-STRICT-WITH-CLUSTERING — δ>0 but tiny and a strongly-clustered pair dominates ((3,4,6),
   δ=0.033, the (2,3) clustering wins): behaves like the boundary; needs MW.

This DOVETAILS with my prime-power-collinearity work: (3,4,6) is mildly-collinear (6 shares primes
with 3,4), near the Melfi direction though admissible. The harmonic condition prevents FULL
collinearity but small-δ partial collinearity can still be MW-hard. The §3 "discreteness supplies
slack" insight SURVIVES (slack is real, fixed-size); what was wrong was attributing the outcome to
strict-vs-boundary rather than margin-vs-clustering. Credit: maverick_ASSAULT_thickness.md v8.

IMPLICATION for the winnable tier: the clean provable sub-case is NOT "all strict ∑>1" but
"δ large enough relative to clustering."

**FURTHER CORRECTION (sumset immune-check): the clustering is LOGARITHMIC and gcd-INDEPENDENT, NOT
about pairwise coprimality.** My "pairwise-coprime D with δ bounded below" was ALSO wrong: (3,4,7)
IS pairwise-coprime (every pair gcd 1) yet is the MW-hard boundary case, because 3^5=243 ≈ 4^4=256
(log4/log3 ≈ 5/4) — a near power-coincidence independent of gcd. [COMP verified: worst relative
|a^p−b^q| over pairs — (3,4,7)→0.026, (3,4,6)→0.054, (3,4,5)→0.049, (3,4,5,7,11,13)→0.0046 BUT
δ=0.43 dominates ⟹ easy.] The correct discriminator is

> **δ = ∑1/(d−1) − 1  VS  the worst LOG-CLUSTERING** = max over base pairs of how nearly their
> powers coincide (small |p·log d_i − q·log d_j|, i.e. small relative |d_i^p − d_j^q|) = exactly
> the Mignotte–Waldschmidt spacing. gcd-INDEPENDENT.

So the winnable hypothesis is "δ exceeds the worst-pair log-clustering," NOT "pairwise coprime + δ>0".
Note (3,4,5,7,11,13) has the TIGHTEST cluster of all tested (3^7=2187 vs 13^3=2197) yet is easy
because δ=0.43 swamps it — confirming it is the COMPARISON δ-vs-clustering that decides, not either
alone. Credit: sumset (sumset_strict_excess_theorem.md). sumset's stronger conclusion: single-block
Cassels is vacuous even for strict excess, and the internal gaps ARE the same MW core — consistent
with my §4b (no elementary route via bare atoms; completeness is multi-base interleaving).

## 4b. HONEST CALIBRATION — what the port actually proves vs what's heuristic [COMP]

After pushing the discrete argument I must flag precisely what is rigorous, to avoid over-claiming:

- **The bare-atom Cassels/Birch single-pass induction is INAPPLICABLE at any k≥1** [COMP, confirms
  maverick]. The smallest atom at k=1 is `d_min^1 = 3 > 1`, so the running-sum condition
  `t_{n+1} ≤ T_n+1` fails at the very first step for EVERY admissible D (strict or boundary). The
  contiguous prefix never starts. So completeness does NOT come from a running-sum filling of the
  atoms — it comes entirely from the multi-base SUBSET-SUM interleaving. (β_total < 2 always, as
  maverick proved — the atom-level density never suffices.)
- **The actual reachable SUMSET has only finitely many TINY gaps (width 1–2), each preceded by a
  bridge ≥ half the gap, then becomes contiguous** [COMP, (3,4,5) and (3,4,7) both]. This is the
  "bounded gaps + finite exceptional set" picture (= the team's Lemma BG), NOT a clean
  thickness-induction down from the top.
- **Therefore the discrete-thickness/Astels connection is the right HEURISTIC and explains the
  threshold and the continuum shadow, but it is NOT by itself a proof of the strict case.** The
  rigorous content is: (i) the threshold `∑1/(d−1)` is exactly the Astels thickness invariant
  [PROVEN, the K_d computation], (ii) the continuum sumset is an interval for `∑>1` [Astels, SEC],
  (iii) the integer problem at `∑>1` is at least as easy (discreteness adds slack) [HEURISTIC +
  strong COMP evidence], but a fully rigorous discrete strict-case theorem still requires either a
  genuine discrete Astels gap-induction on the SUMSET (not atoms) or the team's bounded-gap route.

Net: the port reframes and explains, and gives a winnable TARGET (strict case), but the honest
status of the strict case is "very likely true, reduces to a discrete-sumset gap-induction or
Lemma BG", NOT "proved". I flag this so cassels/maverick build the rigorous bridge rather than
assume the heuristic closes it.

## 5. Death points enumerated (for the record)

1. Newhouse pairwise `τ₁τ₂≥1`: DEAD for distinct admissible d (only (3,3) qualifies; `τ=1/(d−2)`).
   Must use Astels finite-sum form.
2. Astels at equality `∑=1`: DEAD in the continuum (no interval). Strict `>1` works.
3. Discrete port above the floor, strict case: PLAUSIBLY ALIVE (lattice floor = strict excess).
4. Discrete boundary `∑=1`: the real open core; discreteness helps but a uniform argument is still
   missing; (3,4,7) done by MW, general case open.

> NET FOR THE TEAM: the thickness program delivers a likely-provable theorem for `∑1/(d−1) > 1`
> (strict) — that is a publishable advance the team can actually close — and cleanly isolates the
> `∑=1` boundary as the irreducible hard core. The strict case is the place to spend effort.
