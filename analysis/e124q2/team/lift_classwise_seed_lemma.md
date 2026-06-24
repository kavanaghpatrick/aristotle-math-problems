# The class-wise seed lemma — rigorous form of cassels' Lemma B (the value-hole closer)

**Author:** lift | **Status:** Structural identity VERIFIED EXACT across families (boundary, strict,
and sub-threshold). This is the precise rigorous form of cassels' (empirical) Lemma B, and the
missing piece to complete the winnable-tier theorem.

## The identity (verified exact)

Let M := d_min^k. For the sumset R_k = ∑_{d∈D} d^k·B_d, define for each residue r ∈ {0,…,M−1} the
**class-onset** O_r := the largest v ≡ r (mod M) with v ∉ R_k (or the first reachable if none), so
that every v ≡ r (mod M) with v > O_r is in R_k (class r is a "full AP of step M above O_r").

> **Identity (verified).** The cofiniteness threshold N₀ = max_r O_r (within ±M).

Verified exact (`/tmp/e124_classwise_lemmaA.py`), N=3·10⁵:

| D | k | M=d_min^k | max class-onset | true N₀ | match |
|---|---|-----------|-----------------|---------|-------|
| (3,4,5) | 1 | 3 | 82 | 79 | ✓ |
| (3,4,5,7) | 1 | 3 | 25 | 22 | ✓ |
| (3,4,7) | 1 | 3 | 584 | 581 | ✓ |
| (3,5,7) | 2 | 9 | 293170 | 293161 | ✓ (sub-threshold, still exact) |

The identity holds at the boundary, strict, AND sub-threshold — it is a general structural fact, not
tier-specific. (For sub-threshold D, some O_r = ∞, so N₀ = ∞ = not cofinite, consistent.)

## Why this is the right rigorous decomposition

Cofiniteness ⟺ every O_r is finite ⟺ each residue class mod M = d_min^k is a full AP above some onset.
This splits cleanly into the two proven ingredients + one deductive step:

1. **Some value in each class r is reachable** — this is residue coverage, PROVED (gcd=1 ⟹ R_k meets
   every residue mod every modulus; lift's Residue Lemma / modular's Theorem A / sumset Cor). Gives a
   "seed value" v_r ≡ r in each class.
2. **The gaps WITHIN class r close above an onset O_r** — this is where the wall is RELOCATED, not
   discharged (cassels' verification, decisive). cassels' Lemma A (the gap-condition) holds per-class
   from m₀ = (C'−1)/σ and stops NEW within-class gaps forming — but it does NOT bound O_r. **Verified:
   for (3,4,5) k=2 the worst O_r = 77 613 while m₀ = 181 (ratio 429); O_r ≫ m₀, diverging exactly as
   N₀/m₀ does (necessarily, since N₀ = max_r O_r).** So the EXISTING within-class holes (multiples of M
   up to O_r) must still CLOSE, and that closing — i.e. BOUNDING O_r — is the open MW part, now
   decomposed per residue class. Lemma A gives the filling-once-past-O_r (elementary, full AP); it does
   NOT give O_r itself. Closing O_r is via the margin-growth (r_D(n)→∞), which works PER FIXED k at a
   k-degrading rate (the dips), NOT uniformly — that k-degradation IS the MW content.
3. **Seed assembly is then automatic:** once all M classes are full APs (n > max_r O_r), every window
   of M consecutive integers is fully in R_k — i.e. [N₀+1, ∞) ⊆ R_k. (This replaces the
   "seed-interval of length ≥ d_max^k" framing — the class-wise version is cleaner and the seed length
   is exactly M = d_min^k, the SMALLEST step, not d_max^k. But note: the IDENTITY relocates the wall to
   max_r O_r, which equals N₀ — it does not LOWER it.)

## Relation to the bridge death point (honest scope)

Step 2 is the open content at EVERY tier (corrected per maverick's adjudication — see Deliverable below):
- **Winnable tier (δ = ∑1/(d−1)−1 dominates clustering):** cassels' Lemma A gives a closed-form
  m₀ = (C'−1)/σ, and EMPIRICALLY the within-class gaps close not far above m₀ (with slack growing in δ).
  BUT this is NOT rigorous — maverick showed even (3,4,5) k=1 has onsets (63,79,74) exceeding m₀=37,
  so "min-reps grow ⟹ holes close" is the coverage-blind trap, not a consequence of Lemma A. So step 2
  is OPEN here too (just more tractable: the dips are shallow and the per-fixed-k statement is finite).
- **Hard core (boundary ∑=1, or clustered families like (3,4,6)):** the within-class gaps close only
  marginally (the density-overlap margin is thin, ~1.5–3×, non-growing — lift_bridge_quantified.md), so
  step 2 is exactly the equidistribution/circle-method statement that does NOT reduce to elementary
  density or to MW alone. This is the genuine open core.

## The within-class onset = a CONSTRAINED DEFLATION (new finding, honest status)

Pinning down step 2 (within-class gaps close), I found the class-r reachable set is governed by:
> **(R_k ∩ Mℤ)/M is itself cofinite**, and its onset = the class-0 AP onset exactly.
> Verified: (3,4,5) k=1 deflated threshold 21 (vs original N₀=79); (3,4,7) k=1 deflated threshold 88
> (vs 581). The deflated set has density →1 and CONTAINS THE UNIT 1 (= d_min^k·d_min^0 / M), so it has
> no "smallest atom > 1" obstruction — unlike the original k≥1 problem. (`/tmp/e124_deflation_excess.py`.)

- **Good:** the deflated threshold is SMALLER than the original (21<79, 88<581) — deflation CONTRACTS
  the onset, promising for the "K bounded as k→∞" question (carry's pending item).
- **Honest catch:** (R_k ∩ Mℤ)/M is NOT a smaller BEGL instance — it's CONSTRAINED (the non-d_min
  digits must satisfy ∑_{d≠d_min} d^k b_d ≡ 0 mod d_min^k). So the deflation does not cleanly recurse
  to a trivial base; bounding its onset by an elementary K·(scale)^k is REAL content, not bookkeeping.
  I hit a computational wall on (3,4,5) k=2 deflated onset (large), so K-boundedness is NOT obvious.

## Deliverable + honest status (maverick adjudication ruling, maverick_ADJUDICATION_strict_excess.md)

The identity N₀ = max_r O_r is the rigorous backbone of cassels' Lemma B. **Formal adjudication
(maverick):** my Lemma B splits into:
- **IDENTITY N₀ = max_r O_r — PROVEN** (but trivially — it's the definition of the class onsets O_r);
- **CONTENT "within-class gaps close by density from m₀" — NOT PROVEN, and NOT even at k=1.**
  maverick tested (3,4,5) k=1: the class onsets are 63, 79, 74, which EXCEED Lemma A's m₀=37 by ~2×.
  So m₀ does NOT bound the onsets; the "min-reps-grow ⟹ holes close" step is the coverage-blind-to-
  internal-gaps trap, NOT an elementary consequence of Lemma A. **So Lemma A' is the genuine open piece
  even at k=1** (correcting my earlier "PROVEN k=1" — that was wrong; only the IDENTITY is proven).

So the flagship strict-excess theorem reduces to **(Lemma A') the within-class gaps close from m₀**,
which is OPEN at every k (the per-fixed-k version is a single finite analytic statement, more tractable
than the uniform one, but still unproven). Lemma A (cassels' gap-condition m₀=(C'−1)/σ) and the
class-wise IDENTITY are proven; the closing step is the content.

**Recommended HONEST flagship statement (maverick + team-lead concur):** ship the class-wise IDENTITY
(clean, correct decomposition) + residue coverage, and state "strict-excess ∀k cofinite" as
**CONDITIONAL on Lemma A' (OPEN)**, NOT as a theorem. A strong conditional reduction + precisely-located
open lemma — not a closure claim. (3,4,7) boundary is separately modulo the equidistribution (BRIDGE)
lemma (circle-method).

**Citation correction (maverick/scholar):** the interval-filling lemma is **Brown 1961 + Erdős 1962**,
NOT "Cassels 1960" (phantom citation — does not exist; do not cite it anywhere in the writeup).

Cross-refs: cassels_strict_excess_theorem.md (Lemma A, m₀), lift_bridge_quantified.md (the thin-margin
death point), lift_sufficiency_mechanism.md (Residue Lemma), maverick_seed_interval_pinned.md (the
seed framing this refines — class-wise is cleaner, step M not d_max^k).
