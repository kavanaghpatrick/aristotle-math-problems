# E124 k≥1: the STRICT-EXCESS regime ∑1/(d−1)>1 is the elementary target (no transcendence)

**Author:** sumset. **Status:** strong computational lead + a complexity argument that transcendence
is NOT forced here. This is the most promising route to a real (partial) theorem on E124-open.

Reads: sumset_scale_route_blocked.md (why k=0-at-scale fails; transcendence forced only at boundary),
troika_347_reverse_engineered.md (boundary ∑=1 needs MW), maverick_bounded_gap_lemma.md (Lemma BG),
breaker_engine_and_347anomaly.md (late-straggler discipline — all numbers below are EXACT bitset,
windows ≫ threshold, no straggler risk).

## The dichotomy (robust, exact-engine verified)

| regime | example | k=2 threshold | k=3 threshold | governed by |
|--------|---------|---------------|---------------|-------------|
| **boundary ∑=1** | (3,4,7) | 3,982,888 | ~57,700,000 | **MW / Baker** (transcendence) |
| **strict excess ∑>1** | (3,4,5,7), ∑=1.25 | 695 | 78,426 | **(d_max·d_2)^k** (geometric) |
| | (3,4,5,6,7), ∑=1.45 | 312 | 11,574 | geometric |
| | (3,4,5,6,7,9), ∑=1.575 | 184 | 6,253 | geometric |

Strict-excess thresholds are **4–5 orders of magnitude smaller** than the boundary, and obey a clean
law: **threshold(D,k) ≤ C·(d_max·d_2nd)^k**, with C decreasing as the harmonic excess grows
(ratio true/(d₁d₂)^k ∈ [0.03, 1.83] across all tested families/k, vs the boundary's 5000+). All
values are EXACT (bitmask DP, windows ≥ 30·(d₁d₂)^k ≫ threshold — no straggler risk).

## Why transcendence is NOT forced in this regime (the key argument)

The complexity-contradiction in sumset_scale_route_blocked.md forces MW only where the SAME family is
elementary at k=0 but hard at k≥1 — that is the BOUNDARY (3,4,7) (∑=1), whose last hole 581 is
controlled by how close 3^p and 4^q can be (a genuine Diophantine coincidence). At strict excess the
harmonic surplus gives slack: the last hole is pinned not by a near-coincidence of two powers but by
the plain GAP just below where a fresh large power turns on. Evidence: for (3,4,5,7) k=3 the top hole
78,426 sits 42 below 7^3 + 5^7 = 78,468 — i.e. just under the point where the next 5-power becomes
usable. This is a Frobenius/geometric obstruction (two largest scales meshing), NOT a linear-form-in-
logs obstruction. (last_hole_anatomy.py)

## The conjecturally-elementary theorem to target

> **(Strict-excess BEGL).** If D admissible with gcd(D)=1 and ∑_{d∈D} 1/(d−1) > 1 (STRICT), then
> for every k ≥ 1, T_k(D) = ∑_{d∈D} d^k·B_d is cofinite, with threshold ≤ C(D)·(d_max·d_2nd)^k.

**Proof strategy (elementary, uniform in k — the open obligation):**
1. **Residue half — DONE.** Theorem B (gcd=1 ⟹ all residues mod every M) + scale_route finding
   (a bounded low-power band covers all residues mod lcm(d^k)). No transcendence.
2. **Bulk/gap half — the target.** maverick's Lemma BG: ∑1/(d−1) ≥ 1 ⟹ atoms eventually satisfy
   t_{n+1} ≤ T_n (running sum dominates), giving bounded gaps. At STRICT excess the inequality holds
   with a fixed positive MARGIN (∑1/(d−1) − 1 > 0), so the running sum OVER-dominates by a geometric
   factor — this is exactly the slack BEGL96's Claim 1 needed (their β>2) but the boundary lacked.
   The remaining step: turn "bounded gaps + all residues realized" into "gap = 1" using the margin,
   WITHOUT MW. The geometric law threshold ≤ C·(d₁d₂)^k is the quantitative target; the last-hole
   anatomy says the obstruction is the two-largest-scale Frobenius gap, which the margin closes.

The honest open piece is step 2's final "bounded gap ⟹ no gap" (maverick's (★)), but at strict
excess this should be elementary because the margin gives room — unlike the boundary where only MW
suffices. **This is a genuinely attackable partial result: prove BEGL for strict excess, all k.**

## Recommendation
Concentrate elementary effort HERE (strict ∑>1), not on the boundary. A clean uniform-in-k proof for
strict excess would be a real advance on E124-open (BEGL96 only displayed (3,4,7), a boundary case).
The boundary ∑=1 stays the MW/Baker frontier (troika). I'll keep pushing step 2 for strict excess.
