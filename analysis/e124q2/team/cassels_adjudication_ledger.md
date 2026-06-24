# Adjudication ledger: per-fixed-k strict-excess theorem — [PROVEN] vs [VERIFIED] for every step

**Author:** cassels. For maverick's adjudication (lead's order). Brutally honest status of each link.
Resolves the tension "sumset's four-route negative vs cassels' positive": they are about DIFFERENT
claims (uniform-in-k vs per-fixed-k) — see §3.

Citation note: the interval-filling lemma is **Brown 1961** (Amer. Math. Monthly 68, 557–560) +
**Erdős 1962** (Acta Arith. 7), NOT "Cassels 1960" (phantom). I keep the descriptive name below.

## The theorem (per-fixed-k, strict excess)
For finite D, all d≥3, gcd(D)=1, σ := ∑_{d∈D}1/(d−1) − 1 > 0, and EACH FIXED k≥1:
R(D,k) = ∑_{d∈D} d^k·B_d is cofinite. (NOT claimed uniform in k.)

## §1. Step-by-step ledger

| # | Step | Status | Honest detail |
|---|---|---|---|
| 1 | Scaling S(d,k)=d^k·B_d | **[PROVEN]** | Reindex j↦j−k. Trivial, Lean-ready. |
| 2 | R(D,k) = subset-sums of merged atoms A={d^j:d∈D,j≥k} (distinct-value case) | **[PROVEN]** for D with pairwise-distinct atom values; **[VERIFIED]** (0 diff to 3e5) that the tested D have distinct values | General cross-base collision case not handled; for the families in question (distinct prime-ish bases) no collisions. |
| 3 | **Lemma A**: S(X) ≥ m·β − C', m=next atom, β=∑1/(d−1), C'=∑d^k/(d−1) | **[PROVEN]** | Exact: S(X)=∑_d(d·x_d−d^k)/(d−1), each d·x_d≥m, sum. Rational-arithmetic VERIFIED 0/20000 to 1e12 as a cross-check. |
| 4 | Gap-condition onset: a_{n+1}≤S_n+1 for all atoms ≥ m₀=(C'−1)/σ | **[PROVEN]** | Direct from Lemma A + σ>0. Closed form. |
| 5 | Residue coverage: gcd(D)=1 ⟹ R(D,k) hits every residue mod every M | **[PROVEN]** (modular's per-prime+CRT) | Not mine; modular_local_coverage.md. Solid. |
| 6 | **Lemma B**: gap-condition + margin-growth ⟹ value-holes close (cofinite) | **[VERIFIED, NOT PROVEN]** | THE CRUX. lift's mechanism: min #reps r(n)→∞ at strict σ. I verified r(n) GROWS ((3,4,5) k=1: 5→179; (3,4,5,7): 62→4652) but have NO proven lower bound r(n) ≥ f(n,σ,k). Without it, "holes close" is empirical. |
| 7 | k=1 threshold bound N₀ ≤ C·m₀, C absolute | **[VERIFIED, NOT PROVEN]** | N₀/m₀ ≤ 10.84 across all 44 admissible strict D⊆{3..12}, ≤1.5 for larger bases. Empirical; no proof C is uniform. |
| 8 | Assembly: 4+5+6 ⟹ cofinite per fixed k | **[CONDITIONAL on 6]** | The logic is sound GIVEN Lemma B; but Lemma B (step 6) is the unproven link. |

## §2. THE HONEST BOTTOM LINE
- **Fully PROVEN (transcendence-free):** the gap-CONDITION holds from m₀=(C'−1)/σ (Lemma A, steps 3–4),
  exact and closed-form. This genuinely extends past Brown/Erdős (k=0 only) — **this is the real,
  defensible fragment.**
- **NOT proven, only VERIFIED:** that the gap-condition + residue coverage actually CLOSE into
  cofiniteness (Lemma B, step 6). lift's margin-growth is the proposed mechanism but lacks a rigorous
  r(n) ≥ f(n,σ,k) lower bound. So the per-fixed-k theorem is **CONDITIONAL on Lemma B**, which is
  currently empirical.
- Therefore the honest verdict for adjudication is: **"per-fixed-k strict-excess cofiniteness is
  PROVEN-modulo-Lemma-B; Lemma A (the onset) is unconditionally proven and is the new content;
  Lemma B is verified-not-proven (the real gap)."** NOT a clean unconditional theorem yet.

## §3. RESOLVING THE TENSION (sumset's four-route negative vs my positive)
They are NOT contradictory — different quantifier scope:
- **sumset's negatives are about UNIFORM-in-k** (a single argument for all k, or a k-uniform bound).
  Those genuinely FAIL — I independently confirmed: N₀/m₀ diverges with k (2–14 at k=1 → 428–503 at
  k=2), carry's (d_max·d_2)^k/σ² fails k-uniformity at k=3 (0.027→1.35→3.76 for (3,4,5)). So NO clean
  k-uniform elementary theorem. sumset is RIGHT about uniform-in-k.
- **My positive is PER FIXED k** (for each k separately, conditional on Lemma B). The margin grows
  for each fixed k, just at a k-degrading rate. So "cofinite for each fixed k" is compatible with
  "no uniform-in-k bound." NO actual contradiction — we were claiming different things.
- **The honest synthesis:** per-fixed-k is the right scope; even that rests on Lemma B (verified, not
  proven); uniform-in-k provably needs the cross-base spacing (MW). So the only UNCONDITIONALLY proven
  new thing is Lemma A (the gap-condition onset). Everything beyond it is conditional or empirical.

## §4. The {3,4,6} hypothesis question (lead asked explicitly)
{3,4,6}: gcd(D)=1 (admissible), but gcd(d_max,d_2nd)=gcd(6,4)=2. **It IS inside my hypotheses** —
Lemma A requires only σ>0 (here 0.033), and residue coverage requires only gcd(D)=1 (satisfied).
NEITHER requires gcd(d_max,d_2nd)=1. Verified: {3,4,6} k=1 has m₀=91, N₀=986, margin grows
(min#reps=20 at 50k), window fully represented. So {3,4,6} does NOT need density's gcd(d_max,d_2nd)=1
extra hypothesis; my chain covers it via gcd(D)=1 + σ>0. (If density's writeup ADDS gcd(d_max,d_2nd)=1
as a hypothesis, that would EXCLUDE {3,4,6} unnecessarily — flag for reconciliation: my chain is
strictly more general here, OR density's bound needs it for a step mine doesn't. Worth checking which.)

## §5. What I will and will NOT sign
- WILL sign: Lemma A (gap-condition onset m₀=(C'−1)/σ, σ>0), unconditional, transcendence-free, new past Brown/Erdős.
- WILL sign: the per-fixed-k theorem as **CONDITIONAL on Lemma B** (explicitly flagged).
- Will NOT sign: any UNCONDITIONAL per-fixed-k claim until Lemma B has a proven margin lower bound.
- Will NOT sign: any k-UNIFORM claim (sumset's negative stands; needs MW).
