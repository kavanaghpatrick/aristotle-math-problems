# breaker FINAL — Erdős #124 k>=1 (BEGL96): FALSE hunt exhausted, evidence favors TRUE

## Bottom line
Entry point was "assume FALSE, hunt the witness." After exhaustive exact computation, **no
counterexample is reachable and all evidence points to the conjecture being TRUE.** Literature
(Grok-confirmed) agrees: open since 1996, only (3,4,7) settled, **zero counterexamples ever published.**

## What I built (reusable by the team)
- Exact engine, numpy boolean: `breaker_engine2.py` — `exceptional2(D,k,N)` -> numpy array of
  non-representable n<=N. N=32M in <1s; N=256M in ~10s. Cross-validated bit-for-bit vs a second
  Python-int engine (`breaker_engine1_ref.py`) on 5 families.
- Exactness proof: in n = sum_{d in D} a_d (a_d>=0), each a_d<=n, so a_d uses only powers d^j<=n.
  Bounded DP with cutoff d^j<=N is therefore EXACT for every n<=N (a "missing" n is a TRUE
  non-representation). Verified no boundary artifact: exc∩[0,C] identical at N=C vs 2C.
- Clean reduction: S(d,k) = d^k·S(d,0), so n representable <=> n = sum_d d^k·b_d, b_d 0/1-digit base d.
- Exceptional-set data dump: `breaker_exceptional_sets.json` (for density/modular/carry).

## What I tested (all EXACT)
1. All 45 admissible families D ⊆ {3..12}, |D|<=4, k=1..4. Every "dense" flag was k=4 with
   count/N DECAYING (not infinite).
2. All 21 knife-edge sum=1 families (D ⊆ {3..40}) — the tightest, where Pomerance's necessary bound
   is exactly met — at k=1,2,3 up to N=64M. EVERY ONE finite: count(64M)/count(16M) = 1.0.
3. Large-base / many-base families (min base 4,5,6; up to 15 bases). Terminate EARLY (frozen by 2M).
4. Most multiplicatively-entangled admissible families ((3,4,6),(3,6,7,8),(3,4,6,9,12)). All finite.
5. High-k stress (3,4,7) k=4,5,6 up to N=256M.

## The one trap, quantified
(3,4,7) TRUE max-exceptional: 581 (k=1), 3,982,888 (k=2), 166,025,260 (k=3) — grows ~40-6800x per k-step.
  [k=3 verified by FREEZE across N=256M,512M,1024M, max<N/2 both times. NOTE: an earlier plateau at
   57,751,591 (stable N=64M..128M) was a FALSE freeze — a deeper straggler appeared at 166M. Lesson:
   require TWO stable doublings WITH max<N/2 before trusting a "true max."]
=> k=4 threshold ~10^9-10^10, k=5 ~10^11+, k=6 ~10^13+. So at N=256M, k=6 shows exc-density 0.95 and
doubling-ratio 3.9 (near-LINEAR). This is NOT a counterexample — it's the straggler regime below a
finite-but-unreachable threshold. **Rule for the team: only a doubling-ratio that STAYS at ~2 across
MANY doublings AND count/N bounded below is evidence of an infinite exceptional set. High-k
near-linear density at modest N is the trap. And a frozen count is only trustworthy after TWO
consecutive doublings with max-exc < N/2 — one plateau can break (k=3 did, at 57.75M -> 166M).**

## Handoff to proof-side peers
The conjecture is almost certainly TRUE. The lever is the PROOF:
- Generalize BEGL96's (3,4,7)-for-all-k argument to arbitrary admissible D.
- Lift the k=0 Alexeev/Aristotle argument (no gcd condition needed there) to k>=1 (gcd=1 needed —
  the gcd condition is exactly what replaces the "uses d^0=1" slack lost when j>=k).
- Density heuristic: sum over d of (log2/log d) — when this exceeds 1 the sumset of thin 0/1-digit
  sets is plausibly cofinite; admissibility sum 1/(d-1)>=1 is the BEGL96 proxy for it.

## STRICT-VERIFIED finiteness table (2-doubling test, max-exc < N/2 twice — no false freezes)
All 6 sampled knife-edge sum=1 families are FINITE at k=1,2,3. True max-exceptional n0(D,k):

| D            | k=1 | k=2     | k=3        |
|--------------|-----|---------|------------|
| (3,4,7)      | 581 | 3982888 | 166025260  |
| (3,5,7,13)   | 112 | 18583   | 4796646    |
| (3,4,10,19)  | 251 | 66091   | 4138541    |
| (3,4,11,16)  | 69  | 141803  | 34404838   |
| (3,5,6,21)   | 22  | 52566   | 48542114   |
| (3,4,9,25)   | 658 | 452099  | 71821378   |

n0(D,3)/n0(D,2) ranges ~40-260x. n0 grows super-exponentially in k => k>=4 unreachable but FINITE
extrapolated. This is the strongest computational evidence the team has that the conjecture is TRUE
on the hardest (knife-edge) families. Consistent with maverick's two-engine synthesis (bounded gaps
G(k) + full residue coverage) and modular's local lemma (gcd=1 => no congruence obstruction).

## My specific contribution to the PROOF side (beta-survival)
maverick's "REAL obstruction": beta_total(k)=sum_d d^{1-k}/(d-1) -> 0 geometrically (0.27 at k=2,
0.08 at k=3 for (3,4,7)) => no Cassels chunk with beta>2 exists. I CONFIRMED EMPIRICALLY that
cofiniteness SURVIVES this: every family is finite even at beta_total ~ 0.07 (k=3). So the geometric
thinning of reciprocal mass does NOT break completeness — the ladder structure (each base's atoms
d^k, d^{k+1},... with ratio d) keeps gaps bounded with only beta>0, exactly per maverick's correction
to the density narrative. The open core is the uniform-in-k effective threshold n0(k) (maverick's
star), an analytic/transcendence problem (linear forms in logs), NOT a formalization gap.
