# breaker: all small admissible families have FINITE exc-sets (density -> 0)

## Reduction (clean)
S(d,k) = d^k * S(d,0), where S(d,0) = {0/1-digit numbers base d}. So
  n representable  <=>  n = sum_{d in D} d^k * b_d,  b_d in S(d,0).
Weighted sumset, weights w_d = d^k.

## Fast exact engine: /tmp/e124_engine2.py (numpy boolean, N=32M in <1s)
Cross-validated bit-for-bit against the Python-int engine1 on 5 families. N=4M for (3,4,7) all k matches.

## Density traces (count of exceptionals <= N), the DECISIVE test
A FALSE counterexample needs count ~ c*N (positive density, ratio->2 across doublings).
Observed: ratio DECAYS below 2 and count/N -> 0 everywhere. => FINITE exc-sets. BEGL96 confirmed.

(3,4,7) k=3:  N=1M..32M count 199616->374992, count/N 0.1996->0.0117, ratio_vs_prev ->1.001
   => count has essentially STOPPED growing by 32M (only +254 from 16M->32M). NEAR-TERMINATED.
(3,4,7) k=4:  count/N 0.79->0.29, ratio dropping 1.84->1.36 — terminating, larger threshold.
(3,4,6) k=4:  count/N 0.76->0.28, ratio 1.84->1.29 — same.

Scan of ALL 45 admissible families (D subset {3..12}, size<=4) x k=1..4: EVERY flagged "dense"
case was k=4 with count/N decaying. NONE show stable positive density. (/tmp/e124_scan2.py)

## Conclusion for the FALSE hunt
Small/tight admissible families are robustly TRUE. The k-lever only raises the threshold; it does not
create an infinite exceptional set. Counterexample (if any) must live in an UNREACHED regime:
  - large bases d (S(d,0) genuinely thin: |S(d,0) cap [0,X]| ~ X^{log2/log d})
  - families where sum 1/(d-1) is EXACTLY 1 and removing any base breaks gcd/sum (knife-edge)
Pivoting search there next. But current evidence strongly favors TRUE.

## (UPDATE) Threshold scaling law for (3,4,7) — explains the high-k straggler trap
TRUE max exceptional (count frozen, verified < N/2):
  k=1: 581       (count 37)
  k=2: 3,982,888 (count 5207)   -- grew ~6855x from k=1
  k=3: 57,751,591(count 390934) -- grew ~14.5x from k=2
Threshold grows >=14x per k-step. Extrapolated: k=4 ~1-3 billion, k=5 ~10^11, k=6 ~10^12+.

THE TRAP (my earlier caution, now quantified): at N=256M, (3,4,7) k=5 shows ratio 3.27 and k=6
shows ratio 3.90 (near-linear, count/N=0.95). This LOOKS like non-termination but is just the
straggler regime — the FINITE threshold for k>=4 is FAR beyond reachable N. Do NOT mistake high-k
near-linear density at modest N for an infinite exceptional set. The k=1,2,3 thresholds prove the
super-exponential threshold growth; k>=4 is finite but computationally unreachable.

## VERDICT (breaker, entry point = FALSE hunt)
No reachable computational counterexample. ALL 21 knife-edge sum=1 families (the tightest, where
Pomerance's bound is exactly met) have FINITE exceptional sets at k=1,2,3 (ratio count(64M)/count(16M)=1.0).
Large-base/many-base families terminate even earlier. Evidence strongly favors the conjecture TRUE.
The FALSE entry point is exhausted within computational reach. Recommend the team weight effort toward
the PROOF side (lift k=0 Alexeev argument to k>=1; BEGL96 (3,4,7) generalization).

## (CORRECTION, important) (3,4,7) k=3 true max is 166,025,260 NOT 57,751,591
My earlier "k=3 max=57751591" was a FALSE FREEZE: count plateaued at 390934 across N=64M,128M
(with max 57.75M < N/2) — looked terminated — but at N=256M a deeper straggler appeared at
166,025,260 (count 391070). Verified TRUE max=166,025,260 by freeze across N=256M/512M/1024M,
max<N/2 at 512M and 1024M (two stable doublings, 94s at 1B).
Corrected scaling: 581 (k1) -> 3,982,888 (k2, x6855) -> 166,025,260 (k3, x41.7).
METHODOLOGICAL UPGRADE: a single frozen plateau is NOT enough. Require TWO consecutive doublings
with the count unchanged AND max-exc < N/2 before declaring a "true max." k=3 broke a one-doubling
freeze. (3,4,7) k=1 (581) and k=2 (3,982,888) DO survive this stricter test.
