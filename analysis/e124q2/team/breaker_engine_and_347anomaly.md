# breaker: exact DP engine + (3,4,7) k=2 large-exceptional anomaly

## Engine (VALIDATED, exact)
`/tmp/e124_engine.py` — bitmask DP. For each base d: `S(d,k)` = mask of sums of distinct d^j (j>=k).
Sumset over D via shift-OR. Missing bits = exceptional set, EXACT for all n<=N.

Key exactness fact (proven): in n = sum_{d in D} a_d with a_d>=0, each a_d<=n, so a_d uses only
powers d^j <= n. Bounded DP with cutoff d^j<=N is therefore EXACT for representability of every n<=N
(a "missing" n is a TRUE non-representation, not just search-bounded evidence).

No-boundary-artifact test PASSED: exc∩[0,C] identical computed at N=C vs N=2C (C=200000).

Speed: N=4M for a 3-base family in ~1.3s.

## ANOMALY worth attention: (3,4,7) k=2
BEGL96 says (3,4,7) is TRUE (finite exceptional set) for ALL k!=0. My engine finds the exceptional
set is FINITE-LOOKING but with sparse LARGE stragglers:
- N=200k: 5197 exc, max 195353 (looked like it was tracking ~N — but that was the largest below N)
- N=1M, 2M: count frozen at 5205, max 785743 (STABLE across N=1M..2M)
- N=4M: count 5207, max 3982888 (TWO new exceptionals appeared: 3964625, 3982888)

785743 and 3982888 confirmed NON-representable by THREE fully independent checkers
(bitmask DP, recursive subset-sum, itertools-combinations). Neighbors 785742/785744 ARE representable.

Interpretation (UNRESOLVED):
- Most likely: BEGL96 correct, threshold just large; these are last stragglers near high powers of 4.
  Ratios 3982888/785743=5.07, 3964625/767480=5.17 — NOT a clean power-of-4 family, so probably terminate.
- The fact that count jumps by exactly 2 each time a new power-of-4 band opens (just below 4^11) is a
  boundary-band signature: n just below d^J needs no power >= d^J, so it's exact, but it sits in a
  "thin" representability region. These likely DO terminate (consistent with BEGL96).

TAKEAWAY FOR THE TEAM: when you compute an exceptional set, do NOT trust "max exc ~ N" as
non-termination. Recompute at 2N, 4N; only a count that GROWS LINEARLY (density bounded below) is
evidence of an infinite exceptional set. A frozen count with rare large stragglers => probably finite.
