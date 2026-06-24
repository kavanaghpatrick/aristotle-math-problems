Added a standalone verifier at [scripts/erdos985_verify.py](/Users/patrickkavanagh/math/scripts/erdos985_verify.py#L1). It uses a linear sieve for primes and smallest prime factors, then checks the standard criterion
`q^((p-1)/r) != 1 mod p` for every prime divisor `r` of `p-1`; the core loop is in [scripts/erdos985_verify.py](/Users/patrickkavanagh/math/scripts/erdos985_verify.py#L65).

Running `python3 scripts/erdos985_verify.py --limit 1000000` checked all `78,497` odd primes `p <= 10^6` and found no counterexample. I also ran `python3 -m py_compile scripts/erdos985_verify.py`.

**Results**
- No counterexample for any odd prime `p <= 10^6`.
- Distribution of the minimal prime primitive root `q` starts:
  `q=2`: 29,341 primes (37.38%)
  `q=3`: 17,814 (22.69%)
  `q=5`: 10,882 (13.86%)
  `q=7`: 6,841 (8.71%)
  `q=11`: 4,484 (5.71%)
- Cumulative:
  `q <= 5` for 73.94% of primes
  `q <= 11` for 88.36%
  `q <= 19` for 96.20%
  `q <= 43` for 99.55%
- Average minimal prime primitive root up to `10^6`: about `5.84`.

**Structure**
- The largest minimal prime primitive root seen was `149`, attained only at `p = 190321`.
- Record-breakers for the minimal `q` were:
  `(3,2), (7,3), (23,5), (41,7), (109,11), (191,19), (271,43), (2791,53), (11971,79), (31771,107), (190321,149)`.
- Larger minimal `q` tends to occur when `p-1` has more distinct prime factors, which creates more ways for a small candidate to fail the primitive-root test. For example:
  average `omega(p-1)` is about `3.39` when minimal `q=2`, but about `4.38` when minimal `q=43`.
- The extremal case `p=190321` has distinct prime divisors `2,3,5,13,61` in `p-1`, and every prime below `149` fails before `149` finally works.

If you want, I can extend this to `10^7` or produce a CSV of `(p, minimal_q)` for further pattern hunting.