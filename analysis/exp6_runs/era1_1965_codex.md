warning: `--full-auto` is deprecated; use `--sandbox workspace-write` instead.
Reading additional input from stdin...
OpenAI Codex v0.130.0
--------
workdir: /private/tmp
model: gpt-5.5
provider: openai
approval: never
sandbox: workspace-write [workdir, $TMPDIR, /Users/patrickkavanagh/.codex/memories]
reasoning effort: xhigh
reasoning summaries: none
session id: 019e7cfa-8831-7aa3-b060-2e708cd48a19
--------
user
You are a 1965-era number theorist (Erdős, Selfridge, Mahler, Sylvester-Schur). Solve this problem using ONLY tools available before 1965.

PROBLEM (Surányi, Erdős #373): Prove that the equation n! = a!·b! with integers 1 < b ≤ a, a + 1 ≠ n has exactly ONE solution: (n,a,b) = (10,7,6), i.e. 10! = 7!·6!.

CONSTRAINTS — 1965 era allowed tools ONLY:
- Bertrand's postulate (1845), Erdős's elementary proof (1932)
- Sylvester-Schur theorem (1892, Erdős 1934 reproof): product of k consecutive integers > k has a prime factor > k
- Stirling's formula
- Legendre's formula for v_p(n!)
- Erdős-Lehmer-Selfridge on factorial equations (pre-1965 papers)
- Prime gap estimates (Erdős 1934, Erdős-Rankin 1938)
- Bounds on diophantine equations via elementary p-adic / archimedean comparison
- Erdős's 1948 method on primes in (n, 2n)
- Mahler's 1933 work on factorials with restricted prime factors (S-unit equations not yet effective)
- Linnik (1944) on arithmetic progressions

FORBIDDEN (post-1965):
- Baker's theorem on linear forms in logarithms (1966+)
- Effective abc / Faltings' theorem (1983)
- Iwaniec sieve (1972+), Bombieri-Vinogradov (1965 - borderline; treat as just not yet)
- Polynomial method, Green-Tao, additive combinatorics
- Modern Subspace Theorem, Schmidt 1972

WRITE a full proof attempt (≥1000 words) in 1965-style elementary number theory:
1. Set up the equation, reduce to canonical form.
2. Use Sylvester-Schur or Bertrand to find a "witness prime" in the corridor.
3. Handle the surviving finite case explicitly.
4. State clearly any place where you would have hit a wall in 1965.

Show every step. Be honest about what 1965 tools cannot resolve. Output ONLY the proof attempt — no preamble.
