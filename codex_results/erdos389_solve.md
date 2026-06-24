**Correct Statement (Erdős #389)**
- The original problem is: for every `n ≥ 1`, does there exist `k ≥ 1` such that `n(n+1)…(n+k-1) | (n+k)…(n+2k-1)`? It’s listed as **OPEN**, with minimal `k` computed for `1 ≤ n ≤ 18`. ([erdosproblems.com](https://www.erdosproblems.com/389))
- Your `n!·(n+1)…` formulation is *not* equivalent; and “`k=n` gives `C(2n,n)`” applies to the different (easy) fact `n! | (n+1)…(2n)`.

**Python (runs exact search up to a cutoff)**
- Script: `scripts/erdos389.py:1`
- Run: `python3 scripts/erdos389.py --nmax 15 --kmax 8500000`

**Computed minimal `k` (this machine, `n=1..15`)**
- `1, 5, 4, 207, 206, 2475, 984, 8171, 8170, 45144, 45143, 3648830, 3648829, 7979077, 7979076`

**Growth / pattern (empirical)**
- Extremely irregular but very fast growth; a crude fit on known `n=1..19` gives `log10 k ≈ -0.135 + 0.480 n` (so “~ `3^n`” as a very rough heuristic).
- Known continuation from OEIS (note index shift: OEIS `a(n-1)` matches Erdős’s `n`): for Erdős `n=16..19`, minimal `k` is `58068862, 58068861, 255278295, 255278294`. ([oeis.org](https://oeis.org/A375071))

**Math / status clarifications**
- The divisibility is equivalent to `((n+2k-1)!(n-1)!)/(n+k-1)!^2 = C(n+2k-1,k)/C(n+k-1,k)` being an integer.
- For Erdős #389, `k=n` does **not** always work (e.g. `n=2, k=2`: `2·3 ∤ 4·5`). The “central binomial coefficient” proof instead shows `n! | (n+1)…(2n)` since `(n+1)…(2n)/n! = (2n)!/(n!)^2 = C(2n,n) ∈ ℤ`.
- The existential question “does some `k` exist for every `n`?” is the genuinely hard part and remains open. ([erdosproblems.com](https://www.erdosproblems.com/389))