# Summary of changes for run d4ea419d-ffc1-4e18-9302-8a983b3a4e76
## Erdős Problem 373 — Surányi's Conjecture

**Status: OPEN.** This is a famous open conjecture from the 1960s with no known proof in the mathematical literature. The full uniqueness statement remains as `sorry`.

### What was accomplished

The formalization is in `RequestProject/Erdos373.lean`. I proved **6 sorry-free structural results** that characterize the "corridor" any solution must lie in:

1. **`mem_solutions`**: Verified that `(10, 7, 6)` is indeed a solution (`10! = 7! · 6!`).
2. **`bound_a_lt_n`**: Any solution satisfies `a < n`.
3. **`bound_lower`**: Any solution satisfies `a + 2 ≤ n` (combining `a < n` with `a + 1 ≠ n`).
4. **`ascending_eq_factorial`**: Any solution satisfies `n! / a! = b!` (the ascending product equals a factorial).
5. **`no_prime_in_interval`**: No prime exists in `(a, n]` for any solution — if a prime `p` with `a < p ≤ n` existed, it would divide `b!` yet exceed `b ≤ a`, a contradiction.
6. **`bound_upper`**: Any solution satisfies `n < 2a`, proved via Bertrand's postulate and the no-prime result.

### What remains (1 sorry)

The main theorem `erdos_373_suranyi` asserting `SolutionSet = {(10, 7, 6)}` remains as `sorry`. The proved bounds reduce any solution to the corridor `a + 2 ≤ n < 2a` with no prime in `(a, n]`, but closing the gap — showing that the product `(a+1)(a+2)···n` is never a factorial `b!` with `b ≤ a` except at `(10, 7, 6)` — requires bounding `a` from above, which is the core open difficulty. No technique in the literature (Bertrand variants, Stirling bounds, Baker's linear forms in logarithms) has yielded a finite upper bound on `a`.