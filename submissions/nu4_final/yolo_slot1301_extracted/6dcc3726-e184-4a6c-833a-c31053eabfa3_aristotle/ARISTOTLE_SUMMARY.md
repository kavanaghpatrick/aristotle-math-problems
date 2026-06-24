# Summary of changes for run 6dcc3726-e184-4a6c-833a-c31053eabfa3
# Erdős 373 / Surányi's Conjecture — Formalization Report

## Status: OPEN PROBLEM — partial results proved

Surányi's conjecture (1960s) states that the only solution to `n! = a! · b!` with `1 < b ≤ a` and `a + 1 ≠ n` is `(n, a, b) = (10, 7, 6)`. **This is an open problem** — no complete proof exists in the mathematical literature as of 2026. Habsieger (2019, arXiv:1903.08370) verified it computationally up to extremely large bounds but the full uniqueness remains unproven.

## What was accomplished

The file `RequestProject/Erdos373.lean` contains:

### Sorry-free results (fully proved):
1. **`factorial_10_eq`**: Verified that `10! = 7! · 6!` (via `native_decide`).
2. **`solution_10_7_6`**: The triple (10, 7, 6) satisfies all the constraints of the problem.
3. **`n_gt_a`**: If `n! = a! · b!` and `b > 1`, then `n > a` (since `n! = a! · b! ≥ 2 · a! > a!`).
4. **`n_ge_a_add_two`**: Under the additional constraint `a + 1 ≠ n`, we get `n ≥ a + 2` (the "corridor lower bound").
5. **`n_le_a_add_b`**: The upper bound `n ≤ a + b`, from the fact that `(a+b)! / (a! · b!) = C(a+b, a) ≥ 1`.

### Remaining sorry (open conjecture):
- **`erdos_373_suranyi`**: The full uniqueness statement — the set of solutions equals `{(10, 7, 6)}`. This requires proving that no other solution exists, which is the core of the open conjecture.

## Why the informal proof outline fails

The provided informal proof sketch attempts to use a "Hardy-Ramanujan asymptotic uniqueness" argument combined with Stirling's approximation and a transcendence argument about `log(2π)`. This approach has fundamental gaps:
- The asymptotic expansion argument conflates approximate agreement with exact equality.
- The claim that the `½ log(2π)` constant-term mismatch is "irreducible" via Lindemann-Weierstrass is not rigorous — the Bernoulli tail terms are rational functions of n, a, b, and the exact cancellation condition is algebraic, not transcendental.
- The "Hardy-Ramanujan saddle-point uniqueness" is not a standard result applicable in this context.

These are fundamental issues with the proof strategy, not just formalization difficulties. The conjecture remains genuinely open.