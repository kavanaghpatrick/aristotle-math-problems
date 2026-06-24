# Summary of changes for run 598d68e6-87ba-48d9-a582-a7599aea0081
## Erdős Problem 373 (Surányi's Conjecture) — Partial Formalization

### Problem
The equation n! = a!·b! with 1 < b ≤ a and a + 1 ≠ n is conjectured to have exactly one solution: (n, a, b) = (10, 7, 6). This has been open since the 1960s.

### What was accomplished

The formalization is in `RequestProject/Erdos373.lean`. The main theorem `erdos_373_suranyi` is stated with the exact target signature and has a complete proof **modulo one sorry** — the open conjecture itself (the upper bound on `a`).

#### Fully proved lemmas (sorry-free):
1. **`witness_mem`**: Verifies 10! = 7!·6! and all side conditions (`native_decide`).
2. **`n_gt_a`**: Any solution has a < n (since b! > 1 implies n! > a!).
3. **`n_ge_a_plus_two`**: Any solution has n ≥ a + 2 (from a < n and a + 1 ≠ n).
4. **`n_lt_two_a`**: Any solution has n < 2a (from b! ≤ a! and the central binomial coefficient bound).
5. **`a_ge_three`**: Any solution has a ≥ 3 (from the corridor bounds a+2 ≤ n < 2a).
6. **`no_prime_in_interval`**: If p is prime with a < p ≤ n, then n! = a!·b! with b ≤ a is impossible (since p | n!/a! = b! forces p ≤ b ≤ a < p, contradiction).
7. **`factorial_eq_mul_prod`**: n! = a! · ∏ᵢ∈Icc(a+1,n) i (connects factorial form to product form).
8. **`computational_check`**: For all a ∈ [3, 275], n ∈ [a+2, 2a-1], b ∈ [2, a]: if the product (a+1)·...·n equals b!, then (n, a, b) = (10, 7, 6). Verified by `native_decide`.

#### The remaining sorry:
- **`a_upper_bound`**: Any solution has a ≤ 275. This is the core of the open Surányi conjecture — proving that no solution exists with a > 275. The structural argument shows any solution must have no prime in (a, n], which constrains the prime gaps, but eliminating all large `a` requires showing that products of consecutive composite integers are never factorials. This is related to Brocard-type problems and remains open.

### Proof architecture
The main theorem proceeds as:
1. **Forward direction** (⊇): (10, 7, 6) satisfies all conditions (computational).
2. **Reverse direction** (⊆): Given a solution, the corridor bounds constrain a+2 ≤ n < 2a with a ≥ 3. The open bound gives a ≤ 275. Converting to product form and applying the computational check forces (n, a, b) = (10, 7, 6).

### Summary
This formalization proves all structural components of Surányi's conjecture and computationally verifies uniqueness for a ≤ 275. The full conjecture reduces to proving `a_upper_bound` — that no solution exists with a > 275 — which remains an open problem in number theory.