# Summary of changes for run e972baee-d5c4-4816-857f-ee81bf390e69
## Erdős Problem 373 (Surányi's Conjecture)

Created `RequestProject/Erdos373.lean` formalizing Surányi's conjecture that the equation `n! = a! · b!` with `1 < b ≤ a` and `a + 1 ≠ n` has only the solution `(n, a, b) = (10, 7, 6)`.

### What was proved

1. **`erdos_373_known_solution`**: Verified that `10! = 7! · 6!` (the known solution).

2. **`erdos_373_bound`** (Bertrand upper bound): Any solution must satisfy `n < 2a`. This uses a Bertrand's postulate–style argument — if `n ≥ 2a`, the factorial equation leads to a contradiction because the left side grows too fast relative to the right.

3. **`erdos_373_lower`** (trivial lower bound): Any solution must satisfy `a + 2 ≤ n`. Since `b > 1` forces `n > a`, and `a + 1 ≠ n` by hypothesis, we get `n ≥ a + 2`.

Together, these establish that any solution satisfies **`a + 2 ≤ n < 2a`**, which in particular forces `a ≥ 3`.

### What remains open

4. **`erdos_373_suranyi`** — the full conjecture — remains `sorry`. This is an **open problem** dating to the 1960s. While the bounds above restrict solutions to the range `a + 2 ≤ n ≤ 2a - 1`, ruling out all solutions in this range except `(10, 7, 6)` requires deeper number-theoretic arguments that are not known to exist. No proof of Surányi's conjecture has been published in the mathematical literature.