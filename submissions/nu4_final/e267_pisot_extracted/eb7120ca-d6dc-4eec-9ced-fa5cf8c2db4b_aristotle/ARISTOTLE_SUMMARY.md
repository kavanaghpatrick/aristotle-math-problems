# Summary of changes for run eb7120ca-d6dc-4eec-9ced-fa5cf8c2db4b
# Erdős Problem 267 — Lacunary Fibonacci Reciprocal Irrationality

## Summary

I formalized the problem statement and proved the **c ≥ 2 case** (Badea 1987) of Erdős Problem 267, while leaving the full conjecture (open for 1 < c < 2) as `sorry`.

## What was proved

The file `RequestProject/Erdos267.lean` contains:

### 1. A general irrationality criterion (`irrational_of_quadratic_growth_reciprocal_sum`)
If `(a_n)` is a sequence of positive integers with `a_n ≥ 2` and `a_{n+1} ≥ a_n²` for all `n`, then `Σ 1/a_n` is irrational.

The proof uses the **decreasing numerator argument**:
- The tail `R_n = Σ_{k≥n} 1/a_k` satisfies `1/a_n < R_n < 1/(a_n - 1)`
- If `S` were rational, writing each tail `R_n` as a reduced fraction would yield a sequence whose numerators strictly decrease — but a strictly decreasing sequence of positive integers cannot exist

This required several supporting lemmas:
- `growth_step_bound`: The key algebraic identity `1/a + 1/(b-1) < 1/(a-1)` when `b ≥ a²`
- `partial_sum_upper_bound`: Finite partial sums are bounded by `1/(a_n - 1)`
- `tail_sum_le_bound` / `tail_sum_upper_bound`: The infinite tail sum satisfies `< 1/(a_n - 1)`
- `rat_num_decrease`: The numerator-in-lowest-terms of `r - 1/a` is less than that of `r`, when `1/a < r < 1/(a-1)`

### 2. Fibonacci growth bound (`fib_sq_le_fib_double`)
`F_{2n} ≥ F_n²` for `n ≥ 1`, using the doubling identity `F_{2n} = F_n · (2F_{n+1} - F_n)`.

### 3. The c ≥ 2 case (`erdos267_c_ge_2`)
When `n_{k+1} ≥ 2 · n_k` and all `n_k ≥ 3`, the sum `Σ 1/F_{n_k}` is irrational. This combines the irrationality criterion with the Fibonacci doubling bound: `F_{n_{k+1}} ≥ F_{2n_k} ≥ F_{n_k}²`.

### 4. Full conjecture statement (`erdos267`) — sorry
The full Erdős 267 conjecture for arbitrary lacunarity ratio `c > 1` remains as `sorry`. This is consistent with the problem being **genuinely open** for `1 < c < 2`. All known irrationality criteria require at least quadratic denominator growth, which sub-doubling index gaps do not supply. The informal proof sketch using Pisot β-expansions was analyzed and found to have significant gaps in the key steps (Steps 4–5), making it unsuitable for formalization.

## Verification
- All proved theorems compile without `sorry` and use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- The only remaining `sorry` is the full open conjecture `erdos267`.