# Summary of changes
# Erdős Problem 68 — Irrationality of ∑ 1/(n!-1)

## Status: OPEN PROBLEM — Main theorem remains `sorry`

This is a genuinely open problem in number theory (Erdős Problem 68). No complete proof is known in the mathematical literature, and the theorem proving subagent confirmed the difficulty after multiple attempts with different proof strategies.

## What was accomplished

The file `RequestProject/Erdos68.lean` contains:

### Proved helper lemmas (6 lemmas, all sorry-free):
1. **`summable_one_div_factorial_sub_one`** — The series ∑ 1/(n!-1) converges (by comparison with ∑ 1/n!)
2. **`decompose_term`** — Each term satisfies 1/(n!-1) = 1/n! + 1/(n!(n!-1))
3. **`summable_remainder`** — The remainder series ∑ 1/(n!(n!-1)) converges
4. **`sum_inv_factorial_eq_exp`** — ∑ 1/n! = e
5. **`sum_inv_factorial_from_two`** — ∑_{n≥2} 1/n! = e - 2
6. **`sum_decomposition`** — S = (e-2) + ∑ 1/(n!(n!-1))

### Main theorem (`erdos_68`): remains `sorry`

## Why the standard approaches fail

The key difficulty is that **n!-1 does not divide N!** in general, unlike n! which always divides N! for n ≤ N. This breaks the standard irrationality proof for e (multiply by N! and show fractional part is in (0,1)):

- For e: N! · ∑_{n>N} 1/n! is strictly between 0 and 1, giving a contradiction.
- For our sum: N! · ∑_{n≤N} 1/(n!-1) includes non-integer terms (e.g., 6!-1 = 719 is prime, so N!/719 is only an integer when N ≥ 719).

The decomposition S = (e-2) + R shows that if R = ∑ 1/(n!(n!-1)) were rational, irrationality would follow from e's irrationality. However, proving R is rational appears equally difficult.