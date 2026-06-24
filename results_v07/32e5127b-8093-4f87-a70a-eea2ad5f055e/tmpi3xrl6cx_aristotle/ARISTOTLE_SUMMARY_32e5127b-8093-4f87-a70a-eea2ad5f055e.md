# Summary of changes
# Erdős Problem 364 — Formalization Results

## What was accomplished

The file `Erdos364.lean` contains a clean formalization of Erdős Problem 364 (no three consecutive powerful numbers), structured as follows:

### Proved results (no sorry)
- **`IsPowerful`**: Definition of powerful (squarefull) numbers — every prime divisor appears with exponent ≥ 2.
- **`not_powerful_of_two_mod_four`**: If `m ≡ 2 (mod 4)`, then `m` is not powerful (2 divides it but 4 does not).
- **`erdos364_easy_cases`**: If `n % 4 ≠ 3`, then `n, n+1, n+2` cannot all be powerful. This covers 3 of the 4 residue classes mod 4.
- **`erdos364`**: The full conjecture is cleanly reduced to the `n ≡ 3 (mod 4)` case via a `by_cases` split, using `erdos364_mod4` and `erdos364_easy_cases`.

### Open case (sorry remains)
- **`erdos364_mod4`**: The case `n ≡ 3 (mod 4)` — where `n` and `n+2` are both odd and `4 ∣ (n+1)` — remains as `sorry`. This is the **exact open gap** in the literature.

## Why `erdos364_mod4` remains open

This is a genuinely open problem in number theory. The theorem proving subagent was given two substantive attempts with different proof strategies:

1. **Modular sieve approach**: Extending the mod 4 argument to higher moduli (mod 8, mod 36, etc.). This cannot work because for any finite set of primes, CRT produces residue classes that survive all checks.

2. **Algebraic approach**: Using `n(n+2) = (n+1)² - 1` and the structure of powerful numbers. The factorization into coprime parts doesn't yield the needed contradiction.

The problem is known to resist:
- All finite modular sieves
- Elementary Diophantine arguments
- Computational search (no counterexample for `n < 10²²`)

The ABC conjecture would imply at most finitely many counterexamples, but no unconditional proof is known. Partial results by Chan and She (Integers 2025) handle specific structural forms but not the general case.