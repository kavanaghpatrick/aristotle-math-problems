# Summary of changes for run 1862ce29-c8a9-48bf-91fd-bcc56b2fc907
# Erdős Problem 373 — Partial Formalization

## Problem
The conjecture (open since the 1960s) states that the only solution to `n! = a! · b!` with `1 < b ≤ a` and `a + 1 ≠ n` is `(n, a, b) = (10, 7, 6)`, i.e., `10! = 7! · 6! = 3,628,800`.

## What was proved (sorry-free)

The formalization is in `RequestProject/Erdos373.lean`. The following results are proved completely (no sorry, standard axioms only):

1. **Forward direction** (`mem_solution_set`): `(10, 7, 6)` satisfies all constraints.

2. **Corridor bounds**:
   - `corridor_lower`: Any solution satisfies `a + 2 ≤ n`.
   - `corridor_upper`: Any solution satisfies `n < 2 * a`. Proved via the inequality `(2a)! > (a!)²`.

3. **Witness prime lemma** (`witness_prime_kills`): If there exists a prime `p` with `a < p ≤ n`, then `n! ≠ a! · b!` for any `b ≤ a`. The proof uses Euclid's lemma: since `p | n!` but `p ∤ a!` (as `a < p`), we get `p | b!`, contradicting `b ≤ a < p`.

4. **Bounded verification** (`bounded_200`): For `a ≤ 200`, the only solution is `(10, 7, 6)` — proved by exhaustive computation via `native_decide` on the mathematical statement itself.

5. **Combined uniqueness** (`uniqueness_bounded`): Corridor bounds + bounded verification give: any solution with `a ≤ 200` must be `(10, 7, 6)`.

6. **Extended computational check** (`checkBound_1000`): An efficient decision procedure confirms no other solutions exist for `a ≤ 1000`.

## What remains (one sorry)

The main theorem `erdos_373_target` has a single `sorry` for the case `a > 200`. This is the genuinely open part of Surányi's conjecture. The proof strategy proposed in the informal sketch (Erdős–Selfridge witness-prime + Nagura's theorem + finite survivor enumeration) has a mathematical gap: while the witness prime argument eliminates all cases where a prime exists in `(a, n]`, the "prime-gap survivor" set (pairs where no prime exists in the interval) is infinite — it includes all `a` where both `a+1` and `a+2` are composite, which occurs infinitely often. The sketch incorrectly claimed this set terminates at `a = 25`.

## Mathematical analysis

The proof reduces the problem as follows: any solution must satisfy `a + 2 ≤ n < 2a` (corridor), and there must be **no prime** in the interval `(a, n]` (witness prime argument). By Bertrand's postulate, there is always a prime in `(a, 2a)`, so the first prime after `a` is at most `2a`. The open question is: for infinitely many `a` where both `a+1` and `a+2` are composite, can the product `(a+1)(a+2)···n` equal `b!` for some `b ≤ a`? Computational evidence strongly suggests not (verified to `a = 1000`), but no proof exists in the literature.