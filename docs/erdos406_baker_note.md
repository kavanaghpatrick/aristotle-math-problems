# Erdos 406: What Baker-Type Methods Actually Give

We want integers `n` such that

`2^n = sum_{j=1}^r 3^{a_j}`

with distinct exponents `0 <= a_1 < ... < a_r`. This is exactly the same as
asking that the base-3 expansion of `2^n` use only the digits `0` and `1`.

## Immediate reductions

- `n` must be even, because `2^n mod 3` is `1` for even `n` and `2` for odd `n`,
  while a base-3 number with digits in `{0,1}` has last digit `0` or `1`.
- The least ternary digit must be `1`, so `a_1 = 0`.

So every solution has the shape

`2^n = 1 + 3^{a_2} + ... + 3^{a_r}`.

## Fixed Hamming weight: finite by Baker / S-unit methods

If `r` is fixed, then this is an exponential Diophantine equation with
multiplicatively independent bases `2` and `3`. Standard linear-forms-in-
logarithms machinery implies only finitely many solutions for that fixed `r`.

One way to see the Baker input is:

1. Move the largest term to one side:
   `2^n - 3^{a_r} = 1 + 3^{a_2} + ... + 3^{a_{r-1}}`.
2. Divide by `3^{a_r}`:
   `2^n * 3^{-a_r} - 1 = 3^{-a_r} + ... + 3^{a_{r-1} - a_r}`.
3. The right-hand side is very small once the gap pattern is fixed, so we get a
   small nonzero linear form involving `log 2` and `log 3`.
4. Baker-Wustholz / Matveev lower bounds then force explicit bounds on the
   exponents.

Equivalently, this is a special case of `S`-unit equations. For each fixed `r`,
there are only finitely many `n`.

This is the mathematical content behind results of the form:

- for each fixed number of nonzero ternary digits, only finitely many powers of
  `2` can occur;
- stronger explicit work can rule out all sufficiently large solutions with at
  most a given number of `1` digits.

## Why this does not settle the full problem

Erdos 406 asks for finiteness with no a priori bound on `r`, the number of `1`
digits. Baker-type bounds alone do not currently give such a bound on `r`.

So the present situation is:

- `r` fixed: finitely many solutions, effectively bounded in principle.
- `r` unbounded: the full conjecture remains open.

In particular, any infinite family of solutions would need the number of `1`
digits in the ternary expansion of `2^n` to grow without bound.

## Useful references

- Senge-Straus type results on simultaneous digit sums in multiplicatively
  independent bases.
- Stewart, work on representations of integers with few nonzero digits in one
  base and small digit sum in another.
- Robert Saye, *On two conjectures concerning the ternary digits of powers of
  two* (2022), which discusses the Erdos 406 problem and partial progress.
