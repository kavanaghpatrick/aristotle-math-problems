# Erdős Problem 273 Notes

Problem: does there exist a **distinct** covering system whose moduli are all of
the form `p - 1` for a prime `p >= 5`?

The `p >= 3` version is known to be true. The useful structural point is that
`p = 3` contributes the modulus `2`, and `2` is exactly what removes the parity
obstruction below.

## Parity-halving reduction

If

`x ≡ a_i (mod m_i)` with `m_i = p_i - 1`, `p_i >= 5`,

then every `m_i` is even. Split the congruences into two groups by the parity of
`a_i`.

- If `a_i` is even, write `x = 2n`. Then
  `2n ≡ a_i (mod 2k_i)` becomes `n ≡ a_i / 2 (mod k_i)`.
- If `a_i` is odd, write `x = 2n + 1`. Then
  `2n + 1 ≡ a_i (mod 2k_i)` becomes `n ≡ (a_i - 1) / 2 (mod k_i)`.

So Problem 273 is equivalent to:

> Find two disjoint distinct covering systems with moduli `k` such that
> `2k + 1` is prime.

This also explains why the `p >= 3` case is easier: the modulus `2` turns into
the trivial half-modulus `1`, so one parity side can be covered immediately.

## Density constraints

For any covering system with distinct moduli `n_1, ..., n_t`,

`sum 1 / n_i >= 1`

is necessary. Applying that after the parity split gives:

- each parity side must contribute reciprocal mass at least `1`;
- in the original variables, the even-residue classes must have
  `sum 1 / m_i >= 1/2`;
- the odd-residue classes must also have `sum 1 / m_i >= 1/2`;
- therefore the full original system must satisfy `sum 1 / m_i >= 1`.

This is a weak asymptotic obstruction because
`sum_{p prime} 1 / (p - 1)` diverges, but it is a strong finite search screen.

## Prime-power screen

A standard necessary condition for distinct covering systems is:

> If `q^a` is the highest power of the prime `q` dividing one of the moduli in a
> side, then at least `q` moduli on that side must be divisible by `q^a`.

For Problem 273 this must hold **separately on each parity side** after
halving. So if a search family does not even contain `q` candidates divisible by
`q^a`, that family cannot support one side of a solution.

## What the script does

`analysis/erdos273_cover_search.py` searches on the half-modulus side.

- `--mode report` prints the reciprocal-mass and prime-power screens.
- `--mode single` looks for one half-cover.
- `--mode pair` looks for two disjoint half-covers, which would solve the
  original problem after lifting parity back.

The search is heuristic, but verification is exact modulo the chosen period.

## Sample runs

Default period `2520 = 2^3 * 3^2 * 5 * 7`:

- half-side reciprocal mass: `1.903571`;
- this is enough for one side but not enough for two disjoint sides;
- therefore no construction supported only on divisors of `2520` can solve
  Problem 273.

Larger period `27720 = 2^3 * 3^2 * 5 * 7 * 11`:

- half-side reciprocal mass: `2.087338`;
- this clears the basic density threshold for two disjoint sides;
- the script quickly finds one exact half-cover:

`0 (mod 2), 0 (mod 3), 0 (mod 5), 1 (mod 6), 3 (mod 8), 2 (mod 9),`
`2 (mod 15), 5 (mod 18), 3 (mod 20), 11 (mod 30), 17 (mod 36), 89 (mod 90)`;

- with one trial for a second disjoint side, no pair was found, and the second
  side still left uncovered fraction `0.622475`.

That is not evidence of impossibility, only evidence that the easy greedy search
still falls far short even after the reciprocal threshold becomes favorable.
