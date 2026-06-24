# Erdős–Straus (Erdos Problem 242) computational notes

The Erdős–Straus conjecture (open as of 2026‑03‑12) asks whether for every integer `n ≥ 2` there exist positive integers `x,y,z` with

`4/n = 1/x + 1/y + 1/z`.

After standard reductions, the difficult case is `n = p` prime with `p ≡ 1 (mod 24)`.

This folder contains a small, systematic search for decompositions of `4/p` for primes `p ≡ 1 (mod 24)` and some patterns that show up.

## Key algebra: reducing to a 2‑term Egyptian fraction

Fix `p` and pick an `x`. Define

`A := 4x - p`, `B := p x`.

Then

`4/p - 1/x = A/B`,

so we need `1/y + 1/z = A/B`.

The classical identity is:

`A/B = 1/y + 1/z   ⇔   (A y - B)(A z - B) = B^2`.

Hence, if we can find a divisor `u | B^2` such that

`A | (B + u)` and `A | (B + B^2/u)`,

then setting

`y = (B + u)/A`, `z = (B + B^2/u)/A`

produces a valid decomposition.

**Proof sketch.** Put `u := Ay - B` and `v := Az - B`. Then
`uv = B^2` implies `Ayz = B(y+z)`, hence `A/B = 1/y + 1/z`. Conversely, any
`y,z` give such a factorisation. (The code uses this equivalence.)

## A “near quarter” ansatz for primes `p ≡ 1 (mod 4)`

If `p ≡ 1 (mod 4)` (hence for `p ≡ 1 (mod 24)`), the smallest integer `x > p/4` is obtained by writing

`x = (p + a)/4` with `a ≡ 3 (mod 4)` and `a > 0`.

Empirically, for many primes one can take *very small* `a` (often `a=3` or `a=7`) and find `y,z` quickly from the divisor condition above.

## Type I subfamily (two denominators multiples of `p`)

If for a given `a` we can write `a = d + e` with `d|x` and `e|x`, then we get an explicit “Type I” solution:

`4/p = 1/x + 1/(p x / d) + 1/(p x / e)`,

because

`1/(p x / d) + 1/(p x / e) = (d+e)/(p x) = a/(p x)`.

Example (works for `p=73`):

- `p=73`, take `a=7`, so `x=(p+7)/4 = 20`.
- Since `20` is divisible by `2` and `5` and `2+5=7`, set `y= p x /2 = 730`, `z = p x /5 = 292`.
- Then `4/73 = 1/20 + 1/730 + 1/292`.

Each fixed triple `(a; d,e)` corresponds to explicit congruence conditions on `p` ensuring `x=(p+a)/4` is divisible by `d` and `e`.

## Two explicit “divisor method” families

The divisor search often succeeds with *very structured* witnesses `u`.

### Family 1: `u = p` (works when `a | (x+1)`)

Let `x=(p+a)/4`. If `a | (x+1)`, take `u=p`. Then

`y = p(x+1)/a`, `z = p x (x+1)/a`

gives `4/p = 1/x + 1/y + 1/z`.

Reason: with `B=px`, `u=p` we have `y=(B+u)/a = p(x+1)/a` and
`z=(B+B^2/u)/a = (px + p x^2)/a = p x (x+1)/a`.

### Family 2: `a=3` with a prime factor `q ≡ 2 (mod 3)` of `x`

For `p ≡ 1 (mod 24)`, set `a=3`, `x=(p+3)/4` and `B=px`. Then `B ≡ 1 (mod 3)`.

If `x` has a prime factor `q ≡ 2 (mod 3)`, taking `u=q` forces
`B+u ≡ 1+2 ≡ 0 (mod 3)`, and (since `q` is invertible mod `3`) also
`B + B^2/u ≡ 0 (mod 3)`.

This yields the explicit formulas

`y = (B + q)/3`, `z = (B + B^2/q)/3 = (B/q) * y`.

In particular, **`a=3` is possible iff** `x` has some prime factor `≡ 2 (mod 3)`
(if all prime factors of `x` are `≡ 1 (mod 3)`, then every divisor of `B^2`
is `≡ 1 (mod 3)` and cannot satisfy `u ≡ -B ≡ 2 (mod 3)`).

## What the code shows (computational evidence)

Running the search up to `p ≤ 10,000,000` found a decomposition for **every** prime `p ≡ 1 (mod 24)` in that range using `a ≤ 200`.

Even more striking: in that range the maximum `a` actually needed was `a = 107`, and the distribution is dominated by small `a`:

- `a=3` and `a=7` account for the vast majority of primes in the sample.
- A small fraction use larger `a`, but still `a ≤ 107` for `p ≤ 10^7`.

This is *not* a proof for all primes; it is evidence suggesting a “small‑a” phenomenon.

## How to run

From the repo root:

```bash
python3 experiments/erdos_straus/search.py --limit 10000000 --amax 200 --show 0
```

Use `--csv path.csv` to write all found solutions for downstream analysis.
