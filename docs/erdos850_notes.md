# Erdos 850 Notes

As of March 13, 2026, the full `k=3` statement

`rad(x)=rad(y)`, `rad(x+1)=rad(y+1)`, `rad(x+2)=rad(y+2)`, `x != y`

is still open. The repository can support two things cleanly:

1. A rigorous obstruction package that every putative solution must satisfy.
2. A fast search that pushes well past `10^6`.

## 1. Rigorous congruence obstruction

Let `d = y - x > 0`. If

- `rad(x) = rad(y)`
- `rad(x+1) = rad(y+1)`
- `rad(x+2) = rad(y+2)`

then every prime dividing one of `x`, `x+1`, `x+2` divides the matching shifted
term at both `x` and `y`. Subtracting gives

`p | (y - x) = d`

for every prime `p | x(x+1)(x+2)`. Hence

`rad(x(x+1)(x+2)) | d`.

Write

`M = rad(x(x+1)(x+2))`.

Then every solution has

`y = x + tM`

for some integer `t >= 1`.

This immediately implies:

- `x ≡ y (mod 2)`
- `x ≡ y (mod 3)`
- in fact `x ≡ y (mod 6)`
- `|x-y| >= 30`

The last point holds because among three consecutive integers one is divisible
by `2`, one is divisible by `3`, and the third is congruent to `±1 (mod 6)`,
so it has a prime factor at least `5`. Therefore `30 | M`.

This is the key search reduction used in [scripts/erdos850_search.py](/Users/patrickkavanagh/math/scripts/erdos850_search.py).

## 2. Why the standard `k=2` family does not extend

The classical infinite `k=2` family is

`x = 2^n - 2`, `y = x(x+2)` for `n >= 2`.

It works for two shifts because:

- `x+2 = 2^n`, so `rad(y) = rad(x(x+2)) = rad(x)`
- `y+1 = x(x+2) + 1 = (x+1)^2`, so `rad(y+1) = rad(x+1)`

So this gives infinitely many pairs with

`rad(x)=rad(y)`, `rad(x+1)=rad(y+1)`.

But it fails at the third shift in a rigid way:

- `rad(x+2) = rad(2^n) = 2`
- `y+2 = (x+1)^2 + 1`

Now `x+1 = 2^n - 1` is odd, so `(x+1)^2 ≡ 1 (mod 8)`. Therefore

`y+2 = (x+1)^2 + 1 ≡ 2 (mod 8)`.

So `y+2` is even but not divisible by `4`. Since `y+2 > 2`, it must have an odd
prime factor. Hence

`rad(y+2) > 2 = rad(x+2)`.

Therefore no member of this infinite `k=2` family can extend to a `k=3`
solution.

This is the cleanest structural obstruction coming from the known `k=2`
mechanism: the identity `y+1 = (x+1)^2` preserves radicals at shift `+1`, but
then `y+2 = (x+1)^2 + 1` automatically introduces a new odd prime.

## 3. Search results

Commands:

```bash
python3 scripts/erdos850_search.py --k 3 --bound 1000000
python3 scripts/erdos850_search.py --k 3 --bound 10000000
python3 scripts/erdos850_search.py --k 2 --bound 1000000 --family-samples 6
```

Observed results on this machine:

- `k=3`, bound `10^6`: no witnesses
- `k=3`, bound `10^7`: no witnesses
- `k=2`, bound `10^6`: many witnesses, beginning with `(2,8)`, `(6,48)`,
  `(14,224)`, `(30,960)`

The `k=3` search is fast because it only inspects `y` in the progression
`x (mod M)`, where `M = rad(x(x+1)(x+2))`.
