**Bottom Line**

As of March 13, 2026, I do not find a complete impossibility proof. Recent primary sources still treat Erdős 364 as open, so a first example could still exist at a huge size; what we have are local obstructions, special-case exclusions, and strong heuristics.

**Key Points**

- Small correction to item 2: if `n` is the first term of the triple, the mod `9` condition should be `n ≡ 0,7,8 (mod 9)`, not `0,3,6`. Reason: a powerful multiple of `3` is automatically a multiple of `9`, so among `n,n+1,n+2` the divisible-by-`3` term must be `0 mod 9`. Hence the only possible starts mod `9` are `0,7,8`.
- Combining that with `n ≡ 3 (mod 4)` gives `n ≡ 7,27,35 (mod 36)`. If Golomb’s `n ≠ 7 (mod 8)` obstruction is added, the surviving classes reduce to `n ≡ 27,35,43 (mod 72)`.
- Your step 3 is right that the naive `abc` setup is wrong. `abc` does not look at `n / rad(...)`; the useful quantity is the exponent comparison in an equation `a+b=c`.
- The right identity is
  `n(n+2) + 1 = (n+1)^2`.
  If all three terms are powerful, then
  `rad(n(n+1)(n+2)) ≤ (n(n+1)(n+2))^{1/2} ~ n^{3/2}`,
  while `c = (n+1)^2 ~ n^2`.
  So the `abc` quality is roughly `2 / (3/2) = 4/3`, which is favorable, not unfavorable.
- In fact, `abc` would imply only finitely many such triples: for any `ε < 1/3`,
  `(n+1)^2 << rad(n(n+1)(n+2))^{1+ε} << n^{(3/2)(1+ε)}`,
  and the exponent on the right is then `< 2`, forcing `n` bounded.
- This still does **not** prove impossibility. It gives finiteness, not zero.
- For point 4, letting `m = n+1`, the outer-pair condition gives
  `m^2 - 1 = n(n+2)`.
  Unconditionally, this alone does not force `m` to be powerful; `25` and `27` are both powerful, but `26` is not.
- Conditionally on `abc`, the outer-pair condition forces `rad(m)` to be almost maximal:
  `m^2 << (rad(n) rad(n+2) rad(m))^{1+ε} << (n rad(m))^{1+ε}`,
  so `rad(m) >> m^{(1-ε)/(1+ε)}`.
  Thus a twin-powerful pair wants the center to have very large squarefree kernel, while a triple would also require the center itself to be powerful, hence `rad(m) ≤ m^{1/2}`. That tension is the real `abc` mechanism.
- So the exact gap is this: we can see, heuristically and conditionally, that the middle term should be forced to have both very large and very small radical. What is missing is an **unconditional** theorem strong enough to force that contradiction.
- The density heuristic also supports “finitely many, probably none”: since `P(x) ~ C x^{1/2}`, the local density near `x` is about `x^{-1/2}`, and an independence heuristic gives expected triple count up to `X` of order `∑_{n≤X} n^{-3/2}`, which converges. Good heuristic, not proof.
- Current unconditional progress is still partial. Recent papers rule out special structured families, especially cases where the middle term has extra algebraic shape, but not the general problem.

**Status**

- Best evidence from current literature: still open.
- No definitive impossibility proof found.
- Exotic huge examples remain logically possible, though heuristics and `abc` both push toward “at most finitely many,” likely none.

**Sources**

- K. K. Chan, 2025: [arXiv:2507.16828](https://arxiv.org/abs/2507.16828)
- J. She, 2025: [arXiv:2511.00032](https://arxiv.org/abs/2511.00032)

**Next Steps**

1. Fix the mod `9` bookkeeping first: for the first term, use `0,7,8 mod 9`, not `0,3,6`.
2. Treat `abc` through `n(n+2)+1=(n+1)^2`; the naive `rad(n(n+1)(n+2))` comparison by itself is the wrong setup.
3. If you want a real attack, focus on proving an unconditional lower bound on `rad(n+1)` from the outer-pair condition `n,n+2` powerful; that is the missing bridge from heuristic/conditional finiteness to impossibility.