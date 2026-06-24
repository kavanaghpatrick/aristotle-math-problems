As of March 13, 2026, this is still open; the Erdős Problems database entry was still marked open when last edited on December 20, 2025.

The cleanest rigorous point is the `abc` one. If `n` is squarefull and `n+1` is cubefull, then
`rad(n) <= n^{1/2}` and `rad(n+1) <= (n+1)^{1/3}`.
So for the `abc` triple `(1,n,n+1)`,
`rad(n(n+1)) <= n^{1/2}(n+1)^{1/3} < (n+1)^{5/6}`.
Hence
`n+1 > rad(n(n+1))^{6/5}`,
so any such solution has `abc`-quality at least `6/5`. Therefore `abc` would imply only finitely many such pairs. It does not imply zero; it only says this problem is an exceptional-set question, not an infinite-family question.

On the theorem side, there is no standard Stewart-Tijdeman theorem that settles this mixed squarefull/cubefull problem. The relevant classical result is Tijdeman’s theorem on consecutive perfect powers, later sharpened by Mihăilescu: it only kills the pure-power subcase `n=x^2`, `n+1=y^3`. The real difficulty is the kernels. Writing
`n = b u^2`, `n+1 = d v^3`
with `b` squarefree and `d` cubefree gives
`b u^2 + 1 = d v^3`.
For fixed `b,d` this becomes a Mordell curve:
`Y^2 = X^3 - b^3 d^2`
via `X = bdv`, `Y = b^2 d u`. So for each fixed kernel pair there are only finitely many integer points, but the hard part is uniformity as `b,d` vary. That is why Thue-Mahler/S-unit technology is suggestive but not decisive here.

Your local calculation is exactly the right reason finite congruence obstructions cannot work. Since for each prime `p` there are
`p^3 - 2p^2 + p + 1 > 0`
admissible classes mod `p^3`, any finite set of local conditions is compatible by CRT. So any impossibility proof has to be global: `abc`, or a uniform integral-point theorem for the above Mordell family, or a genuine gap theorem for cubefulls.

Current gap results are far too weak. Squarefull numbers have counting function `~ C_2 x^{1/2}`, so average gap size is about `x^{1/2}`. Cubefull numbers have counting function `~ C_3 x^{1/3}`, so average gap is about `x^{2/3}`. Heath-Brown and Shiu prove short-interval results on those natural scales, but Shiu also remarks that for cubefulls we cannot even prove `liminf(q_{m+1}-q_m) < infinity`. So a gap of `1` is far beyond existing technology.

Heuristically, the density near `x` of squarefull numbers is about `const * x^{-1/2}`, and of cubefull numbers about `const * x^{-2/3}`. Treating the conditions as independent up to a positive singular series gives expected overlap
`~ const * x^{-7/6}`.
Since `sum x^{-7/6}` converges, the heuristic predicts finitely many total solutions, not infinitely many. Because the local singular series is positive at every prime, the heuristic does not force impossibility; it predicts “zero or very few”, not “never”. So a first solution at astronomical size is logically possible, but not especially favored by the density model. The natural heuristic guess is: either no solution at all, or a tiny finite set.

Sources:
- Erdős problem page: https://www.erdosproblems.com/366
- Bateman-Grosswald on `k`-full counting: https://celebratio.org/Bateman_PT/article/348/
- Heath-Brown on squarefull short intervals: https://doi.org/10.1017/S0305004100070055
- Shiu on cubefull distribution and gaps: https://doi.org/10.1017/S0017089500008351
- Smart on Thue-Mahler equations: https://doi.org/10.1112/S0024610797005619