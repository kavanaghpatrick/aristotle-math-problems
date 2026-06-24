**Bottom Line**

These are **not equivalent**:

- `n!+1` squarefree for infinitely many `n`
- `n!+1` powerful for only finitely many `n`

The second is much stronger. Your `abc` line proves the **powerful** statement, not the **squarefree** one.

**Argument**

Let `N = n!+1`.

- Bertrand is a red herring here. In fact for every prime `q ≤ n`, `q | n!`, so `q ∤ N`. Hence every prime divisor of `N` is `> n`.
- If `N` is powerful, then `rad(N) ≤ N^{1/2}`.
- Also
  \[
  \operatorname{rad}(n!)=\prod_{p\le n}p < 4^n
  \]
  by the classical Chebyshev bound on the primorial.

Apply `abc` to
\[
1+n!=N.
\]
Since `gcd(1,n!,N)=1`, for every `ε>0`,
\[
N \ll_\varepsilon \operatorname{rad}(n!\,N)^{1+\varepsilon}
= \big(\operatorname{rad}(n!)\operatorname{rad}(N)\big)^{1+\varepsilon}
\le (4^n N^{1/2})^{1+\varepsilon}.
\]
Choose `ε=1/2`. Then
\[
N^{1/4} \ll 8^n,
\]
so `log N = O(n)`. But Stirling gives
\[
\log(n!+1)\sim n\log n,
\]
contradiction for large `n`.

So:

- `abc` implies: `n!+1` is powerful for only finitely many `n`.

Your quality calculation should be corrected to:

- `q(1,n!,n!+1) -> 2`, not `∞`.

That is still enough for `abc`.

**Status**

As of **March 13, 2026**, I found no primary-source unconditional proof of finiteness for powerful values of `n!+1`. Recent primary literature still treats even the narrower square case `n!+1=m^2` via `abc`/Szpiro-type hypotheses, which is evidence that the unconditional problem remains out of reach.

Also:

- The `abc` argument above does **not** address “squarefree infinitely often”.
- Heuristically one expects squarefreeness very often, but that is far beyond current methods.

Sources:

- [Luca 2002](https://doi.org/10.1017/S0017089502001024)
- [Novaković 2025](https://arxiv.org/abs/2509.00931)
- [Bolvardizadeh–Yavari 2025](https://arxiv.org/abs/2502.12047)

1. Separate the two problems: `powerful finitely many` vs `squarefree infinitely often`.
2. If your target is Erdős problem 1108 in the powerful sense, `abc` gives a clean conditional proof.
3. If your target is squarefreeness, a different idea is needed; this `abc` route does not settle it.