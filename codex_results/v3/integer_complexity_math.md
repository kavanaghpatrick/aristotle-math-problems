**Overview**

`‖2^n‖ = 2n` is still open. The multiplicative case is easy; the whole problem is the additive last step. Aristotle’s reduction is mathematically clean, but it replaces one hard statement by a stronger global one, not an obviously easier one.

**Main Points**

1. **Aristotle’s reduction**
   - In [slot654_result.lean](/Users/patrickkavanagh/math/submissions/nu4_final/slot654_result.lean), the weight is
     \[
     w(n)=\sum_{p} v_p(n)\,\|p\|.
     \]
     Then `w(mn)=w(m)+w(n)` and `w(2^n)=2n`.
   - Aristotle proves: if
     \[
     w(a+b)\le w(a)+w(b)\quad(a,b>1)
     \]
     and
     \[
     w(m+1)\le w(m)+1\quad(m>1),
     \]
     then `‖n‖ ≥ w(n)` for all `n`, hence `‖2^n‖ ≥ w(2^n)=2n`.
   - Tractability: as a reduction, yes; as an easier route, no. It would prove a **global** lower bound `‖n‖ ≥ w(n)` for every `n`, which is stronger than the single family `n=2^k`.

2. **What is actually hard**
   - `‖2^n‖ ≤ 2n` is trivial.
   - For the lower bound, strong induction leaves only:
     \[
     a+b=2^n \implies \|a\|+\|b\|\ge 2n.
     \]
   - The multiplicative branch closes immediately, since `a b = 2^n` forces `a=2^i`, `b=2^j`.

3. **Correction on “Guy’s conjecture”**
   - As written, `‖m‖ ≥ 3 log_2 m` is false. Example:
     \[
     \|3\|=3 < 3\log_2 3 \approx 4.755.
     \]
   - The standard universal lower bound is Selfridge’s:
     \[
     \|m\|\ge 3\log_3 m.
     \]
   - Applied to `m=2^n`, this gives
     \[
     \|2^n\|\ge 3n\log_3 2 \approx 1.892789\,n.
     \]
     So the exact linear gap to `2n` is
     \[
     (2-3\log_3 2)n \approx 0.10721074\,n.
     \]

4. **Known bounds and verified range**
   - Iraids–Balodis–Freivalds–Opmanis–Podnieks give the standard bounds
     \[
     3\log_3 n \le \|n\| \le 3\log_2 n,
     \]
     and report average complexity below `3.635 log_3 n`.
   - Altman–Zelinsky proved
     \[
     \|2^a3^k\|=2a+3k \quad \text{for } 0\le a\le 21,
     \]
     so in particular `‖2^n‖=2n` for `n≤21`.
   - Altman’s dissertation extends this to `0≤a≤48`, hence `‖2^n‖=2n` for `n≤48`.
   - If you mean the original Iraids computational checkpoint specifically, the MathOverflow discussion records verification for `n≤39`.

5. **Addition chains and Scholz**
   - Addition-chain length `ℓ(n)` and integer complexity are different invariants, but both ask whether powers of `2` admit hidden shortcuts.
   - Scholz–Brauer is
     \[
     \ell(2^n-1)\le n-1+\ell(n).
     \]
   - Altman–Zelinsky show that natural “doubling-stability” hypotheses for integer complexity imply another hypothesis whose failure would yield counterexamples to Scholz–Brauer. So the `2^n` complexity problem is structurally linked to addition-chain rigidity, not just superficially analogous.

6. **Best plausible proof strategy**
   - The exact structural gap is the additive lemma above.
   - Most targeted route:
     \[
     a+b=2^n,\quad v_2(a)=v_2(b)=t,\quad a=2^t u,\ b=2^t v,\ u,v\text{ odd},\ u+v=2^{n-t}.
     \]
     Then combine:
     - a no-shortcuts-under-doubling statement, e.g. `‖2^t m‖ ≥ 2t + ‖m‖`,
     - with an odd-case lower bound for `u+v=2^r`.
   - The weight-function route is elegant but stronger than necessary.
   - A digit method is conceivable, but Altman–Zelinsky prove that `‖2^n‖=2n` would force a linear lower bound on the ternary digit sum:
     \[
     S_3(2^n) > 0.107\,n.
     \]
     That indicates how hard any base-3 proof would have to be.

**Unresolved / Correction**

- Item 3 needed correction: the valid universal lower bound is `3 log_3`, not `3 log_2`.
- In the sources I checked, the strongest explicit published verification I found is `n≤48`.

**Sources**

- Aristotle reduction: [slot654_result.lean](/Users/patrickkavanagh/math/submissions/nu4_final/slot654_result.lean)
- Iraids et al.: https://arxiv.org/abs/1203.6462
- Altman–Zelinsky: https://arxiv.org/abs/1207.4841
- Altman dissertation: https://deepblue.lib.umich.edu/handle/2027.42/108126
- Altman–Zelinsky digit-sum paper/source: https://arxiv.org/abs/1409.0446
- MathOverflow checkpoint discussion: https://mathoverflow.net/a/75792

**Next Steps**

1. Isolate the exact additive lemma `a+b=2^n => ‖a‖+‖b‖≥2n` into equivalent odd-case statements.
2. Compare the weight-function route against the doubling-stability route `‖2m‖ ?= ‖m‖+2`.
3. If useful, I can next write a clean “research note” version of this with lemmas and implications ordered like a paper outline.