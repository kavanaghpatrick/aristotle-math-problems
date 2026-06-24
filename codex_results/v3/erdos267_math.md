As of March 13, 2026, the problem is open only in the range `1<c<2`. The real obstruction is not convergence; it is that all known black-box irrationality methods here break at the quadratic threshold.

1. **What is known**
- Good proved
  \[
  \sum_{m\ge 0}\frac1{F_{2^m}}=\frac{7-\sqrt5}{2},
  \]
  so the `2^m` case is not just irrational but algebraic.
- André-Jeannin proved \(\sum_{n\ge1}1/F_n\) is irrational; more generally he treated second-order linear recurrences. That proof uses the full recurrence structure, not mere lacunarity.
- Badea’s quick-convergence criterion implies irrationality once
  \[
  a_{k+1}>a_k^2-a_k+1
  \]
  eventually. For \(a_k=F_{n_k}\), the identity
  \[
  F_{2m}=F_m(2F_{m+1}-F_m)>F_m^2-F_m+1
  \]
  shows that \(n_{k+1}\ge 2n_k\) eventually is enough. So the Erdős question has a positive answer for `c>=2`.
- Nguyen proved transcendence when \(\liminf n_{k+1}/n_k>2\).
- Hence the exact open interval is:
  \[
  1<c<2.
  \]

2. **Which criteria actually apply**
- Duverney/Badea/Hančl type criteria are “fast-converging rational series” criteria. They need essentially quadratic denominator growth: \(x_{k+1}\asymp x_k^2\) or stronger.
- Here
  \[
  F_{n_{k+1}}\asymp F_{n_k}^{\,n_{k+1}/n_k},
  \]
  so these criteria naturally turn on at ratio `2`.
- Mere geometric convergence is not enough. Fast convergence alone never forces irrationality; rational telescoping series can also converge very fast.
- I did **not** find a directly applicable Nesterenko-style black-box criterion for arbitrary positive lacunary reciprocal series in this setting. The high-powered method that actually appears in this literature is Schmidt’s Subspace Theorem, and it also hits the same threshold `>2`, not `>1`.

3. **Why doubling is special**
- For \(n_k=2^k\), the index set is closed under doubling, and Fibonacci divisibility is aligned with that structure:
  \[
  F_m\mid F_n \iff m\mid n,\qquad \gcd(F_m,F_n)=F_{\gcd(m,n)}.
  \]
- That gives exact self-similarity. Good’s algebraic evaluation is a symptom of this semigroup structure.
- A bare condition \(n_{k+1}/n_k>1\) gives only size separation. It does **not** create any exact recurrence, Mahler equation, or divisibility chain.
- Inference: the problem for `1<c<2` is hard precisely because it has lacunarity without self-similarity.

4. **Continued fractions**
- First correction: \(1/F_n=[0;F_{n-1},F_{n-2},\dots]\) is false. What is true is
  \[
  \frac{F_{n-1}}{F_n}=[0;\underbrace{1,\dots,1}_{n-1}].
  \]
- Let \(S_N=p_N/q_N\) be the reduced \(N\)-th partial sum and \(R_N=S-S_N\). Crude bounds give
  \[
  q_N\le \prod_{j\le N}F_{n_j}\asymp \phi^{\sum_{j\le N}n_j},\qquad
  R_N\asymp \phi^{-n_{N+1}}.
  \]
- If \(n_k\) grows like \(c^k\), then \(\sum_{j\le N}n_j\sim n_{N+1}/(c-1)\). So, heuristically,
  \[
  q_NR_N \asymp \phi^{\left(\frac{1}{c-1}-1\right)n_{N+1}}.
  \]
- Therefore:
  - `c>2`: truncations alone are good enough to rule out rationality.
  - `c=2`: borderline.
  - `1<c<2`: truncations are too weak.
- Inference: the gap condition by itself does **not** force large partial quotients. Using only truncation quality, you would need something closer to `c>3` to force \(q_N^2R_N\to0\).

5. **The exact gap; the one lemma that would matter**
- Exact open gap: `1<c<2`.
- Exact methodological gap: every current general tool is a **quadratic-growth tool**.
  - Badea/Duverney: need roughly \(a_{k+1}\gtrsim a_k^2\).
  - Subspace-theorem/transcendence methods: need \(a_{k+1}\gtrsim a_k^{2+\varepsilon}\).
  - But for `1<c<2`, we only have \(a_{k+1}\asymp a_k^c\), which is subquadratic.
- The cleanest single missing lemma would be a **multi-step Brun/Badea criterion** for Fibonacci reciprocals:
  - something that can use \(n_{k+r}\ge 2n_k\) for a fixed \(r=r(c)\), even when \(n_{k+1}<2n_k\),
  - i.e. a criterion stable under amortizing the growth over finitely many steps rather than one step.
- In short: current proofs are one-step; the open range needs a genuinely multi-step irrationality criterion tailored to Fibonacci denominators.

**Sources**
- [Erdős Problem 267](https://www.erdosproblems.com/latex/267)
- [Badea, *The irrationality of certain infinite series* (Acta Arith. 1987)](https://eudml.org/doc/206440)
- [Duverney, Kurosawa, Shiokawa, fast-converging series criterion (2020)](https://www.cambridge.org/core/journals/tokyo-journal-of-mathematics/article/irrationality-exponent-of-a-kind-of-series-and-its-fast-computation/AEA998A4DF77C5A03E8D782BB122A13A)
- [Nguyen, *Transcendence of lacunary series involving Fibonacci numbers* (2022)](https://www.ams.org/tran/2022-375-08/S0002-9947-2022-08464-0/)
- [Kyoto survey citing Good’s exact formula](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/0789-16.pdf)
- [Murty survey citing André-Jeannin’s irrationality result](https://jtnb.centre-mersenne.org/articles/10.5802/jtnb.1180/)

**Next Steps**
1. Try to prove a fixed-`r` multi-step Brun criterion for positive reciprocal Fibonacci series.
2. If that fails, split the problem by index arithmetic: divisibility-chain supports versus gcd-sparse supports, since those are the two genuinely different regimes.