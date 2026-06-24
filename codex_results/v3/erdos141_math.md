**Overview**

For the finite problem you stated,
\[
f(N):=\max\{|A|:A\subseteq\{1,\dots,N\}\text{ is multiplicative Sidon}\},
\]
the right order is known:
\[
f(N)=\pi(N)+\Theta\!\left(\frac{N^{3/4}}{(\log N)^{3/2}}\right).
\]
So \(f(N)\sim \pi(N)\sim N/\log N\), not \(N^{1/2}\).

**Main Points**

- Additive vs multiplicative:
  Additive Sidon sets are size \(\sim N^{1/2}\). Multiplicative Sidon sets are much denser because the primes already form a multiplicative Sidon set, giving \(\pi(N)\sim N/\log N\).

- Correction to point 4:
  The set of all prime powers is **not** multiplicative Sidon. Counterexample: \(2\cdot 8=4\cdot 4\).

- Lower bound idea:
  Take all primes \(>\sqrt N\), then add many semiprimes \(pq\) with \(p,q\le \sqrt N\), chosen from a \(C_4\)-free graph on the primes up to \(\sqrt N\).
  Why \(C_4\)-free matters:
  If \((p_1q_1)(p_2q_2)=(p_3q_3)(p_4q_4)\), unique factorization forces the same four primes, which would encode a 4-cycle.
  Since a largest \(C_4\)-free graph on \(m\) vertices has \(\sim \frac12 m^{3/2}\) edges and
  \[
  m=\pi(\sqrt N)\sim \frac{2\sqrt N}{\log N},
  \]
  this gives
  \[
  \Theta\!\left(\frac{N^{3/4}}{(\log N)^{3/2}}\right)
  \]
  extra elements beyond the prime main term.

- Upper bound:
  Your \(|A|\le 2N\) bound is far too weak. Erdős proved in 1938
  \[
  f(N)\le \pi(N)+O(N^{3/4}),
  \]
  and in 1969 improved this to
  \[
  f(N)\le \pi(N)+O\!\left(\frac{N^{3/4}}{(\log N)^{3/2}}\right).
  \]
  Combined with his lower bound, this yields the theorem above.

- So the “answer” to Erdős’s question is:
  \[
  \pi(N)+c_1\frac{N^{3/4}}{(\log N)^{3/2}}
  \le f(N)\le
  \pi(N)+c_2\frac{N^{3/4}}{(\log N)^{3/2}}
  \]
  for absolute constants \(c_1,c_2>0\).

- About Singer/finite geometry:
  There is no direct multiplicative analogue of Singer’s additive construction driving the main term.
  But finite-geometry/extremal-graph constructions do appear indirectly: the lower-order term comes from dense \(C_4\)-free graphs, which are closely tied to projective-plane constructions.

**Open Point**

- The order of magnitude is settled, but not the exact secondary constant. A natural refinement would be to determine whether
  \[
  \frac{f(N)-\pi(N)}{N^{3/4}(\log N)^{-3/2}}
  \]
  has a limit.

**Sources**

- [Liu–Pach 2019, *The number of multiplicative Sidon sets of integers*](https://real.mtak.hu/99393/1/The_number_JCTA.pdf)
- [Pach 2015, *Generalized multiplicative Sidon sets*](https://real.mtak.hu/74695/1/Generalized_multiplicative.pdf)
- [Jing–Mudgal 2025, recent work on additive/multiplicative Sidon subsets in arbitrary sets](https://link.springer.com/article/10.1007/s00208-024-02932-7)

**Next Steps**

1. I can give a clean proof sketch of the \(C_4\)-free graph lower bound.
2. I can also sketch the upper-bound decomposition that leads to \(\pi(N)+O\!\big(N^{3/4}/(\log N)^{3/2}\big)\).
3. If you want, I can compare this finite story with the much harder infinite multiplicative Sidon problem.