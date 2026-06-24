If you literally mean \(\sum 1/n_k\), that statement is false (e.g. \(n_k=2^k\) gives a rational geometric sum). So I assume the intended Erdős–Graham/Fibonacci form is
\[
\sum_{k\ge1}\frac1{F_{n_k}}.
\]

1. Yes, still open for \(1<c<2\) (as of January 18, 2026 in the Erdős problems tracker, citing Badea for \(c\ge2\)).  
2. A precise Badea irrationality criterion (1987) is: if \(a_n,b_n\in\mathbb Z_{>0}\) and for all large \(n\),
\[
b_n a_{n+1}>b_{n+1}a_n^2-b_{n+1}a_n+b_n,
\]
then \(\sum b_n/a_n\) is irrational.  
With \(b_n=1\): if \(a_{n+1}>a_n^2-a_n+1\) eventually, then \(\sum 1/a_n\) irrational.  
For Fibonacci subsequences with \(n_{k+1}\ge2n_k\): \(F_{n_{k+1}}\ge F_{2n_k}=F_{n_k}L_{n_k}>F_{n_k}^2-F_{n_k}+1\), so the criterion applies.  
3. Boundary depends on formulation:  
- In the original lower-bound form \(n_{k+1}/n_k\ge c>1\), \(c=2\) is included (proved).  
- In the limit form \(n_{k+1}/n_k\to c\), only \(c>2\) is immediate from that theorem; \(c=2\) is not automatically covered unless ratios are eventually \(\ge2\).  
For transcendence (stronger), known result is \(c>2\), and \(2\) is best possible (example at \(c=2\)).  
4. For \(c\in(1,2)\): no general theorem known. Known points near boundary are \(c=2\) examples (e.g. \(n_k=2^k\), \(2^k+1\)) and \(c=1\) boundary case \(n_k=k\) (irrational reciprocal Fibonacci constant).  
5. Link to Sylvester/Oppenheim/Egyptian-fraction methods: Badea’s framework is in the Oppenheim-expansion/Brun-criterion tradition (explicitly tagged in Badea 1993). These methods exploit very fast denominator growth in rational approximants.  
6. Structural gap: \(c\ge2\) gives (after passing through \(F_n\sim \varphi^n/\sqrt5\)) essentially quadratic growth between consecutive denominators, matching Brun-type irrationality machinery. For \(1<c<2\), growth is subquadratic, and the same mechanism breaks.  
7. No known rational-valued example with \(c\in(1,2)\) in the Fibonacci problem.

**Sources**
- Erdős problem page (status; \(c\ge2\) proved, \(1<c<2\) open): https://www.erdosproblems.com/267  
- Badea (1987), precise irrationality criterion: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/F61CA06EF543DADB8F3970EF30D9B5CC/S0017089500006868a.pdf/irrationality_of_certain_infinite_series.pdf  
- Badea (1993) metadata (application to open problems; Oppenheim expansions): https://eudml.org/doc/206523  
- Nguyen (2022), transcendence counterpart, threshold \(>2\): https://msp.org/ant/2022/16-7/  
