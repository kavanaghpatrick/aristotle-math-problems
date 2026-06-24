As of March 13, 2026, I did not find a published proof of irrationality for
\[
S:=\sum_{n=2}^\infty \frac1{n!-1}.
\]
The Erdős problem database still lists it as open, with the problem page last edited on September 28, 2025.

1. The literature splits into three relevant method families.

   The old Cantor/Ahmes line, from Oppenheim and Erdős–Straus through Badea and Hančl–Tijdeman, proves irrationality by exploiting divisibility and nested denominators. This is the right framework for sums like \(\sum 1/n_k\), Cantor series, Ahmes series, and many \(\sum a_n/n!\) problems. The basic mechanism is: multiply by a carefully chosen integer, get an integer plus a tiny nonzero remainder.

   Duverney’s work is different. It uses Mahler-type transcendence methods for very fast converging series, especially when the terms come from a rigid functional pattern such as \(a^{2^n}+b_n\). That works when there is a self-similarity or functional equation behind the series.

   Nesterenko’s methods are of a third type: modular/Eisenstein. They apply when the series is a special value of a modular or quasimodular object. For example,
   \[
   E_2(q)=1-24\sum_{n\ge1}\sigma_1(n)q^n,
   \]
   so irrationality/transcendence of \(\sum \sigma_1(n)/t^n\) can be accessed through modular forms at algebraic \(q=1/t\).

   Your series has none of these structures in an obvious way.

2. Why the usual Cantor-series argument fails, and what else one can try.

   The key obstruction is exactly what you said:
   \[
   \gcd(n!-1,(n+1)!-1)=1.
   \]
   So there is no nested divisibility, no denominator chain, and no natural lcm that grows slowly enough.

   The closest analogies are not Cantor series but:
   \[
   \frac1{n!-1}=\sum_{m\ge1}\frac1{(n!)^m},
   \]
   so
   \[
   S=\sum_{m\ge1}\sum_{n\ge2}\frac1{(n!)^m}.
   \]
   For fixed \(m\), the inner sum is hypergeometric:
   \[
   \sum_{n\ge0}\frac{z^n}{(n!)^m}={}_0F_{m-1}(;1,\dots,1;z),
   \]
   and at \(z=1\) this is an \(E\)-function value. That is promising for each fixed \(m\), but the outer sum over \(m\) destroys the finite-dimensional differential structure that Shidlovsky/Nesterenko methods need.

   There is also an entire-function reformulation:
   \[
   F(z):=\prod_{n\ge2}\left(1-\frac z{n!}\right), \qquad S=-\frac{F'(1)}{F(1)}.
   \]
   This is conceptually nice, but no useful differential or functional equation for \(F\) is known.

3. Padé approximation: what would \(q_N\) be?

   The most natural approximant is the partial sum
   \[
   s_N=\sum_{n=2}^N\frac1{n!-1},
   \]
   with denominator
   \[
   q_N=\prod_{n=2}^N (n!-1)
   \]
   before reduction. But this is hopelessly too large.

   Quantitatively,
   \[
   R_N:=S-s_N \asymp \frac1{(N+1)!},
   \]
   while
   \[
   \log q_N \sim \sum_{n\le N}\log(n!) \sim \frac12 N^2\log N.
   \]
   So \(R_N\) is of size \(\exp(-N\log N)\), but \(1/q_N\) is of size \(\exp(-\tfrac12 N^2\log N)\). The natural truncation gives an error vastly larger than \(1/q_N\).

   The double-series truncation is not better. If you truncate at \(n\le N\), \(m\le M\), then a natural common denominator is \((N!)^M\), but multiplying the tail by \((N!)^M\) makes it huge. So any successful Padé construction must use nontrivial cancellation; \(q_N\) cannot be a literal common denominator of the obvious truncation.

   Also, a small correction: \(|S-p_N/q_N|<1/q_N\) by itself is not enough in general. What you really want is a sequence with special divisibility, e.g. \(N!\mid q_N\), and
   \[
   0<|q_NS-p_N|<1.
   \]
   Then rationality is impossible for large \(N\).

4. The \(p\)-adic situation is actually very unfavorable.

   For any prime \(p\), once \(n\ge p\) we have \(n!\equiv 0 \pmod p\), hence
   \[
   n!-1\equiv -1 \pmod p,
   \]
   so
   \[
   v_p\!\left(\frac1{n!-1}\right)=0,\qquad \frac1{n!-1}\equiv -1\pmod p.
   \]
   Therefore the terms do not even tend to \(0\) in \(\mathbf Q_p\). So the series does not converge \(p\)-adically.

   In fact the partial sums drift linearly mod \(p\), and more strongly mod \(p^k\) once \(v_p(n!)\ge k\). So there is no direct \(p\)-adic analytic object here analogous to the real sum. That shuts off the most naive \(p\)-adic approach.

5. Beukers-type integrals / hypergeometric representations.

   There are integral identities, for example
   \[
   \frac1{n!-1}=\int_0^1 \frac{x^{n!-2}}{1-x^{n!}}\,dx
   \]
   and
   \[
   \frac1{n!-1}=\int_0^\infty e^{-(n!-1)t}\,dt.
   \]
   But these do not produce a fixed differential equation or a clean recurrence in \(N\). That is exactly what Beukers/Apéry-type proofs usually need.

   By contrast, for \(\zeta(2)\), \(\zeta(3)\), or modular-form values, the integral representation sits inside a finite-dimensional algebraic/differential structure. Here the exponents \(n!\) are too irregular. So hypergeometric technology applies to each fixed \(m\) in \(\sum_n (n!)^{-m}\), but not to the full sum over \(m\).

6. The exact gap, and the one lemma that would essentially solve it.

   The tail after \(N\) is only about \(1/(N+1)!\), so any contradiction-by-truncation proof needs integer linear forms of “factorial scale”:
   \[
   \log(\text{coefficients}) = O(N\log N).
   \]
   All existing natural denominator-clearing constructions for \(\sum 1/(n!-1)\) are of “product of factorials scale”:
   \[
   \log(\text{coefficients}) = \Theta(N^2\log N).
   \]
   That is the precise quantitative gap.

   A single lemma that would close the problem is this:

   If one could construct integers \(p_N,q_N\) with \(N!\mid q_N\), \(\log q_N = O(N\log N)\), and
   \[
   0<|q_NS-p_N|<1
   \]
   for infinitely many \(N\), then \(S\) would be irrational.

   Equivalently: one needs a Padé-type or linear-form construction that compresses the first \(N\) denominators \(n!-1\) down to factorial size, not product-of-factorials size. Every known method for nearby problems gets that compression from one of three sources:
   divisibility chains, functional equations, or modular/differential structure. For \(\sum 1/(n!-1)\), no such source is known.

**Sources**

[Erdős Problem #68](https://www.erdosproblems.com/68)  
[Peter Borwein, “On the irrationality of certain series” (1992)](https://doi.org/10.1017/S030500410007081X)  
[C. Badea, “The irrationality of certain infinite series” (1987)](https://doi.org/10.1017/S0017089500006868)  
[C. Badea, “A theorem on irrationality of infinite series and applications” (1993)](https://eudml.org/doc/206523)  
[Erdős–Straus, “On the irrationality of certain Ahmes series” (1963), bibliographic entry and review](https://www.emis.de/classics/Erdos/cit/13104902.htm)  
[Hančl–Tijdeman, “On the irrationality of factorial series” (2005)](https://eudml.org/doc/278068)  
[Hančl–Tijdeman, “On the irrationality of factorial series II” (2010)](https://doi.org/10.1016/j.jnt.2009.10.005)  
[Hančl–Tijdeman, “On the irrationality of factorial series III” (2009)](https://doi.org/10.1016/S0019-3577(09)80024-4)  
[Daniel Duverney, “Irrationality of Fast Converging Series of Rational Numbers” (2001)](https://www.ms.u-tokyo.ac.jp/journal/abstract_e/jms080206_e.html)  
[Daniel Duverney, “Transcendence of a fast converging series of rational numbers” (2001)](https://doi.org/10.1017/S0305004100004783)  
[R. Tijdeman, survey “On irrationality and transcendency of infinite sums of rational numbers”](https://pub.math.leidenuniv.nl/~tijdemanr/tijsho3.pdf)  
[Nesterenko, “Modular functions and transcendence problems” (1996)](https://www.erdosproblems.com/latex/250)  
[Kurokawa–Wakayama, “On q-analogues of the Euler constant and Lerch’s limit formula” (2004)](https://doi.org/10.1090/S0002-9939-03-07025-4)  
[Chatterjee–Garg, “On q-analogue of Euler–Stieltjes constants” (2023)](https://www.ams.org/journals/proc/2023-151-05/S0002-9939-2023-16288-7/home.html)

I could not inspect the full text of every paywalled source here, especially Erdős’s 1988 chapter, so the structural comparison above uses abstracts, reviews, and later survey material where needed.