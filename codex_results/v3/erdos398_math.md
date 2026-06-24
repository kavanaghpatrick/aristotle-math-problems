**Overview**

Current picture: no unconditional finiteness proof is known. The strongest unconditional theorem I found is a sparsity result: for \(P\in \mathbb Z[x]\) of degree \(\ge 2\), the number of \(n\le N\) with \(n!=P(x)\) is \(O(N^{33/34})\), so in particular Brocard solutions are \(O(N^{33/34})\). Conditional finiteness is known from weak-Szpiro/abc-type hypotheses, and structurally the problem is equivalent to asking whether \(n!/4\) can be split into two consecutive coprime integers.

1. **State of the art**

   The best peer-reviewed computation I verified is [Berndt–Galway 2000](https://doi.org/10.1023/A:1009873805276): no new solutions for \(n\le 10^9\). The best unconditional global theorem I found is [Bui–Pratt–Zaharescu 2023](https://doi.org/10.1016/j.aim.2023.109021): for any polynomial \(P\) of degree \(\ge 2\),
   \[
   \#\{n\le N:\ n!=P(x)\text{ for some }x\}\ll N^{33/34}.
   \]
   For Brocard, this gives \(O(N^{33/34})\) candidate \(n\), not finiteness.

   On the conditional side, there is a small hierarchy:
   - Overholt’s 1993 result is under a **weak form of Szpiro**, not literally the full abc conjecture, though abc implies it.
   - [Ulas 2012](https://doi.org/10.1017/S0004972712000512) summarizes: Dąbrowski (1996) proved that \(y^2=x!+A\) has finitely many solutions for fixed \(A\), unconditionally if \(A\) is nonsquare, and conditionally if \(A\) is a square. So \(A=1\) is exactly the conditional Brocard case.
   - [Luca 2002](https://web.math.pmf.unizg.hr/glasnik/vol_37/no2_04.html): under abc, \(n!=P(x)\) has only finitely many solutions for every \(P\in\mathbb Z[x]\) with \(\deg P>1\).
   - [Gica–Panaitopol 2005](https://doi.org/10.1112/S0024609305004595): under abc in Szpiro form, the falling-factorial equation \(n(n-1)\cdots(n-k+1)=P(m)\) with quadratic \(P\) has only finitely many solutions when \(k>n^\varepsilon\); this includes \(k=n\), hence \(n!=P(m)\).
   - [Helou–Haddad 2008](https://doi.org/10.1007/s11139-008-9139-8): many infinite families of \(n\) for which \(n!+1\) is not a square, via quadratic reciprocity.
   - [Dąbrowski 2012](https://eudml.org/doc/284217): a separate conjectural reduction, via a conjecture on \(n^2-1\) supported on initial primes, which would imply the expected Brocard solution set.

2. **Exact structural reformulation**

   For \(n\ge 2\), \(m\) is odd. Set
   \[
   A=\frac{m-1}{2},\qquad B=\frac{m+1}{2}.
   \]
   Then
   \[
   AB=\frac{n!}{4},\qquad \gcd(A,B)=1,\qquad B-A=1.
   \]
   This is sharper than just \((m-1)(m+1)=n!\): the problem becomes

   \[
   \frac{n!}{4} = A(A+1)
   \]
   with \(A\) and \(A+1\) coprime.

   Hence for every prime \(p\le n\),
   \[
   v_p(A),v_p(B)\in \{(v_p(n!/4),0),(0,v_p(n!/4))\}.
   \]
   Every prime power goes entirely to one side. There is no room for “sharing”.

3. **Wilson-prime obstruction**

   Your observation is exactly right. If \(n+1=p\) is prime, then by Wilson
   \[
   (p-1)! \equiv -1 \pmod p,
   \]
   so from \(n!+1=m^2\) we get \(m^2\equiv 0\pmod p\), hence \(p\mid m\), hence \(p^2\mid m^2=n!+1\). Therefore
   \[
   (p-1)! \equiv -1 \pmod {p^2},
   \]
   so \(p\) must be a Wilson prime.

   Since the only known Wilson primes are \(5,13,563\), and no others are known below \(2\times 10^{13}\) by [Costa–Gerbicz–Harvey 2014](https://doi.org/10.1090/S0025-5718-2014-02800-7), this collapses all cases \(n=p-1\) to \(n=4,12,562\) in that range; computation then leaves only \(n=4\).

4. **Can Erdős–Selfridge-style prime-distribution arguments work?**

   Not in their original form. Erdős–Selfridge wins because a prime \(p\in(n/2,n]\) has \(v_p(n!)=1\), which is incompatible with \(n!\) being a nontrivial perfect power. Here that same fact is completely compatible with Brocard:
   \[
   v_p(n!)=1
   \]
   just means \(p\) divides exactly one of \(A\) or \(B\).

   So Bertrand-type primes do not create an exponent mismatch. They only create many congruences of the form
   \[
   m\equiv \pm 1 \pmod p.
   \]
   That is useful only after adding extra local information, e.g. quadratic reciprocity or Wilson-type lifting. So prime distribution is a good **sieve amplifier**, but probably not a standalone proof engine.

5. **What Stirling says about \(m\pm1\)**

   Stirling gives
   \[
   m \sim \sqrt{n!}\sim \left(\frac ne\right)^{n/2}(2\pi n)^{1/4}.
   \]
   Therefore \(A\) and \(B\) are consecutive integers of size \(\asymp \sqrt{n!}\).

   Every prime divisor of \(A\) and \(B\) is \(\le n\). So both \(A\) and \(B\) are \(n\)-smooth integers near
   \[
   x\asymp \exp\!\left(\tfrac12 n\log n\right).
   \]
   The smoothness parameter is
   \[
   u=\frac{\log x}{\log n}\sim \frac n2,
   \]
   which is enormous. Smooth-number heuristics then say such integers are fantastically rare, and here we need **two consecutive** such integers. That is the real global obstruction: not just factorization, but adjacency of two ultra-smooth numbers.

6. **The “bit budget” / log-partition view**

   Write
   \[
   \frac{n!}{4}=\prod_{p\le n} p^{e_p},\qquad e_p=v_p(n!/4).
   \]
   Choosing which factor gets each prime power is choosing a subset of weights
   \[
   w_p=e_p\log p.
   \]
   Since \(AB=n!/4\) and \(B=A+1\),
   \[
   \log B-\log A=\log\!\left(1+\frac1A\right)=\frac1A+O(A^{-2}).
   \]
   But \(A\asymp \sqrt{n!}\), so this difference is
   \[
   \exp\!\bigl(-\tfrac12 n\log n + O(n)\bigr),
   \]
   absurdly tiny.

   So the subset \(\{w_p\}\) must split into two sums that match to exponentially tiny precision. That is a very strong heuristic obstruction. The difficulty is making it rigorous: it becomes a subset-sum / linear-forms-in-logs problem with \(\pi(n)\) growing variables.

7. **Which techniques look best?**

   Best **conditional** route: explicit abc / weak-Szpiro. It fits almost perfectly. With
   \[
   A=\frac{m-1}{2},\qquad C=\frac{m+1}{2},
   \]
   we have \(A+1=C\) and
   \[
   \operatorname{rad}(AC)\le \prod_{p\le n} p = e^{\theta(n)}=e^{(1+o(1))n}.
   \]
   Any explicit abc inequality would force
   \[
   C \ll e^{(1+\varepsilon+o(1))n},
   \]
   while Stirling gives
   \[
   C\asymp \exp\!\left(\tfrac12 n\log n-\tfrac12 n\right).
   \]
   Growth mismatch: immediate effective bound on \(n\).

   Best **unconditional** route: not Baker by itself. Classical Baker theory is strongest when the number of logarithms is fixed; here the prime set grows with \(n\). More promising are:
   - the [Bui–Pratt–Zaharescu](https://doi.org/10.1016/j.aim.2023.109021) Padé/Diophantine-approximation framework, specialized to \(P(x)=x^2-1\);
   - quantitative theory of consecutive smooth numbers / \(S\)-unit gaps, because \(A\) and \(A+1\) are the natural objects;
   - local-global sieves combining Wilson primes, reciprocity, and primes in intervals.

   Lang–Waldschmidt is conceptually closer than Baker to item 6, because the obstruction is a near-cancellation of many \(\log p\)’s. But as a practical route it still looks farther away than abc.

**Sources**

- [Berndt–Galway 2000](https://doi.org/10.1023/A:1009873805276)
- [Bui–Pratt–Zaharescu 2023](https://doi.org/10.1016/j.aim.2023.109021)
- [Ulas 2012](https://doi.org/10.1017/S0004972712000512)
- [Luca 2002](https://web.math.pmf.unizg.hr/glasnik/vol_37/no2_04.html)
- [Gica–Panaitopol 2005](https://doi.org/10.1112/S0024609305004595)
- [Helou–Haddad 2008](https://doi.org/10.1007/s11139-008-9139-8)
- [Costa–Gerbicz–Harvey 2014](https://doi.org/10.1090/S0025-5718-2014-02800-7)
- [Dąbrowski 2012](https://eudml.org/doc/284217)

**Unresolved Questions**

- A stronger computational bound \(n\le 10^{15}\) is widely repeated in secondary sources, but I did not verify a primary source for that claim in this pass.
- I did not recover the exact infinite families proved by Helou–Haddad from the abstract alone.

**Next Steps**

1. Write the abc/Szpiro argument cleanly in the \(A+1=C\) form and see exactly what an explicit constant would need to finish the problem.
2. Recast Brocard as a theorem about consecutive \(n\)-smooth numbers near \(\sqrt{n!}\), and compare with the strongest available quantitative smooth-number gap results.
3. Try to hybridize the Bui–Pratt–Zaharescu method with the special factorization \(x^2-1=(x-1)(x+1)\); that is the most plausible unconditional path I see.