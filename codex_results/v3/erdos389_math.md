1. There are two different questions here, and your restatement flips the divisibility direction. The condition is
\[
\prod_{i=0}^{k-1}(n+i)\mid \prod_{i=0}^{k-1}(n+k+i),
\]
equivalently
\[
Q_k(n):=\frac{\prod_{i=0}^{k-1}(n+k+i)}{\prod_{i=0}^{k-1}(n+i)}
=\frac{\binom{n+2k-1}{k}}{\binom{n+k-1}{k}}\in \mathbb Z.
\]
The actual Erdős-Straus problem behind Erdős Problem #389 is: for every fixed \(n\ge 1\), does there exist some \(k\) with \(Q_k(n)\in\mathbb Z\)? Your “for every fixed \(k\), infinitely many \(n\)” variant is different.

2. Small \(k\):
\[
k=1:\quad n\mid n+1 \iff n=1.
\]
\[
k=2:\quad n(n+1)\mid (n+2)(n+3).
\]
Reducing mod \(n\) gives \(n\mid 6\). Reducing mod \(n+1\) gives \(n+1\mid 2\). Hence \(n=1\). So for \(k=2\) the only solution is again \(n=1\).

3. Your binomial ratio should be
\[
\frac{\binom{n+2k-1}{k}}{\binom{n+k-1}{k}},
\]
not \(\binom{2n+2k-1}{k}/\binom{n+k-1}{k}\). By Kummer,
\[
v_p\!\binom{a+b}{a}
\]
equals the number of carries when adding \(a\) and \(b\) in base \(p\). Therefore
\[
v_p(Q_k(n))
=
c_p(k,n+k-1)-c_p(k,n-1),
\]
where \(c_p(x,y)\) is the number of base-\(p\) carries in \(x+y\). So \(Q_k(n)\in\mathbb Z\) iff for every prime \(p\), adding \(k\) to \(n+k-1\) creates at least as many base-\(p\) carries as adding \(k\) to \(n-1\).

4. Equivalently,
\[
v_p(Q_k(n))
=
\sum_{r\ge 1}\Big(
\Big\lfloor\frac{n+2k-1}{p^r}\Big\rfloor
-2\Big\lfloor\frac{n+k-1}{p^r}\Big\rfloor
+\Big\lfloor\frac{n-1}{p^r}\Big\rfloor
\Big).
\]
Failure occurs when some \(p^r\) occurs more often in \([n,n+k-1]\) than in \([n+k,n+2k-1]\), with multiplicity. But there is a much stronger elementary obstruction: if divisibility holds, then for each \(0\le j\le k-1\),
\[
n+j \mid \prod_{i=0}^{k-1}(k+i-j),
\]
because one reduces the numerator modulo \(n+j\). In particular, taking \(j=k-1\),
\[
n+k-1\mid k!.
\]
So for every fixed \(k\), only finitely many \(n\) are possible. That kills the fixed-\(k\) infinitude variant immediately.

5. Central binomial coefficients appear only in the trivial family \(n=1\):
\[
Q_k(1)=\frac{(k+1)\cdots (2k)}{1\cdots k}=\binom{2k}{k}.
\]
Catalan numbers then appear one step stronger:
\[
C_k=\frac{1}{k+1}\binom{2k}{k}.
\]
So Catalan/central-binomial divisibility is a model case, not a reformulation of Problem 389.

6. The exact open gap is this: not “finitely or infinitely many \(n\) for fixed \(k\)” because that is false and easy; rather, “for each fixed \(n\), does at least one \(k\) exist?” That is the original Erdős-Straus question. As of March 2026, the modern Erdős Problems database still lists that original existence question as open. The natural expectation is affirmative existence for every \(n\), but I did not find a primary-source paper giving a sharp conjecture for the size of the least such \(k\).

7. Known nearby literature is mostly adjacent, not decisive. Kummer gives the \(p\)-adic carry criterion. Erdős-Lacampagne-Selfridge and Konyagin study least prime factors of binomial coefficients, which is structurally relevant. Ford-Konyagin prove strong divisibility results for central binomial coefficients, relevant to the \(n=1\) shadow. But I did not find a primary-source paper proving substantial direct progress on Problem 389 itself. I could verify Guy’s book page and its Divisibility chapter, but not the exact entry text from the preview.

Sources:
- [Kummer (1852)](https://eudml.org/doc/147500)
- [Erdős-Graham source volume: *Analytic Number Theory*](https://link.springer.com/book/10.1007/BFb0096450)
- [Erdős Problem #389, current open-status transcription, secondary source](https://www.erdosproblems.com/389)
- [Konyagin, “Estimates of the least prime factor of a binomial coefficient”](https://www.cambridge.org/core/journals/mathematika/article/estimates-of-the-least-prime-factor-of-a-binomial-coefficient/45F7A0914E211853A94C52914D351086)
- [Ford-Konyagin, “Divisibility of the central binomial coefficient \(\binom{2n}{n}\)”](https://www.ams.org/tran/0000-000-00/S0002-9947-2020-08183-5/)
- [Guy, *Unsolved Problems in Number Theory* book page](https://link.springer.com/book/10.1007/978-0-387-26677-0)

I found the original source and adjacent binomial-divisibility papers, but not a primary-source paper with direct new results on Problem 389 itself.