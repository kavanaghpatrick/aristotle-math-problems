**Verdict (as of March 13, 2026):** Kurepa’s conjecture is still open. There is no accepted proof and no known counterexample.

1. **Is it genuinely open?**  
Yes. Multiple post-2011 sources explicitly treat it as open:
- 2021 paper (arXiv 1904.09196 / IPL 167): still open; no odd prime \(p<2^{40}\) with \(p\mid !p\).
- 2022 Gallardo paper: says Barsky–Benzaghou did not prove it, and states no infinite prime family is known.
- 2023 Axioms paper: repeatedly calls it an open/unsolved problem.
- OEIS A049782 (last modified **March 10, 2026**) notes Barsky–Benzaghou withdrew the proof.
- A Nov 2025 note from the Serbian Academy’s Math Institute also says KH is unresolved.

2. **Claim \(!p \equiv 1+\frac{p-1}{2}p \pmod{p^2}\): verified or refuted?**  
Refuted. Counterexample \(p=5\):
\[
!5=0!+1!+2!+3!+4!=34,\quad 34\equiv 9\pmod{25},
\]
but
\[
1+\frac{5-1}{2}\cdot 5=11\equiv 11\pmod{25}.
\]
So \(9\neq 11\).  
Also, if that congruence were true for all odd primes, reducing mod \(p\) would give \(!p\equiv1\pmod p\), already false at \(p=5\) (\(!5\equiv4\pmod5\)).

3. **Exact state of the art**  
- No proof, no disproof.  
- Best large-scale computation (published): no counterexample for odd primes \(p<2^{40}\).  
- Many equivalent reformulations exist (Bell numbers, traces in Artin–Schreier extensions, etc.), but none settles the conjecture.

4. **Connection to Wilson and Wolstenholme**
- **Wilson** gives
\[
k!(p-1-k)!\equiv(-1)^{k+1}\pmod p
\]
for \(1\le k\le p-1\), a core congruence behind many rewrites of \(!p\).
- A standard Bell-number equivalent is
\[
!p\equiv0\pmod p \iff B_{p-1}\equiv1\pmod p.
\]
- **Wolstenholme** (\(p\ge5\): \(H_{p-1}\equiv0\pmod{p^2}\)) enters second-order (\(p^2\)) expansions of binomial/factorial terms, but does not force a simple closed \(p^2\)-formula that settles KH.

5. **Computational verification range**
- 2016: verified for all odd primes \(p<2^{34}\).
- 2021: extended to all odd primes \(p<2^{40}\).
- I found no peer-reviewed extension beyond \(2^{40}\) by March 2026.

6. **Partial results for families of primes**
- No unconditional infinite family of primes is known for which KH is proved.
- There are conditional/special-case results (e.g., Gallardo 2022 under an auxiliary assumption), but not a full family theorem resolving KH.

7. **If Barsky–Benzaghou did not settle it, what did they prove?**
- Their 2004 paper introduced/used deep Bell-number trace formulas over Artin–Schreier extensions and claimed a full proof.
- The full proof claim was later retracted by erratum (2011).
- The Bell-number framework/equivalences are still used in later literature; the final “proof” step is what failed.

**Sources**
1. arXiv 1904.09196 (Improved algorithms; \(p<2^{40}\), still open): https://arxiv.org/abs/1904.09196  
2. AMS page for 2016 Math. Comp. (\(p<2^{34}\)): https://www.ams.org/journals/mcom/2016-85-302/S0025-5718-2016-03098-7/home.html  
3. Gallardo 2022 PDF (explicitly says Barsky–Benzaghou failed; partial conditional result): https://journals.umcs.pl/a/article/download/14452/10060  
4. Gallardo 2022 article page: https://journals.umcs.pl/a/article/view/14452  
5. Axioms 2023 (open/unsolved status): https://www.mdpi.com/2075-1680/12/8/785  
6. OEIS A049782 (includes withdrawal note; modified Mar 10, 2026): https://oeis.org/A049782  
7. Barsky–Benzaghou 2004 paper record: https://jtnb.centre-mersenne.org/articles/10.5802/jtnb.432/  
8. Erratum metadata record (2011): https://eudml.org/doc/219791  
9. Nov 2025 note stating KH unresolved: https://www.mi.sanu.ac.rs/novi_sajt/news/news_pages/Kurepa_prime_numbers.pdf