Let \(I(n)=\sigma(n)/n\) and \(\Delta(n)=\sigma(n)-2n\). Since every deficient non-pseudoperfect number has \(I(n)<2\), Erdős 825 is really about weird numbers:  
\[
C=\sup\{I(n): n \text{ is weird}\}.
\]
So the powers of \(2\) only show the threshold cannot be below \(2\), while \(70\) gives the first genuine lower bound
\[
C\ge I(70)=\frac{144}{70}=\frac{72}{35}\approx 2.05714.
\]

1. The classical conjectural value is \(C=3\), not \(+\infty\).  
Benkoski and Erdős explicitly raised the question whether \(I(n)\) could be arbitrarily large on weird numbers and tentatively suggested the answer should be negative. The Erdős problem page also records Sierpiński’s guess that \(C=3\) might be the right bound.

2. There is a terminology trap here: unbounded additive abundance does not imply unbounded \(I(n)\).  
If by “abundance” you mean \(\Delta(n)=\sigma(n)-2n\), then
\[
I(n)=2+\frac{\Delta(n)}{n}.
\]
So \(\Delta(n)\to\infty\) is compatible with \(I(n)\) staying bounded, or even tending to \(2\).

3. That is exactly what happens in the Kravitz-type primitive weird families \(n=2^k pq\).  
For such numbers,
\[
I(n)=\left(2-\frac1{2^k}\right)\left(1+\frac1p\right)\left(1+\frac1q\right).
\]
In the Iannucci/Melfi/Kravitz constructions, \(p,q\) sit just above \(2^{k+1}\), so \(I(n)\to 2\) as \(k\to\infty\). These constructions are strong evidence for many primitive weird numbers, but not for a large extremal value of \(I(n)\).

4. Primitive weird numbers matter because every weird number has a primitive weird divisor, but odd weird numbers are the real obstruction to a clean small bound.  
Write a weird \(n\) as \(n=2^r m\) with \(m\) odd. Then
\[
I(n)=I(2^r)I(m)<2I(m).
\]
So if \(I(n)\ge 4\), then \(I(m)>2\), hence \(m\) is odd abundant. If \(m\) were pseudoperfect, then \(n\) would also be pseudoperfect, contradiction. Therefore any weird number with \(I(n)\ge4\) has an odd weird divisor. So:

\[
\text{If no odd weird numbers exist, then every weird number satisfies } I(n)<4.
\]

5. Current status as of March 13, 2026.  
The exact optimal \(C\) is still not known. The old folklore guess remains \(C=3\). But the existence of some finite absolute bound is now reported as solved affirmatively by Daniel Larsen on the Erdős problem page. What I could verify from the available sources is:

- Conjectured exact value: \(3\).
- Best clean explicit conditional bound: \(I(n)<4\), assuming odd weird numbers do not exist.
- Best unconditional status: a finite bound now exists, but I could not verify a sharp explicit numerical constant from the accessible sources.

Useful sources:
- [Erdős Problem 825](https://www.erdosproblems.com/825)
- [Erdős Problem 470](https://www.erdosproblems.com/470)
- [Benkoski-Erdős, “On Weird and Pseudoperfect Numbers”](https://www.jstor.org/stable/2319041)
- [Iannucci, primitive weird numbers of the form \(2^k pq\)](https://cs.uwaterloo.ca/journals/JIS/VOL18/Iannucci/iann5.html)
- [Melfi, conditional infinitude of primitive weird numbers](https://combinatorialpress.com/jcmcc-articles/volume-093/conditional-infinitude-of-primitive-weird-numbers/)
- [Fang, no odd weird numbers below \(10^{21}\)](https://arxiv.org/abs/2207.12906)
- [Liddy-Riedl, odd weird numbers need at least 6 prime divisors](https://ideaexchange.uakron.edu/honors_research_projects/728/)

If you want, I can next turn this into a short “research note” style argument centered on the formula \(I(2^k pq)\) and why Kravitz families push toward \(2\), not toward the extremal \(C\).