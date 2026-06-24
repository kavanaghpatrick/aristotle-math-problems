First, a notation cleanup.

The congruence
\[
nB_{\varphi(n)}\equiv -1 \pmod n
\]
for composite \(n\) is already a theorem characterizing what is now usually called a Giuga number. The open Agoh-Giuga conjecture is the prime test
\[
n>1\text{ prime}\iff nB_{n-1}\equiv -1 \pmod n.
\]
Also, some papers use “Giuga number” for a composite counterexample to the \(n-1\) congruence; current usage usually means just \(p\mid(n/p-1)\) for all \(p\mid n\). That ambiguity is behind several of the claims you listed.

1. I assume “Aristotle” is a slip for Agoh or Borwein et al.
The key proved facts are:
- For composite \(n\),
  \[
  \sum_{a=1}^{n-1} a^{n-1}\equiv -1 \pmod n
  \iff
  \forall p\mid n:\ p\mid(n/p-1)\ \text{and}\ (p-1)\mid(n/p-1).
  \]
- So a composite counterexample is exactly a number that is both Carmichael and Giuga in the modern sense.
- The easy lower bound of 9 prime factors is for an odd counterexample to the original conjecture, not for modern Giuga numbers.
- Borwein et al. also introduced Giuga sequences and Carmichael sequences; this is the main structural extension. Their parity analysis shows an odd modern Giuga number would have to have length \(m\equiv 2\pmod 4\), and after ruling out \(m=10\), the first unresolved odd case is \(m=14\).

2. “Only known Giuga numbers: none” is false under your stated definition.
Examples already in Borwein et al. are \(30,858,1722\). So modern Giuga numbers do exist. What is not known is a composite number satisfying the original \(n-1\) congruence, equivalently a composite number that is both Carmichael and Giuga.

3. Extra constraint beyond Carmichael.
Carmichael gives, by Korselt,
\[
n \text{ squarefree},\qquad (p-1)\mid(n-1)\ \forall p\mid n.
\]
Giuga adds
\[
p\mid(n/p-1)\iff n/p\equiv 1\pmod p\iff p^2\mid(n-p).
\]
So the extra condition is genuinely \(p\)-adic: for each prime factor \(p\), the product of the other prime factors must be \(1\) mod \(p\). Combined with Carmichael,
\[
p^2(p-1)\mid(n-p)\qquad(\forall p\mid n).
\]
That is much stronger than Korselt alone.

4. Bernoulli side and prime factorization.
Using von Staudt-Clausen with \(m=\varphi(n)\),
\[
B_{\varphi(n)}+\sum_{q-1\mid \varphi(n)}\frac1q\in \mathbf Z.
\]
Multiplying by \(n\) and reducing mod \(n\), terms with \(q\nmid n\) vanish, so
\[
nB_{\varphi(n)}\equiv -\sum_{p\mid n}\frac{n}{p}\pmod n.
\]
Hence
\[
nB_{\varphi(n)}\equiv -1\pmod n
\iff
\sum_{p\mid n}\frac{n}{p}\equiv 1\pmod n
\iff
\sum_{p\mid n}\frac1p-\frac1n\in\mathbf Z.
\]
This forces:
- \(n\) is squarefree,
- each prime factor is simple,
- \(p^2\mid n-p\) for every \(p\mid n\).

But it does not force Carmichaelness by itself: \(30\) satisfies the \(\varphi(n)\)-Bernoulli condition and is not Carmichael.

5. Tipu (2007) and the current best bound.
Tipu did not improve the exclusion bound; he proved a counting bound for composite counterexamples:
\[
G(X)\ll X^{1/2}\log X.
\]
Luca-Pomerance-Shparlinski (2009) improved this to
\[
G(X)=O\!\left(\frac{X^{1/2}}{(\log X)^2}\right)=o(X^{1/2}).
\]
The best published exclusion bound I found is Borwein-Maitland-Skerritt (2013):
- any composite counterexample has at least \(4771\) prime factors,
- hence exceeds \(10^{19907}\),
- so has at least \(19{,}908\) decimal digits.

If you mean odd modern Giuga numbers, the published structural bound remains: at least \(14\) prime factors.

6. Heuristic/density picture; comparison with odd perfect numbers.
There is a real sparsity heuristic here, but not a proof.
- Rigorous evidence: composite counterexamples, if any, are far sparser than Carmichael numbers.
- Heuristic: after forcing Carmichael structure, the extra congruences
  \[
  n/p\equiv 1\pmod p\quad(\forall p\mid n)
  \]
  behave like independent “probability \(1/p\)” conditions. Their simultaneous satisfaction should be extraordinarily rare.
- So the natural heuristic is not just “density \(0\)” but “possibly finite, maybe empty.”

Compared with odd perfect numbers:
- the Giuga-Agoh problem has a cleaner probabilistic heuristic for nonexistence,
- the odd perfect problem has deeper multiplicative structure but a less convincing random-model heuristic.
So Giuga-Agoh feels more “probably empty by randomness plus arithmetic rigidity,” while odd perfect numbers feel more “structurally overconstrained but not probabilistically modeled as sharply.”

Sources:
- [Agoh 1995, *On Giuga’s conjecture*](https://link.springer.com/article/10.1007/BF02570490)
- [Borwein-Borwein-Borwein-Girgensohn 1996, *Giuga’s Conjecture on Primality*](https://www.math.stonybrook.edu/~moira/mat331-spr10/papers/1996%20BorweinGiuga%27s%20Conjecture%20on%20Primality.pdf)
- [Tipu 2007, *A Note on Giuga’s Conjecture*](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/8A6841B3FDA442A8FAEC89AA702C16F6/S0008439500007244a.pdf/a-note-on-giugas-conjecture.pdf)
- [Luca-Pomerance-Shparlinski 2009, *On Giuga numbers*](https://math.dartmouth.edu/~carlp/PDF/Giuga10.pdf)
- [Borwein-Maitland-Skerritt 2013, *Computation of an Improved Lower Bound to Giuga’s Primality Conjecture*](https://www.emis.de/journals/INTEGERS/papers/n67/n67.pdf)

1. If useful, I can next write out the von Staudt-Clausen derivation in full.
2. Or I can sketch a research strategy focused on ruling out the simultaneous system \(p^2(p-1)\mid n-p\) for all \(p\mid n\).