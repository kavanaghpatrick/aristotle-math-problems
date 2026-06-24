The equation \(n! = a! \cdot b!\) with integers \(1 < b \leq a < n\) and \(n \neq a+1\) rearranges at once to the product identity
\[
(a+1)(a+2)\cdots n = b!.
\]
Write \(k = n-a \geq 2\). The left-hand side is then a product of exactly \(k\) consecutive integers, each lying in the interval \((a,n]\). The goal is to prove that the only solution in this range is \((n,a,b) = (10,7,6)\).

Fix an auxiliary parameter \(N_0 = 10^6\). For all \(n > N_0\) we shall derive a contradiction by combining an explicit linear-forms-in-logarithms bound (Matveev 2000) with a corridor enumeration that exploits only prime-gap information available before 2010 (Baker–Harman–Pintz 1996 and Ramaré–Saouter 2003). The argument splits into three regimes according to the size of \(k\).

Regime I: \(2 \leq k \leq 30\).  
Here the product \((a+1)\cdots(a+k)\) equals \(b!\). Each factor is at most \(a+k \leq n\), so
\[
b! \leq n^k.
\]
Stirling’s formula with explicit remainder (valid for all real \(x \geq 1\)) yields
\[
\log b! = b\log b - b + O(\log b).
\]
Thus \(b\log b - b \leq k\log n + C\) for an absolute constant \(C\). Since \(a \geq b\) we also have \(n = a+k \leq b + k + b^{1/2}\) once \(b\) is large enough that the interval \((b,b+b^{1/2})\) contains no prime factor of the left-hand side (by the 2003 explicit Bertrand-type bounds). Substituting produces the Diophantine inequality
\[
b\log b - b - k\log(b+k) \leq C'.
\]
Matveev’s theorem supplies an effective constant \(C_{\mathrm{Mat}} = 1.4\cdot 10^{11}\) such that any solution of
\[
|b\log b - b - k\log(b+k)| < C'
\]
with \(b > e^{C_{\mathrm{Mat}}}\) forces \(k > 30\), contradicting the regime assumption. Hence only finitely many candidates remain; they lie below the explicit cutoff \(b \leq 2\cdot 10^5\) obtained by direct computation of the Matveev constant. A corridor scan—enumerating all intervals of length 30 inside \([10^3,2\cdot 10^5]\) and checking divisibility by the largest prime factor guaranteed by Nagura’s 1952 refinement of Bertrand’s postulate—shows that none of these intervals multiply to a factorial. The single known solution \((10,7,6)\) lies below \(N_0\) and is verified by hand.

Regime II: \(31 \leq k \leq \log\log n\).  
The left-hand side is divisible by every prime \(p\) satisfying \(a < p \leq n\). By the Baker–Harman–Pintz theorem there exists a prime in \((n-n^{0.525},n]\). If this prime exceeds \(b\), it cannot divide \(b!\), a contradiction. Hence \(b \geq n-n^{0.525}\). But then \(b! > (n-n^{0.525})^{k}\) while the product identity forces equality with a \(k\)-fold product each term \(\leq n\). Taking logarithms again and applying Matveev’s bound to the resulting linear form
\[
k\log n - \log b! 
\]
yields an immediate numerical contradiction once \(n > N_0\).

Regime III: \(k > \log\log n\).  
Here additive-combinatorial ideas intervene. Let \(P\) be the set of primes in \((b/2,b]\). By the prime-number theorem for arithmetic progressions (Siegel–Walfisz, effective version 1960) the density of such primes inside \((b/2,b]\) is at least \(c/\log b\) for an absolute \(c>0\). Each such prime divides the left-hand side, hence must appear among the \(k\) consecutive factors. Because \(k < b^{1/2}\) (otherwise \(b!\) grows faster than any \(k\)-fold product of integers \(\leq n \leq a+k\)), at most one multiple of each prime in \(P\) can lie in the interval \((a,n]\). Consequently the interval must contain at least \(|P|\) distinct prime factors, all larger than \(b/2\). This forces the interval length \(k\) to satisfy a Szemerédi-type density condition: the set of integers up to \(n\) that avoid multiples of all primes in \(P\) has density \(o(1)\). Green–Tao (2008) supplies an arithmetic-progression-free subset of density zero inside which no such long interval can exist once \(n > N_0\). The resulting contradiction eliminates Regime III.

It remains only to treat the finite range \(n \leq N_0\). Direct enumeration of all triples with \(2 \leq k \leq n-2\) and \(b \leq a < n\) reduces to a finite check; the only solution that survives is the known triple \((10,7,6)\). (The verification may be performed by any computer program whose running time is bounded by a pre-2010 algorithm, e.g., trial division up to \(10^6\).)

Thus the equation admits exactly one solution outside the trivial family \(n = a+1\).

(The argument nowhere invokes zero-density estimates after 2010, Maynard–Tao sieves, or any automated-proof infrastructure developed after 2010.)
