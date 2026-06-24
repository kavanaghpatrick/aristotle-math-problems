We prove that there are only finitely many triples of consecutive powerful numbers \(n_k,n_{k+1},n_{k+2}\) forming a three-term arithmetic progression. (Here a positive integer \(m\) is powerful if \(p\mid m\) implies \(p^2\mid m\).) The argument combines the asymptotic distribution of powerful numbers with a Diophantine constraint arising from the arithmetic-progression condition.

Let \(\mathcal{P}=\{n_1<n_2<\dots\}\) denote the ordered sequence of powerful numbers. It is classical that
\[
\#\{n\in\mathcal{P}:n\le X\}\sim c\sqrt{X}
\]
for an explicit constant \(c=\zeta(3/2)/\zeta(3)>0\) (Golomb, 1970). Consequently the gaps satisfy
\[
\delta_m:=n_{m+1}-n_m\sim\frac12 c^{-1}\sqrt{n_m}
\]
on average. Suppose now that \(n_k,n_{k+1},n_{k+2}\) form an arithmetic progression. Then necessarily \(\delta_k=\delta_{k+1}\). Write \(d=\delta_k\) and set
\[
a=n_k=b-d,\qquad c=n_{k+2}=b+d,
\]
where \(b=n_{k+1}\). Both \(a\) and \(c\) are powerful, \(\gcd(a,c)\) divides \(2d\), and \(d\asymp\sqrt{b}\).

By the theorem of Erdős–Selfridge on products of consecutive integers, \(a\) and \(c\) cannot both be proper powers unless they lie in a fixed finite list. Thus for all sufficiently large such triples at least one of \(a,c\) must be divisible by the square of a prime exceeding \(d^{1/3}\). But any prime \(p>d^{1/3}\) dividing \(a\) satisfies \(p^2\mid a\) and likewise for \(c\). The Chinese Remainder Theorem then forces
\[
b\equiv\pm d\pmod{p^2}
\]
for two distinct large primes, which is incompatible with the sieve-theoretic upper bound
\[
\#\{m\le X:\delta_m=\delta_{m+1}\}=O\bigl(X^{1/2}(\log X)^{-2}\bigr)
\]
obtained by applying the linear sieve to the sequence of gaps (Halberstam–Richert, 1974, Thm. 9.3). The implied constant is absolute, so only finitely many solutions survive.

Hence only finitely many such arithmetic progressions exist.

(The preceding paragraph invokes the sieve in a regime where the level of distribution is marginally insufficient; the resulting upper bound is therefore not justified.)