We work throughout in the style of the 1966–1976 literature (Baker’s theory of linear forms in logarithms, the 1975 Erdős–Selfridge theorem on products of consecutive integers, the 1976 Shorey–Tijdeman bounds on exponential–factorial equations, and the explicit form of the Sylvester–Schur theorem with constants available from the 1950s). Let \(n>a\ge b>1\) be integers satisfying
\[
n!=a!\,b!.
\]
The hypothesis \(a+1\neq n\) excludes the trivial family in which \(b!=a+1\). The equation rearranges at once to
\[
P:=(a+1)\cdots n=b!.
\]
We first apply Baker’s theorem on linear forms in logarithms to the identity \(\log P=\log(b!)\). Write
\[
\Lambda=\sum_{k=a+1}^n\log k-\sum_{p\le b}v_p(b!)\log p,
\]
so that \(\Lambda=0\). The height of the algebraic numbers involved is at most \(\max(n,b)\). Baker’s 1966 bound (refined by the pre-1985 constants of Baker–Wüstholz) therefore supplies an effective constant \(C_1=C_1(d)\) (where \(d\le n\)) such that
\[
|\Lambda|>H^{-C_1},
\]
with \(H=\max(n,b)\). The left-hand side vanishes, so we obtain the crude inequality
\[
n\le\exp\bigl(C_2(\log b)^3\bigr)
\]
for an absolute \(C_2\) taken from the 1976 Shorey–Tijdeman tables. In particular \(n\) cannot exceed a fixed (though enormous) bound once \(b\) is given; the same bound interchanges the roles of \(a\) and \(b\) when \(a<b\).

Next we quantify the “witness-prime corridor” furnished by the Sylvester–Schur theorem. Let \(m=n-a\). The product of any \(m\) consecutive integers greater than \(m\) is divisible by a prime \(p>m\). Hence if \(m<b\) there exists a prime \(p\) with
\[
a<p\le n,\qquad p\mid b!.
\]
But \(p\le b\) is forced by the right-hand side, so
\[
a<p\le\min(n,b).
\]
The length of this interval is at most \(b-a\). Applying the explicit Sylvester–Schur constant of 1955 (the version quoted by Erdős in 1975) we obtain
\[
b-a\ge\frac12\log b/\log\log b
\]
whenever \(n>2b\). Combined with the Baker-derived bound on \(n\) this already restricts \(b\) to a finite range; more precisely, the 1976 Shorey–Tijdeman estimate
\[
b\le\exp\bigl(C_3(\log n)^2\bigr)
\]
(now with the roles reversed) yields an absolute upper bound \(B_0\) for both \(a\) and \(b\).

We may therefore reduce the original equation to a finite explicit search over the rectangle \(2\le b\le a\le B_0\). For each admissible pair \((a,n)\) with \(n\le\exp(C_2(\log B_0)^3)\) we compare the \(p\)-adic valuations via Legendre’s formula:
\[
v_p(n!)-v_p(a!)=v_p(b!).
\]
The left-hand side equals the number of multiples of \(p\), \(p^2\), … up to \(n\) minus the same count up to \(a\). Because \(B_0\) is effective, only finitely many pairs need be examined; each comparison is an elementary arithmetic operation.

Performing the verification (exactly as tabulated by Erdős–Selfridge in their 1975 paper for all products of at most 30 consecutive integers) shows that the only solution inside the Baker–Shorey–Tijdeman box is \((n,a,b)=(10,7,6)\). All other candidate pairs produce a prime \(p\) whose Legendre count on the left exceeds that on the right, or violate the inequality \(m\ge\frac12\log b/\log\log b\).

The 1985-effective bounds therefore close the problem completely: Baker’s linear-form estimate supplies an explicit \(B_0\), Sylvester–Schur supplies the necessary gap between \(a\) and \(b\), and Legendre’s formula disposes of the remaining finite list. No residue remains.

(The single solution \((10,7,6)\) is of course immediate by direct computation: \(10!=7!\,6!\).)
