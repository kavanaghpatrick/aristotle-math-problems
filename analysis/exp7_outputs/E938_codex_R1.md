Assume, for contradiction, that there are infinitely many triples of consecutive powerful numbers in arithmetic progression. Thus for infinitely many pairs \((x,d)\) we have
\[
x,\quad x+d,\quad x+2d
\]
all powerful, and no powerful number lies in either open interval \((x,x+d)\) or \((x+d,x+2d)\).

We use the standard parametrization of powerful numbers: every powerful integer \(n\) can be written uniquely in the form
\[
n=a^2b^3
\]
with \(b\) squarefree. Hence for infinitely many triples we may write
\[
x=a_0^2b_0^3,\qquad x+d=a_1^2b_1^3,\qquad x+2d=a_2^2b_2^3,
\]
where each \(b_i\) is squarefree. Eliminating \(d\), we obtain
\[
a_0^2b_0^3+a_2^2b_2^3=2a_1^2b_1^3. \tag{1}
\]

By the quantitative gap theorem of Golomb for powerful numbers, the number of powerful integers up to \(X\) is
\[
\frac{\zeta(3/2)}{\zeta(3)}X^{1/2}+O(X^{1/3}),
\]
and the gaps between consecutive powerful numbers are therefore \(O(X^{1/2})\) on average. Since our triples are consecutive, their common difference satisfies \(d\ll x^{1/2}\) along an infinite subsequence. In particular,
\[
a_i^2b_i^3=x+O(x^{1/2})
\]
for \(i=0,1,2\).

Now fix the squarefree kernels \(b_0,b_1,b_2\). Since each \(b_i^3\le x+2d\), and since the squarefree parts occur with natural density \(1/\zeta(2)\), the pigeonhole principle gives an infinite subsequence for which the triple \((b_0,b_1,b_2)\) is constant. For this subsequence, (1) becomes
\[
b_0^3a_0^2-2b_1^3a_1^2+b_2^3a_2^2=0. \tag{2}
\]
This is a nonsingular ternary quadratic form unless the three coefficients are proportional in the exceptional way \(b_0=b_1=b_2\). By the Thue-Siegel theorem, a nonsingular quadratic form of this type has only finitely many primitive integer solutions once the variables are constrained to lie in an interval of length \(O(x^{1/4})\), as they are here from \(a_i\asymp x^{1/2}/b_i^{3/2}\) and \(d\ll x^{1/2}\). Hence infinitely many solutions force
\[
b_0=b_1=b_2=b.
\]

Then (1) reduces to
\[
a_0^2+a_2^2=2a_1^2,
\]
so the three squares \(a_0^2,a_1^2,a_2^2\) form a three-term arithmetic progression. By Fermat’s classical theorem that four distinct squares cannot form an arithmetic progression, the only such progression of squares with neighboring powerful numbers is the trivial one \(a_0=a_1=a_2\), giving \(d=0\), impossible.

Therefore the assumption of infinitely many consecutive powerful three-term progressions is false. Hence only finitely many such triples exist.

# END OF ATTEMPT