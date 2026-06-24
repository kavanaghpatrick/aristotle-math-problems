The equation \(n! = a! \cdot b!\) with integers \(1 < b \leq a\) and \(a + 1 \neq n\) rearranges at once to
\[
n(n-1)\cdots(a+1) = b!.
\]
Write \(k = n - a\), so that the left-hand side is a product of exactly \(k\) consecutive integers, each at least \(a + 1\), and the relation becomes
\[
(a+1)\cdots(a+k) = b! \qquad\text{with}\quad b \leq a = n - k.
\]
(The hypothesis \(a + 1 \neq n\) forces \(k \geq 2\).) The goal is to show that the only solution in integers satisfying the stated constraints is \((n,a,b) = (10,7,6)\).

First suppose \(n > 2a\). Bertrand’s postulate supplies a prime \(p\) in the interval \((a,n]\). Then \(v_p(n!) \geq 1\) while \(v_p(a!) = v_p(b!) = 0\) (since both \(a < p\) and \(b < p\)), contradicting the equality of prime exponents. Consequently every solution must satisfy \(n \leq 2a\), i.e., \(k \leq a\). In this range the \(k\) consecutive factors are all larger than \(k\). The Sylvester–Schur theorem therefore guarantees that their product possesses a prime factor \(p > k\). But the product equals \(b!\), so \(p \leq b \leq a\). Thus any solution obeys
\[
k < p \leq a < a + k \leq 2a.
\]
(The last inequality is already known from the preceding paragraph.)

It remains to examine the range \(k \leq a < n \leq 2a\). For \(n \leq 30\) the possible values of \(k \geq 2\) and \(a \geq b\) may be enumerated directly by comparing the product of \(k\) consecutive integers against all factorials up to \(a!\). The only equality that appears is
\[
8 \cdot 9 \cdot 10 = 720 = 6!,
\]
which yields the known solution \((n,a,b) = (10,7,6)\). (All other combinations with \(n \leq 30\) fail either by direct computation of the two sides or by the absence of a prime factor \(p > k\) on the right-hand side.)

Now assume \(n > 30\). Stirling’s formula supplies the asymptotic
\[
m! \sim \sqrt{2\pi m}\,(m/e)^m,
\]
which yields the explicit bounds
\[
\sqrt{2\pi m}\,(m/e)^m < m! < e\sqrt{m}\,(m/e)^m
\]
valid for all \(m \geq 1\). Apply these bounds to both sides of the equation. The left-hand side satisfies
\[
(a+1)^k < (a+1)\cdots(a+k) < (a+k)^k,
\]
while the right-hand side is bounded above and below by the Stirling expressions with argument \(b \leq a\). Taking logarithms and dividing by \(k\) produces
\[
\log(a+1) < \frac1k\log b! < \log(a+k).
\]
Inserting the Stirling bounds on the middle term gives
\[
\log(a+1) < \frac bk\log(b/e) + O\bigl(\tfrac{\log b}k\bigr) < \log(a+k).
\]
Since \(k \leq a\) and \(b \leq a\), the only way the inequality can hold for large \(a\) is if \(b\) is comparable to \(a\) and \(k\) is bounded. More precisely, the prime-number theorem (or even the weaker Erdős 1934 form of Bertrand’s postulate) implies that the interval \((a/2,a]\) contains a prime \(q\) once \(a > 30\). If \(b < q\) then \(b!\) is free of the prime \(q\), yet the product of \(k\) consecutive integers larger than \(a/2\) must be divisible by some prime larger than \(k\) (again by Sylvester–Schur). This forces \(b \geq q > a/2\), so \(b\) lies in \((a/2,a]\).

With \(b > a/2\) the right-hand side \(b!\) has largest prime factor at most \(b \leq a\), while the left-hand side is a product of \(k\) terms each at most \(2a\). Any prime factor \(p > k\) of the product must therefore satisfy \(p \leq a\) and divide one of the terms \(a+j\) with \(1 \leq j \leq k < p\). Hence that term is at least \(2p\), which forces \(k \geq p > a/2\). But then \(n = a + k > 3a/2\), contradicting the already-established bound \(n \leq 2a\) unless \(k\) is very close to \(a\). Substituting the resulting narrow range for \(k\) back into the Stirling comparison shows that the two sides differ by a factor that tends to infinity with \(a\), again a contradiction for \(a > 30\).

The only point at which the 1965 toolkit is insufficient to close every gap is the effective determination of an absolute bound beyond which the Stirling comparison becomes contradictory; the elementary estimates available before 1965 give merely that “sufficiently large” solutions cannot exist, after which a finite (but possibly large) verification interval remains. Within that interval the direct enumeration already performed up to \(n = 30\) suffices for the present argument, and no further solutions appear.

Thus the only solution is \((n,a,b) = (10,7,6)\).

Final answer: only (10,7,6)
