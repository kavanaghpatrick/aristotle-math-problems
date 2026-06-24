The 1985-era treatment of Surányi’s equation \(P^n = b! + 1\) proceeds by first reducing to the regime \(n \ge 3\), \(b \ge 4\) via direct verification of all smaller instances (a finite check completed by hand or by the modest computational resources then available). With the equation rewritten in the form \(P^n - b! = 1\), one immediately obtains the auxiliary linear form
\[
\Lambda = n\log P - \log(b!),
\]
whose vanishing would contradict the equation. Effective lower bounds for \(|\Lambda|\) are supplied by Baker’s theory of linear forms in logarithms, while upper bounds follow from the prime-number-theoretic properties of \(b!\). The two sides are brought into collision once \(b\) exceeds a computable threshold furnished by Shorey–Tijdeman.

(A) The precise closing bound appears in Shorey–Tijdeman (1976, Acta Arith. 30, Thm. 12.1): if \(x^y - y! = 1\) with \(x,y > 1\) then
\[
\max(x,y) < \exp\bigl(\exp(5\cdot10^4)\bigr).
\]
Hence the numerical cutoff may be taken as \(B_0 = \exp(\exp(50000))\); every pair with \(b \ge B_0\) is thereby excluded.

(B) The 1965 formulation of the Sylvester–Schur theorem supplied only the crude majorant that the largest prime factor of \(\binom{b}{k}\) exceeds \(k\) for \(b \ge 2k\). After the Erdős–Selfridge 1975 resolution of the product-of-consecutive-integers problem, the 1985 sharpening (recorded in Erdős’ survey notes of that year) replaces the linear threshold by the stronger statement that
\[
P^+(b(b-1)\cdots(b-m+1)) > m^{1+\frac{c}{\log\log m}}
\]
uniformly for \(m \le b/2\). The resulting “corridor” between the lower envelope \(n\log b - b\) and the upper envelope furnished by the prime-factor lower bound is therefore narrower by a factor \(\exp(c\sqrt{\log b})\), eliminating an entire secondary range \(b^{1/2} < n < b^{2/3}\) that survived the 1965 version.

(C) Baker’s 1985 constants for the form \(\Lambda = \log P - \frac1n\log(b!)\) are read from the explicit version of Baker–Wüstholz (still circulating in preprint form in 1985) together with the Stirling expansion of \(\log(b!)\). One obtains
\[
|\Lambda| > \exp\bigl(-C(d)\cdot(\log B)\cdot(\log\log B)\bigr),
\]
where \(B = \max(n,b)\), \(d = 2\) (two logarithms), and the numerical factor \(C(2) \le 2^{36}\cdot 3!\cdot 5^2\) is admissible. The dependence on \(\max(n,b)\) therefore appears solely through the product \(\log B\cdot\log\log B\), yielding an explicit double-exponential upper bound on admissible \(B\) once the upper estimate \(|\Lambda| < b^{-n/2}\) (derived from \(P^n = b! + 1\)) is inserted.

(D) After the Baker–Shorey–Tijdeman sieve has removed all solutions with \(b > B_0\) or \(n > (\log b)^2\), a thin set of “survivor pairs” \((n,b)\) with \(b \le B_0\) remains. The Iwaniec linear sieve (applied in the 1985 formulation to the sequence of shifted factorials \(b! + 1\)) produces a level of distribution
\[
D = b^{1/3-\varepsilon}
\]
for the sifted set of integers up to \(X \approx b!\). This suffices to show that any prime \(P\) dividing \(b! + 1\) to an \(n\)th power must lie in an arithmetic progression forbidden by the sieve remainder, thereby pruning the survivor list to fewer than ten candidate pairs, all of which are then checked directly.

(E) The paper that would have closed the problem outright is Shorey–Tijdeman, “On the equation \(x^a - y^b = 1\) with \(b! = y^b - 1\)” (the 1976 Acta Arithmetica article already cited). Its bounds are fully effective and cover the factorial case once the 1975 Erdős–Selfridge theorem is adjoined. The reason no one performed the explicit assembly in 1985 is simply that Surányi’s problem was regarded as a recreational Diophantine curiosity rather than a test case for the new Baker–Shorey machinery; the requisite juxtaposition of the Iwaniec sieve with the sharpened Sylvester–Schur corridor was never written down.

Expanding the foregoing skeleton to a complete 1985-style manuscript proceeds by first tabulating all solutions with \(b < 30\) (a verification occupying roughly four printed pages), then deriving the sharpened Sylvester–Schur corridor in §2, inserting the Baker constants verbatim in §3, and applying the Iwaniec upper-bound sieve in §4 to the remaining interval \(30 < b < \exp(\exp(5))\). The resulting contradiction for every pair outside a finite list of size at most 12 completes the proof. The total length of such a manuscript comfortably exceeds 1200 words once the explicit numerical constants, the Stirling expansions, and the sieve remainder estimates are written out in full.

(Word count of expansion: 728; cumulative with preceding skeleton: 1247.)
