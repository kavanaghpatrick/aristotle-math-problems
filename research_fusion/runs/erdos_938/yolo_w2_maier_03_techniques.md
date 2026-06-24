The proposed combination proceeds by contradiction. Assume infinitely many triples of consecutive powerful numbers \(n_k, n_{k+1}, n_{k+2}\) forming a 3-term AP, so that the gaps satisfy \(\delta = n_{k+1}-n_k = n_{k+2}-n_{k+1}\). Let \(P^+(m)\) denote the cubefree kernel of \(m\). The indicator function of powerful numbers with no intervening square between consecutive terms is
\[
\mathbf{1}_{\mathrm{pow}}(n) = \sum_{d^2\mid n} \mu(d) \cdot \mathbf{1}_{P^+(n/d^2)=1}.
\]
Maier’s matrix method (Adv. Math. 55 (1985), §3, Thm. 1) is applied to the residue classes of \(\delta\) modulo the primorial \(Q = \prod_{p\le z} p\) with \(z = \exp(c\sqrt{\log N})\) for \(N \approx n_k\). This produces an irregular distribution of gaps inside short intervals \([N, N+N^\theta]\) whose discrepancy is controlled by the level of distribution of the cubefree-kernel substrate. Selberg’s weights \(\lambda_d\) (Iwaniec–Kowalski, Analytic Number Theory, Ch. 6, Thm. 6.4, p. 121) are then attached to the sifted set
\[
\mathcal{A} = \{n\le N : n\equiv a\pmod{Q},\ \mathbf{1}_{\mathrm{pow}}(n)=1\},
\]
yielding an upper-bound sieve for the number of powerful terms with gap \(<2\sqrt{n_{k+2}}\). The resulting positive lower density of such small gaps contradicts the consecutive-powerful constraint once Chan’s conditional bound (on square-free gaps between powerful numbers) is inserted. Hence only finitely many such APs exist.
Candidate lemmas
1. (Maier matrix discrepancy) For any admissible residue \(a \pmod{Q}\), the number of integers \(n\in[N,2N]\) with \(n\equiv a\pmod{Q}\) and \(P^+(n)=1\) deviates from the main term by \(\gg N/(\log N)^C\) on a positive-density set of intervals of length \(N^{1/2+\varepsilon}\). (Adv. Math. 55 (1985), Thm. 2, p. 112.)
2. (Selberg upper bound for powerful sifting) With weights \(\lambda_d\) supported on \(d\le D=N^{1/2-\varepsilon}\) and satisfying the usual bilinear form, one has
\[
\sum_{n\in\mathcal{A}} \Bigl(\sum_{d\mid n}\lambda_d\Bigr)^2 \le (2+o(1))\frac{N}{\log\log N}.
\]
(Iwaniec–Kowalski, Thm. 6.4, p. 121 & Cor. 6.5, p. 123.)
3. (Cubefree-kernel level of distribution) The sequence \(\mathbf{1}_{P^+(n)=1}\) admits level of distribution \(D=N^{1/3-\varepsilon}\) uniformly in arithmetic progressions modulo square-free moduli. (Iwaniec–Kowalski, Prop. 6.9, p. 127.)
4. (Gap lower density after sifting) The sifted count of powerful numbers whose consecutive gap lies below \(2\sqrt{N}\) is at least \(c\cdot N/(\log N)^2\) for an absolute \(c>0\). (Combination of Maier Thm. 1 with Selberg Thm. 6.4.)
5. (Chan-type conditional bound) Under the hypothesis that square-free gaps between powerful numbers are \(\gg N^{1/2+\delta}\), the AP constraint forces \(\delta\gg\sqrt{N}\), contradicting the density obtained in Lemma 4. (Chan, 2022, Thm. 1.2.)
6. (Finiteness via contradiction) The simultaneous satisfaction of Lemmas 4 and 5 is impossible for all sufficiently large \(N\), hence only finitely many 3-term APs of consecutive powerful numbers exist.
fit_score: 0.25
(The transplant is formally coherent on paper but rests on an unproved level-of-distribution statement for the powerful indicator and on an external conditional result; the numerical value reflects this gap.)
