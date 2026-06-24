As of **March 13, 2026**, the original Feit-Thompson divisibility conjecture
\[
\Phi_p(q)=\frac{q^p-1}{q-1}\nmid \Phi_q(p)=\frac{p^q-1}{p-1}
\]
for distinct odd primes \(p,q\) is still **open**. What Stephens disproved in **1971** was the stronger coprimality claim \(\gcd(\Phi_p(q),\Phi_q(p))=1\), via \((p,q)=(17,3313)\) and common factor \(112643=2pq+1\); he explicitly says the original divisibility conjecture remained unresolved.

For the **\(p=3\)** case, yes: it is **fully resolved**. If
\[
q^2+q+1=\Phi_3(q)\mid \frac{3^q-1}{2},
\]
then necessarily:
- \(q\equiv 2 \pmod 3\) (since \(q\equiv1\pmod3\) would force \(3\mid q^2+q+1\)),
- for every prime \(r\mid q^2+q+1\), one has \(\operatorname{ord}_r(q)=3\) and \(\operatorname{ord}_r(3)=q\),
- hence every such \(r\) satisfies \(r\equiv1\pmod{3q}\).

Those are strong local constraints, but Le proved in **2012** that they are never enough: for every odd prime \(q\neq 3\),
\[
q^2+q+1\nmid 3^q-1,
\]
which is exactly the \(p=3\) Feit-Thompson case.

Beyond computation, the verified peer-reviewed theoretical progress I could confirm is still quite limited:
- **Stephens (1971):** common-divisor structure; any common prime divisor \(r\) must satisfy \(r=2kpq+1\), and the stronger coprimality conjecture fails.
- **Motose (2009, 2010):** short partial-result notes.
- **Le (2012):** complete resolution of \(q=3\) / \(p=3\).
- A **2024 preprint** claims the twin-prime case, but it is **not peer reviewed**.

One correction: I could **not** verify the statement that Stephens checked all \(p,q<10^8\). His 1971 paper actually says he checked odd primes with \(p\le 443\), \(pq<200000\), and candidate common divisors \(r<400000\). Le cites an older computation of McKay for the \(p=3\) case up to \(53\times 10^6\), but that is different.

The clean number-theoretic core is this. If \(\Phi_p(q)\mid\Phi_q(p)\), then for **every** prime \(r\mid \Phi_p(q)\),
\[
\operatorname{ord}_r(q)=p,\qquad \operatorname{ord}_r(p)=q.
\]
So every prime divisor of \(\Phi_p(q)\) must lie in the very thin reciprocal-order set
\[
\mathcal C_{p,q}:=\{r\text{ prime}: \operatorname{ord}_r(q)=p,\ \operatorname{ord}_r(p)=q\}.
\]
That is the exact gap. All the congruence towers, residue arguments, power sums, and Fermat-quotient identities are **local filters** on \(\mathcal C_{p,q}\); what is still missing is a **global escape-prime theorem** showing that \(\Phi_p(q)\) always has at least one prime divisor outside \(\mathcal C_{p,q}\).

So the single structural result that would settle the conjecture is:

\[
\textit{For distinct odd primes }p,q,\ \Phi_p(q)\text{ has a prime divisor }r\text{ with }\operatorname{ord}_r(q)=p\text{ but }\operatorname{ord}_r(p)\neq q.
\]

That is the right abstraction. For \(p=3\), Le proved exactly this kind of statement.

The Wieferich/Fermat-quotient connection is at the level of **valuations**. Once a prime \(r\) divides both cyclotomic values, the question whether \(v_r(\Phi_q(p))\) is large enough to cover \(v_r(\Phi_p(q))\) is a Wieferich-type question: extra \(r\)-adic divisibility of \(p^q-1\) or \(q^p-1\) beyond the first power is controlled by Fermat quotients. Cyclotomically,
\[
\Phi_p(q)=N_{\mathbf Q(\zeta_p)/\mathbf Q}(q-\zeta_p),
\]
so the conjecture is naturally about simultaneous prime divisibility of two cyclotomic norms.

Sources:
- Stephens (1971): https://www.ams.org/mcom/1971-25-115/S0025-5718-1971-0297686-1/S0025-5718-1971-0297686-1.pdf
- Le (2012): https://intlpress.com/site/pub/files/_fulltext/journals/pamq/2012/0008/0003/PAMQ-2012-0008-0003-a005.pdf
- Schlage-Puchta on Peterfalvi’s 1984 simplification: https://mathoverflow.net/questions/281043/feit-thompson-conjecture
- Recent literature summary / twin-prime preprint status: https://www.preprints.org/manuscript/202403.1214

I could confirm the existence of Motose’s 2009/2010 papers, but I was not able to inspect their primary text directly here, so I have only treated them as partial results rather than attributing a sharper theorem statement.