Here is the clean picture.

1. The `a=0` classification does extend, and points 3-4 are special cases of the same lemma. For fixed `m` and primes `p` with `p ∤ m`,
   `phi(mp) = phi(m)(p-1)` and
   `mp + a = m(p-1) + (m+a)`.
   So if `phi(mp) | (mp+a)`, then in particular `p-1 | (m+a)`. For infinitely many primes `p`, this forces `m+a=0`. Then the condition becomes `phi(m) | m`. Since `phi(m) | m` iff `m = 2^alpha 3^beta`, we get:
   for every `a = -2^alpha 3^beta` with `alpha+beta>0`, there are infinitely many composite solutions, namely
   `n = 2^alpha 3^beta p`.
   This unifies `a=-2`, `a=-4`, `a=-6`, etc. The exceptional missing case is `a=-1`: there `m=1`, and this construction gives only primes.

2. The `a=-1` case is Lehmer’s totient problem, and it is still open as of March 13, 2026. Known facts:
   `n` must be odd, squarefree, and Carmichael.
   Lehmer (1932): `omega(n) >= 7`.
   Cohen-Hagis (1980): `n > 10^20` and `omega(n) >= 14`.
   Pomerance (1977): the number of composite `n <= x` with `phi(n) | (n-1)` is `O(x^(1/2) (log x)^(3/4))`.
   Luca-Pomerance (2011): improved to `x^(1/2) / (log x)^(1/2+o(1))`.
   Burcsi-Czirbusz-Farkas (2011): if `3 | n`, then `omega(n) >= 40,000,000` and `n > 10^(360,000,000)`.
   There is also a computational note of Pinch claiming no example below `10^30` and hence `omega(n) >= 15`; that claim is widely quoted, but the classical journal bounds are the ones above.

3. Your prime observation is exactly right, and it generalizes: for any fixed `m`, the family `n=mp` can be infinite only for the negative shift `a=-m`, and then only when `phi(m)|m`. So the only “one free prime” infinite families are precisely the `a=-2^alpha 3^beta` ones.

4. `n=2p` is just the case `m=2` of the previous lemma. Likewise `n=4p`, `6p`, `12p`, etc. So points 3 and 4 are not isolated tricks; they are the full fixed-base mechanism.

5. `n=pq` does not give infinite families. Indeed
   `phi(pq) = (p-1)(q-1)`,
   and
   `pq + a = (p-1)(q-1) + (p+q+a-1)`,
   so
   `(p-1)(q-1) | (p+q+a-1)`.
   The left side is size `~pq`, the right side size `~p+q`, so only finitely many semiprime solutions for each fixed `a`.
   In fact Pomerance proved more: after removing the trivial `mp` families above, if `omega(n)=K` is fixed, then `n` is bounded in terms of `a` and `K`. So no infinite family with bounded `omega(n)` can exist. Any genuinely new infinite family would have to satisfy `omega(n) -> infinity`.

6. So “make `phi(n)` small” is not the real issue. The obstruction is valuation overlap. For squarefree `n = prod p_i`,
   `lambda(n) = lcm(p_i-1)`,
   `phi(n) = prod (p_i-1)`.
   Korselt/Carmichael only asks for the lcm to divide `n-1`. Your problem asks for the full product to divide `n+a`. In `q`-adic terms, it replaces
   `v_q(lambda(n)) = max_i v_q(p_i-1)`
   by
   `v_q(phi(n)) = sum_i v_q(p_i-1)`.
   That sum-vs-max jump is the hard part. Mertens helps with size, but not with these exact divisibility requirements.

7. The Giuga/Agoh connection is through Carmichael numbers. Lehmer implies Carmichael because `lambda(n) | phi(n) | (n-1)`. A composite Agoh-Giuga counterexample is also Carmichael, but with a different extra condition: the Giuga congruences `p | (n/p - 1)` for every `p|n`. So both problems live inside the Carmichael world, but Lehmer strengthens `lambda(n)|(n-1)` to `phi(n)|(n-1)`, while Giuga adds different local congruences. They are related, but neither directly reduces to the other.

One extra positive-shift example is worth keeping in mind: if `F_i = 2^(2^i)+1` are prime for `i<k`, then
`n = prod_{i<k} F_i = F_k - 2`
satisfies `phi(n) | (n+1)`. This gives the known `a=1` examples `15, 255, 65535, 4294967295`, but not an infinite family unless one had infinitely many suitable Fermat primes.

So the present state is:
- Proven infinite families for `a = -2^alpha 3^beta`, `alpha+beta>0`.
- `a=-1` is exactly Lehmer and remains open.
- No bounded-`omega` construction can give infinitely many nontrivial solutions for any other fixed shift.
- Any new infinite family would have to be highly composite, very sparse, and Carmichael-like.

Sources: [Erdos Problem 828](https://www.erdosproblems.com/828), [Pomerance 1977](https://math.dartmouth.edu/~carlp/PDF/paper15.pdf), [Luca-Pomerance 2011](https://math.dartmouth.edu/~carlp/Lehmer0.5.pdf), [Burcsi-Czirbusz-Farkas 2011](https://ac.inf.elte.hu/Vol_035_2011/doi/043_35.pdf), [Pinch 2006 poster](https://antsmath.org/ANTSVII/Poster/Pinch_Poster3.pdf), [Agoh 1995](https://eudml.org/doc/156103), [Tipu 2007](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/8A6841B3FDA442A8FAEC89AA702C16F6/S0008439500007244a.pdf/note_on_giugas_conjecture.pdf).