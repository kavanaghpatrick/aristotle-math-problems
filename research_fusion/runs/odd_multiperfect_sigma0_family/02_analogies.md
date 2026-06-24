# Analogies — odd multiperfect σ₀ uniform family

## The cross-domain analog (load-bearing)

**Domain transplant:** the same uniform mod-p cyclotomic-polynomial barrier that closes Catalan's conjecture (Mihăilescu 2004, building on Cassels-Cassels) — namely "Φ_q(p) is a p-adic unit for all distinct primes p ≠ q" — is the exact barrier that powers slot 746. The Lean proof reads `σ(p^10) mod p = 1` because σ(p^10) = Φ_11(p), and Φ_11(p) ≡ 1 (mod p) since the constant term of Φ_11 is 1. Mihăilescu used the same identity Φ_q(p) ≡ 1 (mod p) (for all q prime ≠ p) as the load-bearing fact when he replaced cyclotomic units (x^q − 1)/(x − 1) into the Catalan factorization, getting an obstruction that is uniform in q for the q-th power side.

## Why the analog transplants uniformly to σ₀ ∈ {11, 13, 17, 19}

The Catalan barrier "Φ_q(p) ≡ 1 (mod p)" only depends on q being prime ≠ p. It is INDEPENDENT of the specific prime q. The transplant to σ-arithmetic preserves this q-independence: for ANY prime q ≠ p and any odd prime p, σ(p^(q-1)) = Φ_q(p) and Φ_q(p) ≡ 1 (mod p). Therefore the q ∈ {11, 13, 17, 19} family is closed by literally the same proof with q as a parameter.

This is qualitatively different from Beukers-Heckman or Brauer-Manin (which would require uniform monodromy or uniform Tate-Shafarevich vanishing, neither of which is supplied by elementary cyclotomic identities). It is also stronger than Skolem-Mahler-Lech (which only gives finiteness of solutions, not their non-existence for the explicit congruence). LTE is the wrong direction: LTE computes v_p(a^n − b^n) when p | a − b; here we want v_p(Φ_q(p)) when p ≠ q, which is 0, not ≥ 1.

## Failed parallels we explicitly avoid
- Beukers-Heckman (hypergeometric monodromy): the σ-arithmetic locus is not a hypergeometric local system. No transplant.
- Brauer-Manin: σ-arithmetic is a 0-dimensional sub-locus of N; there is no Brauer group to obstruct.
- Coates-Wiles Iwasawa: irrelevant; we have no elliptic curve or CM modular form.
- F2/em-tautology trap: we are proving an UNIFORM IMPOSSIBILITY, not "P ∨ ¬P". The statement is ∀ q ∈ {11,13,17,19}, ∀ n odd: σ₀(n) = q ⟹ ¬ multiperfect(n). Pure ∀-impossibility, no disjunction.

## Bridge lemma (one sentence)

For every odd prime q and every prime p ≠ q, the q-th cyclotomic polynomial Φ_q(p) = 1 + p + … + p^(q-1) is a p-adic unit (i.e. Φ_q(p) ≡ 1 mod p), and therefore for n = p^(q-1) odd we have v_p(σ(n)) = 0, which together with the multiperfect lift p^(q-1) | σ(n) ⟹ p | σ(n) yields a uniform contradiction in q over {11, 13, 17, 19}.
