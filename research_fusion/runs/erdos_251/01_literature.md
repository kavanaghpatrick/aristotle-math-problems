# Stage 1 — Literature for Erdős 251 (Σ p_n / 2^n irrational)

## Verified primary sources

1. **Erdős, P. (1948)**. "Some unsolved problems." *Mich. Math. J.* — proved Σ d(n)/t^n irrational for integer t ≥ 2. Posed the analogous question for σ, φ, ω, and the n-th prime function.

2. **Erdős, P. (1988c)**. Mentions Σ p_n^k / 2^n as a conjectured irrational for every k ≥ 1.

3. **Tao, T. & Teräväinen, J. (December 2025)**. "Quantitative correlations and some problems on prime factors of consecutive integers." arXiv:2512.01739. UNCONDITIONALLY settles Σ ω(n)/2^n irrational via two-point correlations of multiplicative functions + probabilistic method. Erdős 257.

4. **Pratt, K. (September 2024)**. "The irrationality of a prime factor series under a prime tuples conjecture." arXiv:2409.15185. CONDITIONAL proof of Σ ω(n)/2^n via prime k-tuples.

5. **Guth, L. & Maynard, J. (May 2024)**. "New large value estimates for Dirichlet polynomials." arXiv:2405.20552. Primes in short intervals at exponent 17/30 + ε; updated zero-density estimate N(σ,T) ≪ T^{30(1-σ)/13+o(1)}.

6. **Adamczewski, B. & Bugeaud, Y. (2007)**. "On the complexity of algebraic numbers, I. Expansions in integer bases." *Ann. of Math.* 165, 547–565. Established: if S is irrational and algebraic, its base-b expansion cannot be too simple (complexity must grow super-linearly).

7. **Christol, G. (1979)**. "Ensembles presque périodiques k-reconnaissables." *Theor. Comput. Sci.* 9. Characterized algebraic formal power series over F_p as exactly the p-automatic ones.

8. **Rowland, E. & Yassawi, R. (August 2024)**. "Algebraic power series and their automatic complexity modulo prime powers." arXiv:2408.00750. Improves automaton-size bounds for algebraic-sequence reductions modulo p^α; provides QUANTITATIVE Christol.

## Known partial results on E251 itself

- Convergence: trivial via Bertrand p_n ≤ 2^{n+1}, so Σ p_n/2^n converges.
- OEIS A098990: decimal expansion of the constant.
- Erdős noted that "φ(n), σ(n), and ω(n)" cases seem "to present difficulties" — by analogy, the n-th prime case is HARDER, since n ↦ p_n is not multiplicative.

## Why prior 2-adic bare-lane attempts fail (audit of slots 699, 704, 1219)

The bare-lane integrality argument assumes: if S = a/b with 2 ∤ b' (the odd part of b), then b' Σ_{n > N} p_n · 2^{N-n} must be an integer. But b' · p_{N+1}/2 has denominator 2 (since p_{N+1} odd), and b' · p_{N+2}/4 + ... contributes a value in (0, b' · p_{N+2}/2). This LOCAL parity argument FAILS because the long-range carry sum Σ_{k ≥ 2} b' · p_{N+k} · 2^{-k} can absorb the half-integer via integer carries from higher places — the truncation/integrality logic of slots 699/704 silently assumes the tail series is bounded below 1, which is false (p_{N+k}/2^k grows in real terms before exponential decay dominates around k ~ N).
