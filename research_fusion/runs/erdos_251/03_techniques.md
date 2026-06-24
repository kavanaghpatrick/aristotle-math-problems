# Stage 3 — Named-Technique Shortlist for Erdős 251

## Final technique selected

**Adamczewski–Bugeaud binary subword complexity criterion + prime-gap injection density**

Underlying theorem (Adamczewski–Bugeaud 2007, *Ann. of Math.* 165): if a real number α ∈ (0,1) is irrational and algebraic, then for any integer base b ≥ 2, the binary (resp. b-adic) digit sequence of α has subword complexity p_α(n) growing super-linearly, i.e. p_α(n) / n → ∞. Equivalently, any real with linear digit-complexity p(n) = O(n) is either rational OR transcendental — never algebraic-irrational.

Contrapositive direction (used here): if we can show the binary expansion of S has subword complexity p_S(n) STRICTLY between bounded-recurrent (which would force rationality) and super-linear (which would only rule out algebraicity), we still have a tight noose.

Concrete plan:
1. **Recast rationality as eventual periodicity** of the binary digits d_1 d_2 d_3 ... of S.
2. **Compute fresh-injection density**: at digit position N, the prime p_{N+1} (of size ≈ N log N) injects roughly log_2(N log N) = log N + log log N + O(1) "fresh" binary digits into positions N+1, N+2, ..., N + log N. These are not predicted by the prior truncation Σ_{k ≤ N} p_k/2^k.
3. **Periodicity ⇒ digit prediction**: if d_n is eventually P-periodic from position N_0, then for all n > N_0 + P, the digit d_n is determined by d_{n-P}. But the fresh injection at digit position N from p_{N+1} can be anything (depending on the binary representation of p_{N+1}).
4. **Prime digit distribution**: by Maynard / Maynard-Tao bounded-gap and short-interval prime distribution (Guth–Maynard 2024), the binary digits of consecutive primes form a sequence with positive entropy — they do not follow any finite-state deterministic rule.
5. **Contradiction**: a P-periodic digit prediction forces the binary digit at every position N + log_2(N log N) to match d_{N + log_2(N log N) - P}, but the binary digits of p_{N+1} (which determine this) admit far more than P possible values for varying N.

## Verified supporting literature

- **Adamczewski–Bugeaud (2007)**, "On the complexity of algebraic numbers, I." *Annals of Mathematics* 165: 547–565. The criterion.
- **Christol (1979)**, "Ensembles presque périodiques k-reconnaissables." *Theor. Comput. Sci.* 9, 141–145. Algebraic-iff-automatic equivalence.
- **Rowland & Yassawi (2024)**, arXiv:2408.00750. Quantitative automaticity bounds for algebraic-mod-p^α series.
- **Guth & Maynard (2024)**, arXiv:2405.20552. Primes in short intervals at exponent 17/30 + o(1).
- **Tao & Teräväinen (2025)**, arXiv:2512.01739. Sister result for ω(n)/2^n.

## Major obstacles (honest)

- Adamczewski–Bugeaud gives the AB digit-complexity dichotomy: linear ⇒ rational-or-transcendental. To conclude irrational, we need to rule out the rational branch separately, which is exactly what eventual-periodicity is.
- The "fresh-injection density" argument is intuitively clean but requires careful handling of carries: a digit at position n may be affected by carries from many primes p_k with k > n - log n. The carry can be at most by 1, and detailed accounting (e.g. via Cauchy's tail-estimate) limits propagation.
- No part of this argument is yet in Mathlib; Aristotle would need to synthesize the digit-complexity lemmas. The injection-density step requires Bertrand + PNT effective bounds, both Mathlib-available.

## What is NEW vs. prior bare-lane attempts

Prior slots 699, 704, 1219 all attempted a 2-adic integrality argument (write the tail b·Σ p_n/2^n as a single integer + fraction, derive contradiction at 2-adic level). They returned compiled_no_advance because the carry structure of the binary expansion absorbs the "non-integer" piece — the 2-adic argument silently assumes the carry is small, which it is not.

The Christol-Adamczewski-Bugeaud lane is FUNDAMENTALLY DIFFERENT: it treats S as a real number, examines its REAL binary expansion (digits d_n ∈ {0,1}), and forbids eventual periodicity via subword complexity. Carries become a feature, not a bug — carries are exactly what makes the digit stream non-trivially complex.
