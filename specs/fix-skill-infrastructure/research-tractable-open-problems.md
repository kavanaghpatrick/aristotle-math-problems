---
spec: tractable-open-problems
phase: research
created: 2026-03-13
---

# Research: Tractable Open Problems for Aristotle

## Executive Summary

Surveyed erdosproblems.com (1183 problems, 491 solved), Google DeepMind formal-conjectures (400+ formalized Erdos statements), Ben Green's 100 open problems, and recent breakthroughs. Identified 12 candidates ranked by tractability. **Best bets are problems where (a) specific small cases remain open with k-1 cases proved, (b) the statement is already formalized in Lean, and (c) Mathlib has the prerequisite infrastructure (arithmetic functions, divisor sums, totient, Catalan numbers, etc.).**

Key finding: Problems already attempted by this project (251, 252, 389, 412, 470, 672, 850) have had minimal success. Fresh targets below prioritize DIFFERENT problem families not yet tried.

---

## Candidate Rankings

### TIER 1: Best Tractability (narrow gap, good Mathlib coverage, formalized)

#### 1. Erdos #252 -- sigma_k(n)/n! irrationality for k >= 5

| Aspect | Detail |
|--------|--------|
| Statement | Is sum_{n>=1} sigma_k(n)/n! irrational for all k >= 1? |
| Status | OPEN for k >= 5. Proved for k=1,2 (Erdos), k=3 (Schlage-Puchta 2006), k=4 (Pratt 2022) |
| Why tractable | k=5 is the frontier. Each new k used similar techniques (prime gap estimates + divisor sum asymptotics). Pattern is clear. |
| Conditional | FULLY proved under Schinzel's conjecture or Dickson's conjecture |
| Mathlib | sigma_k defined in `Mathlib.NumberTheory.ArithmeticFunction`. Factorial in `Mathlib.Data.Nat.Factorial`. Irrational API exists. |
| Formalized | Yes, in formal-conjectures: `erdos_252_sum k = sum' n, sigma k n / (n! : R)` |
| Prior attempts | 1 submission (bare gap). No context resubmission yet. |
| Risk | Medium. k=4 proof (Pratt 2022) may require techniques beyond Aristotle's reach. |

**Recommendation**: Resubmit targeting k=5 specifically, with Pratt's k=4 method as context.

---

#### 2. Erdos #672 -- AP products not perfect powers, k >= 35

| Aspect | Detail |
|--------|--------|
| Statement | Product of k terms in AP (coprime gcd) cannot be a perfect l-th power, k >= 4, l >= 2 |
| Status | OPEN. Proved for k <= 34 (Gyory-Hajdu-Pinter). Also proved for sufficiently large k with l > e^{10^k} prime (Bennett-Siksek) |
| Why tractable | The gap is k=35 onward. Methods for k <= 34 are incremental (each step extends prior). k=35 might yield to same methods. |
| Mathlib | Products over Finset, coprimality, prime power definitions all exist. |
| Formalized | Yes, `Erdos672With k l` in formal-conjectures |
| Prior attempts | ~8 submissions, all compiled clean but 0 proven. Mostly bare gap or l=3 specific. |
| Risk | High. The incremental proofs are increasingly computational. |

**Recommendation**: Target k=35, l=2 specifically (square case is historically easier). Reference Bennett-Bruin-Gyory-Hajdu methods.

---

#### 3. Erdos #396 -- Descending factorial divides C(2n,n)

| Aspect | Detail |
|--------|--------|
| Statement | For every k, does there exist n such that prod_{i=0}^{k} (n-i) divides C(2n,n)? |
| Status | OPEN. Pomerance (2014) proved infinitely many n have (n-k) | C(2n,n) for any fixed k. The set of n with prod_{i=1}^{k}(n+i) | C(2n,n) has density 1. |
| Why tractable | Density-1 result for the "ascending" variant is proved. The descending variant needs extending techniques. Catalan numbers C(2n,n)/(n+1) are well-studied. |
| Mathlib | Catalan numbers defined. Binomial coefficients in `Mathlib.Data.Nat.Choose`. Divisibility API extensive. |
| Formalized | Yes, in formal-conjectures. OEIS A375077 has small cases. |
| Prior attempts | 1 submission (bare gap). |
| Risk | Medium. The product divisibility is delicate but infrastructure exists. |

---

#### 4. Erdos #1063 -- Estimate n_k (divisibility of C(n,k))

| Aspect | Detail |
|--------|--------|
| Statement | n_k = smallest n >= 2k such that n-i divides C(n,k) for all but one 0 <= i < k. Estimate n_k. |
| Status | OPEN. Known: n_2=4, n_3=6, n_4=9, n_5=12. Upper bound n_k <= k*lcm(2,...,k-1) <= e^{(1+o(1))k}. |
| Why tractable | Small cases computed. Upper bound established. Proving tighter asymptotics or specific values could work. |
| Mathlib | Binomial coefficients, LCM, divisibility all available. |
| Formalized | Yes, in formal-conjectures. OEIS A389360. |
| Prior attempts | NONE. Fresh target. |
| Risk | Low-Medium. Specific case computations are verifiable. |

**Recommendation**: High priority fresh target. State as "prove n_k <= f(k) for explicit f" or prove specific n_6, n_7 values.

---

### TIER 2: Good Potential (formalized, but wider gap)

#### 5. Erdos #301 -- Maximum subset avoiding unit fraction decomposition

| Aspect | Detail |
|--------|--------|
| Statement | f(N) = max |A subset {1,...,N}| with no 1/a = 1/b1 + ... + 1/bk. Is f(N) = (1/2+o(1))N? |
| Status | OPEN. Lower bound f(N) >= N/2 (trivial: take (N/2, N]). Upper bound f(N) <= (25/28+o(1))N (van Doorn). |
| Why tractable | Gap is 1/2 vs 25/28 ~= 0.893. Improving either bound is meaningful progress. |
| Mathlib | Finset API, divisibility, unit fractions require custom definitions but building blocks exist. |
| Formalized | Yes, in formal-conjectures. |
| Prior attempts | NONE. Fresh target. |
| Risk | Medium. The combinatorial structure is complex but well-defined. |

---

#### 6. Erdos #389 -- Consecutive product divisibility

| Aspect | Detail |
|--------|--------|
| Statement | For every n >= 1, exists k such that n(n+1)...(n+k-1) divides (n+k)...(n+2k-1)? |
| Status | OPEN. Verified for n <= 18 (OEIS A375071). k values grow super-polynomially. |
| Why tractable | Specific small cases are tractable. Proving for n=19 or n=20 would be new. |
| Mathlib | Products over Finset, factorial-like structures available. |
| Formalized | Yes, in formal-conjectures. |
| Prior attempts | 4 submissions (2 with wrong statement!). Results: compiled clean but unresolved. |
| Risk | Medium-High. Growth pattern suggests difficulty increases rapidly. |

---

#### 7. Erdos #249 -- Irrationality of sum phi(n)/2^n

| Aspect | Detail |
|--------|--------|
| Statement | Is sum_{n>=1} phi(n)/2^n irrational? |
| Status | OPEN. Related: sum p_n/2^n (problem 251) also open. Erdos proved sum p_n^k/n! is irrational for all k. |
| Why tractable | Clean statement. Mathlib has Euler totient and power series infrastructure. |
| Mathlib | `Nat.totient` defined. Geometric series, irrational API available. |
| Formalized | Yes, in formal-conjectures. |
| Prior attempts | 3 submissions (as Erdos 249). All compiled clean, no proven theorems. |
| Risk | High. Irrationality proofs are notoriously hard for AI. |

---

#### 8. Erdos #470 -- Odd weird numbers existence

| Aspect | Detail |
|--------|--------|
| Statement | Do odd weird numbers exist? |
| Status | OPEN. No odd weird below 10^21. Must have >= 6 prime factors. |
| Why tractable | Well-constrained: abundant + not pseudoperfect + odd. Strong lower bounds exist. |
| Mathlib | Abundant/Deficient defined. Divisor sums available. Finset.sum for subset sums. |
| Formalized | Yes: `exists n, n.Weird ∧ Odd n` |
| Prior attempts | 1 submission (bare gap). Compiled clean, 2 lemmas proven (likely trivial). |
| Risk | Very High. Nonexistence would be a major result. Existence requires construction. |

---

### TIER 3: Worth Attempting (less infrastructure, but interesting)

#### 9. Erdos #334 -- Smooth decomposition n = a + b

| Aspect | Detail |
|--------|--------|
| Statement | Every n = a + b where a,b are f(n)-smooth. Find optimal f(n). |
| Status | OPEN. Best known: f(n) << n^{4/(9*sqrt(e))+eps} ~= n^0.27 (Balog 1989). Conjectured f(n) = n^{o(1)}. |
| Why tractable | Improving Balog's 1989 bound (37 years old!) would be significant. Smooth number theory is well-developed. |
| Mathlib | Prime factorization via `Nat.factorization`. Smooth number concept needs custom definition. |
| Formalized | Not in formal-conjectures (unlisted). |
| Prior attempts | NONE. Fresh target. |
| Risk | Medium-High. Analytic number theory techniques may be needed. |

---

#### 10. Erdos #1059 -- Primes p where p - k! is always composite

| Aspect | Detail |
|--------|--------|
| Statement | Infinitely many primes p such that p - k! is composite for all k with 1 <= k! < p? |
| Status | OPEN. Examples: p=101, p=211. |
| Why tractable | Clean existential statement. Computational verification possible. Erdos suggested weaker version may be more tractable. |
| Mathlib | Primes, factorial, composite predicates all available. |
| Formalized | Yes, in formal-conjectures. OEIS A064152. |
| Prior attempts | NONE. Fresh target. |
| Risk | Medium. Proving "infinitely many" is hard, but specific instances are verifiable. |

---

#### 11. Erdos #413 -- Barriers for omega(n)

| Aspect | Detail |
|--------|--------|
| Statement | Infinitely many n where m + omega(m) <= n for all m < n? |
| Status | OPEN. Erdos proved F(n) = prod k_i has barriers with positive density. omega barriers form A005236. |
| Why tractable | Related function F already proved. omega is a natural next step. Sieve methods relevant. |
| Mathlib | `Nat.factorization`, omega (distinct prime factors) computable. |
| Formalized | Yes, in formal-conjectures. |
| Prior attempts | NONE. Fresh target. |
| Risk | High. Sieve theory may exceed Aristotle's capabilities. |

---

#### 12. Erdos #414 -- Iterated n -> n + tau(n) convergence

| Aspect | Detail |
|--------|--------|
| Statement | For any m,n, iterating h(x) = x + tau(x) eventually reaches same sequence? |
| Status | OPEN. Erdos-Graham believed yes. |
| Why tractable | Concrete iteration. tau(n) well-defined in Mathlib. Can verify computationally for small cases. |
| Mathlib | `Nat.divisors.card` gives tau. Iteration via `Nat.iterate`. |
| Formalized | Yes, in formal-conjectures. |
| Prior attempts | NONE (problem 412 attempted, different iteration). |
| Risk | High. Convergence proofs for iterative maps are deep. |

---

## Problems Already Heavily Attempted (Deprioritize)

| Problem | Submissions | Best Result | Assessment |
|---------|-------------|-------------|------------|
| Erdos 251 (p_n/2^n irrationality) | 3 | compiled clean, 1-3 proven | Irrationality proofs too hard |
| Erdos 252 (sigma_k/n! irrationality) | 1 | compiled clean, 2 proven | Worth retargeting at k=5 |
| Erdos 389 (consecutive products) | 4 | compiled clean | Statement was wrong in 2/4 submissions |
| Erdos 412 (iterated sigma convergence) | 1 | compiled clean, 2 proven | Deep problem |
| Erdos 470 (odd weird) | 1 | compiled clean, 2 proven | Likely intractable |
| Erdos 672 (AP perfect powers) | ~8 | compiled clean, max 107 proven | Most attempted; infrastructure built |
| Erdos 850 (consecutive same-radical) | 6 | compiled clean, max 42 proven | Constraints found but gap unresolved |
| Erdos-Straus (4/n decomposition) | 2 | submitted, pending | Very hard |

---

## Mathlib Infrastructure Assessment

| Concept | Mathlib Status | Relevant Problems |
|---------|---------------|-------------------|
| Arithmetic functions (sigma, tau, phi) | Full coverage | 249, 251, 252, 413, 414 |
| Divisibility, GCD, LCM | Full coverage | 389, 396, 672, 1063 |
| Primes, factorization | Full coverage | 1059, 413, 334 |
| Binomial coefficients | Full coverage | 396, 1063 |
| Catalan numbers | Defined | 396 |
| Finset operations (sum, prod, filter) | Extensive | All |
| Irrational API | Available | 249, 251, 252 |
| Abundant/Deficient | Defined | 470 |
| Weird numbers | NOT in Mathlib (external repo) | 470 |
| Sidon sets | NOT in Mathlib | 30 |
| Covering systems | NOT in Mathlib | 203 |
| Smooth numbers | NOT in Mathlib (need custom def) | 334 |

---

## Top 5 Recommendations (Prioritized)

1. **Erdos #1063** (n_k estimate) -- FRESH TARGET. Concrete computational problem with small known values. Binomial coefficient infrastructure excellent. Prove n_6 or n_7 value, or tighten upper bound.

2. **Erdos #252 k=5** (sigma_5/n! irrationality) -- RETARGET existing attempt. k=1..4 proved by escalating methods. k=5 is the natural frontier. Include Pratt 2022 (k=4) as context.

3. **Erdos #396** (descending factorial divides C(2n,n)) -- FRESH TARGET. Pomerance's density-1 result for ascending variant suggests methods exist. Catalan number infrastructure in Mathlib.

4. **Erdos #301** (unit fraction avoidance max set) -- FRESH TARGET. Improving the 25/28 upper bound OR proving f(N) > (1/2+epsilon)N for specific epsilon would be new.

5. **Erdos #1059** (primes avoiding factorial differences) -- FRESH TARGET. Clean statement, examples known. Weaker version suggested by Erdos may be within reach.

---

## Recently Solved by AI (Context for What Works)

| Problem | Solver | Method | Date |
|---------|--------|--------|------|
| Erdos #124 | Aristotle (Harmonic) | 6 hours autonomous, Lean formal | 2025-10 |
| Erdos #728 | GPT-5.2 | Original proof, verified by Tao | 2026-01 |
| Erdos #729 | GPT-5.2 | Original proof, verified by Tao | 2026-01 |
| Erdos #397 | GPT-5.2 | Original proof, verified by Tao | 2026-01 |
| Erdos #1051 | Aletheia (Gemini) | Autonomous, formalized in Lean | 2026 |
| Erdos #379 | Cambie-Kovac-Tao | Human-AI collab, formalized | 2025 |
| Erdos #987 | Tao | Formalized in Lean | 2025 |
| Erdos #248 | Tao-Teräväinen | Human proof | 2025 |

**Pattern**: Successfully solved problems tend to be:
- Irrationality/rationality of series (1051)
- Combinatorial existence with concrete small cases (124, 728)
- Problems where existing techniques extend naturally (397)

---

## Sources

- [Erdos Problems Database](https://www.erdosproblems.com/)
- [Google DeepMind Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
- [Mathlib Overview](https://leanprover-community.github.io/mathlib-overview.html)
- [Mathlib NumberTheory.ArithmeticFunction](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction.html)
- [Ben Green's 100 Open Problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf)
- [Erdos Problems Formalization - Xena Blog](https://xenaproject.wordpress.com/2025/12/05/formalization-of-erdos-problems/)
- [Quanta Magazine Year in Math 2024](https://www.quantamagazine.org/the-year-in-math-20241216/)
- [Scientific American - AI Solves Erdos Problems](https://www.scientificamerican.com/article/ai-uncovers-solutions-to-erdos-problems-moving-closer-to-transforming-math/)
- [Three Erdos Problems Fell - Medium](https://medium.com/@cognidownunder/three-erd%C5%91s-problems-fell-in-seven-days-and-terence-tao-verified-every-proof-himself-1a1ff4399bc6)
- [Erdos #1051 - erdosproblems.com](https://www.erdosproblems.com/1051)
- [Tao Mastodon on AI & Erdos](https://mathstodon.xyz/@tao/115855840223258103)
- [Carmichael's totient conjecture - Wikipedia](https://en.wikipedia.org/wiki/Carmichael's_totient_function_conjecture)
- [Erdos-Straus conjecture - Wikipedia](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Straus_conjecture)
- [Grimm's conjecture - Wikipedia](https://en.wikipedia.org/wiki/Grimm's_conjecture)
- [Stefan Steinerberger Open Problems](https://faculty.washington.edu/steinerb/openproblems.pdf)
