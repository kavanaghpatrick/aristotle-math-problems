2026 caveat: the 2012 “open problem” is now solved. Zhang proved bounded gaps via smooth-modulus distribution, and Maynard later gave a different sieve breakthrough. I’m treating your prompt as a 2012 scouting memo and excluding Maynard-Tao from the five because it sits inside the sieve family you marked as the wall.

### Technique 1: Deligne-Weil trace-function completion for multilinear Kloosterman sums
- **Seminal:** [Deligne, “La conjecture de Weil I,” 1974](https://numdam.org/articles/10.1007/BF02684373/); applied to bounded gaps by [Zhang, 2014](https://annals.math.princeton.edu/2014/179-3/p07).
- **Bridge lemma:** Grothendieck-Lefschetz trace formula + Deligne square-root cancellation for l-adic trace functions.
- **Structural analog:** Friedlander-Iwaniec style prime-producing problems and Zhang’s later proof both reduce hard off-diagonal terms to complete exponential sums over finite fields.
- **Diagnosis:** GPY needs level > 1/2; BV/large-sieve methods hit the square-root barrier. The missing object is finite-field monodromy cancellation in Type III sums.
- **Lean/Mathlib:** `AlgebraicGeometry`, `FieldTheory.Finite`, `NumberTheory`. Missing: etale cohomology, l-adic sheaves, Frobenius trace functions, conductor calculus, Weil II.

### Technique 2: Kuznetsov-Deshouillers-Iwaniec spectral large sieve
- **Seminal:** [Deshouillers-Iwaniec, “Kloosterman sums and Fourier coefficients of cusp forms,” 1982](https://www.researchwithrutgers.com/en/publications/kloosterman-sums-and-fourier-coefficients-of-cusp-forms); [Bombieri-Friedlander-Iwaniec, 1986](https://www.researchwithrutgers.com/en/publications/primes-in-arithmetic-progressions-to-large-moduli/).
- **Bridge lemma:** Kuznetsov trace formula converts averages of Kloosterman sums into spectral averages of automorphic Fourier coefficients.
- **Structural analog:** BFI pushed primes in arithmetic progressions beyond the classical large-sieve range for structured, well-factorable moduli.
- **Diagnosis:** Default GPY treats off-diagonal congruence sums as generic. The obstruction is unspectralized Kloosterman cancellation across moduli.
- **Lean/Mathlib:** `NumberTheory.ModularForms`, `Analysis.Fourier`, `MeasureTheory`. Missing: Maass forms, automorphic spectral decomposition, Kuznetsov, Bessel transforms, spectral large sieve.

### Technique 3: Green-Tao-Ziegler dense transference via Gowers norms
- **Seminal:** [Green-Tao, 2008](https://annals.math.princeton.edu/2008/167-2/p03); [Green-Tao, “Linear equations in primes,” 2010](https://annals.math.princeton.edu/2010/171-3/p08); [Green-Tao-Ziegler inverse theorem, 2012](https://annals.math.princeton.edu/2012/176-2/p11).
- **Bridge lemma:** Dense model theorem + generalized von Neumann theorem + inverse Gowers theorem to nilsequences.
- **Structural analog:** Long arithmetic progressions in primes were unlocked by transferring dense combinatorial recurrence into a pseudorandom sparse prime majorant.
- **Diagnosis:** GPY’s weights detect almost-prime density but suffer parity and density-zero obstructions. A transference route would need pseudorandomness strong enough for fixed admissible prime tuples.
- **Lean/Mathlib:** `Combinatorics.Additive`, `MeasureTheory`, finite probability. Missing: Gowers norms, dense model theorem, hypergraph counting/removal, nilmanifolds, nilsequences.

### Technique 4: Bourgain-Katz-Tao finite-field sum-product expansion
- **Seminal:** [Bourgain-Katz-Tao, 2004](https://link.springer.com/content/pdf/10.1007/s00039-004-0451-1.pdf); [Bourgain-Glibichuk-Konyagin, 2006](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/8241A5A73C7EBEB2B43CE669C54F75F9/S0024610706022721a.pdf/estimates_for_the_number_of_sums_and_products-and-for-exponential-sums-in-fields-of-prime-order.pdf).
- **Bridge lemma:** Sum-product expansion implies multilinear exponential-sum cancellation unless variables concentrate in subfields or approximate subgroups.
- **Structural analog:** Finite-field incidence, Kakeya, expander, and subgroup exponential-sum problems were unlocked by proving additive and multiplicative structure cannot both persist.
- **Diagnosis:** Type III sums contain reciprocal maps and mixed additive/multiplicative structure. Large sieve sees none of this expansion and stalls at bilinear barriers.
- **Lean/Mathlib:** `Combinatorics.Additive`, `FieldTheory.Finite`, `Combinatorics.SimpleGraph`. Missing: sum-product theorem, incidence geometry, BSG machinery, expanders, multilinear exponential sums.

### Technique 5: Wooley efficient congruencing for nested p-adic constraints
- **Seminal:** [Wooley, “Vinogradov’s mean value theorem via efficient congruencing,” 2012](https://annals.math.princeton.edu/2012/175-3/p12).
- **Bridge lemma:** Efficient congruencing lifts weak congruence information to stronger p-adic congruence constraints, forcing near-diagonal structure in high moments.
- **Structural analog:** Vinogradov mean value theorem and Waring-type exponential-sum bounds were improved by exploiting nested congruence structure rather than applying Cauchy blindly.
- **Diagnosis:** Default Type I/II/III estimates lose power through repeated Cauchy and divisor decompositions. The obstruction is non-diagonal congruence proliferation.
- **Lean/Mathlib:** `NumberTheory.Padics`, `NumberTheory.Congruence`, `Algebra.BigOperators`. Missing: Weyl sums, Vinogradov systems, p-adic stationary phase, efficient congruencing iteration.

## Ranking

| Rank | Technique | Prior x likelihood |
|---:|---|---|
| 1 | Deligne-Weil trace functions | High prior from adjacent exponential-sum breakthroughs x very high fit to Type III/smooth-modulus structure. This was essentially Zhang’s unlock. |
| 2 | Kuznetsov spectral large sieve | High prior in primes-in-AP beyond 1/2 x strong fit to off-diagonal Kloosterman averages, but less flexible for Zhang’s trilinear smooth-modulus regime. |
| 3 | Finite-field sum-product expansion | Medium-high prior from finite-field cancellation problems x medium fit to reciprocal multilinear sums; plausible but weaker than sheaf monodromy. |
| 4 | Efficient congruencing | High prior in exponential-sum mean values x lower fit because prime gaps need AP distribution, not polynomial-phase moments directly. |
| 5 | Green-Tao-Ziegler transference | Very high prior for sparse prime patterns x low fit to bounded gaps, since pair/tuple positivity still needs prime-correlation input near the parity barrier. |