Bounded prime gaps are no longer open, but treating this as a 2012 scouting memo, the strongest candidates are below. With hindsight, Techniques 1 and 2 were the real unlocks.

### Technique 1: Deligne-Katz Trace-Function Completion for Type III Sums

**Seminal paper/theorem:** Deligne, *La conjecture de Weil II* (1980); used in the Zhang route via Birch-Bombieri/Deligne complete exponential-sum bounds. Zhang’s 2014 Annals paper states the bounded-gaps theorem using a stronger BV theorem for moduli with no large prime factors.

**Structural analog:** Trace-function methods unlocked cancellation in Kloosterman and hyper-Kloosterman-type sums, later systematized by Fouvry-Kowalski-Michel. Analog here: after dispersion, the hardest prime-in-AP errors become complete algebraic sums over finite fields, not generic residue-class sums.

**Why default toolkit failed:** The large sieve treats phases as arbitrary and is sharp at the square-root barrier. It misses geometric monodromy, so it cannot distinguish “random-looking algebraic complete sums” from adversarial coefficients.

**Lean/Mathlib comment:** Infrastructure would live around `AlgebraicGeometry`, `CategoryTheory.Sites.SheafCohomology`, `NumberTheory`, and finite fields. Missing: l-adic sheaves, Frobenius trace functions, weights/purity, Deligne RH, and the completion pipeline from AP sums to finite-field cohomology.

### Technique 2: Maynard-Tao Multidimensional Selberg Sieve Optimization

**Seminal paper/theorem:** Maynard, *Small gaps between primes* (2013 preprint; Annals 2015). Key bridge: the multidimensional sieve variational inequality giving bounded gaps under Bombieri-Vinogradov-level distribution, without needing theta > 1/2.

**Structural analog:** Unlocked bounded intervals containing many primes. Analog here: GPY’s one-dimensional weight tries to prove “one extra prime” through a tight ratio; Maynard’s weights optimize over all tuple coordinates and force multiple primes from the same distribution input.

**Why default toolkit failed:** GPY hit a weight-optimization barrier, not only a distribution barrier. At theta = 1/2, the one-dimensional GPY functional cannot force two primes in an admissible tuple.

**Lean/Mathlib comment:** Would use `NumberTheory`, `Combinatorics`, `Finset`, `Analysis.Asymptotics`, possibly `MeasureTheory` for weighted averages. Missing: Selberg sieve formalization, admissible tuple API, BV theorem, von Mangoldt asymptotics in APs, and finite-dimensional variational optimization with explicit constants.

### Technique 3: Higher-Order Fourier Analysis via Gowers Inverse Theorems and Nilsequence Orthogonality

**Seminal paper/theorem:** Green-Tao-Ziegler, inverse theorem for Gowers `U^{s+1}[N]` norms (2010); Green-Tao, Möbius/nilsequence orthogonality (2012).

**Structural analog:** Green-Tao’s theorem on arbitrarily long arithmetic progressions in primes. Analog here: replace second-moment AP uniformity with higher-order uniformity of the W-tricked prime indicator, isolating nilsequence obstructions rather than averaging over all characters.

**Why default toolkit failed:** BV/large sieve are essentially `L^2` tools. They cannot see whether the remaining error is structured or genuinely random, and they do not cross parity-type limitations of linear sieve information.

**Lean/Mathlib comment:** Current bases are `Combinatorics.Additive`, `Dynamics.Ergodic`, `MeasureTheory`, and `Analysis.Fourier`. Missing: Gowers norms, nilmanifolds, quantitative Leibman equidistribution, dense model/transference machinery, and Möbius/nilsequence orthogonality.

### Technique 4: Decoupling / Efficient Congruencing for Multilinear Exponential-Sum Moments

**Seminal paper/theorem:** Wooley, efficient congruencing proof of near-optimal Vinogradov mean value estimates (2012); Bourgain-Demeter-Guth, sharp decoupling and VMVT (2016).

**Structural analog:** VMVT and Waring’s problem were unlocked by replacing pointwise exponential-sum estimates with sharp high-moment/incidence estimates. Analog here: Type II/III dispersion sums can sometimes be recast as counting structured congruence solutions, where higher moments beat a bare large-sieve `L^2` bound.

**Why default toolkit failed:** The large sieve saturates at second moment. It has no mechanism for exploiting multilinear curvature, diagonal dominance, or high-order incidence geometry.

**Lean/Mathlib comment:** Would sit in `Analysis.Fourier`, `MeasureTheory`, `Analysis.Normed.Lp`, and `Combinatorics.Additive.Energy`. Missing: Fourier restriction/decoupling, VMVT, polynomial congruence incidence estimates, and usable finite Fourier analysis over `ZMod`.

### Technique 5: p-adic Stationary Phase and Newton-Polyhedron Bounds for Prime-Power Moduli

**Seminal paper/theorem:** Igusa’s p-adic stationary phase/local zeta function theory; Denef-Sperber exponential-sum bounds via Newton polyhedra, developed through the 1990s and 2000s.

**Structural analog:** Prime-power conductor subconvexity and high prime-power Kloosterman analyses use p-adic phase geometry to get cancellation invisible over integers. Analog here: smooth/friable moduli factor into controllable local prime-power pieces, so p-adic critical-point analysis could improve dispersion sums for structured moduli.

**Why default toolkit failed:** Classical dispersion estimates treat moduli too coarsely. They do not exploit local analytic structure modulo `p^k`, so they lose exactly where smooth-modulus factorization should help.

**Lean/Mathlib comment:** Relevant namespaces: `NumberTheory.Padics`, `RingTheory.LocalRing`, `Analysis.Normed.Field`, `AlgebraicGeometry`. Missing: p-adic integration, Igusa zeta functions, stationary phase, resolution/Newton polyhedra, and uniform exponential-sum estimates modulo `p^k`.

## Ranking

1. **Deligne-Katz trace-function completion**  
   Prior: high, because it had already broken square-root barriers in structured exponential sums. Likelihood: high, because GPY’s bottleneck reduces to structured complete sums after dispersion. Posterior: strongest. This was essentially Zhang’s route.

2. **Maynard-Tao multidimensional sieve**  
   Prior: medium; changing the sieve functional is riskier than improving estimates, but GPY’s obstruction was visibly variational. Likelihood: high, because it bypasses theta > 1/2 entirely. Posterior: very strong. This was the second actual route.

3. **Decoupling / efficient congruencing**  
   Prior: medium-high from adjacent exponential-sum breakthroughs. Likelihood: medium, since Type sums contain multilinear congruence geometry, but translating prime AP distribution into decoupling form is nontrivial.

4. **p-adic stationary phase**  
   Prior: medium; strong for prime-power and smooth moduli. Likelihood: medium-low, because bounded gaps need global prime distribution, not only local cancellation. Still plausible as a Zhang-style smooth-modulus amplifier.

5. **Higher-order Fourier / nilsequence machinery**  
   Prior: high in prime-pattern problems. Likelihood: lower here, because bounded gaps are governed by distribution in residue classes and sieve weights rather than long additive configurations. Useful conceptually, but less directly matched.

Sources used: Zhang Annals page on bounded gaps, Maynard arXiv/Annals record, Green-Tao-Ziegler inverse theorem, Wooley Annals VMVT, Bourgain-Demeter-Guth Annals decoupling/VMVT, Mathlib4 docs for `AlgebraicGeometry`, `CategoryTheory.Sites.SheafCohomology`, `Combinatorics.Additive`, `Dynamics.Ergodic`, `Analysis.Fourier`, and `NumberTheory.Padics`.