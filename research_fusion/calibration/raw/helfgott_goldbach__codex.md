Historical note: weak Goldbach is now a theorem, proved by [Helfgott, 2013](https://arxiv.org/abs/1312.7748). Below is the requested 2012-style cross-domain scouting list, excluding “push Vinogradov harder” routes.

### Technique 1: Green-Tao dense-model transference with the enveloping-sieve restriction lemma

- **Seminal source:** Green, [“Roth’s theorem in the primes,” 2005](https://annals.math.princeton.edu/2005/161-3/p11); Green-Tao, [“The primes contain arbitrarily long arithmetic progressions,” 2008](https://annals.math.princeton.edu/2008/167-2/p03); Green-Tao, [“Linear equations in primes,” 2010](https://arxiv.org/abs/math/0606088).
- **Structural analog:** Unlocked arithmetic progressions and finite-complexity linear systems in primes. Ternary Goldbach is the finite-complexity equation `p1 + p2 + p3 = n`; the W-trick removes local congruence noise.
- **Default-toolkit obstruction:** Density-zero obstruction. Circle-method minor arcs need strong pointwise exponential-sum control; transference replaces sparse primes by a dense model inside a pseudorandom majorant.
- **Lean/Mathlib:** Would sit across `Mathlib.Combinatorics.Additive`, `ZMod.dft`, `AddChar`, `Nat.Prime`. Missing: von Mangoldt, W-trick, enveloping sieve, dense-model theorem, linear-forms/correlation conditions.

### Technique 2: Croot-Sisask Lp almost-periodicity plus Bogolyubov-Ruzsa lemma

- **Seminal source:** Croot-Sisask, [“A probabilistic technique for finding almost-periods of convolutions,” 2010](https://arxiv.org/abs/1003.2978); Croot-Laba-Sisask, [2011/2013](https://arxiv.org/abs/1103.6000); Sanders, [“On the Bogolyubov-Ruzsa lemma,” 2012](https://arxiv.org/abs/1011.0107).
- **Structural analog:** Unlocked long progressions/structured neighborhoods inside sumsets `A+B`. Here a missing representation means a hole in `P+P+P`; almost-periodicity can turn isolated holes into large structured deficits.
- **Default-toolkit obstruction:** Local-hole obstruction. Circle estimates control global averages; they do not automatically rule out a structured exceptional residue or interval where the convolution vanishes.
- **Lean/Mathlib:** Base infrastructure in `Finset`, `Mathlib.Combinatorics.Additive.CauchyDavenport`, `PluenneckeRuzsa`, `ApproximateSubgroup`. Missing: Bohr sets, finite `Lp` convolution theory, Croot-Sisask sampling lemma, sparse relative version for primes.

### Technique 3: Deligne-Katz l-adic trace-function method via Grothendieck-Lefschetz and Fourier-Deligne completion

- **Seminal source:** Deligne, [“La conjecture de Weil II,” 1980](https://numdam.org/articles/10.1007/BF02684780/); Katz, *Gauss Sums, Kloosterman Sums, and Monodromy Groups*, 1988; Fouvry-Kowalski-Michel, [“Algebraic trace functions over the primes,” 2012/2014](https://arxiv.org/abs/1211.6043).
- **Structural analog:** Unlocked square-root cancellation for complete finite-field exponential sums and trace-function twists of primes. Goldbach minor arcs, after bilinear decomposition/completion, expose complete sums where sheaf monodromy can certify cancellation.
- **Default-toolkit obstruction:** Char-0 vs char-p obstruction. Dirichlet zero-free regions see characters; they miss nonabelian algebraic trace correlations arising in completed bilinear sums.
- **Lean/Mathlib:** Would use `AlgebraicGeometry`, `CategoryTheory.Sites`, `ZMod`, `AddChar`, `DirichletCharacter`, `Analysis.Fourier`. Missing: etale/l-adic cohomology, Frobenius trace functions, conductors, Fourier-Deligne transform, Deligne weights.

### Technique 4: Deshouillers-Iwaniec/Kuznetsov spectral large sieve for Kloosterman bilinear forms

- **Seminal source:** Kuznetsov trace formula, 1979; Deshouillers-Iwaniec, [“Kloosterman sums and Fourier coefficients of cusp forms,” 1982](https://eudml.org/doc/142975); Bombieri-Friedlander-Iwaniec, [“Primes in arithmetic progressions to large moduli,” 1986](https://www.researchwithrutgers.com/en/publications/primes-in-arithmetic-progressions-to-large-moduli/).
- **Structural analog:** Unlocked distribution of primes in APs beyond the Bombieri-Vinogradov square-root barrier and prime-producing sieve problems. Goldbach’s bad minor arcs can be recast as bilinear Kloosterman-type sums.
- **Default-toolkit obstruction:** Square-root/dispersion barrier. Classical large sieve loses after absolute values; Kuznetsov trades Kloosterman averages for spectral `L2` bounds.
- **Lean/Mathlib:** Relevant pieces: `ModularForm`, `UpperHalfPlane`, `MeasureTheory.Group`, `RepresentationTheory`, `Algebra.Lie`. Missing: Maass forms, automorphic representations, Kloosterman sums, Petersson/Kuznetsov trace formulas, spectral large sieve.

### Technique 5: Linnik-Ratner homogeneous dynamics with Dani-Margulis linearization

- **Seminal source:** Margulis’s Oppenheim proof, 1987; Ratner, [“On Raghunathan’s measure conjecture,” 1991](https://annals.math.princeton.edu/1991/134-3/p02); Duke, [1988](https://eudml.org/doc/143559); Einsiedler-Lindenstrauss-Michel-Venkatesh, [2012](https://ems.press/journals/lem/articles/12101).
- **Structural analog:** Oppenheim was a local-global representation problem where analytic methods stalled; homogeneous dynamics solved it via orbit closures/equidistribution. Goldbach also has local congruence obstructions and a global representation count.
- **Default-toolkit obstruction:** Missing homogeneous lift for primality. Dynamics can solve representation problems once the objects are orbit points; primes are not naturally homogeneous orbit data.
- **Lean/Mathlib:** Would live in `Dynamics.Ergodic`, `MeasureTheory.Group`, `Geometry.Manifold.Algebra.LieGroup`, `Algebra.Lie`, `NumberTheory.NumberField.AdeleRing`. Missing: quotients `Γ\G`, unipotent flows, Ratner theorem, effective mixing, adelic prime-weighted orbit coding.

## Ranking

Conditional on a non-standard 2012 unlock:

| Rank | Technique | Bayesian score | Reason |
|---:|---|---:|---|
| 1 | Green-Tao transference | `0.35 prior × 0.55 likelihood = 0.19` | Already fits linear equations in primes; Goldbach has exactly that structure. |
| 2 | Kuznetsov spectral large sieve | `0.25 × 0.45 = 0.11` | Strong record against distribution barriers; Goldbach minor arcs plausibly expose Kloosterman bilinear sums. |
| 3 | Croot-Sisask almost-periodicity | `0.20 × 0.35 = 0.07` | Good structural match to sumset holes; sparse-prime adaptation is the hard part. |
| 4 | Deligne-Katz trace functions | `0.25 × 0.20 = 0.05` | Powerful cancellation engine, but bridging Archimedean prime sums to finite-field sheaves is nontrivial. |
| 5 | Linnik-Ratner dynamics | `0.15 × 0.08 = 0.012` | Huge prior from Oppenheim-style breakthroughs; weak likelihood because primality lacks a natural orbit model. |