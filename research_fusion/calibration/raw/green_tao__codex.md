### Technique 1: Relative Szemerédi Transference via Hahn-Banach Dense Model Lemma

1. **Seminal paper/theorem:** Green-Tao, 2004 preprint / 2008 Annals, *The primes contain arbitrarily long arithmetic progressions*; main new ingredient named as a transference principle. Source: https://annals.math.princeton.edu/2008/167-2/p03  
2. **Structural analog:** Sparse quasirandom graph principle: dense subgraphs of a pseudorandom sparse host obey dense extremal theorems. Analog here: primes have positive relative density inside a pseudorandom almost-prime/Selberg majorant after the `W`-trick.  
3. **Default-toolkit obstruction:** Density-zero issue plus sieve/parity barrier. Sieve weights can majorize primes, but cannot directly certify all entries of a long pattern are prime. Transference bypasses direct prime counting.  
4. **Lean/Mathlib:** Infrastructure would span `Mathlib.Analysis.NormedSpace.HahnBanach.*`, `Mathlib.NumberTheory.VonMangoldt`, `Mathlib.NumberTheory.SelbergSieve`, `Mathlib.Combinatorics.Additive.AP.Three`. Missing: pseudorandom measures, linear forms condition, dense model theorem, relative Szemerédi theorem.  
5. **Comment:** This is the historical unlock.

### Technique 2: Gowers Uniformity Norms via Generalized von Neumann + Inverse Theorem

1. **Seminal paper/theorem:** Gowers, 1998/2001, *A new proof of Szemerédi’s theorem*. Source: https://sites.math.rutgers.edu/~zeilberg/akherim/GowersMasterpiece.pdf  
2. **Structural analog:** Quantitative Szemerédi was unlocked by replacing Fourier-only control with `U^{k-1}` control. Analog here: a `k`-AP count in primes should be controlled by high-order uniformity of the normalized `W`-tricked von Mangoldt function.  
3. **Default-toolkit obstruction:** Circle method mostly sees `U²`/linear Fourier structure. For 4-term and longer APs, quadratic and higher-order phases become the obstruction.  
4. **Lean/Mathlib:** Would live around `Mathlib.Combinatorics.Additive.*`, `Mathlib.Data.ZMod.Basic`, finite sums/expectations, and normed-space APIs. Missing: `GowersNorm`, cube derivatives, generalized von Neumann theorem, inverse Gowers theorem.  
5. **Comment:** This supplies the right language for “random enough for APs,” not just “well-distributed in residue classes.”

### Technique 3: Sparse Hypergraph Removal via Relative Counting Lemma

1. **Seminal paper/theorem:** Gowers, 2007, *Hypergraph regularity and the multidimensional Szemerédi theorem*; independently Nagle-Rödl-Schacht-Skokan. Source: https://annals.math.princeton.edu/2007/166-3/p07  
2. **Structural analog:** Hypergraph removal proves multidimensional Szemerédi by encoding patterns as simplex copies. Analog here: encode `k`-APs as hypergraph configurations inside a sparse pseudorandom host.  
3. **Default-toolkit obstruction:** Dense graph/hypergraph regularity assumes a dense ambient universe. Primes give a sparse universe; without a relative counting lemma, dense Szemerédi machinery cannot be imported.  
4. **Lean/Mathlib:** Existing pieces: `Mathlib.Combinatorics.SimpleGraph.Regularity.*`, `Mathlib.Combinatorics.SimpleGraph.Triangle.Removal`. Missing: uniform hypergraphs, hypergraph regularity/removal, sparse relative counting/removal.  
5. **Comment:** This is a combinatorial route to the same wall-crossing as transference.

### Technique 4: Furstenberg Correspondence + Weighted Multiple Recurrence

1. **Seminal paper/theorem:** Furstenberg, 1977, ergodic proof of Szemerédi. Source: https://cris.huji.ac.il/en/publications/ergodic-behavior-of-diagonal-measures-and-a-theorem-of-szemer%C3%A9di-/  
2. **Structural analog:** Multiple recurrence unlocked Szemerédi and later polynomial recurrence. Analog here: APs in primes become recurrence of shifted prime-weighted sets after a sparse/weighted correspondence principle.  
3. **Default-toolkit obstruction:** Classical correspondence requires positive upper density. The primes vanish in natural density, so one needs a relative invariant measure or weighted recurrence theorem.  
4. **Lean/Mathlib:** Existing: `Mathlib.Dynamics.Ergodic.*`, `Mathlib.MeasureTheory.*`, `Mathlib.Probability.ConditionalExpectation`. Missing: Furstenberg correspondence, multiple recurrence, Host-Kra seminorms, weighted/sparse recurrence.  
5. **Comment:** Conceptually strong, but historically less computable than additive-combinatorial transference.

### Technique 5: Nilsequence Obstruction Theory via Leibman Equidistribution + Möbius-Nilsequence Orthogonality

1. **Seminal paper/theorem:** Leibman, 2005, polynomial orbits on nilmanifolds; Green-Tao, 2010, *Linear equations in primes*, using inverse Gowers/Möbius-nilsequence machinery. Sources: https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/article/abs/pointwise-convergence-of-ergodic-averages-for-polynomial-actions-of-mathbbzd-by-translations-on-a-nilmanifold/D2AD1ABEC2FB78ACC1A3224C56FB54FF and https://annals.math.princeton.edu/wp-content/uploads/annals-v171-n3-p08-p.pdf  
2. **Structural analog:** Linear equations in primes were unlocked by showing prime weights do not correlate with nilsequences, the structured obstructions to Gowers uniformity. Analog here: any failure of AP pseudorandomness should factor through a nilsequence.  
3. **Default-toolkit obstruction:** Missing obstruction classifier. Sieve/circle methods detect divisibility and linear characters, but not nilpotent higher-order structure.  
4. **Lean/Mathlib:** Existing: `Mathlib.Geometry.Manifold.Algebra.LieGroup`, `Mathlib.Algebra.Lie.Nilpotent`, `Mathlib.GroupTheory.Nilpotent`, `Mathlib.Dynamics.Ergodic.*`. Missing: nilmanifolds with lattices, Mal’cev coordinates, polynomial sequences, quantitative equidistribution, Möbius-nilsequence theorem.  
5. **Comment:** Overpowered for just Green-Tao APs, but very plausible as the general high-order framework.

## Ranking

| Rank | Technique | Bayesian reason |
|---:|---|---|
| 1 | Relative Szemerédi transference | Prior high from sparse pseudorandom graph analogies; likelihood very high because it directly crosses density zero. Historically correct. |
| 2 | Gowers uniformity norms | Prior high from solving quantitative Szemerédi; likelihood high because `k`-AP counts are exactly high-order-uniformity problems. |
| 3 | Sparse hypergraph removal | Prior medium-high from removal lemmas; likelihood high but implementation burden large. |
| 4 | Nilsequence obstruction theory | Prior medium from ergodic/additive structure theorems; likelihood medium-high for higher-order prime correlations, but heavier than needed for linear APs. |
| 5 | Furstenberg weighted recurrence | Prior high historically for Szemerédi; likelihood medium because sparse/weighted recurrence is the hard missing bridge and tends to become non-effective. |