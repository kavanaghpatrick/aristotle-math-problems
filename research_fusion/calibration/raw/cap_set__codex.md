Historical caveat: this was solved shortly after “early 2016” by the polynomial/slice-rank method. I’m treating the prompt as pre-breakthrough scouting, with hindsight noted where relevant.

### Technique 1: CLP-Ellenberg-Gijswijt Low-Degree Polynomial / Slice-Rank Method

1. **Seminal paper/theorem**: Frankl-Wilson polynomial rank method, 1981; Croot-Lev-Pach, 2016; Ellenberg-Gijswijt, 2016/2017. CLP handled `Z_4^n`; Ellenberg-Gijswijt gave the cap-set bound in `F_q^n`. Sources: [CLP](https://annals.math.princeton.edu/2017/185-1/p07), [Ellenberg-Gijswijt](https://annals.math.princeton.edu/2017/185-1/p08), [Frankl-Wilson](https://www.sciencedirect.com/science/article/pii/0097316581900207).

2. **Key bridge lemma**: diagonal tensor/slice-rank lemma. Restrict the tensor `1[x + y + z = 0]` to `A^3`; cap-set freeness makes it diagonal, so slice rank is `|A|`. Low-degree polynomial expansion bounds the same slice rank by a monomial count.

3. **Structural analog**: Frankl-Wilson unlocked restricted-intersection theorems and fed into Kahn-Kalai’s Borsuk counterexample. Analog here: a forbidden configuration forces an evaluation matrix/tensor to become diagonal.

4. **Why default toolkit failed**: Fourier density increment hit a **rank-certificate barrier**. Large Fourier coefficients detect linear bias; the cap-set obstruction is a low-degree Hilbert-function/tensor-rank obstruction.

5. **Lean 4 / Mathlib**: infrastructure lives around `MvPolynomial`, `TensorProduct`, `LinearMap`, `FiniteDimensional`, `ZMod`, `Finset`. Missing: slice rank/partition rank, diagonal tensor lemma, monomial-count entropy estimates, quotient normal forms modulo `X_i^3 - X_i`.

### Technique 2: Delsarte-Schrijver Terwilliger-Algebra SDP

1. **Seminal paper/theorem**: Delsarte’s association-scheme LP method, 1973; Schrijver’s Terwilliger-algebra SDP bounds, 2005. Sources: [Delsarte](https://ir.cwi.nl/pub/14098), [Schrijver](https://arxiv.org/abs/cs/0501046).

2. **Key bridge lemma**: positivity of distance distributions/MacWilliams transforms, upgraded by Terwilliger block diagonalization to finite SDP constraints.

3. **Structural analog**: coding-theory upper bounds in Hamming schemes. Analog here: caps are independent sets in the affine-line hypergraph on `F_3^n`, with huge affine symmetry `F_3^n ⋊ GL_n(F_3)`.

4. **Why default toolkit failed**: Fourier/Roth methods face a **global dual-certificate barrier**. They increment density locally; SDP can certify impossibility globally through symmetry-reduced moment matrices.

5. **Lean 4 / Mathlib**: `Matrix`, `PosSemidef`, `SimpleGraph`, `LinearAlgebra`. Missing: association schemes, Bose-Mesner algebra, Terwilliger algebra, Krawtchouk polynomials, SDP duality, rational certificate checking.

### Technique 3: Hypergraph Containers With Balanced Supersaturation

1. **Seminal paper/theorem**: Balogh-Morris-Samotij, 2015; Saxton-Thomason, 2015. Sources: [BMS](https://www.cambridge.org/core/journals/journal-of-the-london-mathematical-society/article/abs/independent-sets-in-hypergraphs/90288D4F2F66BE8D303FE6859D4FD9B9), [Saxton-Thomason](https://www.repository.cam.ac.uk/items/391de077-7f33-4154-aeec-2d794b2c9983).

2. **Key bridge lemma**: container lemma plus balanced supersaturation. Independent sets lie in few smaller containers if every large set spans many well-distributed hyperedges.

3. **Structural analog**: counting `H`-free graphs and sum-free/Rado-free sets. Analog here: cap sets are independent sets in the 3-uniform hypergraph of affine lines.

4. **Why default toolkit failed**: **density-zero/supersaturation barrier**. Meshulam gives line existence at polynomially small density; the conjecture needs control at exponentially small relative density.

5. **Lean 4 / Mathlib**: `SimpleGraph` and `Finset` help, but a usable `Hypergraph` namespace is missing. Need uniform hypergraphs, codegrees, independent sets, container theorem, affine-line supersaturation.

### Technique 4: Furstenberg Correspondence + Host-Kra Characteristic Factors

1. **Seminal paper/theorem**: Furstenberg’s ergodic proof of Szemerédi, 1977; Host-Kra characteristic factors, 2005. Sources: [Furstenberg](https://eudml.org/doc/218318), [Host-Kra](https://annals.math.princeton.edu/2005/161-1/p09).

2. **Key bridge lemma**: correspondence principle plus characteristic-factor reduction: recurrence questions become structured dynamical-system questions.

3. **Structural analog**: Szemerédi’s theorem and multidimensional recurrence. Analog here: a positive-density sequence of cap sets would produce a limiting system with forbidden 3-term recurrence.

4. **Why default toolkit failed**: **quantitative compactness barrier**. Ergodic methods prove density-zero statements; cap-set needs an exponential rate. For 3APs over `F_3^n`, the relevant Host-Kra factor collapses close to Fourier/Kronecker structure.

5. **Lean 4 / Mathlib**: `MeasureTheory`, `Dynamics.Ergodic`, `MeasurePreserving`, `MeanErgodic`. Missing: Furstenberg correspondence, Host-Kra seminorms, nilsystems, finitary quantitative transference.

### Technique 5: Kalai Exterior Algebraic Shifting / Stanley-Reisner Hilbert Functions

1. **Seminal paper/theorem**: Stanley-Reisner/Stanley Hilbert-function method, 1975; Kalai algebraic shifting, 1984. Sources: [Stanley](https://onlinelibrary.wiley.com/doi/10.1002/sapm1975542135), [Kalai shifting reference](https://combinatorics.sites.stanford.edu/events/gil-kalai-hebrew-u-exterior-algebraic-shifting-and-erdos-ko-rado-theorem).

2. **Key bridge lemma**: exterior algebraic shifting preserves `f`-vectors while replacing a complex by a shifted one; Stanley-Reisner Hilbert functions convert extremal face counts into algebra.

3. **Structural analog**: Erdős-Ko-Rado-type extremal set problems and upper-bound-theorem style `f`-vector bounds. Analog here: caps are faces of the independence complex of the affine-line hypergraph.

4. **Why default toolkit failed**: **extremal-shape barrier**. Fourier gives density increments but not a canonical extremizer. Shifting could expose a lex/monomial obstruction, if affine-line freeness survives in a usable shadow form.

5. **Lean 4 / Mathlib**: `ExteriorAlgebra`, `ExteriorPower`, `Ideal`, `MvPolynomial`, `RingTheory.Polynomial.HilbertPoly`. Missing: abstract simplicial complexes at this level, Stanley-Reisner rings, algebraic shifting, Hilbert-series `f`-vector machinery.

## Ranking

1. **Technique 1**: prior `0.18` × structural likelihood `0.80` = `0.144` normalized ≈ `62%`. Best fit: product space, finite field, forbidden diagonal tensor. Retrospectively, this was the actual unlock.

2. **Technique 2**: prior `0.12` × likelihood `0.45` = `0.054` normalized ≈ `23%`. Strong symmetry match, but 3-uniform affine-line constraints are harder than pairwise distance constraints.

3. **Technique 3**: prior `0.10` × likelihood `0.25` = `0.025` normalized ≈ `11%`. Containers fit “independent sets in hypergraphs,” but the needed balanced supersaturation is nearly the original problem.

4. **Technique 5**: prior `0.06` × likelihood `0.12` = `0.007` normalized ≈ `3%`. Algebraic extremal-shape methods have precedent, but the affine-line constraint is not obviously shift-stable.

5. **Technique 4**: prior `0.12` × likelihood `0.03` = `0.004` normalized ≈ `2%`. High historical success on recurrence, poor quantitative fit for an exponential finite-field bound.