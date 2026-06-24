Scope note: I’m not listing perfectoid tilting itself, since Scholze already used it for new special cases and it is now part of the p-adic geometry toolkit. General weight-monodromy remains open beyond known cases. ([math.ac.vn](https://math.ac.vn/acta/2014-Volume39/1/perfectoid-spaces-and-the-weight-monodromy-conjecture-after-peter-scholze?utm_source=openai))

### Technique 1: Denef-Pas/Cluckers-Loeser motivic transfer principle
- **Bridge lemma:** equality of constructible motivic exponential functions transfers between characteristic 0 and positive-characteristic local fields with matching residue data.
- **Seminal:** Cluckers-Loeser, “Constructible exponential functions, motivic Fourier transform and transfer principle,” 2010; applied to the Fundamental Lemma transfer by Cluckers-Hales-Loeser. ([annals.math.princeton.edu](https://annals.math.princeton.edu/2010/171-2/p08?utm_source=openai)) ([arxiv.org](https://arxiv.org/abs/0712.0708?utm_source=openai))
- **Structural analog:** the Fundamental Lemma had a char-0/char-p transfer bottleneck; motivic transfer moved identities of orbital integrals across that wall. Here, equal-characteristic weight-monodromy is known, while mixed characteristic is the blocked side.
- **Why default toolkit failed:** the obstruction is the **char-0 vs char-p transfer barrier**. Classical p-adic Hodge comparison is not a field-uniform transfer theorem; it does not make purity of nearby-cycle traces a residue-field-definable invariant.
- **Lean 4/Mathlib:** infrastructure would live around `ModelTheory`, `FirstOrder`, `RingTheory.Valuation`, `MeasureTheory`. Missing: Denef-Pas language, quantifier elimination for valued fields, motivic constructible functions, motivic integration, and specialization/transfer theorems.

### Technique 2: Cyclotomic trace + Nygaard-filtered TC/prismatic method
- **Bridge lemma:** the cyclotomic trace relates algebraic K-theory to topological cyclic homology; BMS-style `AΩ`/Nygaard filtrations specialize to de Rham, crystalline, and etale theories.
- **Seminal:** Nikolaus-Scholze, “On topological cyclic homology,” 2018; Bhatt-Morrow-Scholze, “Integral p-adic Hodge theory,” 2018. ([arxiv.org](https://arxiv.org/abs/1707.01799?utm_source=openai)) ([numdam.org](https://www.numdam.org/articles/10.1007/s10240-019-00102-z/?utm_source=openai))
- **Structural analog:** integral p-adic Hodge theory unified formerly separate cohomology theories by passing through homotopy-theoretic TC/prismatic objects. That is structurally analogous to needing one object that sees both Q_p and F_p coefficients plus Frobenius/monodromy.
- **Why default toolkit failed:** the obstruction is **coefficient discontinuity and torsion loss**. Fontaine period rings and comparison theorems work after choosing a coefficient regime; they tend to separate rational, mod-p, and integral data.
- **Lean 4/Mathlib:** would touch `AlgebraicTopology`, `CategoryTheory`, `HomologicalAlgebra`. Missing: spectra as stable infinity categories, cyclotomic spectra, THH/TC, derived p-completion, prismatic complexes, Nygaard filtration.

### Technique 3: Schmid-CKS nilpotent-orbit / SL2-orbit theorem
- **Bridge lemma:** a polarized nilpotent orbit determines a limiting mixed Hodge structure whose weight filtration is the monodromy filtration; the SL2-orbit theorem supplies canonical splitting/control.
- **Seminal:** Schmid, “Variation of Hodge Structure: The Singularities of the Period Mapping,” 1973; Cattani-Kaplan-Schmid, “Degeneration of Hodge structures,” 1986. ([maths.ed.ac.uk](https://www.maths.ed.ac.uk/~v1ranick/papers/schmid.pdf?utm_source=openai)) ([annals.math.princeton.edu](https://annals.math.princeton.edu/1986/123-3/p02?utm_source=openai))
- **Structural analog:** complex semistable degenerations are controlled by the Clemens-Schmid package. The same formal object appears here: nilpotent monodromy `N` and a conjectural weight filtration with pure graded pieces.
- **Why default toolkit failed:** the obstruction is **missing positivity/polarization**. p-adic Hodge theory has filtered `(phi,N)`-modules, but not an analytic Hodge metric or positivity theorem strong enough to force the SL2 package.
- **Lean 4/Mathlib:** would sit across `Geometry.Manifold`, `Analysis.InnerProductSpace`, `LinearAlgebra`, `RepresentationTheory.LieAlgebra`. Missing: complex manifolds at this level, variations of Hodge structure, polarized mixed Hodge structures, period maps, nilpotent orbit theorem.

### Technique 4: Taylor-Wiles-Kisin patching with local-global compatibility
- **Bridge lemma:** patched deformation modules identify Galois deformation rings with Hecke algebras; local-global compatibility reads Weil-Deligne monodromy from automorphic representations.
- **Seminal:** Wiles, “Modular elliptic curves and Fermat’s Last Theorem,” 1995; Taylor-Wiles, “Ring-theoretic properties of certain Hecke algebras,” 1995. ([annals.math.princeton.edu](https://annals.math.princeton.edu/1995/141-3/p01?utm_source=openai)) ([annals.math.princeton.edu](https://annals.math.princeton.edu/1995/141-3/p02?utm_source=openai))
- **Structural analog:** modularity lifting converted local Galois representations into automorphic objects where purity and local parameters are constrained by Hecke theory. Here, etale cohomology gives local Galois representations whose monodromy weights might be forced after global automorphic realization.
- **Why default toolkit failed:** the obstruction is a **local-only barrier**. Purely local p-adic Hodge tools do not impose the global Hecke constraints that automorphic representations satisfy.
- **Lean 4/Mathlib:** would use `NumberTheory`, `RingTheory`, `RepresentationTheory`, `AlgebraicGeometry`. Missing: adeles, automorphic forms, Hecke algebras at scale, Galois deformation functors, patched complexes, local Langlands compatibility.

### Technique 5: Bondarko Chow weight structures + conservative weight complex functor
- **Bridge lemma:** a Chow weight structure on triangulated motivic categories gives functorial weight spectral sequences and a conservative weight-complex functor to complexes of Chow motives.
- **Seminal:** Bondarko, “Weight structures vs. t-structures; weight filtrations, spectral sequences, and complexes,” 2010. ([app.scinito.ai](https://app.scinito.ai/article/W3099558573?utm_source=openai))
- **Structural analog:** motivic coniveau and weight spectral sequences become realization-independent. Weight-monodromy looks like the statement that the etale realization’s monodromy filtration is the shadow of a motivic weight structure.
- **Why default toolkit failed:** the obstruction is **realization non-conservativity**. Etale/cohomological spectral sequences can hide extension data; the existing toolkit sees realizations, not a prior motivic filtration that every coefficient theory must respect.
- **Lean 4/Mathlib:** mainly `CategoryTheory`, `HomologicalAlgebra`, `AlgebraicGeometry`. Missing: triangulated/stable infinity categories robust enough for motives, Voevodsky/Chow motives, weight structures, realization functors.

## Ranking
Bayesian scoring here means: **posterior score ∝ prior success in adjacent hard problems × likelihood that the method matches this problem’s obstruction**. These are relative weights among the five, not claims that any path is likely.

1. **Technique 2: TC/Nygaard/prismatic method**  
   Prior 0.25 × likelihood 0.45 = relative posterior **35%**. Best match to the Q_p/F_p coefficient-unification obstruction.

2. **Technique 1: motivic transfer principle**  
   Prior 0.20 × likelihood 0.35 = **22%**. Strong match to the char-p-to-char-0 wall, but only if purity can be made motivic/definable.

3. **Technique 3: nilpotent-orbit / SL2 package**  
   Prior 0.18 × likelihood 0.32 = **18%**. Perfect structural match for monodromy filtrations, but p-adic positivity is the hard missing ingredient.

4. **Technique 5: Bondarko weight structures**  
   Prior 0.16 × likelihood 0.30 = **15%**. Conceptually exact, but depends on very large motivic foundations and conservativity input.

5. **Technique 4: Taylor-Wiles patching**  
   Prior 0.22 × likelihood 0.15 = **10%**. Extremely successful elsewhere, but general varieties are not expected to be automorphic in any currently usable sense.