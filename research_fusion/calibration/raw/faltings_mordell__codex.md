Hindsight note: the actual 1983 unlock was not one isolated trick, but a package. The best 1982 scout would have looked for techniques that turn “height” into geometry on moduli.

### Technique 1: Faltings-Arakelov height via arithmetic Riemann-Roch
- **Key bridge lemma:** replace classical height by the arithmetic degree of the hermitian Hodge line bundle, then compare it using arithmetic intersection theory.
- **Seminal:** Arakelov, *Intersection theory of divisors on an arithmetic surface* (1974); Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern* (1983), which explicitly targets Mordell, Shafarevich, Tate, modular height, and Tate modules. ([mathnet.ru](https://www.mathnet.ru/eng/im2004?utm_source=openai)) ([eudml.org](https://eudml.org/doc/143051))
- **Structural analog:** function-field Mordell/Shafarevich: surfaces over curves already let “height” become degree/intersection. The number-field analog is an arithmetic surface with archimedean Green-function fibers.
- **Why default toolkit failed:** **height-bound obstruction**. Néron-Tate heights control points on a fixed abelian variety, not compactness of abelian varieties in an isogeny class. The missing term is archimedean intersection data.
- **Lean/Mathlib:** would live around `AlgebraicGeometry` plus `NumberTheory.NumberField`; Mathlib has number fields/rings of integers and schemes, but lacks hermitian line bundles, Green currents, arithmetic Chow groups, arithmetic Riemann-Roch, and Faltings height. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Basic.html)) ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Scheme.html))

### Technique 2: Baily-Borel/Siegel moduli compactification with modular-height comparison
- **Key bridge lemma:** compare Faltings height with a projective modular height on a compactified Siegel moduli space; then apply Northcott-type finiteness.
- **Seminal:** Mumford, *Geometric Invariant Theory* (1965); Baily-Borel compactification (1966); Deligne-Mumford stable curves (1969). ([link.springer.com](https://link.springer.com/article/10.1007/s10711-024-00962-8)) ([pmihes.centre-mersenne.org](https://pmihes.centre-mersenne.org/articles/10.1007/BF02684599/))
- **Structural analog:** stable-curve moduli: degenerating families become controllable only after adding boundary strata. Here, abelian varieties in an isogeny class become rational/integral points on finite-type moduli.
- **Why default toolkit failed:** **missing compactness bridge**. Reduction modulo primes gives many local constraints, but no global parameter space on which “bounded height” implies finiteness.
- **Lean/Mathlib:** `AlgebraicGeometry`, `CategoryTheory`, future `AlgebraicGeometry.Stacks/Moduli`. Missing: stacks, GIT quotients, abelian schemes, Siegel modular varieties, compactifications, Hodge line bundles, and projective height theory on moduli.

### Technique 3: Tate-module isogeny criterion via semisimple ℓ-adic Galois representations
- **Key bridge lemma:** `Hom(A,B) ⊗ Z_ℓ ≅ Hom_{G_K}(T_ℓ A, T_ℓ B)`; in particular, compatible Tate modules force isogeny.
- **Seminal:** Tate, *Endomorphisms of Abelian Varieties over Finite Fields* (1966); Faltings’s number-field isogeny theorem (1983). ([eudml.org](https://eudml.org/doc/141848?utm_source=openai)) ([eudml.org](https://eudml.org/doc/143051))
- **Structural analog:** Honda-Tate over finite fields: Frobenius linear algebra classifies isogeny classes. The analogous structure over number fields is the compatible family of Galois representations attached to an abelian variety.
- **Why default toolkit failed:** **Frobenius-shadow obstruction**. Reduction at many primes sees traces, but classical methods cannot reconstruct morphisms or isogenies from those shadows.
- **Lean/Mathlib:** `FieldTheory.Galois`, `RepresentationTheory`, `LinearAlgebra`, `AlgebraicGeometry`. Missing: abelian varieties, Tate modules, profinite/ℓ-adic representations at scale, étale cohomology, Chebotarev in the needed form, and the Tate/Faltings isogeny theorem.

### Technique 4: Serre-Tate/Grothendieck-Messing deformation of p-divisible groups
- **Key bridge lemma:** the infinitesimal deformation theory of an abelian scheme is controlled by its p-divisible group; isogeny kernels become finite-flat/crystalline deformation data.
- **Seminal:** Serre-Tate, *Good reduction of abelian varieties* (1968); Messing, *The Crystals Associated to Barsotti-Tate Groups* (1972). ([annals.math.princeton.edu](https://annals.math.princeton.edu/1968/88-3/p05)) ([link.springer.com](https://link.springer.com/book/10.1007/BFb0058301))
- **Structural analog:** good-reduction criteria for abelian varieties: local p-adic group schemes detect whether a char-0 abelian variety extends well. The analogous feature here is controlling isogenies through their kernels at bad/local primes.
- **Why default toolkit failed:** **char-0 vs char-p lifting obstruction**. Reduction modulo p forgets infinitesimal lift data; Chabauty-style p-adic analysis sees points, not the deformation space of isogeny kernels.
- **Lean/Mathlib:** would sit in `AlgebraicGeometry`, `RingTheory`, `TopologicalAlgebra`, future `AlgebraicGeometry.FormalScheme`. Missing: finite flat group schemes, p-divisible groups, PD-thickenings, crystals, Dieudonné modules, and Grothendieck-Messing deformation theory.

### Technique 5: Griffiths-Schmid Hodge curvature plus Arakelov slope inequality
- **Key bridge lemma:** the Hodge bundle of a non-isotrivial family has positive curvature, and the Kodaira-Spencer/Higgs map bounds its degree by the log-cotangent degree of the base.
- **Seminal:** Griffiths on variations of Hodge structure (1968); Schmid’s nilpotent orbit theorem (1973); Arakelov’s finiteness theorem for families of curves with fixed degeneracies (1971). ([publications.ias.edu](https://publications.ias.edu/sites/default/files/periodsofintegral.pdf)) ([maths.ed.ac.uk](https://www.maths.ed.ac.uk/~v1ranick/papers/schmid.pdf?utm_source=openai)) ([mathnet.ru](https://www.mathnet.ru/php/archive.phtml?jrnid=im&option_lang=eng&paperid=2171&wshow=paper&utm_source=openai))
- **Structural analog:** Shafarevich finiteness over function fields: finitely many nonconstant curve families of fixed genus and fixed bad fibers. Parshin’s construction turns rational points into such family data.
- **Why default toolkit failed:** **missing slope/curvature inequality**. Roth-style approximation estimates divisors; it does not force positivity of a Hodge bundle in a varying family.
- **Lean/Mathlib:** `Analysis.Complex`, `Geometry.Manifold`, `AlgebraicGeometry`. Missing: analyticification, complex vector bundles with connection, Hodge structures/VHS, curvature/Chern-Weil theory, Higgs bundles, and slope inequalities.

## Ranking

1. **Faltings-Arakelov height.** Prior from function-field analogs: 0.40. Fit to this problem’s exact missing input: 0.90. Posterior score: 0.36. This is the direct attack on “height boundedness.”
2. **Siegel moduli compactification.** Prior from moduli boundedness: 0.35. Fit: 0.80. Score: 0.28. It supplies the finite-type/projective space where height bounds become finiteness.
3. **Tate-module isogeny criterion.** Prior from finite-field abelian varieties: 0.30. Fit: 0.75. Score: 0.225. It converts reductions and Galois data into actual isogenies.
4. **p-divisible/crystalline deformation.** Prior from good-reduction theory: 0.25. Fit: 0.70. Score: 0.175. Highly relevant locally, but less obviously a standalone global finiteness engine.
5. **Hodge curvature/slope inequality.** Prior from function-field Shafarevich: 0.30. Fit over number fields: 0.50. Score: 0.15. Conceptually strong, but needs Arakelov arithmetic geometry to cross from complex/function-field geometry into number fields.