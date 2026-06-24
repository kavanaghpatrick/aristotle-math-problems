### Technique 1: Ax-Kochen-Ershov transfer principle
**Technique name**: Ax-Kochen-Ershov transfer principle via ultraproducts (with Los' theorem bridge lemma)  
**Seminal paper or theorem**: Ax-Kochen, "Diophantine problems over local fields I" (Amer. J. Math. 87, 1965)  
**Structural analog**: Solved Artin's conjecture on nontrivial zeros of homogeneous forms over p-adics by transferring from positive-characteristic local fields; the analogous feature here is the existence of a weight filtration on etale cohomology, which transfers directly from the known positive-characteristic function-field case once etale cohomology and monodromy are expressed in a first-order language.  
**Diagnosis of why the default toolkit failed**: char-0 vs char-p obstruction (no geometric Frobenius lift in mixed characteristic prevents direct comparison theorems from carrying purity).  
**Implementation comment**: Lives in Mathlib's `model_theory` and `ultrafilter` namespaces (with `first_order.language` for structures); missing: formalization of etale cohomology functors as first-order definable objects and a `weight_filtration` predicate compatible with ultraproducts.

### Technique 2: Ratner measure rigidity
**Technique name**: Ratner orbit-closure theorem with measure-classification bridge lemma  
**Seminal paper or theorem**: Ratner, "On Raghunathan's measure conjecture" (Ann. of Math. 134, 1991)  
**Structural analog**: Classified unipotent orbit closures to resolve Oppenheim's conjecture on quadratic forms; the analogous feature is the monodromy representation of inertia acting on the flag variety of filtrations on etale cohomology, where rigidity of invariant probability measures forces the existence of a unique weight filtration with pure graded pieces.  
**Diagnosis of why the default toolkit failed**: missing computable bridge (p-adic Hodge rings B_dR/B_crys yield filtrations only up to conjugacy; no rigidity theorem controls the closure of monodromy orbits).  
**Implementation comment**: Would sit in a prospective `dynamics.homogeneous` or `lie_group.action` namespace extending current `ergodic_theory`; missing: formalization of Ratner-type theorems for p-adic Lie groups and the monodromy action on cohomology lattices.

### Technique 3: Pila-Wilkie o-minimal counting
**Technique name**: Pila-Wilkie theorem with definable-set point-counting bridge lemma  
**Seminal paper or theorem**: Pila-Wilkie, "The rational points of a definable set" (Duke Math. J. 133, 2006)  
**Structural analog**: Gave effective bounds leading to proofs of Andre-Oort for certain Shimura varieties (Pila-Tsimerman et al.); the analogous structural feature is viewing the set of "bad" Galois representations (those without a weight-monodromy filtration) as a definable set in an o-minimal structure on the p-adics, where point-counting forces it to be empty.  
**Diagnosis of why the default toolkit failed**: density-zero issue (etale cohomology methods produce only density-zero control on monodromy images; no effective height bounds).  
**Implementation comment**: Belongs in `model_theory.o_minimal` (current stubs exist for real subanalytic sets); missing: p-adic o-minimal structures (Cluckers-Miller) and a `definable_etale_cohomology` API linking to `algebraic_geometry.etale_cohomology`.

### Technique 4: Balmer tt-geometry spectrum
**Technique name**: Balmer spectrum construction for tensor-triangulated categories with support-theory bridge lemma  
**Seminal paper or theorem**: Balmer, "The spectrum of prime ideals in tensor triangulated categories" (Invent. Math. 167, 2005)  
**Structural analog**: Classified thick ideals in the stable homotopy category and recovered Hopkins-Smith nilpotence; the analogous feature is realizing p-adic etale motives as a tt-category whose Balmer spectrum classifies supports corresponding to weights, forcing the monodromy filtration to exist by support purity.  
**Diagnosis of why the default toolkit failed**: missing computable bridge (Fontaine rings give only local data; no global geometric object parametrizes all possible weights simultaneously).  
**Implementation comment**: Would extend `category_theory.tensor_triangulated` and `algebraic_geometry` (current tt-category formalizations are minimal); missing: `motive` or `etale_motive` namespace with Balmer spectrum and support functors for p-adic coefficients.

### Technique 5: Furstenberg correspondence principle
**Technique name**: Furstenberg correspondence principle with multiple-recurrence bridge lemma  
**Seminal paper or theorem**: Furstenberg, "Ergodic behavior of diagonal measures and a theorem of Szemeredi on arithmetic progressions" (J. Analyse Math. 31, 1977)  
**Structural analog**: Transferred Szemeredi's theorem on arithmetic progressions from ergodic multiple recurrence; the analogous feature is recasting the monodromy action on etale cohomology as a measure-preserving system on a probability space of filtrations, where multiple recurrence detects the pure-weight graded pieces.  
**Diagnosis of why the default toolkit failed**: density-zero issue (standard comparison theorems only control "generic" fibers; no recurrence mechanism forces purity on a positive-measure set of specializations).  
**Implementation comment**: Extends existing `ergodic_theory` and `measure_theory` namespaces; missing: formalization of monodromy representations as measure-preserving actions and the correspondence between etale cohomology and invariant measures.

## Ranking
**Rank 1: Technique 1 (Ax-Kochen-Ershov transfer)** – Prior ≈0.35 (high success rate in transferring local-field statements from char-p to char-0, e.g. Artin conjecture, Ax's work on Hilbert's 17th). Likelihood given structure ≈0.7 (weight-monodromy is known precisely in function fields via Deligne; the only global obstruction cited is char-0 vs char-p). Posterior ≈0.245.  
**Rank 2: Technique 2 (Ratner measure rigidity)** – Prior ≈0.25 (solved several homogeneous-space diophantine problems cleanly). Likelihood ≈0.55 (monodromy is literally a unipotent action on a flag variety; rigidity directly produces the filtration). Posterior ≈0.137.  
**Rank 3: Technique 3 (Pila-Wilkie o-minimal counting)** – Prior ≈0.20 (strong track record on unlikely-intersections problems in arithmetic geometry). Likelihood ≈0.45 (requires re-expressing the non-existence of filtrations as a definable set of "special points"; works but needs height machinery). Posterior ≈0.09.  
**Rank 4: Technique 4 (Balmer tt-geometry spectrum)** – Prior ≈0.15 (tt-geometry classified large swaths of stable homotopy and motivic categories). Likelihood ≈0.4 (p-adic motives exist but their tt-category is not yet built; spectrum would give weights as supports, yet formalization distance is large). Posterior ≈0.06.  
**Rank 5: Technique 5 (Furstenberg correspondence)** – Prior ≈0.10 (successful mainly for density statements in combinatorics). Likelihood ≈0.35 (monodromy action can be ergodicized, but constructing a probability measure on filtrations compatible with p-adic Hodge theory is indirect). Posterior ≈0.035.