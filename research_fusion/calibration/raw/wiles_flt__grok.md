### Technique 1: Ribet level-lowering + Frey-curve Galois deformation bridge
**Technique name**: Ribet level-lowering + Frey-curve Galois deformation bridge  
**Seminal paper or theorem**: Ribet, "On modular representations of Gal(ℚ̄/ℚ) arising from modular forms" (Invent. Math. 100, 1990; core ideas circulated 1985–86).  
**Structural analog**: Proved Serre's conjecture for semistable elliptic curves (unlocking Mazur's torsion theorem extensions); the analogous feature here is that a hypothetical primitive solution (a^p, b^p, c^p) produces a Frey elliptic curve y² = x(x−a^p)(x+b^p) whose mod-p Galois representation is irreducible yet unramified outside p, forcing a modular lift that contradicts the conductor.  
**Diagnosis of why the default toolkit failed**: missing computable bridge (no explicit map from cyclotomic class groups to the deformation ring of the elliptic Galois representation).  
**Implementation comment**: Mathlib namespace `number_theory.elliptic_curves` and `representation_theory.galois_representation`; missing is the full deformation-ring machinery (`galois_deformation`) and Taylor–Wiles patching lemmas.

### Technique 2: Pila–Wilkie o-minimal point-counting + Pfaffian parameterization bridge
**Technique name**: Pila–Wilkie o-minimal point-counting + Pfaffian parameterization bridge  
**Seminal paper or theorem**: Pila & Wilkie, "The rational points of a definable set" (Duke Math. J. 133, 2006).  
**Structural analog**: Unlocked the André–Oort conjecture for products of modular curves (Pila 2011); the analogous structural feature is that solutions to a^n + b^n = c^n embed into the real points of the Fermat curve inside (ℂ^*)², a set definable in an o-minimal expansion of ℝ_exp whose transcendental part admits effective height bounds independent of n.  
**Diagnosis of why the default toolkit failed**: height bound (Iwasawa-theoretic regulators give only logarithmic control; no uniform upper bound on naive height that grows slower than any power of the conductor).  
**Implementation comment**: Would live in `model_theory.o_minimal` (currently a stub in Mathlib); missing is the cell decomposition API for ℝ_an,exp and the Pila–Wilkie counting lemma formalized over number fields.

### Technique 3: Ratner measure-classification + unipotent orbit closure bridge
**Technique name**: Ratner measure-classification + unipotent orbit closure bridge  
**Seminal paper or theorem**: Ratner, "On Raghunathan’s measure conjecture" (Ann. of Math. 134, 1991).  
**Structural analog**: Solved the Oppenheim conjecture on values of indefinite quadratic forms at integer points ( Dani–Margulis 1989–91); the analogous feature is the logarithmic embedding of units (log|a|, log|b|, log|c|) lying on a homogeneous space SL(3,ℝ)/SL(3,ℤ) where a^n + b^n = c^n forces a diagonal flow orbit whose closure must be algebraic, contradicting volume estimates unless the only orbits are the trivial torsion ones.  
**Diagnosis of why the default toolkit failed**: density-zero issue (cyclotomic/Iwasawa methods control p-adic places but give no equidistribution at the Archimedean place needed to rule out sparse integer points).  
**Implementation comment**: Mathlib namespace `dynamics.homogeneous_space` and `ergodic_theory.measure_preserving`; missing is formalization of Ratner’s theorems, Dani correspondence, and the classification of invariant measures on SL(n,ℝ)/Γ.

### Technique 4: Green–Tao–Ziegler inverse theorem for Gowers norms + uniformity-norm equidistribution bridge
**Technique name**: Green–Tao–Ziegler inverse theorem for Gowers norms + uniformity-norm equidistribution bridge  
**Seminal paper or theorem**: Green, Tao & Ziegler, "An inverse theorem for the Gowers U^{s+1}[N]-norm" (Ann. of Math. 176, 2012).  
**Structural analog**: Proved existence of arbitrarily long arithmetic progressions in the primes (Green–Tao 2008); the analogous structural feature is that the set of nth powers (viewed as a subset of ℤ/Nℤ with N = p^k large) would have small Gowers U^{2}-norm if many solutions to a^n + b^n ≡ c^n existed, forcing an algebraic correlation (nilsequence) that contradicts the pseudorandomness inherited from Bernoulli-number criteria.  
**Diagnosis of why the default toolkit failed**: sieve barrier / parity (regular-prime descent only sieves one prime at a time; no uniform inverse theorem that detects additive structure across all large primes simultaneously).  
**Implementation comment**: Would sit in `additive_combinatorics.gowers_norm` (Mathlib has only rudimentary uniformity); missing are the inverse theorems, nilsequence equidistribution, and the quantitative PET induction.

### Technique 5: Faltings Arakelov height inequality + stable Faltings height gap bridge
**Technique name**: Faltings Arakelov height inequality + stable Faltings height gap bridge  
**Seminal paper or theorem**: Faltings, "Finiteness theorems for abelian varieties over number fields" (Invent. Math. 73, 1983).  
**Structural analog**: Proved the Mordell conjecture (finitely many rational points on curves of genus ≥2); the analogous structural feature is that the Fermat curve x^p + y^p = 1 has genus (p−1)/2 → ∞, so its Jacobian’s Arakelov height forces only finitely many rational points whose naive height is bounded independently of any fixed prime, allowing a uniform descent that kills non-trivial solutions.  
**Diagnosis of why the default toolkit failed**: char-0 vs char-p (Kummer descent works only after fixing p and reducing to regular primes; no global height machine that produces effective bounds uniform in p).  
**Implementation comment**: Mathlib namespace `algebraic_geometry.curves` and `arithmetic_geometry.arakelov`; missing is the full Arakelov intersection theory, stable Faltings height, and the proof of the height inequality (requires formalization of moduli stacks of abelian varieties).

## Ranking
**Rank 1 (highest probability ≈ 45 %)**: Technique 1 (Ribet level-lowering + Frey-curve bridge). Bayesian prior: algebraic-geometry methods had already succeeded on congruent-number problems and Mazur’s torsion theorem (≈ 0.35 prior on “modular methods unlock Diophantine equations of this shape”); likelihood given FLT’s structure is high because the Frey curve supplies an explicit, computable Galois representation exactly where cyclotomic class-group data are insufficient. Posterior dominates all others.

**Rank 2 (≈ 20 %)**: Technique 3 (Ratner measure-classification). Prior ≈ 0.15 (Ratner solved several long-standing homogeneous-space Diophantine problems post-1985); likelihood boosted by the exact match between the logarithmic embedding of Fermat solutions and the diagonal flow on SL(3,ℝ)/SL(3,ℤ), but docked because one still needs an effective rate of equidistribution not yet available in 1985-era homogeneous dynamics.

**Rank 3 (≈ 15 %)**: Technique 2 (Pila–Wilkie o-minimal counting). Prior ≈ 0.10 (o-minimality had solved several transcendence problems but few pure Diophantine ones); likelihood moderate because the Fermat curve is definable in ℝ_an,exp, yet the required parameterization lemmas for the multiplicative group are not fully automatic, lowering conditional probability.

**Rank 4 (≈ 12 %)**: Technique 5 (Faltings Arakelov height). Prior ≈ 0.25 (Faltings 1983 had just solved Mordell); likelihood reduced because the theorem only yields finiteness, not effective absence of points, and the height gap is too coarse to kill the trivial points uniformly in p without an extra descent step that reverts to Kummer-type arguments.

**Rank 5 (≈ 8 %)**: Technique 4 (Green–Tao–Ziegler inverse theorem). Prior ≈ 0.05 (additive-combinatorics inverse theorems post-date 1985 and succeeded on sparse sets like primes); likelihood lowest because perfect powers are exponentially sparser than primes, so the uniformity-norm control would require quantitative bounds far beyond current technology, making success on FLT conditional on several unproven density improvements.