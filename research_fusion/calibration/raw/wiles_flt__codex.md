Below is a hindsight-aware 1985 scouting list: the real escape is to stop attacking cyclotomic class groups directly and attach geometric or analytic objects with global constraints.

### Technique 1: Frey-Serre-Ribet level lowering via the epsilon-conjecture bridge

- **Seminal paper/theorem:** Frey’s stable elliptic-curve bridge, 1986; Ribet’s level-lowering theorem, 1990. Frey attaches \(y^2=x(x-a^p)(x+b^p)\) to a Fermat solution; Ribet proves the missing epsilon conjecture/level-lowering step. Sources: Frey curve history and references; Ribet 1990 citation.
- **Structural analog:** Generalized Fermat equations solved by the modular method: primitive solution -> Frey curve -> mod \(p\) representation -> impossible low-level newform. The analogous FLT feature is the extremely constrained conductor/discriminant of the Frey curve.
- **Why Kummer/Iwasawa failed:** **Wrong object obstruction.** Cyclotomic descent studies \(\mathbb{Q}(\zeta_p)\) class groups; it does not convert a putative solution into a rigid two-dimensional Galois representation with forced conductor.
- **Lean/Mathlib:** Infrastructure lives around `Mathlib.AlgebraicGeometry.EllipticCurve`, `Mathlib.NumberTheory.ModularForms`, `Mathlib.FieldTheory.AbsoluteGaloisGroup`, `Mathlib.NumberTheory.RamificationInertia`. Missing: modular curves, Galois reps attached to newforms, conductors of elliptic curves, and Ribet level lowering.

### Technique 2: Taylor-Wiles `R = T` modularity lifting via numerical patching

- **Seminal paper/theorem:** Wiles, “Modular elliptic curves and Fermat’s Last Theorem,” 1995; Taylor-Wiles, “Ring-theoretic properties of certain Hecke algebras,” 1995, same Annals issue.
- **Structural analog:** Unlocks semistable elliptic-curve modularity: local deformation conditions on a residual Galois representation are matched to Hecke algebra geometry. The FLT analog is exact: Frey curves are semistable, so modularity plus Ribet gives a contradiction.
- **Why default toolkit failed:** **Missing reciprocity bridge.** Kummer-style methods cannot prove “this elliptic curve comes from a modular form.” The obstruction is char-0 global reciprocity, not more cyclotomic computation.
- **Lean/Mathlib:** Relevant base: `Mathlib.RingTheory.LocalRing`, `Mathlib.RingTheory.PowerSeries`, `Mathlib.CategoryTheory.Abelian`, `Mathlib.NumberTheory.ModularForms`. Missing: deformation functors, complete Noetherian local deformation rings, Hecke algebras, patched modules, Gorenstein/complete-intersection numerical criteria.

### Technique 3: Oesterle-Masser `abc` via the Mason-Stothers radical-height inequality

- **Seminal paper/theorem:** Mason-Stothers polynomial `abc` theorem, 1981/1984; Oesterle-Masser `abc` conjecture, 1985. The integer conjecture relates height to the radical and would imply a new proof of FLT; Mason-Stothers is the polynomial analog.
- **Structural analog:** Polynomial FLT is killed because \(A^n+B^n=C^n\) has huge degree but small radical. Integer FLT has the same shape: \(\operatorname{rad}(a^p b^p c^p)=\operatorname{rad}(abc)\), so powers inflate height without inflating radical.
- **Why default toolkit failed:** **Radical-height barrier.** Cyclotomic descent sees ideal divisibility and class groups, not a global inequality forcing many distinct prime factors in \(abc\).
- **Lean/Mathlib:** `Mathlib.NumberTheory.FLT.MasonStothers` already exists for the polynomial side; also `Mathlib.Data.Nat.Squarefree`, `Nat.primeFactors`. Missing: integer radical API as a first-class object, logarithmic/projective heights, formal `abc`, and the derivation `abc -> FLT for p >= 5`.

### Technique 4: Faltings-Parshin-Arakelov finiteness via Shafarevich height compactness

- **Seminal paper/theorem:** Faltings, “Endlichkeitssätze für abelsche Varietäten über Zahlkörpern,” 1983, proving Mordell/Shafarevich/Tate finiteness. Faltings’ introduction explicitly uses Tate modules, Shafarevich finiteness, Mordell, and Arakelov’s dictionary.
- **Structural analog:** Mordell’s conjecture: genus \(>1\) curves have finitely many rational points. Fermat curves \(X_p: x^p+y^p=z^p\) have genus \((p-1)(p-2)/2\); FLT asks that all rational points are trivial.
- **Why default toolkit failed:** **Ineffective finiteness/uniformity gap.** Kummer methods give prime-by-prime criteria and density-zero failures; Faltings gives global compactness, but not an explicit list of rational points uniformly in \(p\).
- **Lean/Mathlib:** `Mathlib.AlgebraicGeometry`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.CategoryTheory`, `Mathlib.NumberTheory.NumberField`. Missing: smooth projective curves as a mature API, Jacobians/abelian varieties, Neron models, Arakelov heights, Faltings height, Shafarevich finiteness.

### Technique 5: Coleman-Chabauty p-adic integration via the annihilating differential lemma

- **Seminal paper/theorem:** Chabauty’s method, 1941; Coleman’s effective Chabauty, 1985. Coleman’s “Effective Chabauty” is Duke Math. J. 52, 1985; his p-adic Abelian integrals paper is also 1985.
- **Structural analog:** Rational-point computations on high-genus curves when \(\operatorname{rank} J(\mathbb{Q})<g\). Fermat curves have huge genus and Jacobians with CM decompositions; annihilating differentials could isolate rational points residue disk by residue disk.
- **Why default toolkit failed:** **Mordell-Weil rank barrier.** Cyclotomic descent does not produce rank bounds for \(J(X_p)\), nor p-adic analytic functions vanishing on rational points.
- **Lean/Mathlib:** `Mathlib.NumberTheory.Padics`, `Mathlib.Topology.Algebra`, `Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian` for tiny fragments. Missing: p-adic manifolds on curves, Coleman integration, Jacobians of general curves, Mordell-Weil theorem, rank algorithms.

## Ranking

| Rank | Technique | Bayesian sketch |
|---:|---|---|
| 1 | Frey-Serre-Ribet level lowering | Prior high from modular forms/elliptic curves already solving Diophantine structure; likelihood extremely high because a Fermat solution gives exactly the needed semistable Frey curve. Posterior weight: **0.24**. |
| 2 | Taylor-Wiles `R = T` patching | Prior medium: deformation theory was young, but reciprocity was the right scale. Likelihood very high once Technique 1 identifies semistable modularity as the target. Posterior weight: **0.18**. |
| 3 | `abc` / Mason-Stothers | Prior medium from function-field success; likelihood high because the radical-height mismatch is perfectly aligned with powers. Discount: proving `abc` is at least as hard as a major new theory. Posterior weight: **0.09**. |
| 4 | Faltings-Parshin-Arakelov | Prior high for rational points on curves; likelihood modest because FLT needs explicit uniform no-points, not just finiteness for each \(p\). Posterior weight: **0.045**. |
| 5 | Coleman-Chabauty | Prior medium for explicit rational points; likelihood lower because the required uniform rank inequality for Fermat Jacobians is a serious missing input. Posterior weight: **0.028**. |

Techniques 1 and 2 are coupled: 1 supplies the FLT-specific contradiction, 2 supplies the modularity theorem needed to activate it.