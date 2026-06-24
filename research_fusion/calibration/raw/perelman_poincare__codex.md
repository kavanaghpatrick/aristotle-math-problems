Mathlib already has the 3D Poincare statement as `proof_wanted` in `Mathlib.Geometry.Manifold.PoincareConjecture`; none of the analytic proof infrastructure below is formalized at that level.

### Technique 1: Gross-Li-Yau entropy method + entropy-to-noncollapsing bridge
- **Seminal paper/theorem:** Gross, “Logarithmic Sobolev inequalities” 1975; Li-Yau heat-kernel differential Harnack, 1986. Hindsight target: Perelman’s entropy/reduced-volume machinery, 2002.
- **Structural analog:** Huisken’s monotonicity formula unlocked mean-curvature-flow singularity analysis. Analog here: Ricci flow needs a scale-invariant Lyapunov quantity that survives blow-up.
- **Default-toolkit failure:** `collapsing-at-bounded-curvature obstruction`. Cheeger-Gromov compactness needs injectivity radius; Hamilton’s estimates control curvature, not volume collapse.
- **Lean/Mathlib:** `MeasureTheory`, `ProbabilityTheory`, `Analysis.FunctionalSpaces.SobolevInequality`, `Geometry.Manifold.Riemannian`. Missing: Ricci curvature tensors, heat equation on manifolds, Ricci flow, W-functional, reduced distance, log-Sobolev-to-noncollapse theorem.

### Technique 2: Lions concentration-compactness + defect-measure/bubble-tree quantization lemma
- **Seminal paper/theorem:** P.-L. Lions, concentration-compactness principle, 1984; Sacks-Uhlenbeck, minimal 2-spheres, 1981.
- **Structural analog:** Yamabe-type compactness and harmonic-map bubbling: loss of compactness becomes finitely many bubbles plus a defect measure. Analog here: singular Ricci-flow regions should decompose into classified blow-up models plus controlled necks.
- **Default-toolkit failure:** `critical-scale bubbling defect`. Subsequence limits exist, but curvature can concentrate and vanish into neck regions without a quantitative bookkeeping measure.
- **Lean/Mathlib:** `MeasureTheory`, `Analysis.Normed`, `Analysis.FunctionalSpaces`, `Topology.MetricSpace`, `Geometry.Manifold`. Missing: Sobolev maps between manifolds, weak compactness/profile decompositions, defect measures, bubble-tree compactness, parabolic regularity.

### Technique 3: Almgren-Pitts sweepout min-max + almost-minimizing replacement lemma
- **Seminal paper/theorem:** Pitts, *Existence and Regularity of Minimal Surfaces on Riemannian Manifolds*, 1981; Almgren’s varifold program, 1965.
- **Structural analog:** Yau’s embedded-minimal-surface existence problem was attacked by converting topology into sweepouts and extracting regular minimal hypersurfaces. Analog here: use canonical minimal spheres/tori as topological witnesses for prime/JSJ cuts.
- **Default-toolkit failure:** `surgery-certification gap`. Local geometric necks do not by themselves give a global, canonical topological certificate that the cut/discard step preserves the target conclusion.
- **Lean/Mathlib:** `MeasureTheory`, `Geometry.Manifold`, `AlgebraicTopology.SingularHomology`, `Geometry.Manifold.Bordism`. Missing: currents, varifolds, mass/flat topology, first variation, replacement regularity, min-max sweepouts.

### Technique 4: Bestvina-Paulin R-tree limits/Rips machine + Rips-Sela JSJ extraction
- **Seminal paper/theorem:** Bestvina-Feighn stable actions on real trees, 1995; Rips-Sela cyclic splittings/JSJ for finitely presented groups, 1997; Bowditch convergence groups, 1998.
- **Structural analog:** Equations and splittings in hyperbolic groups were unlocked by taking limiting actions on R-trees and extracting canonical decompositions. Analog here: thin neck/collapse regions should correspond to splittings over small subgroups.
- **Default-toolkit failure:** `JSJ-recognition gap`. PDE collapse sees thin geometry but not the exact algebraic decomposition into spherical, Seifert, and hyperbolic pieces.
- **Lean/Mathlib:** `GroupTheory`, `GroupTheory.FreeGroup`, `Topology.Algebra.ProperAction`, `AlgebraicTopology.FundamentalGroupoid`. Missing: finitely presented groups as 2-complexes, Bass-Serre theory, R-trees, hyperbolic groups, convergence boundaries, 3-manifold group recognition.

### Technique 5: Monopole/Heegaard Floer surgery exact triangle + adjunction inequality bridge
- **Seminal paper/theorem:** Witten’s Seiberg-Witten invariants, 1994; Kronheimer-Mrowka adjunction machinery, 1995; Ozsvath-Szabo Heegaard Floer invariants, 2001.
- **Structural analog:** Gauge/Floer methods unlocked smooth 4-manifold rigidity and later knot-surgery detection problems. Analog here: homology 3-spheres might be distinguished by a computable invariant stable under controlled surgery.
- **Default-toolkit failure:** `topological-invisibility gap`. Ricci flow changes topology at singular times; without an independent invariant, discarded components are hard to certify globally.
- **Lean/Mathlib:** `Geometry.Manifold`, `AlgebraicTopology`, `Algebra.Homology`, `Algebra.Lie`, `CategoryTheory`. Missing: Spin^c structures, Clifford bundles, elliptic Fredholm theory, gauge moduli spaces, transversality/orientations, Floer chain complexes, exact triangles.

## Ranking

| Rank | Technique | Prior from adjacent wins | Likelihood given this obstruction | Bayesian read |
|---:|---|---:|---:|---|
| 1 | Entropy-to-noncollapsing | 0.35 | 0.80 | Highest. Directly targets collapse and singularity control; this is essentially the historical unlock. |
| 2 | Concentration-compactness | 0.30 | 0.45 | Strong. Correct shape for blow-up analysis, but still needs a Ricci-specific monotone quantity. |
| 3 | Almgren-Pitts min-max | 0.20 | 0.25 | Plausible auxiliary unlock. Gives topological certificates, not full long-time metric control. |
| 4 | R-tree/Rips-Sela JSJ | 0.18 | 0.18 | Useful for geometrization structure, weaker for simply-connected Poincare directly. |
| 5 | Floer/gauge exact triangles | 0.22 | 0.12 | Powerful but indirect. Detects topology, unlikely to control Ricci-flow singularities itself. |