1. Aristotle did not prove this; the triangular case is just elementary inversion. For
\[
F(x,y)=(x+p(y),\,y+c),
\]
one has
\[
F^{-1}(u,v)=(u-p(v-c),\,v-c).
\]
The real gap is structural: triangular maps preserve a coordinate flag and can be inverted one variable at a time. A general Keller map only satisfies `det JF = const ≠ 0`, which is one scalar PDE constraint, not a flag. After the Bass-Connell-Wright reduction, the hard core is already the case `F = X - H` with `H` cubic homogeneous and `JH` nilpotent. The triangular case is the very special subcase where this polynomial Jacobian can be made strictly triangular by a linear change of variables. That is exactly what fails in the genuinely coupled case. Even in dimension 2, nontriangular automorphisms of Hénon type show the gap is real.

2. Yes, but only stably. Wang proved degree `≤ 2`; Bass-Connell-Wright and Jagzev reduce the full conjecture to cubic homogeneous maps in arbitrary dimension, and Druzkowski reduces further to cubic linear maps of the form `x + (Ax)^{*3}`. So proving the conjecture for degree `3` in all dimensions would settle it. But proving it only for degree `3` in one fixed dimension would not: the reductions increase dimension.

3. As of March 13, 2026, `JC_2` is still open. The main approaches have been:
the Abhyankar-Moh/Moh approach via branches at infinity, approximate roots, semigroups, and Newton polygons; geometric surface methods using compactifications, properness, and Riemann-Hurwitz; formal-inverse/combinatorial expansions; and noncommutative reformulations via Weyl algebras.
The two-dimensional work has produced strong restrictions, not a proof: one-place-at-infinity cases are controlled, there are no counterexamples of degree `≤ 100` in Moh’s 1983 work, and later papers keep tightening the possible Newton-polygon shape of a minimal counterexample.
On the Dixmier side: yes, there is a stable equivalence. Precisely, `DC_n ⇒ JC_n` and `JC_{2n} ⇒ DC_n`, so the full Jacobian and Dixmier conjectures are equivalent globally. This is conceptually important, but it has not made `JC_2` easier in practice.

4. Nothing “went wrong” with Moh’s valid partial results; what failed is the hope that Newton-polygon data alone force the last step. The Jacobian condition implies very strong restrictions at infinity, but in dimension 2 it gets you only to “at most two points at infinity,” not automatically to one. The surviving two-point configurations allow subtle cancellations under coordinate changes and approximate-root expansions. Newton polygons see leading exponents well, but not enough of the global interaction of the two branches and dicritical behavior. So the method gives degree bounds and shape theorems, but not a complete exclusion of all counterexamples.

5. Reading van den Essen’s surveys together with the 2021 follow-up book, the most promising structural directions are:
the symmetric/gradient reduction `F = x - ∇P` with `P` homogeneous quartic and Hessian nilpotent;
Zhao’s vanishing-conjecture/image-conjecture/Mathieu-Zhao program, which turns invertibility into eventual Laplacian vanishing statements;
and the Dixmier/Poisson/characteristic-`p` route.
If you want a direct attack on `JC_2`, the best live route is still the geometry-at-infinity/Newton-polygon program. If you want the cleanest conceptual reformulation, the symmetric reduction plus Zhao’s vanishing conjecture is probably the sharpest. None currently looks close to a full proof.

6. There is real hope for Lean formalization, but mainly as verification infrastructure, not as a proof-finding strategy. The conjecture is not inherently nonconstructive. Large parts are purely algebraic: multivariate polynomials, Jacobian matrices, nilpotence, cubic and symmetric reductions, and special cases. As of 2026, mathlib already has multivariate polynomials and partial derivatives, determinant machinery, affine-scheme/etale infrastructure, and Ax-Grothendieck. So formalizing the standard reductions and known special cases is realistic. What Lean will not do is supply the missing idea. Its best use here is to make claimed proofs far more trustworthy in a literature famous for subtle gaps.

Sources:
- Bass, Connell, Wright (1982): https://www.ams.org/bull/1982-07-02/S0273-0979-1982-15032-7/
- Druzkowski (1983): https://eudml.org/doc/163789
- de Bondt, van den Essen (2005): https://www.ams.org/proc/2005-133-08/S0002-9939-05-07570-2/
- Wright survey (2007): https://ems.press/content/serial-article-files/46087
- Belov-Kanel, Kontsevich (2007): https://www.mathnet.ru/eng/mmj279
- McKay, Wang (1991): https://www.ams.org/proc/1991-111-01/S0002-9939-1991-1034887-3/
- Druzkowski, geometric approach in `C^2` (1991): https://eudml.org/doc/262260
- Makar-Limanov (2017): https://www.sciencedirect.com/science/article/pii/S002186931630312X
- van den Essen, Kuroda, Crachiola (2021): https://link.springer.com/book/10.1007/978-3-030-60535-3
- Lean/mathlib Ax-Grothendieck: https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/AxGrothendieck.html
- Lean/mathlib partial derivatives: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/PDeriv.html

If you want, I can turn this into a sharper research memo focused only on `JC_2`, or only on the symmetric/Zhao route.