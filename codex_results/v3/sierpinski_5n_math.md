For integral `a,b,c`, this is not an open conjecture. It is a direct corollary of the Gauss-Legendre three-square theorem.

\[
n=a^2+b^2+c^2+5c
\quad\Longleftrightarrow\quad
4n+25=(2a)^2+(2b)^2+(2c+5)^2.
\]

Conversely, if `4n+25=x^2+y^2+z^2`, then `4n+25 ≡ 1 (mod 4)`, so exactly one of `x,y,z` is odd and two are even. After permuting, write `x=2a`, `y=2b`, `z=2c+5` with `c=(z-5)/2 ∈ Z`. So

\[
n \text{ is represented by } a^2+b^2+c^2+5c
\iff
4n+25 \text{ is a sum of three squares.}
\]

By Legendre, a positive integer is a sum of three squares iff it is not of the form `4^r(8s+7)`. But `4n+25 ≡ 1` or `5 (mod 8)`, and is never divisible by `4`, so `4n+25` is never of that forbidden shape. Hence every positive integer `n` is represented.

1. The gap between “almost all” and “all” is normally enormous: density zero can still be infinite. Here, though, the gap is completely closed by the exact reformulation above. The density argument is much weaker than the classical theorem you actually need.

2. The exact arithmetic obstruction set is empty. For the ternary form `x^2+y^2+z^2`, the only local obstruction is `4^r(8s+7)`. Your progression `4n+25` never meets it. So there is no surviving local, genus, or spinor obstruction on this progression. The set that “resists” the density proof is only a proof artefact, not a real obstruction class.

3. The right quadratic-form viewpoint is not the 290-theorem. It is the conductor-2 inhomogeneous ternary polynomial attached to the coset `ν+Z^3` with `Q=x^2+y^2+z^2` and `ν=(0,0,5/2)`. General theory of almost-universal ternary inhomogeneous polynomials lives here. The 290-theorem is about universal positive-definite integer-valued quadratic forms over `Z`, essentially a rank-4-and-higher story in the homogeneous setting.

4. Yes, it reduces to finitely many checks in a vacuous way: none are needed. An explicit bound is `N0=1`; in fact the theorem already gives all `n≥1` outright.

5. As of March 13, 2026, the state of the art for this specific polynomial is: it is already classically solved, and equivalent to the three-square theorem restricted to the progression `4n+25`. So it is not an open universality problem. If you meant `a,b,c ≥ 0` instead of arbitrary integers, that is a different problem.

Sources:
- [Pollack-Schorn, “Dirichlet’s proof of the three-square theorem” (AMS, 2019)](https://www.ams.org/mcom/2019-88-316/S0025-5718-2018-03349-X/)
- [Bhargava-Hanke, *Universal quadratic forms and the 290-Theorem*](https://math.stanford.edu/~vakil/files/290-Theorem-preprint.pdf)
- [Haensch, “A characterization of almost universal ternary inhomogeneous quadratic polynomials with conductor 2”](https://doi.org/10.1016/j.jnt.2015.04.016)
- [Chan-Ricci, “The representation of integers by positive ternary quadratic polynomials”](https://doi.org/10.1016/j.jnt.2015.03.007)
- [Kala et al., “Ternary quadratic forms representing a given arithmetic progression”](https://doi.org/10.1016/j.jnt.2021.09.017)

