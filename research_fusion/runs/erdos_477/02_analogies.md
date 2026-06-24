# Erdős 477 — Stage 2 Analogies (W4-D, May 31 2026)

## Primary cross-domain analog: Newman-de Bruijn polynomial tiling of Z

The unique-representation requirement z = a + f(n) for every z ∈ Z is exactly a **TILING of Z by translates of the set f(N>0) = {f(1), f(2), ...}**. The translate set is A; the prototile is the polynomial image.

Newman (J. Number Theory, 1977) classified periodic tilings of Z by finite prototiles. The key invariant: if A ⊕ T = Z (uniquely), then the indicator generating function 1_A(z) · 1_T(z) = 1/(1-z) (a unit in Z[[z]]). For an **infinite** prototile T = {f(n) : n > 0} this becomes the formal identity

$\left(\sum_{a \in A} z^a\right) \cdot \left(\sum_{n > 0} z^{f(n)}\right) = \frac{1}{1-z}$ (as formal Laurent series in $z, z^{-1}$).

The right side is a unit in Z[[z, z^{-1}]] with a single pole at z = 1; this is the "generating-function unit" criterion mentioned by Grok-4.3 in earlier consultation (May 30 2026), **but the unit criterion alone has no concrete cyclotomic obstruction for cubes** — the cube generating function $\sum_{n \geq 1} z^{n^3}$ is a transcendental theta-like series with no cyclotomic root structure.

The cleaner analog is Sekanina's own X^2 argument transferred to X^3.

## Sekanina X^2 sketch (template to transfer)

For f(n) = n^2, the differences f(n+1) − f(n) = 2n + 1 enumerate ALL odd positive integers, **each appearing exactly once**. If A is an exact unique-representation complement of {n^2 : n ≥ 1}, then for every odd positive integer 2k+1 there is a unique pair (a, n) with a ∈ A, z = 2k+1 + (something). Sekanina translates this into a counting identity on A and uses parity / mod-4 cube residues to derive a finite contradiction.

## Sekanina-style template for X^3

For f(n) = n^3, the differences f(n+1) − f(n) = 3n^2 + 3n + 1 are precisely the **centered hexagonal numbers** = {1, 7, 19, 37, 61, ...}. These are all ≡ 1 (mod 6), and every positive integer ≡ 1 (mod 6) is NOT necessarily a centered hexagonal — the centered hexagonals are a much sparser set (density ~ √(x/3) up to x). So the analog of Sekanina's "all odd numbers" fact FAILS for X^3: the cubic differences do NOT enumerate a clean residue class.

This is exactly why the X^3 case is harder: the cubic difference operator does not give the same "all-of-residue-class" tightness that the quadratic one does. Sekanina's argument is degree-specific.

## Alternative analog: Erdős–Freud–Hegyvári type bounds

Erdős–Freud–Hegyvári (Acta Arith 1990) — bounds on sumset covers by sparse sequences. For squares (r=2) they give a quantitative lower bound on A(x)B(x) - x. The result generalises to r-th powers (Cilleruelo 1993). But these are all **average** results (covering), not unique-representation results. The unique-representation strengthening fails because uniqueness is a much rarer property than covering.

## Plünnecke–Ruzsa sumset bound (weak)

Pl-R applied to A ⊕ C = Z with |C ∩ [1,N]| ~ N^{1/3} forces |A ∩ [-N,N]| ~ N^{2/3}. Then |A + A| ≪ |A|^{4/3} · N^{1/3} ≪ N^{4/3}. This is a sumset upper bound, but **the uniqueness constraint pushes |A+A| toward |A|^2 = N^{4/3}, matching exactly — so Plünnecke–Ruzsa is borderline tight and does NOT immediately contradict.**

## The cleanest analog: arithmetic progressions and Hajós factorisation

Z = A ⊕ B with B = f(N>0) is an *unbounded* analog of Hajós's theorem on factorising finite abelian groups by ordered sets. Hajós showed for finite cyclic groups Z/n that if B is a "complete" set (i.e. one of {0, 1, ..., k-1} times some generator), then the complement structure is rigid. For infinite Z with B = cubes, the natural analog would say: **the cubes are "too spread" to be a Hajós-factor of Z** — exactly the X^3 conjecture.

## Honest assessment

There is NO known cross-domain technique that directly resolves the X^3 case. The natural analogs (Newman tiling, Sekanina mod-4 transfer, Pl-R sumset bound, Hajós factorisation) all fail to close. The MOST PLAUSIBLE attack route is a **Sekanina-style counting refinement** using the centered-hexagonal structure of cubic differences and a finer modular obstruction (mod 7, mod 9, mod 13, or higher), but this has not been pulled off in the published literature.
