**Correction**
- Your items `1` and `2` mix up different problems.
- Erdős problem `#672` is the product problem
  \[
  x(x+d)\cdots(x+(k-1)d)=y^\ell,\qquad \gcd(x,d)=1,\ \ell\ge 2,
  \]
  not “`35` cubes in arithmetic progression”.
- For actual cubes in AP, the problem is already dead at length `3`: a nontrivial 3-term AP of `n`-th powers with `n>=3` would solve \(X^n+Y^n=2Z^n\), ruled out by Darmon–Merel.
- For the product being a cube, `k=35` is also not open: Hajdu–Tengely–Tijdeman rule out positive solutions for `k<39`.
- So `k=35` is the first open case only for the **general product-is-a-perfect-power problem**, with exponent \(\ell\) unspecified.

**Answers**
- `2.` Correct rephrasing for `#672`:
  \[
  x,\ x+d,\ \dots,\ x+34d \text{ in AP, with } x(x+d)\cdots(x+34d)=y^\ell.
  \]
  If you mean “35 cubes in AP”, that is a different question, and it is already impossible because length `3` is impossible.

- `3.` If you force the superelliptic model for fixed prime \(\ell\),
  \[
  C_{35,\ell}: Y^\ell = X(X+1)\cdots(X+34),
  \]
  then the smooth projective genus is
  \[
  g=\frac{(\ell-1)(35-1)-\gcd(\ell,35)+1}{2}.
  \]
  Hence:
  - \(g=17(\ell-1)\) for prime \(\ell\neq 5,7\)
  - \(g=66\) for \(\ell=5\)
  - \(g=99\) for \(\ell=7\)

  But this is not how GHP09 actually prove `k<=34`. They reduce to many auxiliary ternary equations of signatures \((\ell,\ell,2)\), \((\ell,\ell,3)\), \((\ell,\ell,\ell)\), then eliminate those by modular and local methods.

- `4.` There is no known general Jacobian-rank computation for \(J(C_{35,\ell})(\mathbf Q)\). In the `k=35` case, Chabauty–Coleman is not presently usable because the key inequality \(\operatorname{rank}J(\mathbf Q)<g\) is not established. So the honest answer is: **the rank is not known here in any form useful enough to run Chabauty**.

- `5.` Modular methods are central. GHP09 reduce surviving cases to ternary equations like
  \[
  AX^\ell+BY^\ell=CZ^2
  \]
  and, for \(\ell=5\), also \(AX^5+BY^5=CZ^5\). They attach Frey curves, use modularity and level lowering, then combine this with local congruence sieves. So yes: Galois representations help, but only after the combinatorial reduction to finitely many ternary signatures.

- `6.` The exact `k=34` to `k=35` gap is **not** a new mathematical obstruction at `35`. GHP09 explicitly say they “do not see any theoretical obstacle” to going further; they stopped at `k=34` because the tuple enumeration plus iterative sieving became too expensive computationally. More precisely:
  - \(\ell=2\) is already handled far beyond `35`
  - \(\ell=3\) is already handled up to `k<39`
  - so the unresolved `k=35` cases must lie in the \(\ell=5\) and \(\ell\ge 7\) branches
  - those are exactly the branches covered by GHP09 Theorems `1.3` and `1.2`, and the missing step is extending their full tuple-cover/sieve computation from `k=34` to `k=35`

- `7.` A uniform all-`k` proof is not currently known. The closest existing framework is:
  - Faltings: finiteness for fixed \((k,\ell)\), but ineffective
  - Bennett–Siksek `2016`: for fixed `k`, only finitely many prime exponents \(\ell\), with an explicit enormous bound
  - Bennett–Siksek `2020`: for sufficiently large `k`, only finitely many solutions

  What is still missing is an effective argument that kills the remaining medium-sized `k`, especially `k=35`, without a large bespoke computation.

**Sources**
- Bennett–Bruin–Győry–Hajdu `2006`: https://doi.org/10.1112/S0024611505015625
- Győry–Hajdu–Pintér `2009`: https://doi.org/10.1112/S0010437X09004114
- GHP09 preprint/PDF with the computational remarks: https://math.unideb.hu/sites/default/files/inline-files/k34new4.pdf
- Darmon–Merel `1997`: https://perso.imj-prg.fr/loic-merel/wp-content/uploads/merel-pub/winding.pdf
- Hajdu–Tengely, “Arithmetic progressions of squares, cubes and n-th powers”: https://math.unideb.hu/sites/default/files/inline-files/lhszt.pdf
- Hajdu–Tengely–Tijdeman, “Cubes in products of terms in arithmetic progression”: https://math.unideb.hu/sites/default/files/inline-files/lhsztrt.pdf
- Bennett–Siksek `2016`: https://doi.org/10.1112/S0010437X16007569
- Bennett–Siksek `2020`: https://doi.org/10.4007/annals.2020.191.2.2

**Next Steps**
1. Decide which problem you want to attack: `35 cubes in AP`, `35 perfect powers in AP`, or Erdős `#672`.
2. If it is really Erdős `#672`, focus on extending GHP09’s `\ell=5` and `\ell>=7` sieve/modular branches from `k=34` to `k=35`.
3. Do not start with Chabauty on \(J(C_{35,\ell})\); start with the GHP09 ternary-equation reduction, because that is where the actual `34 -> 35` bottleneck lives.