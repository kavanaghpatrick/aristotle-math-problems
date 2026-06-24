# Erdős 672 — Stage 1 Literature (k = 4, ℓ = 3 case)

**Problem**. Erdős asked whether, for positive integers `n, d` with `gcd(n, d) = 1`,
the product `n(n+d)(n+2d)(n+3d)` can equal `y^3` for some integer `y`.

**Formal-conjectures reference**. `FormalConjectures/ErdosProblems/672.lean`.
The Lean file states the general conjecture (any `k >= 4`, any `l > 1`) is open,
and lists Euler `(k=4, l=2)` and Obláth `(k=5, l=2)`, `(k=3, l in {3,4,5})` as solved.

**The specific (k=4, l=3) sub-case has been resolved unconditionally**:

1. **Hajdu, Tengely, Tijdeman 2009** —
   "Cubes in products of terms in arithmetic progression",
   *Publ. Math. Debrecen* 74 (1-2), 215-232 (2009).
   Result: For `2 < k < 39` and `gcd(n, d) = 1`, the product
   `n(n+d)...(n+(k-1)d)` is never a perfect cube.
   Method: Reduction to Thue equations + Frey curve + Galois representations.

2. **Győry, Hajdu, Pintér 2009** —
   "Perfect powers from products of consecutive terms in arithmetic progression",
   *Compos. Math.* 145(4), 845-864 (2009).
   Result: For `3 < k < 35` and any `l >= 2`, no perfect `l`-th power.
   Method: Frey + Galois + cyclotomic local arguments.

3. **Bennett, Bruin, Győry, Hajdu 2006** —
   "Powers from products of consecutive terms in arithmetic progression",
   *Proc. London Math. Soc.* 92(2), 273-306 (2006).
   Result: `4 <= k <= 11` for any perfect power.
   Method: Frey curves, modularity, Bennett-Skinner level-lowering.

4. **Győry, Hajdu, Saradha** — earlier covered `k = 4, 5`.

5. **Bajpai, Bennett, Chan 2023** (arXiv:2302.03113) —
   abc-conditional bound `gcd(d, N) >> max(d, N)^{3/7 - eps}` for 4-term APs
   of 3-full numbers. Same problem family. Establishes the bounded-height
   window after which the AP-of-3-fulls problem becomes unconditional.

**Bottom line.** The mathematical statement is a *theorem* (HTT 2009 + GHP 2009),
not an open conjecture. The bare-mode submissions (slots 698, 1218, 1243, 1248)
returned `compiled_no_advance`, indicating Aristotle's MCGS formalizer cannot
reconstruct the named-technique chain without explicit guidance.

**Open gap (closure framing)**. What remains genuinely open is the
*uniform* claim `forall k >= 4, forall l >= 2, ...` for all `k` simultaneously
(GHP only covers `k < 35`; HTT-cubes only covers `k < 39`). The asymptotic
case `k >= 35` is open for general `l`, and `k >= 39` is open for `l = 3`.

**Aristotle-relevant context**. The prior compiled-no-advance verdicts mean
the bare formalizer never reached the Frey + Galois + Bennett-Skinner chain.
The FUSION lane's role: name the technique chain so Aristotle's informal
reasoner formalizes the known proof for `k = 4, l = 3`.
