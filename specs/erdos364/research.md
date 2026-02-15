---
spec: erdos364-consecutive-powerful
phase: research
created: 2026-02-13
---

# Research: Erdos 364 — No Three Consecutive Powerful Numbers

## Executive Summary

Erdos 364 (the Erdos-Mollin-Walsh conjecture) asserts no three consecutive integers are all powerful. The mod 36 constraint is PROVEN (slot622). Two 2025 papers (Chan, She) rule out specific "near-cube" families using Pell/Thue equations and elliptic curves, but the general case remains wide open. ABC conjecture implies finiteness only. The most promising sketch targets are: (1) extending the cube-center exclusion to broader families, (2) ABC-conditional full proof, (3) ruling out specific parametric families via Thue-Mahler equations.

## What We Already Have (PROVEN)

| Result | Source | Status |
|--------|--------|--------|
| n % 4 = 3 | slot581, slot622 | PROVEN in Lean |
| n % 9 in {0,7,8} | slot581, slot622 | PROVEN in Lean |
| n % 36 in {7,27,35} | slot622 | PROVEN in Lean |
| No triple below 10^8 | slot622 (native_decide) | PROVEN in Lean |
| 1209 survivors mod 44100 | slot622 (native_decide) | PROVEN in Lean |
| No quadruple | formal-conjectures | PROVEN in Lean |
| Powerful iff a^2*b^3 | slot622 | PROVEN in Lean |

## External Research

### Chan (2025) — INTEGERS 25, #A7

**Paper**: "A note on three consecutive powerful numbers" — [arXiv:2503.21485](https://arxiv.org/abs/2503.21485), [INTEGERS](https://math.colgate.edu/~integers/z7/z7.pdf)

**What is ruled out**: No triple (n, n+1, n+2) exists where:
- Middle term n+1 = x^3 (a perfect cube)
- n = x^3 - 1 = p^3 * y^2 (exactly one prime factor to an odd power, cube form)
- n+2 = x^3 + 1 = q^3 * z^2 (exactly one prime factor to an odd power, cube form)

**Methods**:
1. Generalized Pell equation u^2 - 3v^2 = -2, with solutions u_k = 4u_{k-1} - u_{k-2}
2. Elliptic curves Y^2 = X^3 +/- 3X^2 + 9X (solved via SageMath: only trivial integer points)
3. Factorization via gcd(x-1, x^2+x+1) = 1 or 3 (case split on x mod 3)
4. Second-order recurrences with growth bound u_k > 3u_{k-1}

**Key insight**: The factorizations x^3 - 1 = (x-1)(x^2+x+1) and x^3 + 1 = (x+1)(x^2-x+1) produce coprimality constraints. Combined with the requirement that the result is p^3*y^2, this forces Pell-type equations whose solution sequences grow too fast to match.

**Limitation**: Only covers the case where flanking terms have EXACTLY one prime to an odd power, in cube form (p^3*y^2, not p^2*y^3 or general powerful).

### She (2025) — INTEGERS 25, #A103

**Paper**: "Nonexistence of Consecutive Powerful Triplets Around Cubes with Prime-Square Factors" — [arXiv:2507.16828](https://arxiv.org/abs/2507.16828)

**What is ruled out**: No triple where:
- Middle term n+1 = x^3
- n = x^3 - 1 = p^2 * a^3 (prime-square form)
- n+2 = x^3 + 1 = q^2 * b^3 (prime-square form)

This is the COMPLEMENTARY case to Chan (who handled p^3*y^2).

**Methods**:
1. Case analysis on gcd(x-1, x^2+x+1) = g_- and gcd(x+1, x^2-x+1) = g_+, each 1 or 3
2. Mordell curves: u^2 + u + 1 = v^3 has solutions u in {-19, -1, 0, 18} only (Lemma 3)
3. Thue equations: u^3 - v^3 = 2 has unique solution (1,-1) (Lemma 5)
4. Cubic Thue: u^3 - 2v^3 = 1 and u^3 - dv^3 = 1 for d in {4, 18, 36}
5. p-adic valuations via Lifting-the-Exponent lemma

**Corollary**: x^6 - 1 = p^2 * q^2 * a^3 has no integer solutions.

**Open conjecture from paper**: For all x > 1 and n > 2, x^n - 1 is NOT powerful. (Stronger than Catalan/Mihailescu.)

### Combined State After Chan + She (2025)

For triples centered at a cube x^3:
- **RULED OUT**: n+1 = x^3, n = p^3*y^2, n+2 = q^3*z^2 (Chan)
- **RULED OUT**: n+1 = x^3, n = p^2*a^3, n+2 = q^2*b^3 (She)
- **STILL OPEN**: n+1 = x^3, with flanking terms having >= 2 distinct primes to odd powers
- **STILL OPEN**: n+1 NOT a perfect cube (the vast majority of cases)

### ABC Conjecture Implications

**Conditional result** ([Nitaj ABC page](https://nitaj.users.lmno.cnrs.fr/abc.html)):
- ABC implies only FINITELY MANY triples of consecutive powerful numbers
- Does NOT prove zero exist

**Mechanism**: If n, n+1, n+2 are powerful, write n = a*b^2 where b = squarefree kernel. Then rad(n) <= sqrt(n). For coprime decomposition n + (n+2) = ... apply ABC to get n+2 < K_epsilon * rad(n(n+1)(n+2))^{1+epsilon}. Since rad of powerful numbers is small (rad(n) <= n^{1/2}), this gives n < K * n^{(3/2)(1+epsilon)/(something)} which for large n yields contradiction for any fixed epsilon.

**Precise bound** (from Chan 2023, JIS): For 3-term AP of powerful numbers with d=1 (i.e. consecutive), ABC implies no such triple with N sufficiently large.

### Thue-Mahler Framework

Writing n = a^2*b^3 and n+2 = c^2*d^3 (with b,d squarefree), the equation c^2*d^3 - a^2*b^3 = 2 is a generalized Thue-Mahler equation.

**Known results**:
- Mahler (1933): finitely many solutions (ineffective)
- Evertse: at most (5 * 10^6 * r)^s essentially distinct solutions (where s = |S|)
- Bugeaud-Gyory (1996): effective bounds on solution size

**Challenge**: The equation involves FOUR unknowns (a,b,c,d) plus the squarefree constraints on b,d. Not a standard Thue equation (which has 2 unknowns).

### Parametric Pair Constructions

Infinitely many PAIRS of consecutive powerful numbers exist:
- (8, 9): 2^3, 3^2
- (288, 289): 2^5*3^2, 17^2
- Generated by Pell equation x^2 = 8y^2 + 1 (Mahler)
- Walker: 7^3*x^2 = 3^3*y^2 + 1 also gives infinite family

These pairs provide the "building blocks" for hypothetical triples. A triple would require TWO overlapping pairs: (n,n+1) and (n+1,n+2) both pairs.

### Computational Bounds

| Bound | Source |
|-------|--------|
| No triple below 10^5 | slot581 (native_decide, Lean-verified) |
| No triple below 10^8 | slot622 (native_decide, Lean-verified) |
| No triple below 10^22 | OEIS A060355 (claimed, not Lean-verified) |

## Codebase Analysis

### Existing Proofs
- `/Users/patrickkavanagh/math/submissions/nu4_final/slot622_erdos364_powerful_triples_result.lean`: Complete mod 36, mod 44100, bounded verification, pair enumeration
- `/Users/patrickkavanagh/math/submissions/nu4_final/slot581_erdos364_powerful_result.lean`: Mod 4, mod 9, bounded to 10^5
- `/Users/patrickkavanagh/math/submissions/erdos/tier3/erdos_364_erdos_364.lean`: Formal-conjectures statement (sorry)

### Computational Scripts
- `/Users/patrickkavanagh/math/scripts/erdos364_residue.py`: Mod 44100 sieve, confirms 1209 survivors
- `/Users/patrickkavanagh/math/scripts/erdos364_analysis.py`: Deeper pattern analysis of survivors

### What's NOT in the codebase
- No Pell equation / Thue equation approach
- No cube-center exclusion (Chan/She results)
- No ABC-conditional proof
- No parametric family exclusion beyond modular sieving

## Feasibility Assessment

| Target | Viability | Effort | Notes |
|--------|-----------|--------|-------|
| Prove mod 36 constraint | DONE | - | slot622 |
| Prove no 4-consecutive | DONE | - | formal-conjectures |
| Prove bounded case (10^8) | DONE | - | slot622 |
| ABC-conditional finiteness | Medium | M | Needs rad(n) bounds + ABC formalization in Lean |
| Cube-center with 1 odd prime (Chan) | Medium-High | L | Pell eqs + elliptic curves in Lean/Mathlib |
| Cube-center prime-square (She) | Medium | L | Mordell curves + Thue eqs in Lean |
| General cube-center exclusion | Low | XL | Would need to handle arbitrary powerful factorizations |
| Full conjecture | Very Low | XXL | Still an open problem after 50 years |

## Recommendations for Sketch Targets

### Target 1 (HIGHEST VALUE): Cube-Center Exclusion — General Case

**Theorem**: If n, n+1, n+2 are consecutive powerful numbers, then n+1 is NOT a perfect cube.

**Why valuable**: Chan proved it for p^3*y^2 flanking. She proved it for p^2*a^3 flanking. If we can handle the general case (flanking terms have arbitrary powerful structure), this rules out the entire "cube-centered" family.

**Approach**: Write x^3-1 = (x-1)(x^2+x+1) and x^3+1 = (x+1)(x^2-x+1). Both factors of each product must contribute to a powerful number. The gcd structure (1 or 3) severely constrains factorizations. Use:
- Cyclotomic factor x^2+/-x+1 has no repeated prime factors (unless p=3)
- If x^2+x+1 = powerful and x-1 = powerful with gcd=1, then x^2+x+1 must itself be powerful
- Apply known results: x^2+x+1 = y^2 has solutions only at x=0,-1 (Mordell curve)
- x^2+x+1 = y^3 has solutions only at x in {-19,-1,0,18} (Lemma 3 from She)

**Sketch viability**: HIGH. The key algebraic constraints are already in the literature. The proof needs to enumerate all factorization types of the cyclotomic factors and show none can be powerful.

### Target 2 (HIGH VALUE): No Triple Below 10^{12} or 10^{15}

**Approach**: Push the computational bound much higher. Use the a^2*b^3 representation to enumerate powerful numbers efficiently. The count up to N is ~c*sqrt(N), so 10^12 has ~10^6 powerful numbers — tractable.

**Lean approach**: native_decide may struggle at 10^12. Alternative: prove it in Python, encode as a certificate.

### Target 3 (MEDIUM VALUE): ABC-Conditional Finiteness

**Theorem** (conditional on ABC): There are at most finitely many triples of consecutive powerful numbers.

**Approach**: If n, n+1, n+2 are powerful, apply ABC to the triple (1, n, n+1) or (n, 1, n+1):
- rad(n) <= n^{1/2} for powerful n
- rad(n+1) <= (n+1)^{1/2}
- rad(n+2) <= (n+2)^{1/2}
- Apply ABC to n + 2 = (n+1) + 1: rad((n+1)*1*(n+2)) <= (n+2)^{1/2} * (n+1)^{1/2} ~ n
- ABC says n+2 < K_eps * n^{1+eps} which is trivially true... NEED BETTER DECOMPOSITION.

Better: Apply ABC to n*(n+2) = (n+1)^2 - 1. Then a = 1, b = n*(n+2), c = (n+1)^2. Coprime since gcd(n*(n+2), (n+1)^2) | gcd(n*(n+2), n+1)^2. Since gcd(n, n+1)=1 and gcd(n+2, n+1)=1, we get gcd=1. So:
- (n+1)^2 = n*(n+2) + 1
- rad(n*(n+2)*(n+1)^2) = rad(n)*rad(n+1)*rad(n+2) <= n^{1/2}*(n+1)^{1/2}*(n+2)^{1/2} ~ n^{3/2}
- ABC: (n+1)^2 < K_eps * (n^{3/2})^{1+eps}
- So n^2 < K * n^{3/2 + 3eps/2}
- This gives n^{1/2} < K * n^{3eps/2} which fails for large n when eps < 1/3.

**This works!** For any eps < 1/3, ABC gives an upper bound on n. Hence finitely many triples.

### Target 4 (MEDIUM VALUE): Ruling Out Specific Parametric Families

Since pairs come from Pell equations, triples would need OVERLAPPING pairs. The Mahler family (8y^2+1 = x^2) gives pairs (8y^2, 8y^2+1) = (8y^2, x^2). A triple starting at n=8y^2-1 needs:
- 8y^2 - 1 = powerful (odd, not div by 2)
- 8y^2 = powerful (always: 2^3 * y^2)
- 8y^2 + 1 = powerful (the x^2 from Pell)

So: 8y^2 - 1 must be powerful, and 8y^2 + 1 = x^2 must be powerful.
Now x^2 is always powerful. So need 8y^2 - 1 powerful.
8y^2 - 1 powerful means every prime p | (8y^2-1) has p^2 | (8y^2-1).

This is a specific Diophantine constraint. Could prove: for all Pell solutions (x,y) to x^2 = 8y^2+1, 8y^2-1 is NOT powerful. This uses properties of the Pell sequence.

## What Structural Families Remain Unruled After Chan + She?

1. **Non-cube centers**: n+1 is powerful but NOT a perfect cube (the vast majority). No structural result exists.
2. **Multi-prime odd-exponent flanking**: n = x^3 - 1 with >=2 primes to odd power. Not covered.
3. **Arbitrary powerful triples**: The general case with no assumptions on the form of n+1.

The cube-centered case is special because x^3-1 and x^3+1 factor algebraically (cyclotomic). For non-cube centers, there's no such algebraic handle, making the problem much harder.

## Open Questions

1. Has anyone extended Chan/She to rule out ALL cube-centered triples (not just single-prime-power flanking)?
2. Is the ABC-conditional proof for consecutive powerful triples already in the literature, or is our derivation novel?
3. Can the Pell-family exclusion (ruling out triples from Mahler pairs) be made rigorous?
4. What is the exact count of 1209 survivors mod 44100 after further sieving with primes 11, 13?

## Sketch Recommendations (Ordered by Value)

1. **General cube-center exclusion**: Prove n+1 cannot be a perfect cube. Uses cyclotomic factorization + Mordell/Thue. Extends Chan+She. ~80 lines, HIGH value.
2. **ABC-conditional finiteness**: Prove that ABC implies at most finitely many consecutive powerful triples. Uses the (n+1)^2 = n(n+2)+1 decomposition. ~60 lines, MEDIUM value.
3. **Pell-family exclusion**: Prove the Mahler Pell pairs cannot extend to triples. ~50 lines, MEDIUM value.
4. **Extended modular sieve**: Prove no triple mod 2^2*3^2*5^2*7^2*11^2 = 5336100. If survivors = 0, done! ~40 lines, HIGH value if it works.

## Sources

- [Chan 2025 - INTEGERS z7](https://math.colgate.edu/~integers/z7/z7.pdf)
- [Chan 2025 - arXiv:2503.21485](https://arxiv.org/abs/2503.21485)
- [She 2025 - arXiv:2507.16828](https://arxiv.org/abs/2507.16828)
- [She 2025 - INTEGERS z103](https://math.colgate.edu/~integers/z103/z103.pdf)
- [Erdos Problems #364](https://www.erdosproblems.com/364)
- [Nitaj ABC consequences](https://nitaj.users.lmno.cnrs.fr/abc.html)
- [CrowdMath - ABC and powerful numbers](https://arxiv.org/abs/2005.07321)
- [Chan 2023 - APs among powerful numbers (JIS)](https://cs.uwaterloo.ca/journals/JIS/VOL26/Chan/chan33.pdf)
- [Beckon - On Consecutive Triples](https://scholar.rose-hulman.edu/rhumj/vol20/iss2/3/)
- [Murty - Fundamental units and consecutive squarefull](https://mast.queensu.ca/~murty/fundamental-units.pdf)
- [Wikipedia - Powerful number](https://en.wikipedia.org/wiki/Powerful_number)
- slot622 result: `/Users/patrickkavanagh/math/submissions/nu4_final/slot622_erdos364_powerful_triples_result.lean`
- slot581 result: `/Users/patrickkavanagh/math/submissions/nu4_final/slot581_erdos364_powerful_result.lean`

## Quality Commands

| Type | Command | Source |
|------|---------|--------|
| Lint | Not found | No package.json |
| TypeCheck | Not found | No package.json |
| Unit Test | Not found | No package.json |
| Build | Not found | No package.json |
| Lean build | `lake build` | Lean project |

**Local CI**: Project uses Lean/Mathlib. Quality verification via `lake build` and Aristotle submission.
