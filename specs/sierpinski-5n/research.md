---
spec: sierpinski-5n
phase: research
created: 2026-02-13
---

# Research: Sierpinski Conjecture 5/n -- Open Frontier

## Executive Summary

The Sierpinski conjecture (1956) states 5/n = 1/x + 1/y + 1/z has positive integer solutions for all n >= 2. Verified to 10^18 with NO exceptions (arXiv:2511.16817). We already proved the trivial cases (2|n, 3|n, 5|n) in slot626. The genuinely open part: primes p with p = 1 mod 30 (coprime to 30). The most recent paper (arXiv:2508.07367) reduces the entire conjecture to a single case: n = 5q+1 where q = 0 mod 252 (= 4*9*7), verified to 10^10 but not proven. This is the target for a sketch.

## External Research

### The Conjecture

- **Statement**: For every n >= 2, 5/n = 1/x + 1/y + 1/z in positive integers (Sierpinski 1956, generalized by Schinzel).
- **Equivalent integer form**: 5*x*y*z = n*(y*z + x*z + x*y), avoiding rational arithmetic.
- **Reduction to primes**: If it holds for prime p, it holds for all multiples kp (take kx, ky, kz).
- **Computational verification**: No exceptions found up to 10^18 ([arXiv:2511.16817](https://arxiv.org/abs/2511.16817)).
- **For 4/n (Erdos-Straus)**: verified to 10^14; Mordell's identities cover all n except n = 1, 121, 169, 289, 361, 529 mod 840.

### Key Paper: arXiv:2508.07367 ("Almost a Complete Proof")

**Source**: [arXiv:2508.07367](https://arxiv.org/abs/2508.07367) (2025)

**Results by residue class of a mod 5**:

| Case | Identity | Status |
|------|----------|--------|
| a = 5k (a = 0 mod 5) | 5/(5k) = 1/(k+1)^2 + 1/(k(k+1)^2) + 1/(k+1) | SOLVED |
| a = 5k+2 (a = 2 mod 5) | Split by parity of k; explicit polynomials | SOLVED |
| a = 5k+3 (a = 3 mod 5) | 5/(5k+3) = 1/(5k^2+8k+3) + 1/(5k^2+8k+3) + 1/(k+1) | SOLVED |
| a = 5k+4 (a = 4 mod 5) | 5/(5k+4) = 1/(5(k+1)^2(5k+4)) + 1/(5(k+1)^2) + 1/(k+1) | SOLVED |
| a = 5q+1 (a = 1 mod 5) | Requires subdivision by q mod 12, then q mod 84, then q mod 252 | ALMOST SOLVED |

**For a = 5q+1, subdivision**:

The paper uses polynomial p_1(x,y,z) = z(x(5y-1)-y)-x which generates q values admitting solutions.

| Sub-case | Method | Status |
|----------|--------|--------|
| q = 2 mod 12 | p_1 with (x,y,z)=(1,1,1+4t) | SOLVED |
| q = 5 mod 12 | p_1 with (x,y,z)=(1,1,2+4t) | SOLVED |
| q = 8 mod 12 | p_1 with (x,y,z)=(1,1,3+4t) | SOLVED |
| q = 6 mod 12 | p_1 with (x,y,z)=(1,2+3t,1) | SOLVED |
| q = 10 mod 12 | p_1 with (x,y,z)=(1,3+3t,1) | SOLVED |
| q = 1,3,4,7,9,11 mod 12 | Condition 02 with polynomials p_2, p_3 | SOLVED |
| q = 0 mod 12, q != 0 mod 84 | Further subdivision, u = q/12 mod 7 | SOLVED |
| q = 0 mod 84, q != 0 mod 252 | v = q/84 mod 3, using p_5 | SOLVED |
| **q = 0 mod 252** | **CONJECTURED: p_1 covers all** | **OPEN** |

**The Conjecture (from the paper)**: For every positive integer L, there exist x,y,z in N* such that p_1(x,y,z) = 252*L. Equivalently, every multiple of 252 is representable as z(x(5y-1)-y)-x.

**Verification**: Checked for 5q+1 up to ~2*10^10 with zero failures (396,829 solutions verified).

### Example: q = 252 (hardest first case), a = 1261

The paper provides: 5/1261 = 1/(252*86 + ...) with denominators from p_5 polynomial.

For q = 252L, v = 3w + i subdivision, y=1 case gives:
5/(5*p_5(x,1)+1) = 1/((126x+43)(140x+47)(1260x+421)) + 1/(35280x^2+23884x+4042) + 1/(252x+86)

### 252 = 2^2 * 3^2 * 7

This modulus arises as the LCM of intermediate divisibility constraints from the paper's Lemma 2.1 conditions (5) and (6). The cascade is: mod 5 -> mod 12 -> mod 84 -> mod 252 -> OPEN.

### Exceptions Paper: arXiv:2511.16817

**Source**: [arXiv:2511.16817](https://arxiv.org/abs/2511.16817) (Nov 2025)

Key results:
- **Schinzel's general conjecture FAILS for large m**: For m >= 6.52*10^9, there exists a prime p in (m^2, 2m^2) where m/p has no 3-unit-fraction decomposition.
- **BUT m=4 and m=5 appear to be special**: For m=5, every prime p < 10^13 except 2 and 5 has a Type II solution. The authors conjecture this holds for all p.
- **Density**: For m=5, exceptions (if any) have zero density among primes.

This means: the Sierpinski conjecture for m=5 is NOT affected by the general Schinzel failure. It likely holds, but proving it requires resolving the q = 0 mod 252 case.

### Elsholtz-Tao Classification

**Source**: [arXiv:1107.1010](https://arxiv.org/abs/1107.1010)

For m/n = 1/x + 1/y + 1/z:
- **Type I**: n | x, gcd(n, y) = gcd(n, z) = 1
- **Type II**: gcd(n, x) = 1, n | y, n | z

For 5/p with prime p, the equation becomes:
- Type I: x = pk, then 5/(pk) - 1/(pk) = (5-1/k)/(pk) ... need 5k-1 | p*k^2 in some form.
- Type II: y = pa, z = pb, then 5/p = 1/x + 1/(pa) + 1/(pb), so 5/p - 1/(pa) - 1/(pb) = 1/x.

The Elsholtz-Tao framework lifts the Cayley surface to a 3-variety in 6-space. They completely classify which congruence classes admit polynomial solutions. The obstruction: polynomial solutions cannot cover n where n is a quadratic residue mod the covering modulus.

### Prior Art: Partial Resolution Paper (arXiv:2502.20935)

**Source**: [arXiv:2502.20935](https://arxiv.org/abs/2502.20935) (Feb 2025)

Introduces two analytical formulas for decomposing a/n into 3 unit fractions under:
1. Specific divisibility conditions
2. Existence of certain perfect squares

Reduces the problem to finding a suitable perfect square. Represents a partial resolution.

### What's Known for 4/n (Analogous Problem)

For the Erdos-Straus 4/n case, Mordell's polynomial identities cover all n except n = 1, 121, 169, 289, 361, 529 mod 840. The hard cases are primes p = 1 mod 840. Recent work (arXiv:2404.01508) proposes a complete congruence system using polynomials of form 4dn-1 as moduli. Another paper (arXiv:2508.07383) constructs 4 polynomial families conjectured to cover all n = 1 mod 4, verified to 10^9.

## Codebase Analysis

### Existing Proven Results (slot626)

File: `/Users/patrickkavanagh/math/submissions/nu4_final/slot626_erdos_straus_k5_result.lean`

Proven in Lean 4 with Aristotle:
1. `egyptian_fraction_5_div_3m`: 5/n for 3|n (witnesses: x=m, y=2m, z=6m)
2. `egyptian_fraction_5_div_5m`: 5/n for 5|n (witnesses: x=2m, y=2m+1, z=2m(2m+1))
3. `egyptian_fraction_5_div_2m`: 5/n for 2|n (witnesses: x=m, y=m, z=2m)
4. `egyptian_fraction_5_small_n`: 5/n for 2 <= n <= 30 (native_decide)
5. `egyptian_fraction_existence`: General Egyptian fraction existence (greedy algorithm)

### Existing Proven Results (slot604)

File: `/Users/patrickkavanagh/math/submissions/nu4_final/slot604_erdos_straus_result.lean`

For 4/n (Erdos-Straus):
1. `ErdosStraus` definition and integer equivalence
2. Reduction to primes
3. Even numbers, n = 3 mod 4, n = 0 mod 3
4. Full reduction to p = 1 mod 12 or p = 5 mod 12
5. Bounded verification to n = 100

### Gap: What's NOT Proven

The hard open part for 5/n:
- **Primes p = 1 mod 30** (coprime to 2, 3, 5) — no construction exists covering all such primes
- More precisely: **p = 5q+1 where q = 0 mod 252** — the paper's remaining case
- Equivalently: **p = 1261, 2521, 3781, ...** (p = 1260k + 1 for all k)

## Feasibility Assessment

| Aspect | Assessment | Notes |
|--------|------------|-------|
| Technical Viability | Medium-High | Paper provides explicit polynomial framework; conjecture is narrow |
| Effort Estimate | M | Sketch the polynomial coverage approach for Aristotle |
| Risk Level | Medium | The q=0 mod 252 case is genuinely open; but bounded cases are provable |
| Novelty | High | First formalization of parametric coverage beyond trivial cases |

## Recommendations for Sketch

### Option A: Prove the Full Parametric Reduction (HIGH VALUE)

Sketch the complete case analysis from arXiv:2508.07367:
1. Cases a = 0,2,3,4 mod 5 — explicit witnesses (we have 0,2,3 already; add a=4 mod 5)
2. Case a = 1 mod 5: subdivision by q mod 12
3. Each sub-case via polynomial p_1 or p_2/p_3
4. Reduce to: "5/n solvable for all n EXCEPT possibly n = 5q+1 where 252 | q"
5. This is a genuine open-problem reduction — novel formalization

The key theorem would be:
```
theorem sierpinski_5n_reduction :
  (forall q : N, 252 | q -> q > 0 ->
    exists x y z : N, 0 < x /\ 0 < y /\ 0 < z /\
      5*x*y*z = (5*q+1)*(y*z + x*z + x*y)) ->
  forall n >= 2, exists x y z : N, 0 < x /\ 0 < y /\ 0 < z /\
    5*x*y*z = n*(y*z + x*z + x*y)
```

### Option B: Prove the q=0 mod 252 Case for Bounded q (MEDIUM VALUE)

Use native_decide or explicit witnesses for q = 252, 504, 756, ..., up to some bound. Combined with the parametric reduction, this proves the conjecture for all n up to ~1260*bound.

### Option C: Attack the Polynomial Representation Conjecture (HIGHEST VALUE, HARDEST)

The open conjecture: every positive integer L has x,y,z in N* with z(x(5y-1)-y)-x = 252*L.

This is equivalent to: the image of the polynomial p_1(x,y,z) = z(x(5y-1)-y)-x contains all multiples of 252.

Approach ideas:
- For fixed y=1: p_1(x,1,z) = z(4x-1)-x = 4xz - z - x. Need 4xz-z-x = 252L.
- This is a linear Diophantine equation in x,z for each L. Solvable when gcd(4z-1, z) | 252L+z, but gcd(4z-1,z) = gcd(-1,z) = 1. So for ANY z, there exists x with 4xz-z-x = 252L iff 4z-1 | 252L+z.
- Equivalently: 252L + z = 0 mod (4z-1), i.e., 252L = -z mod (4z-1).
- Since gcd(4z-1, z) = 1, need 252L = -z mod (4z-1).
- Question: does there always exist z such that 4z-1 | 252L+z?
- Note 252L+z = 252L + (4z-1+1)/4... this gets into divisibility questions.

Alternative: for fixed x=1, p_1(1,y,z) = z(5y-1-y)-1 = z(4y-1)-1. Need z(4y-1) = 252L+1.
Since 252L+1 is odd (252L is even, +1 is odd), and 4y-1 is always odd, this works when 252L+1 has an odd factor d >= 3 with d = 3 mod 4 (so d = 4y-1 has y = (d+1)/4 integer).
Actually d = 4y-1 requires d = 3 mod 4. So we need: 252L+1 has a divisor d = 3 mod 4 with d >= 3.
252L+1: for L=1, 253 = 11*23. 11 = 3 mod 4. Works: y=(11+1)/4=3, z=253/11=23. Check: 23*(4*3-1)-1 = 23*11-1 = 253-1 = 252.

**This approach works unless 252L+1 is a power of 2 or all prime factors are 1 mod 4.** But 252L+1 = 1 mod 4 always (since 252 = 0 mod 4, so 252L+1 = 1 mod 4). So 252L+1 = 1 mod 4, meaning the product of all prime factors (with multiplicity) is 1 mod 4. This means either: all primes are 1 mod 4, or an even number are 3 mod 4.

If ANY prime factor p = 3 mod 4 divides 252L+1, then p^2 | 252L+1 (since even number of 3-mod-4 factors multiply to 1 mod 4), and we can use d = p.

The hard case: 252L+1 is a product of primes all = 1 mod 4. Then no divisor is 3 mod 4. But we can use x >= 2 or y >= 2 to get more flexibility.

**This is a viable proof strategy**: show that p_1's image covers all multiples of 252 by analyzing divisibility. The obstacle is when 252L+1 has all prime factors = 1 mod 4 (which is a density-zero set by Dirichlet/Chebotarev, but proving it never happens for all L is the challenge).

### Recommended Strategy: Option A + C combined

Write a sketch that:
1. States the full parametric reduction (Options A)
2. Proposes the proof of the polynomial conjecture via the divisibility argument (Option C)
3. Lets Aristotle formalize what it can -- at minimum the reduction, ideally the polynomial coverage

## Open Questions

1. Can the divisibility argument for p_1 be made unconditional, or does it require number-theoretic assumptions?
2. For the x=1 case: how often is 252L+1 a product of primes all = 1 mod 4? (Landau's theorem: density 0, but can we prove it never happens?)
3. Is there a simpler polynomial that covers all multiples of 252 without the mod-4 obstruction?
4. Does the approach via x >= 2 in p_1 cover the remaining cases?

## Related Specs

| Spec | Relevance | mayNeedUpdate |
|------|-----------|---------------|
| erdos364 | Low — different problem domain (powerful numbers) | false |
| math-forge | Low — tooling only | false |

## Quality Commands

| Type | Command | Source |
|------|---------|--------|
| Lint | Not found | N/A |
| TypeCheck | Not found | N/A |
| Unit Test | Not found | N/A |
| Build | Not found | N/A |
| Test | Not found | N/A |

No package.json or Makefile found. This is a math research project, not a software project.

## Sources

- [arXiv:2508.07367 - Almost a Complete Proof of 5/a](https://arxiv.org/abs/2508.07367)
- [arXiv:2511.16817 - Exceptions to Erdos-Straus-Schinzel](https://arxiv.org/abs/2511.16817)
- [arXiv:2502.20935 - Partial Resolution using Analytical Formulas](https://arxiv.org/abs/2502.20935)
- [arXiv:1107.1010 - Elsholtz-Tao Counting Solutions](https://arxiv.org/abs/1107.1010)
- [arXiv:2404.01508 - Complete Congruence System for Erdos-Straus](https://arxiv.org/abs/2404.01508)
- [arXiv:2508.07383 - Exact Polynomial Families](https://arxiv.org/abs/2508.07383)
- [Erdos-Straus conjecture - Wikipedia](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Straus_conjecture)
- [Tao blog - Counting solutions](https://terrytao.wordpress.com/2011/07/31/counting-the-number-of-solutions-to-the-erdos-straus-equation-on-unit-fractions/)
- slot626 result: `/Users/patrickkavanagh/math/submissions/nu4_final/slot626_erdos_straus_k5_result.lean`
- slot604 result: `/Users/patrickkavanagh/math/submissions/nu4_final/slot604_erdos_straus_result.lean`
