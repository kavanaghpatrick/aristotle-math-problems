# Research Fusion Analysis: Erdős 938 (Powerful 3-term AP)

**Agent:** F5 of 10 (research-fusion pull) | **Date:** 2026-05-30
**Problem:** Let A = {n_1 < n_2 < ...} be powerful numbers. Are there only finitely many 3-term progressions of *consecutive* terms n_k, n_{k+1}, n_{k+2}?
**Formal statement:** {P : Finset ℕ | IsAPOfLength P 3 ∧ ∃ k, P = {nth Powerful k, nth Powerful (k+1), nth Powerful (k+2)}}.Finite
**Status:** OPEN. Tied to Erdős-Mollin-Walsh conjecture (no three consecutive powerful integers).

---

## A. Recent literature pull (2020–2026)

1. **Chan, T.H. (2022/2023)** — *Arithmetic Progressions among Powerful Numbers* (arXiv:2210.00281, JIS 26). Under abc-conjecture, d ≫_ε N^(1/2-ε). Unconditionally constructs infinitely many 3-term APs with d ≪ N^(1/2). Proves partial results for k ≥ 4. The most directly relevant paper for E938.
2. **Bajpai, Bennett, Chan (Feb 2023)** — *Arithmetic progressions in squarefull integers* (arXiv:2302.03113). Constructs infinitely many 3-term APs of coprime cubefull. Doesn't say "consecutive" though.
3. **Chan, T.H. (March 2025)** — *A note on three consecutive powerful numbers* (arXiv:2503.21485). Pell-equation + elliptic-curve methods. Resolves the case where middle is a perfect cube with single odd-power prime in n±1.
4. **She, J. (July 2025)** — *Nonexistence of Consecutive Powerful Triplets Around Cubes with Prime-Square Factors* (arXiv:2507.16828). Extends Chan: no triplets x³−1 = p²a³, x³, x³+1 = q²b³ for primes p, q.
5. **2022 arXiv 2207.08874** — *A note on powerful numbers in short intervals*. Bounds on powerful number gaps, with implications for AP-density.

**Critical:** E938 asks about **consecutive** powerful numbers in AP. Chan 2022 addressed *general* powerful APs (with arbitrary gap d); E938 with "consecutive" = "no other powerful number between" is a tighter condition. The "consecutive" word in the problem makes this a finiteness question, NOT a 3-consecutive-integers question (which is Erdős-Mollin-Walsh).

---

## B. Adjacent-domain analogs

### B1. Algebraic geometry — Curves of Diophantine type
A 3-term AP of consecutive powerful numbers is a solution to (a²b³, c²d³, e²f³) with 2c²d³ = a²b³ + e²f³ and an additional gap-constraint. The pair (a²b³, e²f³) corresponds to a rational point on a curve of varying genus. **Strong analog**: rational-points problems on the Fermat-like surface x²y³ + z²w³ = 2 u²v³.

### B2. Diophantine approximation — S-integer equations
Powerful number n = a²b³ with rad(n) | (ab) is an S-integer in the S = {primes ≤ √n}-localization. A 3-AP becomes a system of 2 S-unit equations: x + z = 2y, x = a²b³, y = c²d³, z = e²f³ in S-units modulo squares-cubes. **Strong analog**: Evertse's theorem on S-unit equations gives finiteness for each S.

### B3. Modular forms — Frey curve at powerful AP
For (n, n+d, n+2d) consecutive powerful: write n = a²b³, n+d = c²d³, n+2d = e²f³. The Frey curve E: Y² = X(X−a²b³)(X+e²f³) has discriminant Δ = (4a²b³e²f³(a²b³+e²f³))² with controlled radical. Level-lowering reduces to weight-2 cusp forms. **Strong analog**: Bennett-Skinner on x^n + y^n = 2z^2.

### B4. Dynamical systems / Ergodic theory — Density of powerful
Powerful numbers have density (ζ(2)/ζ(3)) · 1/√n in [1, N] — sparse but not finite. **Analog**: counting closed orbits of period n in dynamical systems. Erdős-Wirsing/Bombieri-Davenport-style approach: powerful numbers form a "structured sequence" amenable to additive combinatorics.

---

## C. Technique-transfer candidates

1. **Granville-Stewart abc-style explicit-bound theorems**. The abc conjecture implies E938 finiteness; explicit "almost-abc" results (Stewart-Tijdeman 1986, Stewart-Yu 2001) give partial finiteness. Citation: Stewart, C.L., Yu, K. "On the abc conjecture, II" Duke 2001.
2. **Pell equation parametrization of powerful pairs**. Infinite family of pairs (8, 9), (288, 289), ... from x² − 2y² = 1 — known parametrization. Extending to triples is exactly the open question. Citation: Mollin, R., Walsh, P.G. "On powerful numbers."
3. **Erdős-Selfridge superelliptic curve framework + Faltings**. The system n+id = a_i²b_i³ for i=0,1,2 (with the consecutive constraint via uniqueness of factorization) maps to rational points on a fiber product of superelliptic curves. Citation: Bennett, M.A., Siksek, S. "Rational points on Erdős-Selfridge superelliptic curves."
4. **Modular Frey method (Bennett-Skinner type)** as in B3. Citation: Bennett, M.A., Skinner, C.M. "Ternary Diophantine equations via Galois representations and modular forms."
5. **Mass-increment method (Tao 2024)** — recently used to attack Sander conjecture on Erdős-Selfridge curves. Uses quantitative Faltings + combinatorial increments. Citation: 2024 arXiv work extending Bennett-Siksek.

---

## D. Most promising fusion: **Frey-Hellegouarch curve attached to consecutive powerful triple**

**Specific idea:** Given a putative consecutive powerful 3-AP (n_k, n_{k+1}, n_{k+2}) = (a²b³, c²d³, e²f³) with d = (n_{k+2} − n_k)/2 and the "consecutive" condition (no other powerful in between), attach a Frey curve

E_{a,b,e,f}: Y² = X(X − a²b³)(X − 2c²d³)

with discriminant Δ = 16 a²b³ · c²d³ · e²f³ · (a²b³ − e²f³)².

The mod-p Galois rep ρ_p(E) for p prime ≥ 5 dividing none of a, b, c, d, e, f, is unramified outside a finite set. By Ribet's level-lowering, ρ_p arises from a weight-2 cusp form of level N(Δ_min). For specific (a, b, e, f), the relevant cusp form space is small (often 0-dimensional) — contradiction.

**Why fusion-amenable now (2026):**
- Mathlib has growing modular-forms infrastructure (`ModularForms.LevelOne`, `CuspForm`).
- LMFDB tables of S_2(Γ_0(N)) for N < 1000 are computed and downloadable.
- Aristotle has demonstrated ability on modular-form-style arguments (slot737 Sophie Germain divisor scan, though different mechanism).

**The cross-domain ingredient**: **modular forms + Galois representations** — neither powerful-number combinatorics nor Pell-equation parametrization alone closes E938. The Frey method imports the heaviest 1990s-2010s number-theory artillery (Wiles, Ribet, Bennett-Skinner) into a problem currently treated combinatorially.

**Risk:** The Frey curve approach often gives "infinitely many possible levels" for unknown a, b. Requires a uniform bound — typically obtained by separately handling small radicals. The full argument may require checking S_2(Γ_0(N)) for several N up to 10^4, which is huge.

---

## E. What we'd need to feed Aristotle

Beyond bare gap:

```
OPEN GAP: Erdős 938 — finite many 3-term APs of consecutive powerfuls
Source: erdosproblems.com/938

Statement: The set of 3-term APs {n_k, n_{k+1}, n_{k+2}} where each is consecutive
in the enumeration of powerful numbers is finite.

theorem erdos_938_finite :
  {P : Finset ℕ | Set.IsAPOfLength P.toSet 3 ∧ ∃ k,
    P = {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k+1),
         Nat.nth Nat.Powerful (k+2)}}.Finite := by sorry

Direction (HINT, not a proof):
For each putative AP (a²b³, c²d³, e²f³) of consecutive powerful, attach the
Frey-Hellegouarch curve E : Y² = X(X − a²b³)(X − 2c²d³).
- Compute Δ_min(E) = product of primes dividing abcdef.
- By Ribet's level-lowering, the mod-p Galois representation ρ_p(E) corresponds
  to a weight-2 cusp form of level dividing rad(Δ_min(E))^2.
- For each small prime p of good reduction, count cusp forms in S_2(Γ_0(N(p))).
- If S_2(Γ_0(N)) = 0 for forced levels N, contradiction.

Concrete partial result: Chan, 2022 (arXiv:2210.00281). Under abc-conjecture,
d ≫_ε N^(1/2-ε) for any AP of powerful, ruling out consecutive APs for N > N_0.

If the abc-conditional argument can be made unconditional via Bennett-Skinner-style
Frey curves, the conjecture becomes effective.
```

**Crucial cross-domain ingredient**: explicitly invite the **Frey-Hellegouarch + Ribet level-lowering** machinery. Aristotle has substantial knowledge of mod-p Galois reps in Mathlib (`Module.Finite.Galois`) but no native level-lowering toolkit. The sketch must inline the key lemma:

> "For the Frey curve E_{n,d}: Y² = X(X − n)(X + d), with n = a²b³ and n + d = c²d³ both powerful coprime, the conductor N(E) satisfies rad(N) | 2 · rad(abcd), and the mod-3 Galois rep ρ_3 corresponds to a cusp form in S_2(Γ_0(N))."

**Honest assessment:** Plausibility 4/10 for full closure. Chan 2022 has done extensive partial work. The remaining gap (unconditional finiteness with "consecutive" constraint) likely requires *some* form of effective abc-progress that nobody has obtained. The Frey-curve route is the genuine new tool, but tying down the cusp-form spaces for the relevant levels is non-trivial.
