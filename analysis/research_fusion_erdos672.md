# Research Fusion Analysis: Erdős 672 k=4, ℓ=3 (Powerful AP)

**Agent:** F5 of 10 (research-fusion pull) | **Date:** 2026-05-30
**Problem:** ∃ a 4-term coprime AP (n, n+d, n+2d, n+3d) with gcd(n,d)=1 whose product is a perfect cube?
**Formal statement:** ¬ Erdos672With 4 3 (existence of counterexample to Erdős conjecture at k=4, ℓ=3)
**Status:** OPEN at (k,ℓ)=(4,3). Solved for (4,2) by Euler, (5,2) and (3,3..5) by Obláth.

---

## A. Recent literature pull (2020–2026)

1. **Győry, Hajdu, Pintér (2009)** — *Perfect powers from products of consecutive terms in arithmetic progression* (Compositio Math 145). Foundational: for 4 ≤ k ≤ 11, no coprime k-term AP has product a perfect power (UNCONDITIONAL). This appears to settle E672. But the cited theorem requires technical hypotheses on prime factor support — the specific case (k=4, ℓ=3) may be uncovered by precise sub-hypotheses.
2. **Bennett, Siksek (2016)** — *Rational points on Erdős-Selfridge superelliptic curves* (Compositio Math 152). Faltings-based, finite for each (k, ℓ).
3. **Das, Laishram, Saradha, Sharma (2023)** — *Rational solutions to variants of Erdős-Selfridge superelliptic curves* (Int. J. Number Theory 19, p.1707). Specifically targets variants with omitted/repeated terms.
4. **Bajpai, Bennett, Chan (Feb 2023)** — *Arithmetic progressions in squarefull integers* (arXiv:2302.03113). Constructs 3-term cubefull APs; addresses partial results for k ≥ 4.
5. **Natarajan, S. (2025)** — Book chapter *Erdős-Selfridge Theorem and Some Generalizations* in *Perfect Powers — An Ode to Erdős* (Infosys Springer). Covers cubes and higher powers in AP products.

**Critical literature gap:** Verify whether GHP 2009 (technical hypothesis) actually covers (k=4, ℓ=3). If yes, the problem is SOLVED, not open. If no, the gap is in the parameter range left uncovered.

---

## B. Adjacent-domain analogs

### B1. Algebraic geometry — Rational points on superelliptic curves
The product (n)(n+d)(n+2d)(n+3d) = y³ defines a superelliptic curve C: y³ = x(x+1)(x+2)(x+3)·(known scalings). Faltings says C has finitely many rational points if genus ≥ 2. For k=4, ℓ=3 the curve has genus (3-1)(4-2)/2 = 2, exactly at the threshold. **Strong analog**: classify all rational points on a specific genus-2 curve via Chabauty/Mordell-Weil sieve.

### B2. Modular forms — Frey curves and level lowering
The Bennett-Skinner method for Ax^n + By^n = Cz^2 attaches a Frey elliptic curve and uses Ribet level-lowering + modular forms in a small space. For AP product = cube: a generalized Frey curve E_{n,d}: Y^2 = X(X-n d)(X+2nd) attached to the AP. The Galois representation ρ_3 (Y^2 = ...) is geometrically tractable.

### B3. Combinatorics — Polynomial method on AP-free sets
Croot-Lev-Pach / Ellenberg-Gijswijt cap-set bound: |A ⊂ F_3^n with no 3-AP| ≤ O(2.756^n). Reduces 4-AP-detection in F_p^n to bilinear-form analysis. Adapted to integers via Bohr-set arguments: the integers with cube-free factorization in a Bohr set near 0 have density 0, restricting where a 4-AP-cube can live.

### B4. Number-theoretic Diophantine — Thue and S-unit equations
The equation (a^2 b^3)(c^2 d^3)(e^2 f^3)(g^2 h^3) = (xyz)^3 in coprime 4-term AP is a system of 4 S-unit equations. Each term's signature (a^2 b^3) is constrained by the AP relation. **Strong analog**: Mihăilescu's resolution of Catalan via S-unit equations + heights.

---

## C. Technique-transfer candidates

1. **Bennett-Skinner Frey-curve method** (2004 Canad. J. Math). For each fixed term n in the AP, attach Frey curve E_n: Y² = X(X-n)(X+(n+d)). Level-lower the mod-3 Galois rep to weight-2 cusp form on Γ_0(N(n,d)). Citation: Bennett, M.A., Skinner, C.M. "Ternary Diophantine equations via Galois representations and modular forms."
2. **Bilu-Tichy method on quartic Diophantine** — for Y² = quartic in X, decompose via Bilu-Tichy theorem on functional equations of polynomials. Citation: Bilu, Tichy "The Diophantine equation f(x) = g(y)" Acta Arith 2000.
3. **Sander conjecture mass-increment** (Hyrlek, Tao 2024) — uses "novel mass increment argument loosely inspired by additive combinatorics" + quantitative Faltings to attack Sander-type questions on Erdős-Selfridge curves. Citation: Recent 2024 arXiv work extending Bennett-Siksek.
4. **Chabauty method on rank-1 quotient** — if the Jacobian J(C) of the AP-cube curve has Mordell-Weil rank 1 over ℚ, then Chabauty gives effective bounds on rational points. Citation: Stoll, M. "Independence of rational points on twists of a given curve."
5. **abc-conjecture-style descent** (Mochizuki / Stewart-Yu hybrid). The product equation forces strong shape on rad(nd(n+d)(n+2d)(n+3d)) vs y^3. abc would give an explicit upper bound on |y|. Citation: Stewart, Yu "On the abc conjecture, II" Duke 2001.

---

## D. Most promising fusion: **Frey curve + Mordell-Weil sieve on the genus-2 quotient**

**Specific idea:** Reduce E672 at (k=4, ℓ=3) to a finite-rank-Jacobian computation.

The curve C: y³ = X(X+a)(X+2a)(X+3a) (after normalizing d → 1 by scaling) has genus 2 and Jacobian J(C). If J(C) has Mordell-Weil rank ≤ 1 over ℚ, then **Chabauty's method** (via Stoll, Bruin-Stoll) gives an effective bound on rational points. Combined with a few small primes of good reduction (p = 5, 7, 11, 13), Mordell-Weil sieve eliminates all but finitely many candidate rationals — and these can be checked.

This is the same machinery that resolved (k=4, ℓ=2), (k=5, ℓ=2), and (k=3, ℓ=3,4,5) historically (Euler, Obláth, modern reformulations).

**Why fusion-amenable now (2026):**
- Mathlib has `EllipticCurve.Jacobian` and `RationalPoints` (mature by 2025).
- LMFDB has tables of genus-2 curves with rank ≤ 1 — direct database lookup possible.
- Aristotle has shown capacity on Brocard-type structured finite reductions (slot 738).

**Risk:** If J(C) for the specific E672 curve has rank ≥ 2, Chabauty fails and we're back to Faltings-only (ineffective). The rank computation is the crucial ingredient.

---

## E. What we'd need to feed Aristotle

Beyond bare gap:

```
OPEN GAP: Erdős 672 at (k=4, ℓ=3) — disproof candidate
Source: formal-conjectures/FormalConjectures/ErdosProblems/672.lean

Statement: ∃ (n d : ℕ), n > 0 ∧ d > 0 ∧ Nat.gcd n d = 1 ∧
  ∃ q : ℕ, n * (n+d) * (n+2*d) * (n+3*d) = q^3

theorem erdos_672_k4_l3_witness :
  ∃ n d q : ℕ, n > 0 ∧ d > 0 ∧ Nat.gcd n d = 1 ∧
    n * (n+d) * (n+2*d) * (n+3*d) = q^3 := by sorry

Equivalent geometric framing:
The Diophantine equation defines a curve C : y^3 = x(x+1)(x+2)(x+3) (after rescaling).
By Faltings (1983), C has finitely many rational points (genus = 2).
By Chabauty-Coleman (if rank J(C) ≤ 1), the rational points are effectively listable.

Hint: examine the Jacobian J(C) over ℚ for rank. If rank ≤ 1, enumerate rational
points via Mordell-Weil sieve at primes p ∈ {5, 7, 11, 13}.

Search bound: existing exhaustive search at scripts/erdos672_k4_l3_search.py up to
N ≤ 10^9 — no witness found. The conjecture is that no witness exists, so this is
a disproof-of-witness (positive direction of E672 at this parameter pair).
```

**Crucial cross-domain ingredient**: invite Aristotle to attempt either:
- **Path A (witness)**: Find explicit (n, d, q) — likely doesn't exist, but a small search up to 10^12 with cube-detection via residue tables.
- **Path B (non-witness)**: Apply Frey-curve modular method, citing Bennett-Skinner 2004. Specifically: for any putative AP cube, the four factors n, n+d, n+2d, n+3d each have cube-shape, attach 4 elliptic Frey curves, level-lower to weight-2 cusp form, derive contradiction from spaces S_2(Γ_0(N)) at small N.

**Honest assessment:** Plausibility 5/10 for closure. The problem is **arguably already solved** by Győry-Hajdu-Pintér 2009 — needs literature verification. If indeed open, the genus-2 Chabauty approach is the right path but requires explicit Jacobian rank input that Aristotle cannot compute alone.
