# E324 h=0 Slice — Novelty Audit

**Result audited:** Aristotle UUID `da7abd31` (`erdos_324_h_zero`)
Claim: if a⁵+b⁵=c⁵+d⁵ and a+b=c+d, then {a,b}={c,d}.

## 1. Algebraic verification — PASSES

Identity `-3s² + 4sa - 4a² = -(3(s - 2a/3)² + 8a²/3)` confirmed by sympy
(expand difference → 0). The quadratic q(t) = t² - st + (s² - sa + a²) has
discriminant Δ = -3s² + 4sa - 4a²; as a quadratic in s, Δ has discriminant
-32a² ≤ 0, so 3s²-4sa+4a² ≥ 0 always, with strict inequality unless
a = s = 0. Hence q has no real roots ≠ {a, b}, forcing (c,d)=(a,b). The
algebra is correct.

## 2. Novelty — ELEMENTARY / FOLKLORE

This is a **textbook-level classical result**, provable at least three ways:

**(a) Strict convexity.** For any k > 1, f(x) = xᵏ is strictly convex on
ℝ≥0. If a+b = c+d = S then aᵏ+bᵏ as a function of (a,b) with a+b=S
fixed is strictly convex in |a-b|, so the value determines |a-b|, hence
{a,b}. Holds for *all* k > 1, not just k=5. (Cited in Asiryan,
arXiv:2512.00551.)

**(b) Newton's identities (1666).** Two reals are determined by their
first two power sums p₁=a+b and p₂=a²+b² (char ≠ 2). Given p₁=p₁',
equality of any higher pₖ (k≥2) is equivalent to equality of p₂ via
Newton recurrence, hence determines the pair.

**(c) Asiryan's factorization (2026 preprint, arXiv:2512.11072 /
2512.00551).** Symmetrize via S=a+b, u=b-a. Then 16(a⁵+b⁵) =
S⁵+10S³u²+5Su⁴. When S=T, equality reduces to
5S(u²-v²)(2S²+u²+v²)=0 → u²=v². This is the *modern* elementary proof
of the h=0 slice and is explicitly the easy case in linear-slice
methods for E324. The hard problem is h ≠ 0.

R7/Aristotle's proof — the (t-a)(t-b)q(t) factorization with negative
discriminant on q — is a fourth elementary route, but it solves
exactly the same h=0 problem all three classical methods solve.

## 3. Honest classification

**ELEMENTARY / FOLKLORE.** This is not novel mathematics. It is the
trivial slice of E324, dispatched in Asiryan's papers (Mar/Dec 2026) as
the easy starting case before the genuine work on h ≠ 0. Strict
convexity gives it in two lines for *any* exponent k>1.

## 4. Research impact on E324 — NEGLIGIBLE

The open problem is positive-integer solutions with a+b ≠ c+d (h ≠ 0).
The h=0 slice has been known to be trivial since Newton. R7 has
produced a **NOVEL FORMALIZATION** (likely the first Lean 4 proof of
this specific statement) but **zero structural advance** toward closing
E324. The MDO (5 | h) and the genus-one Jacobian analysis on h ≠ 0
slices are where the real frontier lies.

**Verdict: NOVEL FORMALIZATION of an ELEMENTARY result. Do not market
as progress on E324.**

## Sources
- [Asiryan, Linear Slicing Method, arXiv:2512.00551](https://arxiv.org/pdf/2512.00551)
- [Asiryan, Genus-One Fibrations, arXiv:2512.11072](https://arxiv.org/pdf/2512.11072)
- [Newton's Identities (Wikipedia)](https://en.wikipedia.org/wiki/Newton's_identities)
- [Lander-Parkin-Selfridge (Wikipedia)](https://en.wikipedia.org/wiki/Lander,_Parkin,_and_Selfridge_conjecture)
