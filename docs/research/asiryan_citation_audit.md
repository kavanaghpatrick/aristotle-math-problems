# Asiryan Citation Audit (arXiv:2512.11072)

**Date:** 2026-05-30
**Auditor:** Claude (verification agent)
**Trigger:** R7 (E324 fusion) flagged citation as possibly hallucinated.

## VERDICT: REAL — paper is genuine and accurately cited.

## Evidence

### Primary paper (cited in R7 E324 fusion)
- **arXiv ID:** 2512.11072 [math.NT, cross-list math.AG]
- **Title:** "Genus-One Fibrations and the Jacobian of Linear Slices in the Quintic Equal-Sum Problem"
- **Author:** Valery Asiryan
- **v1 submitted:** Dec 11, 2025
- **v3 (current):** Mar 15, 2026
- **URLs verified:**
  - https://arxiv.org/abs/2512.11072
  - https://arxiv.org/pdf/2512.11072
  - https://arxiv.org/html/2512.11072
- **MSC:** 11D41, 11G05, 11Y50, 11A07, 14H52

### Companion paper (referenced by 2512.11072)
- **arXiv ID:** 2512.00551 [math.NT]
- **Title:** "The Linear Slicing Method for Equal Sums of Like Powers: Modular and Geometric Constraints"
- **Author:** Valery Asiryan
- **Submitted:** Nov 29, 2025 (v1); Dec 6, 2025 (v2)
- Establishes the general Modular Divisibility Obstruction (MDO) for a^k+b^k=c^k+d^k under linear slicing; k=5 instance is M_5=30.

## Confirmed Technical Content (matches what S6/R7 cited)

The paper studies a^5+b^5=c^5+d^5 under linear slice constraint (c+d)−(a+b)=h:

1. **30|h modular obstruction** — self-contained proof of the necessary congruence (this is exactly the "30|h" hook S6 flagged).
2. **Symmetrization:** S=a+b, u=b−a, T=S+h, v=d−c → biquadratic in v with discriminant D_Z(S,u).
3. **Genus-one fibration:** Y²=D_Z(S,u) over Q(S), passes to Jacobian E_h/Q(S).
4. **2-torsion analysis:** Global rational 2-torsion section exists; full rational 2-torsion never occurs (S·Q_5(S,h) has odd valuation at S=0).
5. **Universal genus-two curve:** Square condition reduces to rational points on a universal hyperelliptic curve — only (0,0) and two points at infinity per MAGMA Chabauty-Coleman computation (rank-0 bound).
6. **Slice h=30:** Explicit Weierstrass model; Gusić-Tadić specialization criterion → rank ≤ 1; explicit infinite-order section → rank = 1.
7. **Author's stated limitation:** Does NOT resolve unconstrained a^5+b^5=c^5+d^5.

## Why R7 false-flagged it

The R7 review agent likely did not have web access at audit time, or queried with the wrong identifier format. The paper is fresh (v1 Dec 2025, current v3 Mar 2026) and may not appear in older indices, but it is fully visible on arxiv.org with three accessible URLs and MSC classifications matching the cited domain.

## Action Required

**NO correction needed.** Submissions and reports citing arXiv:2512.11072 are factually grounded:

- R7 E324 Asiryan iter3 submission UUID `da7abd31` — citation accurate
- S6 technique scouting report — citation accurate
- Any fusion companion files referencing 30|h genus-one fibration — citation accurate

The R7 agent's "no known publication" flag was a **false negative**, not a real hallucination. Verification stands: cite freely.

## Sources

- [arXiv:2512.11072 (Asiryan, Genus-One Fibrations)](https://arxiv.org/abs/2512.11072)
- [arXiv:2512.00551 (Asiryan, Linear Slicing Method)](https://arxiv.org/abs/2512.00551)
