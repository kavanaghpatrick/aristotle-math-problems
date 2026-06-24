# R3 FT-Family Theorem at q≤2000 — Publishability Assessment

**Date:** 2026-05-30
**UUID:** `09a5b938-dc48-4956-8aed-7fed081157ad`
**Sketch:** `submissions/sketches/FT_p3_q71mod72_qLE2000_iter5.ID.txt`

## R3's Theorem

> ∀ q prime, q ≡ 71 (mod 72), q ≤ 2000, ¬ (q³−1)/(q−1) ∣ (3^q − 1)/2.

In Feit–Thompson notation with p=3: this asserts A=Φ₃(q)=(q³−1)/(q−1) does NOT divide B=Φ_q(3)=(3^q−1)/2 for the listed q. This is a **restricted bounded sub-case of the p=3 case of the Feit–Thompson conjecture**.

## Literature Survey

### Feit–Thompson conjecture (1962)
For distinct primes p<q: A=(q^p−1)/(q−1) does NOT divide B=(p^q−1)/(p−1). Originally proposed to shorten Feit–Thompson's odd-order theorem proof. Remains open in general.

### Computational verifications (already in literature)
- **Stephens (1971)**: refuted the *stronger* coprimality conjecture; counterexample (p=17, q=3313).
- **Motose (2009)** explicitly states (Proc. Japan Acad. 85A, p.17, citing Guy *Unsolved Problems in NT* 3rd ed.):

  > "At the present, it is known by computer that no other such pairs exist for p<q<10⁷ and **p = 3 < q < 10¹⁴**."

  → The **p=3 case has been computer-verified up to q ≈ 10¹⁴ since at least 2004.**

### Theoretical resolution of p=3
- **Le, M.-H. (2012)**, "A divisibility problem concerning group theory," *Pure Appl. Math. Quart.* 8(3), 689–692.
  → Le proves the **p=3 case unconditionally for ALL primes q** (similarly Stephens 1971 for p=2).
- **Motose (2009, 2010)** had already proven partial cases:
  - p=3, q≡1 (mod 3) (trivial via Φ_3(q) ≡ 0 mod p logic)
  - p ≡ 3 (mod 4) AND q ≡ 1 (mod 4)
  - p=3, q>3, A=Φ_3(q) composite
- **Twin primes case**: 2024 preprint (Preprints.org 202403.1214) extends to p, q twin primes.

## Classification: **TRIVIAL**

R3's theorem is **strictly subsumed** by:

1. **Le (2012)** — proves the same statement for ALL primes q, not just q≡71 (mod 72) and q≤2000.
2. **Guy / Motose (2009)** — cites computational verification at p=3 up to q<10¹⁴, i.e., **5 × 10¹⁰× larger range** than R3's q≤2000.
3. **Motose's Proposition** — handles q ≡ 1 (mod p) and the composite-A case unconditionally without bound.

A "verified for q ≡ 71 (mod 72), q ≤ 2000" result is approximately **0.0000002%** of the range already in print. It is:
- Not a new theoretical result (Le 2012 covers it).
- Not a new computational frontier (Guy/Motose's q<10¹⁴ is 10 orders of magnitude larger).
- Not a meaningful step toward the open part of the conjecture (open case is p ≥ 5).

## Mathlib-worthiness

Marginal. The interesting Mathlib target would be **Le (2012)'s unconditional p=3 theorem**, not a bounded sub-residue-class slice. Formalizing q≤2000 ∧ q≡71 mod 72 would be a curio, not a contribution.

## Realistic Publication Venue

**None.** This result cannot be published:
- Not a journal paper (subsumed by Le 2012 + Motose 2009).
- Not a Math. Comp. computational note (range is 10¹⁰× smaller than known computational bound).
- Not a Mathlib PR (wrong target; Le's full theorem is the goal).
- Not even a preprint (no new contribution over Le 2012).

## Recommendation

**Mark this submission as `compiled_no_advance`** with contribution_statement=NULL. Stop iterating on FT p=3 q≡71 mod 72 family. The entire p=3 column of Feit–Thompson is *solved* — Le (2012) — and computationally verified to q<10¹⁴ — Motose (2009) citing Guy.

The genuinely open part of Feit–Thompson is **p ≥ 5**. If targeting FT at all, the gap to attack is e.g. "p=5 case" (Motose 2009 §3 has partial results; Le has not extended). A bare gap-targeting submission for p=5 would be defensible; q≤2000 slices for p=3 are not.

## Sources

- [Wikipedia: Feit–Thompson conjecture](https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_conjecture)
- [Motose, *Notes to the Feit-Thompson conjecture*, Proc. Japan Acad. 85A (2009)](https://projecteuclid.org/journals/proceedings-of-the-japan-academy-series-a-mathematical-sciences/volume-85/issue-2/Notes-to-the-Feit-Thompson-conjecture/10.3792/pjaa.85.16.pdf) — explicit p=3, q<10¹⁴ computational bound, partial theoretical results.
- [Motose, *Notes II*, Proc. Japan Acad. 86A (2010)](https://projecteuclid.org/journals/proceedings-of-the-japan-academy-series-a-mathematical-sciences/volume-86/issue-8/Notes-to-the-Feit-Thompson-conjecture-II/10.3792/pjaa.86.131.pdf)
- Le, M.-H. (2012), "A divisibility problem concerning group theory," *Pure Appl. Math. Quart.* 8(3), 689–692. DOI 10.4310/pamq.2012.v8.n3.a5. — **unconditional p=3 theorem**.
- Stephens, N. M. (1971), Math. Comp. 25(115), 625. — p=2 unconditional + counterexample to stronger form.
- Guy, R. K., *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004 — original citation for q<10¹⁴ bound at p=3.
- [2024 twin-primes extension](https://www.preprints.org/manuscript/202403.1214/v1)
