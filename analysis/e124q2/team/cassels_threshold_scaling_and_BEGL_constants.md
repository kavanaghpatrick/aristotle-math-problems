# E124: corrected threshold-scaling data, the scaling conjecture, and BEGL96 constant corrections

**Author:** cassels. **Status:** Data VERIFIED-STABLE where marked; scaling conjecture stated with
the honest caveat that the boundary (∑=1) and strict (∑>1) regimes scale DIFFERENTLY. Three BEGL96
printed constants found to be off by +1 (independently double-checked).

Engines: my bitset `code/reach.py` + recreated numpy `code/fast_engine.py` (= breaker's method).
Cross-validated: both reproduce BEGL96's (3,4,7) s=1 value 581 exactly.

---

## 1. BEGL96 small-example constants — THREE are off by +1 (correction to the literature)

BEGL96 §3 prints four largest-missing values for s=1. Verified against the actual Lean definition
(`∑_{d∈D} sumsOfDistinctPowers d 1`), with my numpy engine AND an independent 4-fold brute force:

| D | BEGL96 prints | VERIFIED (this work) | note |
|---|---|---|---|
| (3,4,7) | 581 | **581** | ✓ matches |
| (3,4,5) | 78 | **79** | paper's 78 IS representable; 79 is the true largest gap |
| (3,5,7,13) | 111 | **112** | 111 = 12+30+56+13 (representable); 112 is the true largest gap |
| (3,6,7,13,21) | 16 | **17** | paper's 16 representable; 17 is the true largest gap |

Pattern: three of four are exactly paper+1, and in each the paper's printed value IS representable
under the standard convention while paper+1 is the genuine largest missing. (3,4,7)=581 is correct.
Most likely: **typos in BEGL96's example list** (the (3,4,7) headline figure, which the MW argument
actually targets, is right). **Anyone formalising or citing should use 581, 79, 112, 17.** This is
also why scholar's relayed "(3,5,7,13)=111" looked off — the paper itself prints 111.
(Raw paper text: `_raw_begl96_fulltext.txt`, lines with "largest missing integer".)

**Also confirmed from the raw text:** BEGL96's displayed (3,4,7) result is **for s=1 ONLY**
("the largest integer not in Σ(Pow({3,4,7};1)) is 581"). The paper does NOT prove (3,4,7) for all
k — the "for any s" appears only in the *conjecture*. So the Lean lemma
`erdos124.ne_zero_three_four_seven` (claims all k≠0) asserts MORE than BEGL96 proves. It is true
empirically (see §2) but its proof for general k is not in BEGL96. [flag for scholar / formalisers]

---

## 2. Verified-stable threshold data (largest non-representable integer)

"Stable" = window N extends well past the value with no further gaps (the straggler trap below
makes this essential). All values below are stable unless flagged.

| D | ∑1/(d−1) | k=1 | k=2 | k=3 |
|---|---|---|---|---|
| (3,4,7) — boundary | 1.000 | 581 | **3,982,888** | **166,025,260** (stable, N=700M) |
| (3,4,5) — strict | 1.083 | 79 | 77,613 | 4,330,731 |
| (3,4,6) — strict | 1.033 | 986 | 242,113 | — |

**Team-wide CORRECTION:** the widely-circulated (3,4,7) k=2 = 785,743 (troika, early lift, early
cassels) and k=3 = 57.7M (breaker, troika) are BOTH window-truncation artifacts. Correct k=2 =
3,982,888 (stable at N=16M). Correct k=3 = **166,025,260** (count 391,070; stable at N=700M, largest
gap < N/3 with the top gaps clustering at 166M and nothing above). The 57.7M figure was truncated by
~2.9×.

Corrected ratios (boundary (3,4,7)): N₀(k+1)/N₀(k) = 6857 (k1→k2), 41.7 (k2→k3). N₀/84^k =
6.9, 564, 280 — NOT constant (product-law fails at the boundary, see §3). Note the per-step ratio is
itself non-monotone (6857 then 41.7), so even the boundary growth is not a clean single exponent.

### The straggler trap (methodological, important for the whole team)
For (3,4,7) k=2, local coverage hits 1.000 across [100k, 800k], yet the true last gap is at 3.98M.
**Local saturation to density 1 does NOT imply cofiniteness has begun** — isolated stragglers
persist far above a region that looks complete. A reported threshold is valid ONLY if the window
extends far past it (rule of thumb: ≥3–4× the claimed value, and verify zero gaps in the tail).

---

## 3. The scaling conjecture (task #7) — with the honest boundary/strict split

Let N₀(D,k) = largest non-representable integer. Building on troika's self-similar recursion
(R: T_k = C_k + T_{k+1}) and maverick's monotonicity (N₀ non-decreasing in k):

> **Conjecture S (strict regime, ∑1/(d−1) > 1).** N₀(D,k) ≍ C(D) · P^k where P = ∏_{d∈D} d
> (product of bases). Evidence: (3,4,5) gives N₀/60^k = 1.3, 21.6, 20.0 for k=1,2,3 — the ratio
> STABILISES at k≥2, consistent with clean geometric growth at scale P=product.

> **Conjecture B (boundary regime, ∑1/(d−1) = 1).** N₀(D,k) grows STRICTLY FASTER than C·P^k.
> Evidence: (3,4,7) gives N₀/84^k = 6.9 (k=1), 564 (k=2) — ratio grows ~80×, NOT stabilising.
> The boundary family's threshold inflates super-geometrically relative to the base-product. This
> matches scholar's structural point: at exactly-critical density the gap-closing is governed by
> Diophantine near-coincidences of powers (Mignotte–Waldschmidt |3^p−4^q|), not by counting, so the
> threshold is controlled by transcendence-theoretic spacing, which decays slower than any P^k law.

**This split REFUTES troika's single "N₀ ≈ C·84^k" law** (built on the truncated 785,743): the law
holds for strict families but breaks at the boundary, which is exactly the regime that makes E124
open. The scaling itself encodes WHY the boundary is the hard case.

What is NOT a tower/iterated-exponential: even the boundary growth is polynomial-in-P^k bounded
above (breaker's data: finite at every tested k, ratio per k-step ≈ ×40–80, super-geometric but
not iterated-exp). So "difficulty controlled, but boundary needs a non-counting input."

---

## 4. How this connects to the completeness lemma (cassels_completeness_lemma.md)

The threshold identity N₀ = (last +M-closure violation) + M (M=b^k) means N₀ is exactly the height
of the last failure of the step-M Cassels filling. Conjecture S/B are therefore conjectures about
how high the last +b^k-closure failure sits:
- strict ∑>1: last failure at height ≍ P^k (density supplies enough slack to repair +M steps early);
- boundary ∑=1: last failure pushed much higher by power-near-coincidences (no density slack;
  repair waits for a Diophantine gap to open). **The boundary's last +M-failure is the precise
  object a Baker-type bound would have to control.**
