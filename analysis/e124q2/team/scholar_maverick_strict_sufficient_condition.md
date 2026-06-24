# The precise strict-excess sufficient condition (scholar × maverick, co-written)

**Authors:** scholar (continuum-thickness + literature) × maverick (independent thickness assault +
{3,4,6} kill). Consolidates the team's triangulated finding into ONE precise, honestly-scoped
sufficient condition for the (A)/archimedean half of E124 Q2. All pieces below are team-verified;
attributions inline. This is the "winnable tier" statement — NOT the full conjecture.

> **CITATION NOTE:** "Cassels/Brown gap-condition" = the interval-filling completeness criterion.
> Correct refs: **Brown 1961** (Amer. Math. Monthly 68, 557–560) + **Erdős 1962** (Acta Arith. 7,
> 345–354). "Cassels 1960" is a PHANTOM — do not cite. Astels thickness = **Astels, Trans. AMS 352
> (2000)**.

---

## 0. The object (settled team reduction)
`B_d` = base-d 0/1-digit integers; `R_k = ∑_{d∈D} d^k·B_d` (sumset's scaling). Q2: is `R_k` cofinite
for admissible D (all d≥3, gcd(D)=1, β:=∑1/(d−1) ≥ 1) and every k≥1? Two halves (lift's (R)/(A)):
- **(R) residue/congruential** — PROVED (lift/sumset/modular): gcd=1 ⟺ R_k hits every residue mod
  every M. = BEGL96 Claim 4, formalizable.
- **(A) archimedean/gap-filling** — the open core. THIS document gives the winnable sub-case.

## 1. The discriminator is δ vs LOG-CLUSTERING (NOT strict-vs-boundary, NOT pairwise-coprime)
Two over-simplifications were refuted and corrected (verified):
- **maverick's {3,4,6} kill:** δ = β−1 = 0.033 > 0 (STRICT excess) but `R_k` threshold GROWS with k
  (n₀(1)=986 > the boundary (3,4,7)'s 581; the normalized threshold n₀/(d_max·d_2)^k climbs
  41→420→3000). Cause: `6 = 2·3`, so `6^j = 2^j·3^j` clusters with 3^b, 4^a via small |2^a − 3^b| —
  MW survives strict excess. ⟹ "strict excess ⟹ easy" is FALSE.
- **sumset's coprimality refutation:** (3,4,7) is PAIRWISE-coprime yet MW-hard at δ=0, because
  `3^5=243 ≈ 4^4=256` (log4/log3 ≈ 5/4) is a LOGARITHMIC near-coincidence, gcd-independent.
- **scholar's clincher:** (3,4,5,7,11,13) has the TIGHTEST log-cluster tested (3^7=2187 vs 13^3=2197,
  rel 0.0046) yet is EASY — because δ=0.43 swamps it. So it's the COMPARISON that decides.

> **Definition (log-clustering).** `Λ(D,k) := max over base pairs (d_i,d_j) and exponents p,q≥k of
> [1 − |d_i^p − d_j^q| / min(d_i^p, d_j^q)]⁺`, the worst relative near-coincidence of two atoms (≈ the
> Mignotte–Waldschmidt spacing; large when two bases' powers nearly collide). Λ is governed by the
> continued-fraction convergents of log d_i/log d_j and is k-uniform (lift §B: raising k only discards
> small pairs).

## 2. The sufficient condition (co-written statement)

> **Conjecture/Target (strict-excess, margin-dominates-clustering).** Let D be admissible
> (all d≥3, gcd=1, β≥1) and k≥1. If the harmonic margin DOMINATES the worst-pair log-clustering —
> **δ = β − 1 > δ₀(D,k)** for a Baker-floor-derived threshold δ₀ — then `R_k` is cofinite, with an
> effective threshold N₀(D,k) computed by ELEMENTARY means ABOVE δ₀.

> **⚠ HONESTY GUARDRAIL (maverick): the winnable tier is BAKER-CONDITIONAL AT THE EDGE, not fully
> transcendence-free.** The threshold δ₀(D,k) below which clustering wins is ITSELF a Baker/MW quantity
> — it is set by the closest cross-base coincidence |d_i^p − d_j^q|, i.e. by Λ, which is transcendence-
> theoretic. So the honest statement is: "for δ exceeding the Baker-floor δ₀(D), the cofiniteness proof
> is elementary; but δ₀ itself is an MW quantity." The interior of the winnable region is
> transcendence-free; its BOUNDARY is transcendence-set. This matches the canonical line (non-minimal
> proven via Lemma M / minimal open / k=1 Baker-conditional) and troika's hardness fact (NO computable
> discriminator decides β). Do NOT state the winnable tier as "transcendence-free" simpliciter — state
> it as "elementary above an MW-set floor." (Both maverick's 1/(d_max−1) single-ray artifact and
> scholar's earlier strict-vs-boundary binary were over-claims caught by peers; this guardrail prevents
> the next one.)

The pieces that assemble it (all team-PROVED or verified, no MW needed in this regime):
- **Lemma A (cassels): gap-CONDITION onset.** `S(X) ≥ m·β − C'` (C'=∑d^k/(d−1)) ⟹ the Brown/Erdős
  gap-condition `next-atom ≤ S(X)+1` holds for all atoms `m ≥ m₀ := (C'−1)/σ`, σ=δ. Finite for δ>0,
  ∞ at δ=0. [NEW as a stated result, scholar prior-art; elementary geometric-series estimate.]
- **No-new-gaps (Lemma A corollary):** above m₀ no new gap can form.
- **Locality (cassels Lemma B, empirical):** gap-closing is local (V/N₀ ∈ [1.03,1.14]) ⟹ a finite
  computation to O(N₀) certifies.
- **Residue seed (R-half, PROVED):** gcd=1 ⟹ each class mod M=d_min^k is hit; the gap-condition makes
  it a full AP above its onset; the seed (M consecutive integers) exists once all class-onsets pass.
- **Astels/thickness (scholar): WHY β≥1 is the threshold** — γ(K_d)=1/(d−1), ∑γ≥1 is exactly Astels'
  sum-of-thicknesses interval criterion (continuum shadow). The STRICT version ∑γ>1 gives a continuum
  interval; the lattice floor adds slack ⟹ integer cofinite — PROVIDED no coincidence (Λ small).

**What δ > Φ(Λ) buys:** when the margin exceeds the clustering, the only place the gap-condition could
fail (the MW near-coincidence atoms) is overpowered by the surplus reach δ·(scale) — so m₀ is finite
AND the existing low gaps close locally without any transcendence input. Λ small (mult.-independent
bases, large margin) ⟹ elementary; Λ ≥ δ (boundary δ=0, OR coincidence families like {3,4,6}) ⟹ the
surplus can't cover the clustered atoms ⟹ MW required. This is the exact line between winnable and core.

## 3. Honest scope (what is and isn't proved)
- PROVED elementarily in this regime: (R) residue half; Lemma A gap-condition onset (δ>0); locality
  (empirical); the threshold-IS-Astels-thickness explanation.
- NOT yet proved: that δ > Φ(Λ) makes the EXISTING low gaps all close (the seed/onset assembly) with a
  fully rigorous, k-uniform Φ. maverick's {3,4,6} shows Φ must genuinely depend on Λ (clustering), not
  just δ>0. The precise Φ — how much margin beats a given clustering — is the open quantitative core of
  the WINNABLE tier. (The BOUNDARY δ=0 and coincidence families are the SEPARATE MW core, not here.)
- So: this is a sufficient-condition TARGET with most pieces proved and the residual being "pin Φ."
  It is NOT "strict excess ⟹ cofinite" (false, {3,4,6}) and NOT the full conjecture (boundary+
  coincidences need MW). Frame any writeup as "elementary cofiniteness under margin-dominates-clustering."

## 4. The two genuinely-new fragments this regime yields (prior-art cleared, scholar)
1. **Lemma A** (shifted gap-condition onset m₀=(C'−1)/σ) — NEW vs Brown/Erdős (unit-seeded k=0 only).
2. **The margin-vs-log-clustering dichotomy** itself (winnable ⟺ δ>Φ(Λ); MW ⟺ Λ≥δ) — the precise
   placement of the BEGL96 boundary is unpublished; it's the analytic content behind "why (3,4,7) is
   hard but (3,4,5) easy." Connects to INV-S10 (Riesz-product decorrelation = the Fourier face of Λ).
