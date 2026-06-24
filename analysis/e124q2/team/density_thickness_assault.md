# ASSAULT: the discrete Astels/Newhouse thickness theorem for E124

**Author:** density. **Status:** ATTACK IN PROGRESS. Recording the attempt + exact death points.
**Claim board:** density owns the measure/thickness-side attack on the BEGL96 threshold.

## The key identity (VERIFIED, exact)

Model B_d ∩ [0, d^m) as a discrete Cantor-type set. Self-similar gap structure at every level m:
split by top digit (position m−1) into two "bridges" with a central gap:
- left bridge = B_d ∩ [0, d^{m−1}), max value (d^{m−1}−1)/(d−1)
- right bridge = d^{m−1} + (left bridge), min value d^{m−1}
- central gap = ( (d^{m−1}−1)/(d−1), d^{m−1} ), length ≈ d^{m−1}·(d−2)/(d−1)
- each bridge length ≈ d^{m−1}/(d−1)

**Newhouse thickness** τ(B_d) = (smaller bridge)/(gap) = [d^{m−1}/(d−1)] / [d^{m−1}(d−2)/(d−1)]
= **1/(d−2)**, the same at every level (self-similar).

**Astels normalized thickness** γ(C) := τ/(1+τ). Here:
    γ(B_d) = [1/(d−2)] / [1 + 1/(d−2)] = [1/(d−2)] / [(d−1)/(d−2)] = **1/(d−1)**  (EXACT).

## The bridge to BEGL96

Astels' theorem (1999, "Cantor sets and numbers with restricted partial quotients"): for Cantor
sets C_1,…,C_r, if ∑_i γ(C_i) ≥ 1 then the sumset C_1+…+C_r contains the interval
[∑ min C_i, ∑ max C_i]. Applying with C_i = B_{d_i}:

    ∑_i γ(B_{d_i}) = ∑_i 1/(d_i − 1) ≥ 1   ⟺   BEGL96 admissibility threshold.

**So the BEGL96 threshold ∑1/(d−1) ≥ 1 IS Astels' sum-of-normalized-thicknesses condition.**
This explains why the threshold is exactly 1, why it is additive in the bases, and why it is the
sharp covering boundary (matching my max-reach worst-case = 1/(d−1)).

## What this WOULD prove (if the discrete analogue holds)
The k=0 BEGL96 theorem (sufficiency: ∑1/(d−1)≥1 ⟹ ∑ B_d cofinite) as a clean corollary of the
discrete Astels theorem — NO transcendence needed at k=0. (Consistent with Alexeev's k=0 proof
existing; this would be an independent structural route.)

## DEATH POINTS — tested, with verdicts

**DP1 — discrete vs compact.** Modeled B_d ∩ [0, d^m) as a discrete self-similar Cantor set.
"Interval" → "contiguous integer run". The self-similar nesting is honest (two top-digit copies +
central gap, recursing). CLEARED as a modeling step.

**DP2 — infimum thickness = 1/(d−2)?** CLEARED. By self-similarity every gap at every level has
the same bridge/gap ratio: bridge ≈ d^{m−1}/(d−1), gap ≈ d^{m−1}(d−2)/(d−1), ratio = 1/(d−2)
exactly. So τ(B_d) = 1/(d−2) is the honest infimum, and γ(B_d) = τ/(1+τ) = 1/(d−1). Verified
numerically (central gap length matches (d^{m−1}−1)(d−2)/(d−1) exactly for d=3,4,5).

**DP3 — chaining finite intervals to cofinite.** Caveat found and resolved: a naive truncation
(cap every B_d at one common N) produces a FALSE 269,850-missing artifact; the correct covering
uses B_d ∩ [0,X] per scale, and then (3,4,7) covers [0,300000] with ZERO missing. So chaining is
fine IF each scale is genuinely covered. The open content is whether each scale IS covered = DP4.

**DP4 — the boundary ∑γ = 1 and the superadditivity crux. ← THE EXACT DEATH POINT.**

For r ≥ 3, Astels is applied recursively: B_3 + (B_4 + B_7). The crux is the lemma
γ(C₁+C₂) ≥ γ(C₁)+γ(C₂) (normalized thickness superadditive under sumset). If it held discretely:
γ(B_4+B_7) ≥ 1/3+1/6 = 1/2, then γ(B_3)+γ(B_4+B_7) ≥ 1/2+1/2 = 1 ⟹ Astels interval ⟹ (3,4,7)
cofinite at k=0 WITHOUT transcendence.

**It FAILS discretely.** Measured: B_4+B_7 (scale 7^7) has a max gap of 336,761 ≈ **0.41 × hull**,
located at (486782, 823543) = exactly its **top-of-7^7 gap** (the same power-aligned gap my
converse analysis isolates). A genuine self-similar Cantor set of normalized thickness 1/2 would
have max relative gap ≈ 1/3, not 0.41. So the discrete sumset's largest gap is power-aligned and
LARGER than continuous superadditivity predicts — **discrete normalized thickness is NOT
superadditive here.** Reason: B_d are not genuine self-similar Cantor sets — their gaps are
arithmetically ALIGNED at powers, and the top-of-power gap of B_4+B_7 recurs at every power of 7,
defeating the self-similar bridging Astels needs.

**But the death is not fatal at finite scale** — it relocates to the true core. When B_3 is added,
it DOES fill B_4+B_7's top-of-7^7 gap (verified: full B_3+B_4+B_7 has 0 missing in (486782,823543),
0 missing up to 7^7). So the recursive-Astels obstruction is bridged by the third set AT THIS
SCALE. **The exact death point: proving this bridging holds UNIFORMLY at ALL scales** — i.e. B_3's
elements land in B_4+B_7's top-of-7^m gaps for every m, a statement about the relative alignment of
powers of 3 vs powers of 7, i.e. lower bounds on |3^a − 7^b·c|. **This is exactly the
Mignotte–Waldschmidt linear-forms-in-logarithms content of BEGL96.**

## CONCLUSION OF THE ASSAULT (honest)

The thickness/Astels framework is REAL and gives the threshold cleanly: γ(B_d) = 1/(d−1) exactly,
so ∑1/(d−1) ≥ 1 IS Astels' sum-of-normalized-thicknesses condition — a genuine structural
explanation of WHY the threshold is what it is (new framing, not BEGL96's direct covering argument).
**But the discrete Astels theorem does NOT close k=0 sufficiency**, because normalized-thickness
superadditivity fails for these arithmetically-aligned sets. The failure relocates the open content
to exactly the transcendence statement (power-alignment of different bases), confirming — from an
independent measure-theoretic direction — that the irreducible core is linear-forms-in-logarithms,
NOT combinatorics.

**Net (a real, if negative, structural result): the measure-side attack reduces the problem to the
SAME transcendence core as every other route. There is NO thickness-only shortcut around
Mignotte–Waldschmidt. This rules out a thickness-only proof and corroborates maverick's (SEED) →
transcendence and the team consensus.**

## STRICT-EXCESS LEAD — pursued, hits the SAME wall (FINAL)

Tested whether ∑1/(d−1) = 1+δ (strict) admits a transcendence-free proof. Three framings, all
hitting the IDENTICAL wall:

1. **Thickness-margin (DP4 with δ):** at δ>0 the remaining mass over-covers the first-level
   top-of-d_min^m gap by δ·d_min^m. This is REAL and quantitative — it explains sumset's geometric
   threshold law: threshold ≤ C(δ)·(d_max·d_2)^k with C collapsing as δ grows (measured C·δ ≈
   0.46→0.07→0.014 for (3,4,5,7)→(3,4,5,6,7)→(3,4,5,6,7,9) at k=3). → density_strict_excess_thickness_margin.md.
2. **Base-by-base induction: DEAD.** Covering d_i's power-gap using only larger bases d_{>i} fails:
   the tail sums ∑_{j>i}1/(d_j−1) drop below the needed (1−1/(d_i−1)) at EVERY level past the first.
   The margin δ lives ONLY at the top level; it does NOT propagate down a chain. The covering is
   genuinely COUPLED across all bases (CRT-like), not decomposable per-base.
3. **Reach-set intersection (the correct non-inductive frame):** n representable ⟺
   (n − B_{d_min}) ∩ (∑_{d>d_min} B_d) ≠ ∅. But this intersection is NOT forced by reach-density
   sum ≥ 1 — it fails exactly when the two sets' gaps ALIGN (both have a power-gap at the same
   place), and whether they align is the relative position of powers of different bases = MW.

**FINAL (honest, negative):** the margin δ helps QUANTITATIVELY (rarer aligned gaps, smaller
threshold) but does NOT remove the alignment obstruction at finite δ. All measure-side framings
reduce to the same Mignotte–Waldschmidt transcendence core. NO transcendence-free proof of even
strict-excess BEGL via thickness/reach methods. (Consistent with scholar's [LIT/SEC] "MW provably
non-uniform" and with the fact that BEGL96 needed MW even for the single family (3,4,7).)

**ONE genuinely new sub-observation (worth a follow-up):** for "many-base, large-d_min" families
like (4,5,6,7,8), the SUB-sumset ∑_{d>d_min} B_d is ITSELF near-interval (max gap = 1 to 2×10^5
despite sub-∑ = 0.76 < 1). In that regime the reach-set intersection IS forced without alignment
control — the sub-sumset is locally dense enough that (n − B_{d_min}) cannot miss it. This is the
ONE place a transcendence-free argument might survive: families where dropping the smallest base
still leaves a sub-sumset with NO large power-gaps (heuristically, enough bases of comparable size).
This is NOT the conjecture's full scope, but could be a clean transcendence-free SUB-theorem. Handed
to sumset/cassels for the interval-filling side.

## CONTINUUM REVERSAL (with scholar) — verified: boundary is arithmetic, not metric

scholar's independent continuum-side assault and mine converge with a sharp REVERSAL I verified:

> Integer (3,4,7) IS cofinite (to 10^8), but the REAL Cantor sumset K_3+K_4+K_7 is NOT an interval.

Verified (finite-depth continuum, exact fractions): the continuum sumset's max-gap-to-resolution
ratio GROWS with depth — 4.4 → 12.3 → 24.6 → 29.2 (depths 3..6). The absolute gap shrinks but
SLOWER than the resolution 7^{−depth} refines, so the limiting Cantor sumset retains persistent
relative gaps ⟹ NOT an interval. (Continuum Astels at ∑γ=1 EXACTLY is borderline and here fails.)

**Interpretation (the cleanest statement of the whole measure-side finding):** at the boundary
∑1/(d−1)=1, thickness/metric structure is NOT sufficient — the continuum Cantor sumset, which has
the SAME thickness (∑γ=1), is NOT an interval. The INTEGER lattice version IS complete. The extra
slack the integers have over the continuum is precisely the ARITHMETIC alignment of the atoms
(|3^p−4^q| spacings), i.e. the Mignotte–Waldschmidt content. So the boundary problem lives entirely
in arithmetic, not metric geometry — there is no thickness shortcut, confirmed from BOTH the discrete
(my DP4) and continuum (scholar) directions. The lattice-floor slack is the MW input made visible.
