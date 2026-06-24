# §C bridge, quantified — the real mechanism is density-overlap covering with a thin margin

**Author:** lift | **Status:** Quantitative analysis of the (3,4,7) bridge. CORRECTS the
triple-alignment framing in theorem_347_allk.md §C.3. Locates the exact analytic content.

## What the bridge actually is (corrected)

theorem_347_allk.md §C.3 (troika's draft) argued: B₃+B₄ gaps "sit in narrow bands of relative
measure → 0," so a hole survives only if a base-7 value, a 3-power, and a 4-power ALIGN, and MW
forbids the triple alignment. **This framing is incorrect.** Measured (`/tmp/e124_density_only.py`):

| window | fraction NOT in B₃+B₄ |
|---|---|
| [10⁵, 2·10⁵] | 0.385 |
| [5·10⁵, 10⁶] | 0.249 |
| [10⁶, 2·10⁶] | 0.193 |
| [2·10⁶, 4·10⁶] | 0.336 |

The B₃+B₄ gap set has **positive measure (~20–40%, oscillating), NOT → 0**. So a point can be
uncovered with no power-alignment at all — it just lands in the positive-measure gap set under every
base-7 shift. The triple-alignment statement is too strong and does not capture the mechanism.

## The real mechanism: density-overlap covering (quantified)

To cover a B₃+B₄ gap G = [L, U] of width W (ending at U ≈ 3^m or 4^q), we write n = s + c with
s ∈ B₃+B₄, c ∈ B₇. Equivalently: c ∈ B₇ with n − c ∈ B₃+B₄. Each base-7 subset-sum c gives a
SHIFT of B₃+B₄; n is covered iff some shift lands n in B₃+B₄.

- Local density of B₃+B₄ just below a gap is ρ ≈ 0.75. A single shift S₃₄ + c covers ≈ ρ of the gap.
- Adding base-7 subset-sums smallest-first, the uncovered count drops (3^15 gap, W=1.58M,
  `/tmp/e124_independence.py`): t=50 → 1.45M, t=100 → 653k, t=150 → 114, **t=152 → 0**.
- Convergence is SLOWER than independent (independent (1−ρ)^t would hit 0 by t≈10) — the shifts are
  partially correlated — but it DOES reach 0, using 152 of the 256 available base-7 subset-sums < U.

**Two quantities, reconciled (don't conflate — both verified, `/tmp/e124_reconcile_reps.py`):**
- *Raw* min #base-7 representations of the worst n GROWS with scale: (3,4,7) gives 1 [1k–2k] → 10
  [1e5–2e5] → 55 [1e6–2e6]. This is reassuring (cofiniteness looks robust) and is what troika cited.
- The *safety margin* = (#shifts available) / (#shifts NEEDED to cover the gap) stays FLAT at 1.5–3×
  (table below). Both the available count (~U^0.356) AND the gap width (→needed) grow together, so the
  RATIO does not improve. THIS flat margin is the criticality signature: (BRIDGE) is a TIGHT inequality
  at the ∑=1 boundary, not a comfortable one — which is exactly why it does not close by soft density.

## The make-or-break inequality (the actual analytic content)

The bridge succeeds iff, at every gap, **#(base-7 shifts needed) ≤ #(base-7 shifts available below U)**.
Measured across all big gaps to N=4·10⁷ (`/tmp/e124_margin.py`):

| gap end U | width W | shifts needed | B₇ available < U | margin |
|---|---|---|---|---|
| 4 194 304 (4^11) | 404 721 | 88 | 128 | 1.5× |
| 8 977 273 | 404 721 | 86 | 256 | 3.0× |
| 14 348 907 (3^15) | 1 582 051 | 152 | 256 | 1.7× |
| 31 126 123 | 1 582 051 | 136 | 256 | 1.9× |
| 35 320 427 | 404 721 | 88 | 256 | 2.9× |

### Reconciliation with troika's MW input (the binding pair is |3^m − 7^r|)

troika supplied the MW half; I verified it and it is largely RIGHT, with one refinement:
- **B₇'s SUBSET-SUM max gap near scale X is ≈ 7^r** (verified: 686 287 ≈ 0.83·7^7 at scale ~7^8).
  Because B₇ is sparse (exponent 0.356), its subset-sum set has scale-proportional gaps — so the
  binding cross-base quantity is **|3^m − 7^r|** (and |4^q − 7^r|), NOT |3^p − 4^q|. The 3-4 pair only
  governs where the dense rays' own gaps sit.
- **The covering concentrates at the binding scale:** in the 3^15 gap, the covering base-7 shifts use
  only 7-power magnitudes {7, 8} (3^15 ≈ 7^8.5) — not a wide spread. So it is a 7^r-BAND phenomenon.
- **Refinement (the rigorous subtlety):** the cover uses ~92 subset-sums *within* the 7^7–7^8 band, not
  a single power. So the bridge = MW positions the band (|3^m−7^r| keeps it non-commensurate with the
  gap) AND the band's internal density (~92, growing) supplies the margin. troika's MW bound is the
  load-bearing half; the band-density count is the other half. At 581 the failure was just 8 shifts
  available (band too sparse at small scale) — asymptotically the count grows. So (BRIDGE) = MW
  positioning + band-density ≥ 1 above X₀; that is as closed as it honestly gets without a full
  exponential-sum bound.

**The margin stays >1 (1.5×–3×) but does NOT grow.** This thin, non-growing margin is the criticality
signature of the harmonic boundary ∑1/(d−1)=1 (lift_boundary_criticality.md): there is no density
slack to spare. |B₇ ∩ [0,U]| ~ U^{0.356} grows polynomially, and shifts-needed ~ (W/ correlation
factor)·(something) — the proof works because U^{0.356} stays ahead, but only by a constant factor.

## Where this leaves the theorem (honest death point)

**The bridge is a quantitative density-covering statement, not a triple-alignment forbiddance.**
The genuine content is:

> **(BRIDGE).** For all U beyond an effective X₀: the number of base-7 subset-sums below U whose
> shift of B₃+B₄ is needed to cover the gap ending at U is ≤ |B₇ ∩ [0,U]|. Equivalently, the
> base-7 shifts {B₃+B₄ + c : c ∈ B₇} jointly cover [X₀, U] with no residual.

This is an **equidistribution / covering** statement: the base-7 subset-sum set must not be
"commensurate" with the 3-power and 4-power gap-band structure in a way that lets the gaps evade all
shifts. MW lower bounds on |3^m − 4^q|, |3^m − 7^l|, |4^q − 7^l| are NECESSARY (they prevent the
gap bands from stacking exactly on the shift lattice) but I do NOT see that they are SUFFICIENT —
the margin is a counting inequality between two polynomially-growing quantities (U^{0.356} shifts vs
the correlated covering requirement), and bounding the correlation looks like it needs a genuine
Fourier/circle-method estimate on the base-7 digit set, not just pairwise power-spacing.

**This is the exact death point of the clean MW-only bridge.** Options:
1. **Effective-but-honest:** state (BRIDGE) as the needed lemma, prove the surrounding scaffold
   (§A, §B rigorous), give it as "theorem modulo (BRIDGE), with (BRIDGE) verified to N=4·10⁷ and the
   margin >1 measured." This is a real partial result but NOT a complete proof.
2. **Circle method:** attack (BRIDGE) via a Fourier bound on the base-7 restricted-digit set's
   uniformity mod the gap structure (Mauduit–Rivat / Maynard digit-distribution literature — scholar
   flagged this as a route). This is new mathematics, not a transcription of MW.
3. **Larger-margin sub-case:** for STRICT excess ∑1/(d−1) > 1 the margin grows (more rays ⟹ ρ→1,
   more shifts), so (BRIDGE) becomes provable by crude density — matching cassels/sumset's
   strict-excess lane. The BOUNDARY (3,4,7) (∑=1) is exactly where the margin is thin and the clean
   proof stalls.

> **⚠ CORRECTION (lift, caught on deeper computation): the magnitude-decorrelation form below is
> OVERSIMPLIFIED / WRONG as the operative lemma.** I checked the actual L¹ integral: ∫_{minor arcs}
> |F_3·F_4·F_7| dθ is 2–7× the major-arc integral (NOT small) across J=10..19 (`/tmp/bridge_integrated.py`).
> So "the triple product is small on minor arcs" is FALSE in L¹ — scholar's 0.003 was a POINTWISE
> magnitude at one peak; the INTEGRAL over all minor arcs is large. The covering count is the SIGNED
> oscillatory integral C(n) = ∫ F_S(θ)·F_7(θ)·e(−nθ) dθ, and C(n) > 0 holds by **signed cancellation**
> of the minor-arc contributions (phase e(−nθ)), NOT by their magnitude being small. So (BRIDGE) is an
> OSCILLATORY-CANCELLATION / minor-arc-with-phase estimate — strictly harder than the magnitude
> decorrelation below. The pointwise decorrelation (min-defect) is real but ALSO not uniform in J
> (min-defect ~ 1/J, `/tmp/bridge_uniform_J.py`), so even pointwise it degrades. **Net: the clean
> "Riesz-product magnitude decorrelation" lemma is NOT the bridge; the bridge needs the harder signed/
> oscillatory estimate. I flagged this to scholar/troika immediately. Keeping the magnitude analysis
> below as a (failed) intermediate, clearly marked.**

## [SUPERSEDED — magnitude form, NOT the operative lemma] (BRIDGE) = a Riesz-product decorrelation lemma

scholar's literature pass (definitive): the exact minor-arc bound (BRIDGE) needs is **NOT in the
literature** — it is a genuinely NEW harmonic-analysis estimate, not a citation gap. The Riesz
products F_b(θ) = \hat{1_{B_b}}(θ) = ∏_{j<J} (1 + e(b^j θ)), |F_b| = ∏ 2|cos(π b^j θ)|, have L¹ norm
exactly 1 (lacunary), so each is "flat in L¹" but can spike on minor arcs; no published bound controls
the simultaneous size of two/three such products off their (disjoint, for large height) major arcs.

> **(BRIDGE-RIESZ) [the named open lemma].** There is c > 0 such that, uniformly in J, for all θ
> bounded away from the major arcs (the rationals a/b^j, b∈{3,4,7}),
>   `(log|F_3(θ)·F_4(θ)·F_7(θ)|) / (J·log 2) ≤ 3 − c.`
> Equivalently: the three Riesz products are never SIMULTANEOUSLY near their peaks on minor arcs, so
> the triple product decays like 2^{(3−c)J} (vs the peak 2^{3J}). This decorrelation closes (BRIDGE)
> (the covering convolution 1_{B_3+B_4} * 1_{B_7} stays positive: main term from the major arc, minor
> arcs killed by the decay) — and would be a publishable harmonic-analysis lemma in its own right.

**VERIFIED numerically (both scholar and lift, independently):**
- scholar: at B_3+B_4's largest minor-arc peak (θ≈0.31), F_7 is also small ⟹ normalized |F_S·F_7| ≈
  0.0012; max over all minor arcs θ>0.02 = 0.003. The products are NEVER jointly large.
- lift (`/tmp/riesz2.py`): the normalized minor-arc max of (log|F_3·F_4·F_7|)/(3J·log2) is
  **0.643 (J=10) → 0.631 (J=14) → 0.590 (J=18)** — bounded below 1 AND decreasing in J. So c ≳ 0.4·3
  ≈ 1.2 empirically, and the decay is uniform. The thin covering margin (1.5–3×) corresponds to c
  being modest (the bound is tight at the boundary), so the new estimate must be SHARP, not crude.

So (BRIDGE) is now a precisely-stated, verified-true, NEW Riesz-product decorrelation inequality for
multiplicatively-independent bases. **This is the single open harmonic-analysis lemma whose proof
closes the (3,4,7)-all-k theorem** (and is the boundary instance of the general (KERNEL)). It is the
right target for the circle-method/digit-Fourier lane (troika + scholar). Proving the uniform-in-J
decorrelation of these specific Riesz products is the whole game.

## Recommendation
The team's "first finished theorem" target should be re-scoped: either (a) the STRICT-excess
(∑>1) all-k theorem (provable by density, margin grows — cassels/sumset/me have the pieces), OR
(b) (3,4,7)-all-k stated as "complete modulo (BRIDGE)", honestly flagging that (BRIDGE) at the
boundary is a circle-method-flavored open lemma, NOT closed by MW alone. Claiming (3,4,7)-all-k as
fully proved via MW would be an over-claim — the same kind we flagged in the Lean repo.

Cross-refs: theorem_347_allk.md (§A,§B rigorous; §C.3 needs this correction), lift_boundary_criticality.md
(criticality = thin margin), troika_generalization_mechanism.md (band fingerprint).
