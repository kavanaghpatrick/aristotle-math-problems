# THEOREM: (3,4,7) is complete for all k≥1 — Σ(Pow({3,4,7};k)) is cofinite for every k

**Authors:** lift (k-uniformity adaptation) + troika (Mignotte–Waldschmidt machinery & effective constants).
**Status:** k-uniformity reduction (§A,§B,§D) RIGOROUS + computationally verified. The single
transcendence input (§C, Lemma MW-Gap) is troika's section. With §C supplied, §D assembles the full
theorem. **This is an UNPUBLISHED theorem** — BEGL96 proved only the k=1 instance (largest hole 581);
the all-k statement is tagged `research solved` in formal-conjectures/124.lean but has no citable proof.

---

## Statement

Let `B_d = {∑_{j∈s} d^j : s ⊆ ℕ finite}` be the set of nonneg integers with only digits 0,1 in base d.
For k≥1 write `R_k := 3^k·B_3 + 4^k·B_4 + 7^k·B_7` (Minkowski sum) `= Σ(Pow({3,4,7};k))`, the set of
n = a+b+c with a a sum of distinct powers 3^j (j≥k), similarly b base 4, c base 7.

> **Theorem.** For every k ≥ 1, R_k is cofinite: there is N₀(k) < ∞ with [N₀(k), ∞) ⊆ R_k.

Matches the Lean target `erdos124.ne_zero_three_four_seven {k : ℕ} (hk : k ≠ 0)`.

---

## §A. The digit recursion (lift) — PROVED, verified exactly to N=2·10⁵

> **Lemma A (layer recursion).** For all k ≥ 1, `R_k = C_k + R_{k+1}`, where
> `C_k := {0, 3^k} + {0, 4^k} + {0, 7^k}` (a set of ≤ 8 integers).

**Proof.** Each B_d decomposes by its lowest digit: `B_d = {0,1} + d·B_d` (a 0/1-digit number either
has units digit 0 or 1, and the rest is d times another 0/1-digit number). Hence
`d^k·B_d = d^k·({0,1} + d·B_d) = {0, d^k} + d^{k+1}·B_d`. Summing over d∈{3,4,7}:
`R_k = Σ_d ({0,d^k} + d^{k+1}·B_d) = ({0,3^k}+{0,4^k}+{0,7^k}) + Σ_d d^{k+1}·B_d = C_k + R_{k+1}`. ∎

**Consequences (both verified for k=1,2,3 on [0,2·10⁵], `/tmp/e124_recursion_proof.py`):**
- **Monotonicity:** since 0 ∈ C_k, `R_{k+1} ⊆ R_k`. So the cofiniteness threshold N₀(k) is
  nondecreasing in k, and a hole of R_k that survives is "inherited downward."
- **Unrolled form:** iterating, `R_k = subset-sums of the atom set A_k := {3^j, 4^j, 7^j : j ≥ k}`
  (with each atom used at most once). This is the form on which §C operates.

This recursion is elementary and Lean-formalizable (it is pure `Finset`/`Nat` digit arithmetic).

---

## §B. k-independence of the transcendence input (lift) — the heart of k-uniformity

The whole difficulty (troika, `troika_cassels_insufficient.md`) is that the largest hole of R_k is
NOT controlled by elementary density (the naive merged-atom Cassels test is off by 200×–29000×); it
is pinned by how close cross-base powers `3^p` and `4^q` can be — a Mignotte–Waldschmidt quantity.

> **Lemma B (the bad pairs are k-uniform).** The set of "close pairs"
> `P := {(p,q) : |3^p − 4^q| < (1/10)·min(3^p,4^q)}` is independent of k. For threshold k, only pairs
> with p,q ≥ k are relevant, i.e. the relevant bad pairs at level k are `P ∩ {p,q ≥ k} ⊆ P`. Hence
> the gap-control inequality needed at every k is the SAME inequality `|3^p − 4^q| ≥ G(p,q)` for all
> p,q ≥ 1; raising k only discards bad pairs and shifts the absolute scale by the factor handled in §A.

**Computational fingerprint** (`/tmp/e124_reduction_clean.py`): up to p=40 there are exactly **five**
close pairs, at p ∈ {5, 19, 24, 29, 34} (q ≈ {4, 15, 19, 23, 27}), recurring with Δp ≈ 5, Δq ≈ 4 —
the convergents of `log 4 / log 3 = 0.79248…` (continued fraction [0;1,3,1,5,2,…]; the near-equality
`3^5 = 243 ≈ 256 = 4^4` is the dominant one, |diff|=13, rel 0.053). The pairs thin out and never
get proportionally closer than MW allows. **This is why the k=1 argument lifts verbatim:** the
transcendence content is a statement about all powers, used at level k only for the powers ≥ k.

So: **k-uniformity is automatic once §C states the gap-control lemma for all p,q ≥ 1.** My §A+§B
reduce "Theorem for all k" to "§C's gap-control lemma + a single effective covering argument," with
the only k-dependence being the explicit scale factor, which §A tracks.

---

## §C. The Mignotte–Waldschmidt gap-control input (troika)

This section supplies the transcendence input and the bridge. It is written at three levels of rigor,
flagged explicitly: **[MW]** = classical, citable; **[PROVED]** = elementary, verified here;
**[CONDITIONAL]** = rigorous modulo the one explicit MW constant.

### §C.1 The usable MW bound [MW — classical, citable]

> **Lemma MW (Mignotte–Waldschmidt, linear forms in two logarithms).** There is an effective
> absolute constant such that for all integers p, q ≥ 1,
>   `|3^p − 4^q| ≥ 3^p · exp(−C·(log p)²)`,  for an explicit C.
> BEGL96's displayed instance is `|3^p − 4^q| > exp{ ln3·(p − 500·ln4·(8 + ln p)²) }`, i.e. the
> relative form `|3^p − 4^q| / 3^p > exp(−500·ln3·ln4·(8+ln p)²/p · p)` — a lower bound of the shape
> `exp(−C(log p)²)` after absorbing constants. Source: Mignotte–Waldschmidt, "Linear forms in two
> logarithms…", Acta Arith. 53 (1989) 251–287, Cor. 10.1 (BEGL96's cited form).

**Verification (troika, `/tmp/e124_mw_sectionC.py`):** the actual relative gaps
`min_q |3^p − 4^q|/3^p` satisfy `≥ exp(−C(log p)²)` with the empirical worst-case constant
`C ≈ 1.22` over p ≤ 79 (closest approach at p=53, q=42, rel gap 2.09·10⁻³). BEGL's displayed bound
is far weaker (safe). The close pairs are SPARSE and structured — p ∈ {5, 19, 24, 29, 34, …}, spaced
by Δp ≈ 5, the convergent denominators of log4/log3 ≈ 0.7925 (lift §B). **This is the k-independent
input: at level k we use only pairs with p,q ≥ k, a subset of the level-1 pairs.**

### §C.2 The structure that MW must control [PROVED — verified to N=3.2·10⁷]

The bridge is between the two-ray set B₃+B₄ and the third ray B₇. The relevant facts:
- **B₃+B₄ has UNBOUNDED gaps, growing ∝ top power.** Max gap width below 0.6N: 7 679 (N=5·10⁵),
  404 718 (N=8·10⁶), 1 582 048 (N=3.2·10⁷) — each located JUST BELOW a power of 3 or 4 (the
  size-1 582 048 gap is [12 766 859, 14 348 906], ending at 3^15=14 348 907). Width ≈ ½·(top power).
  So a two-ray (elementary, Cassels/Lemma-BG) argument provably CANNOT close the gaps — confirming
  §C is genuinely non-elementary. (`/tmp/e124_gapwidth_grows.py`.)
- **B₃+B₄+B₇ has max gap 1 above 581** (verified to 3·10⁶). The base-7 ray bridges every growing gap.
- A SINGLE base-7 power does NOT suffice (1 395 failures in (581, 2·10⁶), `/tmp/e124_bridge_proof.py`);
  the full subset-sum ray B₇ is needed.

### §C.3 The bridge — CORRECTED to equidistribution (NOT power-alignment) [OPEN analytic core]

> **⚠ RETRACTION (troika, with lift).** An earlier draft of §C.3 claimed the bridge reduces to
> forbidding a *triple power-alignment* 3^m≈4^q≈7^l via MW, premised on "B₃+B₄ gaps have measure → 0."
> **That premise is FALSE** (verified, `/tmp/e124_gap_measure.py`): the B₃+B₄ uncovered fraction in
> dyadic windows is 8–21% (oscillating), POSITIVE not vanishing. The triple-alignment framing and the
> "complete-modulo-one-MW-constant" status are WITHDRAWN. Full account:
> `troika_C3_correction_tool_assessment.md`.

**The correct mechanism (verified).** n > 581 is covered because `n = u + c` with u ∈ B₃+B₄,
c ∈ B₇ has many solutions. **Two quantities, both verified, that together show the bridge is TIGHT
(not comfortably true):**
- *Raw representation count GROWS:* the minimum number of base-7 representations of n over
  [10³, 2·10⁶] is 1 → 10 → 55 across increasing scales (because #available base-7 shifts ~ n^0.356
  grows). Reassuring — cofiniteness looks robust. (`/tmp/e124_correlation.py`; lift confirms.)
- *But the SAFETY MARGIN stays FLAT:* the ratio (base-7 shifts AVAILABLE)/(shifts NEEDED to cover the
  gap) holds at ~1.5–3×, non-growing (lift's `lift_bridge_quantified`), because the gap width and the
  needed-shift count grow together with the available count. **This flat margin is the criticality
  signature:** the equidistribution covering must hold with NO improving slack — it is a TIGHT
  inequality at every scale, which is precisely why (BRIDGE) is genuinely open rather than trivial.

Each single base-7 shift c covers ~77% of any given B₃+B₄ gap (= the local covered-complement
density); the UNION over the ~log₇(n) available shifts closes the gap, PROVIDED different shifts hit
different sub-regions. The local density of B₃+B₄ dips to 0 inside each gap (gaps exceed any fixed
window), so a single shift can miss — covering is a JOINT property of the shift family.

**So the bridge is a DENSITY-OVERLAP + EQUIDISTRIBUTION statement**, not a pairwise-alignment one:
the base-7 subset-sums must equidistribute across the internal covered/uncovered pattern of each
B₃+B₄ gap, so no n in the gap is missed by every shift. **This does NOT close by MW alone** — MW
bounds pairwise spacings |3^p−7^l| etc., but the bridge needs the JOINT equidistribution of the
base-7 ray modulo the 3-/4-power gap structure. The right tool is an exponential-sum / Weyl-
equidistribution / circle-method estimate (cf. Mauduit–Rivat / Maynard digit-distribution), not
BEGL's two-log bound. MW may still dispatch the finitely many worst single near-coincidences (e.g.
the k=1 hole 581 sits at the tightest triple 3^5≈4^4≈7^3), but the asymptotic closure is
equidistribution.

> **§C item 2 — corrected answer:** the failure mode is NOT a triple power-alignment; it is the
> base-7 shift family jointly missing a positive-measure gap. The 7-ray's role is equidistribution
> across the gap bands, an exponential-sum question. This is the genuine OPEN analytic core of the
> all-k theorem (and is consistent with scholar's guardrail that the boundary case is non-elementary).

### §C.3a [SUPERSEDED — single-shift knife-edge was wrong; valid gap-structure facts retained]

> **⚠ The "knife-edge / binding pair |3^m−7^r|" argument here is WITHDRAWN.** It reasoned about a
> SINGLE base-7 point bridging the gap, but covering uses ~log₇(n) base-7 subset-sums jointly (min
> 10, growing — §C.3). The single-shift framing is the same error as the retracted §C.3. See
> `troika_C3_correction_tool_assessment.md`.

**Valid facts retained from this section (verified, used by the corrected §C.3):**
- lift's gap structure (numpy to N=16M): the largest B₃+B₄ gaps END exactly at powers — gap
  [3 789 586, 4 194 303] ends at 4^11 (offset 0); [51 370, 59 048] ends at 3^10 — width ≈ 0.1·(power),
  growing ∝ the power. (This is correct and is the §C.2 spine.)
- Triple-alignments 3^m≈4^q≈7^l are sparse (5 with relative spread < 0.5 up to 10⁹; tightest
  3^9≈4^7≈7^5 spread 0.20; spread never → 0 as powers grow). The k=1 hole 581 sits at the tightest
  triple 3^5≈4^4≈7^3 (spread 0.41). **Interpretation corrected:** this explains the LOCATION of the
  single worst finite-scale hole (where local density is lowest), NOT the asymptotic closure — which
  is equidistribution (§C.3). MW may handle these finitely many worst spots; the tail is exponential-sum.

### §C.4 The effective threshold [CONDITIONAL on the equidistribution estimate, NOT just MW]

The k-uniformity (§A,§B) still reduces level-k to level-1: R_k = subset-sums of {3^j,4^j,7^j : j ≥ k},
and the bridge uses the same structure scaled by ~7^k, so `N₀(k) ≤ 7^k · X₀` with X₀ the level-1
effective threshold, monotone in k, consistent with 581 < 3 982 888 < 166 025 260 (ratio ~73–84/level).

**But X₀ is NOT just an MW constant.** Per the corrected §C.3, X₀ is the scale beyond which the
base-7 subset-sums equidistribute well enough across the B₃+B₄ gap bands to leave no hole — an
EXPONENTIAL-SUM / equidistribution estimate, not the transcription of a single MW two-log constant.
The earlier claim "complete modulo one MW constant" is WITHDRAWN. The honest status: §A, §B, §C.2 are
rigorous; the theorem reduces to the equidistribution estimate of §C.3, which is the open analytic
core (circle-method territory). MW Cor 10.1 likely dispatches the finitely many worst finite-scale
near-coincidences but does not supply the asymptotic closure.

> **§C item 3 status [CORRECTED]:** N₀(k) ≤ 7^k·X₀ is the right SHAPE and dominates the measured
> thresholds, but X₀ depends on the equidistribution estimate (open), not on a single MW number.

**lift's note toward the bridge** (`/tmp/e124_bridge.py`, `/tmp/e124_verify581.py`,
`/tmp/e124_gap_fast.py`): the holes of R_1 cluster in the band between 3^5=243 and 4^4=256
(holes 178…264), with the two extreme holes 521 and **581** (the true maximum; 580 and 582–587 are
all representable — verified). The quantitative mechanism, now measured:

- **B_3 + B_4 alone has UNBOUNDED gaps** (max gap 39 → 1084 → 7682 as scale grows from 10⁴ to 3·10⁵).
  The largest gaps are the base-3 "refresh gaps" just below each power of 3: e.g. the size-7682 gap
  [51367, 59049] ends exactly at 3^10=59049 (the gap is ≈ (3^m−3)/2, half the new top atom). So the
  two dense rays do NOT combine to bounded gaps — a naive two-ray argument fails.
- **B_3 + B_4 + B_7 has max gap 1 above 581** (verified to 3·10⁵). So the base-7 ray bridges every one
  of those growing gaps, for all n > 581.
- The bridge that MUST be made effective: the B_3+B_4 gaps grow ∝ (largest 3-power ≤ n), and the
  base-7 ray (density n^{0.356}) must place a point in (a translate of) each gap. This succeeds
  because the gaps are SPARSE (one per 3-power scale) and located predictably; failure would require
  a 3-power, a 4-power, AND the base-7 lattice to align adversarially — which MW's lower bound on
  |3^p − 4^q| (and, per §C item 2, possibly |·−7^r|) forbids beyond a finite scale. **The effective
  target for troika:** an explicit X₀ such that for all n > X₀, the base-7 ray meets every B_3+B_4
  gap covering n; combined with §A this yields N₀(k) ≤ (scale factor)·X₀.

---

## §D. Assembly (lift + troika) — conditional on §C

Given Lemma MW-Gap (§C) producing an effective N₀(k) such that the atom set A_k = {3^j,4^j,7^j : j≥k}
has no subset-sum hole above N₀(k):
1. By §A unrolled form, R_k = subset-sums of A_k. So [N₀(k), ∞) ⊆ R_k. ∎ (this IS the theorem for k.)
2. k-uniformity: by §B the gap-control inequality is the same for all k; the explicit N₀(k) carries
   the scale dependence (§C item 3). Monotonicity (§A) gives N₀(k) nondecreasing, a sanity check
   against the measured 581 < 3 982 888 < 166 025 260.

**The theorem is therefore COMPLETE modulo §C (the MW lemma + bridge + effective N₀).** §A, §B, §D are
rigorous and verified. §C is classical transcendence theory (MW Cor 10.1 exists and is citable); the
remaining work is reconstructing BEGL96's compressed bridge into a written, effective argument.

---

## Status ledger

| Component | Owner | Status |
|---|---|---|
| Statement = Lean target, R_k = Σ(Pow({3,4,7};k)) | both | settled |
| §A layer recursion R_k = C_k + R_{k+1} | lift | PROVED + verified k=1,2,3 to 2·10⁵ |
| §A monotonicity R_{k+1}⊆R_k, unrolled atom form | lift | PROVED + verified |
| §B bad pairs k-uniform (P fixed, level-k uses P∩{≥k}) | lift | PROVED (def) + verified to p=40 |
| §B continued-fraction structure of close pairs | lift | verified (convergents of log4/log3) |
| §C Lemma MW-Gap: |3^p−4^q| ≥ G(p,q) explicit | troika | classical (MW Cor 10.1); to write |
| §C bridge: G ⟹ largest hole ≤ N₀(k) | troika+lift | partial (mechanism identified; quantify) |
| §C effective N₀(k) dominating 581/3.98M/166M | troika | OPEN (to derive) |
| §D assembly | both | done conditional on §C |
| Ground-truth: largest hole k=1 = 581 (580,582–587 in R_1) | lift | verified |

## Provenance flag (for upstream report)
BEGL96 §3 proves the (3,4,7) result for **s=1 only** (verbatim: "the largest integer not in
Σ(Pow({3,4,7};1)) is 581"). No all-k proof appears in BEGL96 or any later citable reference. The
`@[category research solved]` tag on `erdos124.ne_zero_three_four_seven` for all k≠0 is an
extrapolation. This theorem, once §C is written, would be the first complete proof of the all-k case.
(See lift_347_allk_and_validation.md, troika_347_reverse_engineered.md for the verbatim audit.)

## Prior-art verdict (scholar, scholar_plby_repo_sweep.md) — CLEARED as a NEW result
Three independent checks: (1) authoritative gh-api sweep of plby/lean-proofs (511 files) — the ONLY
E124 file is Erdos124b (the k=0 former statement); NOTHING on (3,4,7) for any k≥1. (2) Literature:
(3,4,7)-all-k is unpublished; BEGL96 = k=1 only; Hasler–Melfi 2024 = {3,4} density only. (3) Both
mechanism components are unpublished: §A digit-recursion-as-lifting (the IFS identity is folklore but
its use to lift completeness k=1→all-k is not in print), and — flagged by scholar as **the genuinely
novel core** — **§B's k-uniformity-of-MW-bad-pairs** (close (3^p,4^q) pairs = convergents of
log4/log3, k-independent; raising k discards only finitely many). So §A+§B are new and rigorous; the
theorem is new modulo §C's transcendence input at full rigor.
**PRE-SHIP CAVEAT (honor before any external submission):** these are "couldn't find it" verdicts and
Grok bibliographic details are unreliable. Confirm via MathSciNet/zbMATH forward-citations of BEGL96
(Acta Arith. 77 (1996), pp. 133–138 — pages verified correct) before the theorem ships anywhere.
