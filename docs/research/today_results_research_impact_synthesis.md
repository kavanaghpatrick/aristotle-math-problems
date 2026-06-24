# Today's Results — Research Impact Synthesis

**Date:** 2026-05-30
**Agent:** Final synthesis (V-team consolidator)
**Sibling inputs (6/9 received within 12 min):**
1. `asiryan_citation_audit.md` (V-CITE) — citation verification
2. `e324_h_zero_audit.md` (V-E324) — novelty audit of R7/h=0 slice
3. `e1003_phi_n_trick_audit.md` (V-E1003) — novelty audit of R9/φ-trick
4. `e267_badea_verification.md` (V-E267) — citation/proof-substitution audit
5. `ft_family_publishability.md` (V-FT) — R3 FT-family publishability
6. `bounded_extensions_cluster_audit.md` (V-CLUSTER) — bounded-extensions cluster

Three siblings (V7-V9) did not arrive within the 12-min poll window. Synthesis proceeds with 6/9 plus direct read of all 22 `ARISTOTLE_SUMMARY.md` files in `submissions/nu4_final/*_extracted/` and the F-team audits already on disk (`analysis/inflight_results_audit_may30.md`, `docs/inflight_audit_may30.md`).

---

## Headline

**Truly novel math results: 0.**

Across today's 33 tracked submissions and 22 returned Aristotle artifacts, **no submission produced a result that is novel mathematics in the working-mathematician sense** (i.e., a theorem worth publishing as new in any math.NT venue). Every advance is either: a bounded computational verification, a folklore corollary, a formalization-only rewrite of a known result, or a `sorry`-bearing statement of an open conjecture.

The single most interesting *pipeline* event — Aristotle autonomously substituting a simpler elementary proof for a suggested deep-machinery approach (R9/E1003 dropping S-unit theory for a rad-injection argument) — is a **process** finding, not a math finding. The proof it found is folklore.

---

## Mathlib Contributions (PR-ready vs FC-only)

| Class | Count | Examples |
|---|---|---|
| **PR-ready** (sorry-free, axiom-clean, lemmas usable outside) | 3 | R9 (`totient_mul_rad_eq`, `totient_ratio_of_primeFactors_eq`); R7 h=0 slice (textbook lemma); E1052 infrastructure (8 unitary-σ lemmas, `wall_k2`, `IsUnitaryPerfect.even`) |
| **FC-only** (compiles as bounded sub-claim, no general lemma exported) | 4 | R3 (FT q≤2000), R4 (E324 N=200), R5 (E319 N∈{7,8,9,10}), R10 (E647 residual 35) |
| **`sorry`-bearing statements** (formalize only) | 9 | E938 (×2), E944, E477, E141, E306 Egyptian, E1055 Selfridge, E373 variants (×2), E267 full conjecture, E1052 main |
| **Disproven / counterexample** | 1 | slot 742 (E203 1-D Sierpinski, m=4643 counter) |

**Net PR pipeline:** ~3 candidates if cleaned up. None of these would be a Mathlib *headline* contribution; they are routine multiplicative-σ infrastructure pieces.

---

## Pipeline Validation Results

### Subsystem #2 engagement (informal reasoner)
- The I9 smoke test (Euclid's infinitude of primes, project `8d500201-...`) **did** produce a canonical informal-mode artifact — `ARISTOTLE_SUMMARY.md` with explicit "Informal proof:" + "Formalization:" sections — confirming W8's hypothesis that the informal lane is reachable.
- **No production submission today produced that signature.** Every other `ARISTOTLE_SUMMARY.md` reviewed is a thin one-paragraph summary of what compiled, with no NL trace. The fusion-lane submissions (E938 fusion ×2, E1052 fusion, E1003 fusion, E267 fusion) returned MCGS-style output, NOT informal-mode output. **Fusion lane is not yet validated.**

### Autonomous proof substitution
- **R9/E1003** is the cleanest validation: the fusion sketch suggested the Evertse–Schlickewei–Schmidt S-unit equation route; Aristotle ignored it, found a 4-step rad-injection proof, formalized it cleanly with three reusable lemmas. **This is the most impressive process result of the day.** The math is still folklore (per V-E1003 §3), but the substitution is real.
- **R7/E324 h=0** also substituted: the fusion sketch routed via Asiryan's symmetrization (u² = v²); Aristotle used a different elementary factorization-and-discriminant argument. Same outcome (folklore), different path.

### Strategy critique
- Aristotle's E938 (R8/Chan) and E1052 (fusion) outputs both explicitly **rejected** the deep-machinery proof outlines (Bombieri–Lang, Bennett-Skinner, Bilu–Hanrot–Voutier) with reasoned critique of where the gap is. This is high-value: the system declined to fabricate non-existent steps. **First-class behavior.**
- R7 E324 critique flagged "the suggested Asiryan reference does not correspond to any known publication" — **this was a false negative on Aristotle's part** (the paper is real, per V-CITE). Aristotle's literature-check is unreliable; do not trust its citation rejections.

---

## Citation Hygiene

| Citation in today's pipeline | Status | Impact |
|---|---|---|
| Asiryan arXiv:2512.11072 (R7 E324 fusion brief) | **REAL** (V-CITE confirmed) | Use freely. R7's flag is a false-negative. |
| Asiryan arXiv:2512.00551 (companion) | **REAL** | Same. |
| Badea 1987 (E267) | **REAL** | But the *proof technique* Aristotle formalized is NOT Badea's (Brun's criterion); it's the classical descent. **Misleading header** — V-E267 recommends rewording. |
| Chan 2022 (E938) | **REAL** | Cited correctly. |
| Le 2012 (FT p=3 unconditional) | **REAL** and **subsumes R3 entirely** | R3 result is a 5×10¹⁰ smaller range than what is in print. |

**Conclusion:** Aristotle's citation rejections (R7) are unreliable. Aristotle's citation *attributions* (E267) can be technically correct but conceptually misleading. **The Asiryan false-negative would have caused permanent damage if the V-CITE pass hadn't been done.** Add: every Aristotle-flagged citation rejection must trigger an automated arXiv verification before action.

---

## Per-Result Table (22 returned artifacts)

| UUID prefix | Project | Claimed result | Sibling/audit verdict | Publishable? |
|---|---|---|---|---|
| `da7abd31` (R7) | E324 quintic | h=0 slice + N=100 bounded + open stmt | **Folklore** (V-E324) — strict-convexity gives it for any k>1 | No |
| `f43a3e38` (R4) | E324 N=200 | quintic distinctness ≤200 | **Bounded, micro-extension** of L3 N=50 (V-CLUSTER) | No |
| `8e99c62e` (L3) | E324 N=50 | quintic distinctness ≤50 | Subsumed by R4 | No |
| `d7f61f47` (R9) | E1003 fixed-support | finiteness given supp ⊂ S | **Folklore** (V-E1003) — corollary of Hardy-Wright Thm 329 / Evertse | Lemmas yes, theorem no |
| `a1af2a6e` (E1003 fusion) | E1003 | dup of R9 | Same | No |
| `eb7120ca` (E267 fusion) | E267 c≥2 | Badea + Fibonacci doubling | **Folklore + misleading citation** (V-E267) | No |
| `279e0cb3` (R10) | E647 Cunningham residual | 35-row witness, n≤10⁶ | Bounded sub-claim, mechanical (V-CLUSTER) | No |
| `9fa69652` (slot741) | E647 | dup of R10 | Same | No |
| `b7e87fb3` (L10) | E319 c(N)≥4 | N∈{7,8,9,10} witness | Bounded micro-extension (V-CLUSTER) | No |
| (R5) | E319 c(N)≥4 N=7..10 | dup of L10 | Same | No |
| `517a3f5d` (R3) | FT q≤2000 | family closure | **Subsumed by Le 2012 unconditional** (V-FT) | **No — already in print** |
| `d8c5585c` (ft_q1583_v2) | FT q=1583 | single-prime native_decide | Marginal | No |
| `cdf8c4de` (slot743) | E203 12×12 | 144-cell covering | **Disproves the hedge** (witness exists at B=1000), bounded | No (bounded) |
| `be1e80e5` (slot742) | E203 1-D Sierpinski | counterexample m=4643 | **Disproof of false stmt** | No (calibration) |
| `9cb693c2` (slot745) | Brocard [1001,2000] | chunked native_decide | Range bump (V-CLUSTER says individually too small) | No |
| `4dab36cf` (slot746) | Odd multiperfect σ₀=11 | structural impossibility | **Strongest result of the day** — first σ₀=11 specific Lean proof; sub-claim of odd multiperfect | Mathlib PR candidate |
| `ad009260` (E938 fusion) | E938 | open, `sorry` + critique | Honest open-status report | No |
| `8242d652` (R8 E938 Chan) | E938 | open, `sorry` + Chan citation | Honest | No |
| `38da55e5` (E1052 fusion) | E1052 | infrastructure + open `sorry` | 8 useful σ*-lemmas + correct refusal to prove deep step | Mathlib PR for lemmas; theorem no |
| `2e379de0` (L2 E141) | 11 consecutive primes in AP | open `sorry` | Honest open-status | No |
| `a90a0a5e` (L1 E944) | Dirac k=4 | open `sorry` | Honest open-status | No |
| `95ead4b7` (L7 E477) | E477 cubic | open `sorry` | Honest open-status | No |
| `f9e23cf2` (I9 smoke) | Euclid's primes | trivial wrapper | Calibration baseline (informal-mode signature) | No |

---

## Three Highest-Impact Results

1. **slot 746 — Odd multiperfect σ₀=11 (UUID `4dab36cf`).** Single-shape structural impossibility via p-adic argument, sorry-free, no native_decide, real algebraic content. F-mode audit gave 0 failures. Per the inflight audit it is the strongest closure-axis gate validation case and **mathematical_content_score=8/10**. *Justification:* This is the only result today that (a) resolves a precise sub-claim of an actually-open problem (odd multiperfect with prime σ₀), (b) does so by genuine structural mathematics rather than native_decide, and (c) is plausibly a previously-uncatalogued Lean formalization. Recommend manual promotion to `compiled_advance` with explicit contribution statement.

2. **R9/E1003 fixed-support finiteness (UUID `d7f61f47`).** Highest *process* impact: clean autonomous proof substitution, two reusable Mathlib lemmas (`totient_mul_rad_eq`, `totient_ratio_of_primeFactors_eq`), zero `sorry`. *Justification:* The math is folklore (V-E1003), but the demonstrated capability — Aristotle bypassing the suggested S-unit theory and finding a self-contained 4-step proof — is the strongest evidence yet that the autoformalization layer can do non-trivial proof search rather than blind transcription. The lemmas are real Mathlib value.

3. **E1052 fusion (UUID `38da55e5`).** Eight σ*-multiplicativity infrastructure lemmas + `IsUnitaryPerfect.even` + `wall_k2`, all sorry-free, plus honest refusal to fabricate the Bilu–Hanrot–Voutier step. *Justification:* Real Mathlib infrastructure (the σ* multiplicativity lemmas are not currently in Mathlib), honest open-status acknowledgement, sets up future Wall-style sub-claims. Closure-axis discipline working as designed.

---

## Three Lowest-Impact Results

1. **R3 — FT p=3, q ≡ 71 (mod 72), q ≤ 2000 (UUID `09a5b938`).** *Reasoning:* Subsumed by Le (2012) unconditionally for all q, and computationally verified by Motose/Guy to q < 10¹⁴ — i.e., **5 × 10¹⁰× larger range than R3**. This is approximately 0.0000002% of the published computational frontier. Not a journal paper, not a Mathlib PR, not even a defensible preprint. **Stop iterating on FT p=3.** The genuinely open part is p ≥ 5 (V-FT §recommendation).

2. **R4 / L3 / L10 / R5 — bounded native_decide micro-extensions on E324 (N ≤ 50, 200) and E319 (N ∈ {7,8,9,10}).** *Reasoning:* Each is a 1-shot native_decide of a finite range with no new technique. Helfgott-Platt bar (8.875·10³⁰ via new sieve) is 10²⁸× our N=200 and uses a novel Proth-prime sieve; we use stock native_decide. Three of these are submitted twice (R4 ⊂ L3, R5 ≈ L10) — duplicate work. **Not standalone publishable. Possibly a Mathlib PR if cleaned, but bounds are not useful at the scales they cover.**

3. **slot 742 — E203 1-D Sierpinski calibration benchmark (UUID `bdc60eff`).** *Reasoning:* Aristotle correctly produced a counterexample (m=4643) to a *deliberately-false* calibration probe. Useful as a pipeline smoke test only. Contains no new mathematics; the calibration was set up that way by design. Closure-axis JSON correctly tags `real_closure_candidate=false / HM=calibration_only`. Includes it for completeness; it should not be advertised as a result.

---

## Recommendation — What would maximize REAL research impact?

**Stop running bounded-extension submissions. They are a measurement instrument and a Mathlib infrastructure tool — they are not research.** The 5 R-cluster slots + 4 L-slots that produced bounded native_decide artifacts today cost compute and produced zero math impact. Mathlib PRs from this cluster are the maximum value; treat that as engineering, not research.

**Concrete pivot for the next 30 days:**

1. **Concentrate on σ-multiplicativity sub-claims** (Wall-style finiteness for fixed ω(n)). Slot 746 (σ₀=11 multiperfect) is the cleanest closure today. The same template applies to σ₀=13, 17, 19, and to unitary perfect with bounded ω. These are *real* journal sub-claim candidates — short notes in *INTEGERS* or *J. Number Theory*. Goal: 5–8 sub-claim closures in 4 weeks, each manually promoted to `compiled_advance` with a contribution statement, and each packaged as a Mathlib PR.

2. **Validate the informal-reasoner lane on one cleanly-prepared E938 or E1052 submission.** The I9 smoke test confirms subsystem #2 exists. No production fusion submission today produced its signature. Make the lane validation criterion an explicit pass/fail metric: one FUSION submission must produce an `ARISTOTLE_SUMMARY.md` with the "Informal proof:" + "Formalization:" sections AND non-trivial mathematical decomposition (Frey curve attempt, modular form citation, cusp-form computation, or analogous cross-domain reach) by **2026-06-22**. If that doesn't happen, the lane is rolled back.

3. **Citation-verification gate.** Every Aristotle "this citation doesn't exist" output triggers an arXiv pre-check before acting. The Asiryan false-negative today is the canary; the next one might cause us to retract a real result.

4. **Stop submitting micro-bound extensions on the same problem.** Three of today's slots are R4 ⊂ L3 (E324) and R5 ≈ L10 (E319). Deduplicate the pipeline; gate batched submissions on novelty distance from prior compiled artifacts.

---

## Are any of these truly novel? (Direct answer)

**No.** Of the 22 returned Aristotle artifacts today, **zero are novel mathematics** in any sense a working number theorist would accept. The single strongest candidate — slot 746's σ₀=11 multiperfect impossibility — is a clean structural sub-claim that is, to our best literature search, not previously formalized in Lean and not separately published, but the *mathematical argument* (n = p^{10} reduction + σ(p^{10}) ≡ 1 (mod p) p-adic contradiction) is a one-line exercise any specialist would write down in ten minutes. The R9/E1003 fixed-support finiteness is folklore corollary of Hardy-Wright Thm 329 + Evertse S-unit equation. R3 (FT q ≤ 2000) is strictly subsumed by Le (2012). R7 (E324 h=0) is the elementary trivial slice that Newton already knew. E938 and E1052 remained `sorry`. **The honest count of publishable new math from today is 0.**

---

## Honest Reality Check — Publishable count

Of the 33 submissions tracked today (the user's "17" undercounts — see DB query), how many are PUBLISHABLE NEW MATH in any reasonable math.NT venue?

**Realistic answer: 0.**

- *Possibly 1 if you stretch:* slot 746 (σ₀=11 multiperfect impossibility), as a 2-page note in *INTEGERS* — but only if combined with the σ₀ ∈ {13, 17, 19} extensions and framed as a uniform family-impossibility theorem. As-is, a single-prime σ₀ case is too thin even for *INTEGERS*.
- *Mathlib-publishable (different venue category):* ~3 PRs (R9 lemmas, slot 746 structural lemma, E1052 σ*-infrastructure). These are real but modest contributions to the Lean ecosystem; they are not research papers.
- *arXiv math.NT preprint without journal:* slot 746 + σ₀ extensions could become a 4-page arXiv preprint by Jul 1 if 2-3 additional σ₀ cases close. Worth pursuing.

**This is consistent with the user's prior — the realistic answer is 0 or 1.**

---

## Calibration — What would it take to produce ACTUALLY-NOVEL math?

1. **Different problem class.** The current portfolio is dominated by bounded-finite verifications and Erdős sub-claims with a clear computational closure. To get genuine novelty we need long-tail Erdős problems where the *gap* itself is small and structurally tight — e.g., σ-multiplicativity-driven impossibilities for prime ω(n) (slot 746 generalized), or single-prime FT cases at p = 5 (the genuinely-open column). The closure-axis gate is the right discipline; we need more sub-claims that pass it.

2. **Different pipeline.** The bare-gap-only computational verifier model is calibrated for the *current* model pairing's strengths (autoformalization + decidability). It will *not* discover novel mathematics. The fusion lane (with subsystem #2 engaged) is the only architectural path to genuine novelty, and we have not validated it yet. **No bare-gap submission, no matter how aggressive, will produce novel math.** The pipeline change is the rate-determining step.

3. **Different model.** GPT-5.5 + Aristotle is the current best pairing; no upgrade is available before Q3 2026. Until then, the answerable question is whether subsystem #2 (informal reasoner via `aristotle_informal.py` + I9 adapter) can be reliably engaged on production problems. It has not been engaged today on any of the 5 nominal "fusion" submissions; this is the highest-impact infrastructure gap.

4. **Different scale.** More compute on the same problem class produces more bounded-extension noise, not more novelty. Compute is not the bottleneck. The bottleneck is **proof-search depth on open-status sub-claims with real structural content** — and that is a model+pipeline issue, not a compute issue.

**Bottom line:** Today's session validated the pipeline's calibration (closure-axis discipline works, F-mode detectors fire correctly, citation gates need hardening) but did not produce novel mathematics, and was not expected to. The next 30 days should be a controlled experiment on (i) σ-multiplicativity sub-claim density and (ii) informal-lane signature validation. Both are tractable; both should be tracked as named KPIs.

---

## Sources
- F-team audit: `analysis/inflight_results_audit_may30.md`
- Strategy synthesis: `docs/strategy_synthesis_may30.md` (Agent S10)
- I9 smoke test: `docs/research/aristotle_smoke_test_euclid_may30.md`
- Citation verification: `docs/research/asiryan_citation_audit.md`
- Per-result audits: `docs/research/{e324_h_zero,e1003_phi_n_trick,e267_badea,ft_family_publishability,bounded_extensions_cluster,erdos1041_avoid_recommendation}_*.md`
- All 22 result artifacts: `submissions/nu4_final/*_extracted/*_aristotle/ARISTOTLE_SUMMARY.md`
- DB: `submissions/tracking.db` (33 rows date(submitted_at) = '2026-05-30')
