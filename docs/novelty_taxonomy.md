# Novelty Taxonomy — Operational Bright Lines

**Author:** Agent #8 of 10
**Date:** 2026-05-30
**Mission:** Operationally define "truly novel" so a `compiled_advance` row can be honestly tagged as journal-quality math vs. folklore / formalization / bounded-extension / sub-claim work.
**Inputs:** `closure_taxonomy_may30.md` (HM axis), `today_results_research_impact_synthesis.md` (V-team verdict: 0/22 today qualify), `PILOT_ERDOS850.md` (em-tautology root cause), per-result audits (`e1003_phi_n_trick_audit.md`, `e324_h_zero_audit.md`, `bounded_extensions_cluster_audit.md`, `ft_family_publishability.md`).
**Authority:** Refines Axis 4 of `closure_taxonomy_may30.md`. Splits its single `journal_clean` value into `journal_clean_novel` + `journal_clean_extension` and adds `solved_elsewhere`. All other axes unchanged.

---

## 1. Operational definition of "truly novel"

A submission is **truly novel** iff it satisfies **all five** of the following bright lines. Any single failure downgrades the HM. No discretion; each line is mechanical.

| # | Bright line | Failure mode it blocks | Mechanical check |
|---|---|---|---|
| **N1** | **No subsumption.** The claim, after unfolding `def`s, is not implied by any published theorem in zbMATH / MathSciNet / arXiv math.NT 2000–2026 found by a 30-minute literature scan. Subsumption includes: weaker hypotheses give a stronger conclusion; bounded version is dominated by a known computational frontier (e.g., Helfgott–Platt, Motose–Guy, Mehta table). | "R3 FT q≤2000" subsumed by Le 2012 unconditional; "R4 E324 N=200" subsumed by Motose–Guy q<10¹⁴ frontier. | Literature search log attached to certificate; specific citation that would subsume must be enumerated and ruled out. |
| **N2** | **Not derivable in < 1 page by a competent specialist.** A working number theorist / combinatorialist in the problem's subfield, given the open-conjecture statement, cannot write down the proof in under one page using standard techniques (Newton's identities, strict convexity, Euler's φ formula, S-unit equation, Hardy–Wright Thm 327/329, native_decide). | "R7 E324 h=0" derivable in 2 lines from strict convexity for any k>1; "R9 E1003 fixed-support" is a corollary of Hardy–Wright Thm 329 + Evertse. | Reviewer specialist sketches a < 1-page proof using only stated standard tools; if successful, FAIL N2. |
| **N3** | **Resolves a stated open conjecture, disproves it, or proves a non-trivial new bound.** A "non-trivial new bound" must improve the published state-of-the-art by a factor that a referee at *Acta Arithmetica* / *Combinatorica* / *INTEGERS* would describe as a "meaningful extension" (typically ≥ 2× or a new asymptotic regime), not a constant-factor or fixed-N micro-extension. | "Brocard [1001,2000]" extends a verified range by < 2× and stays bounded; "E319 c(N)≥4 for N∈{7..10}" is a fixed-N enumeration with no new technique. | Compare to published bound; require ≥ 2× improvement OR a new asymptotic regime OR closing/disproving the open statement itself. |
| **N4** | **Uses a technique or insight not previously applied to this problem.** The proof must introduce either a new method or a new application of an existing method to this specific problem. Re-running `native_decide` on a larger range is not a new application. Re-formalizing a published proof in Lean is not a new application. | Today's R-cluster bounded extensions all reuse the same `native_decide` template; R7's discriminant argument is one of four standard h=0 routes. | Method must be either (a) novel in the literature, or (b) novel for this conjecture (i.e., no prior paper attacked this conjecture via this method). |
| **N5** | **Journal-acceptable in some form.** The result, with the actual proof Aristotle produced (not a hypothetical stronger version), would be reviewed favorably at *INTEGERS*, *J. Number Theory*, *Acta Arith.*, *Combinatorica*, or a comparable venue, as a stand-alone note or main result. "Could be packaged into a longer paper if 5 more cases worked" does not count. | Slot 746 (σ₀=11 multiperfect impossibility) alone is too thin for *INTEGERS*; would need σ₀∈{13,17,19} family to be journal-acceptable. | Specific named venue + length-class (note / short paper / full paper) declared on the certificate. |

A submission with N1∧N2∧N3∧N4∧N5 = TRUE receives **HM = `journal_clean_novel`** and is the only HM value that may be celebrated as resolving new mathematics.

---

## 2. Refined HM values

Replaces the single `journal_clean` of `closure_taxonomy_may30.md` Axis 4. All other values unchanged in spirit; renumbered:

| HM | Definition | All N-criteria? | Example |
|---|---|---|---|
| `journal_clean_novel` | All five N-criteria hold. Genuinely new mathematics. | N1∧N2∧N3∧N4∧N5 | (Hypothetical) "Min-degree-3 graph on >17 vertices with no 2⁴-cycle, disproving Dirac k=4" |
| `journal_clean_extension` | Improves the published state-of-the-art by a factor ≥ 2× or in a new asymptotic regime; not full closure. N2/N3/N4/N5 hold; N1 holds against tighter bound only. | partial (N1 weakened) | (Hypothetical) Brocard verified to n ≤ 10¹⁰ with a structurally new sieve (not stock `native_decide`) |
| `journal_partial` | Bounded version is publishable as a research note ("verified for n ≤ N"), but does NOT close the open question, and uses standard techniques. N2/N3 fail; N4 may or may not. | no | slot 720 (FT q≤1000), slot 745 (Brocard [1001,2000]) |
| `journal_subclaim` | A strict sub-statement of the open conjecture is closed by genuine structural mathematics; the sub-statement is named in the literature OR is a natural midpoint a journal would accept. | partial (N5 holds for the sub-claim only) | slot 746 (σ₀=11 multiperfect impossibility), if framed as a sub-claim |
| `infrastructure_only` | Mathlib value (named lemmas, decidability instances, residue-class enumerations). Not publishable as research math. | no | R9 lemmas (`totient_mul_rad_eq`), E1052 σ*-multiplicativity infrastructure |
| `solved_elsewhere` | The claim is strictly subsumed by a published result; this submission is duplicate work. N1 fails. | no (N1 fail) | R3 (FT q≤2000) subsumed by Le 2012; R7 (E324 h=0) subsumed by Newton 1666 + Asiryan 2026 |
| `calibration_only` | Deliberately-constructed false probe / smoke test / informal-mode signature check. Not research math by design. | no | slot 742 (1-D Sierpinski counterexample), I9 Euclid smoke test |

The pre-refactor `journal_clean` is now **disallowed** as a tag. Any submission previously tagged `journal_clean` must be re-tagged to one of the seven values above.

---

## 3. Retroactive application to today (2026-05-30)

From `today_results_research_impact_synthesis.md` per-result table (22 returned Aristotle artifacts):

| Slot / UUID | Old HM (closure_taxonomy) | New HM | N1 | N2 | N3 | N4 | N5 |
|---|---|---|---|---|---|---|---|
| `da7abd31` R7 E324 h=0 | `infrastructure_only` | `solved_elsewhere` | FAIL (Newton 1666; Asiryan 2026) | FAIL (2-line strict-convexity) | FAIL | FAIL | FAIL |
| `f43a3e38` R4 E324 N=200 | `journal_partial` | `journal_partial` | FAIL (Motose–Guy ranges) | FAIL | FAIL (< 2× extension) | FAIL | FAIL |
| `8e99c62e` L3 E324 N=50 | `journal_partial` | `journal_partial` (dup of R4) | FAIL | FAIL | FAIL | FAIL | FAIL |
| `d7f61f47` R9 E1003 φ trick | `infrastructure_only` | `infrastructure_only` (lemmas useful) | FAIL (Hardy–Wright 329 + Evertse) | FAIL (one-page) | FAIL | FAIL (folklore method) | FAIL |
| `a1af2a6e` E1003 fusion | dup of R9 | `infrastructure_only` | FAIL | FAIL | FAIL | FAIL | FAIL |
| `eb7120ca` E267 fusion | `infrastructure_only` | `solved_elsewhere` (Badea 1987) | FAIL | FAIL | FAIL | FAIL | FAIL |
| `279e0cb3` R10 E647 35-row residual | `journal_subclaim` | `journal_partial` | partial | FAIL | FAIL (bounded) | FAIL | FAIL |
| `9fa69652` slot741 | dup of R10 | `journal_partial` | partial | FAIL | FAIL | FAIL | FAIL |
| `b7e87fb3` L10 E319 c(N)≥4 N=7..10 | `journal_partial` | `journal_partial` | partial | FAIL | FAIL (fixed-N) | FAIL | FAIL |
| R5 E319 | dup of L10 | `journal_partial` | partial | FAIL | FAIL | FAIL | FAIL |
| `517a3f5d` R3 FT q≤2000 | `journal_partial` | `solved_elsewhere` (Le 2012) | **FAIL** | FAIL | FAIL | FAIL | FAIL |
| `d8c5585c` FT q=1583 v2 | `infrastructure_only` | `infrastructure_only` | partial | FAIL | FAIL | FAIL | FAIL |
| `cdf8c4de` slot743 E203 12×12 | `journal_partial` | `journal_partial` | partial | FAIL | FAIL | FAIL | FAIL |
| `be1e80e5` slot742 E203 1-D Sierpinski counter | `infrastructure_only` | `calibration_only` (by design) | n/a | n/a | n/a | n/a | n/a |
| `9cb693c2` slot745 Brocard [1001,2000] | `journal_partial` | `journal_partial` | partial | FAIL | FAIL (< 2× extension) | FAIL | FAIL |
| `4dab36cf` slot746 σ₀=11 multiperfect | `journal_subclaim` | `journal_subclaim` | partial | partial | partial (closes a single ω-case) | partial (cleanest structural reduction today) | FAIL alone (needs σ₀∈{13,17,19} for venue) |
| `ad009260` E938 fusion | `infrastructure_only` (`sorry`) | `infrastructure_only` | n/a | n/a | n/a | n/a | FAIL |
| `8242d652` R8 E938 Chan | `infrastructure_only` (`sorry`) | `infrastructure_only` | n/a | n/a | n/a | n/a | FAIL |
| `38da55e5` E1052 fusion | `infrastructure_only` | `infrastructure_only` | partial | FAIL | FAIL | FAIL (refuses BHV step) | FAIL |
| `2e379de0` L2 E141 11-AP | `infrastructure_only` (`sorry`) | `infrastructure_only` | n/a | n/a | n/a | n/a | FAIL |
| `a90a0a5e` L1 E944 Dirac k=4 | `infrastructure_only` (`sorry`) | `infrastructure_only` | n/a | n/a | n/a | n/a | FAIL |
| `95ead4b7` L7 E477 cubic | `infrastructure_only` (`sorry`) | `infrastructure_only` | n/a | n/a | n/a | n/a | FAIL |
| `f9e23cf2` I9 Euclid smoke | `infrastructure_only` (calibration) | `calibration_only` | n/a | n/a | n/a | n/a | n/a |

**Retroactive count of `journal_clean_novel` today: 0.**

The single closest contender is slot 746 (σ₀=11 multiperfect impossibility), which tagged `journal_subclaim`. To reach `journal_clean_novel`, it would need at least 2-3 additional σ₀ cases (σ₀∈{13,17,19}) closed by the same p-adic structural reduction *as a uniform family-impossibility theorem*. That extension has not been submitted.

The retroactive distribution is:

| HM | Count |
|---|---|
| `journal_clean_novel` | **0** |
| `journal_clean_extension` | 0 |
| `journal_partial` | 7 |
| `journal_subclaim` | 1 |
| `infrastructure_only` | 11 |
| `solved_elsewhere` | 3 |
| `calibration_only` | 2 |

This is consistent with the V-team conclusion (0/22).

---

## 4. The bright line, by hypothetical

| Example | Verdict | Which N-criterion is decisive |
|---|---|---|
| R9 E1003 φ/n / rad-injection trick | NOT novel | N1 (Hardy–Wright Thm 329 + Evertse subsumes) AND N2 (one-page derivation) |
| R4 E324 N=200 quintic distinctness | NOT novel | N1 (Motose–Guy frontier 10¹⁴) AND N3 (< 2× extension, no new method) |
| R3 FT p=3, q ≡ 71 (mod 72), q ≤ 2000 | NOT novel | N1 (Le 2012 is unconditional for all q) — single failure, but absolute |
| R7 E324 h=0 slice | NOT novel | N1 (Newton 1666) AND N2 (2-line strict convexity) |
| **Hypothetical:** disprove Dirac k=4 by exhibiting a min-degree-3 graph on >17 vertices with no 2⁴-cycle, verified by `decide` | **NOVEL** | N1 (open conjecture; no subsumption) ∧ N2 (specialist cannot exhibit graph) ∧ N3 (disproves stated open) ∧ N4 (constructive disproof is the novel application) ∧ N5 (publishable as a research note) |
| **Hypothetical:** prove σ₀=11 multiperfect impossible AND extend to σ₀∈{13,17,19} as a uniform p-adic family-impossibility theorem | **NOVEL** | All five N-criteria hold once the family extension is included |
| **Hypothetical:** extend Brocard verified range to n ≤ 10¹⁰ using a structurally new sieve (not stock `native_decide`) | `journal_clean_extension` | N1 partial (against the published range only); N3 satisfied via new asymptotic regime; N4 satisfied by the new sieve |

**The bright line is N2 ∧ N3 ∧ N4 simultaneously.** A submission that fails any one of those three is non-novel in the working-mathematician sense, regardless of how clean the Lean compilation is.

---

## 5. The single criterion that is hardest to satisfy

**N4 — Uses a technique or insight not previously applied to this problem.**

Aristotle's strongest scaffolds (S1, S2, S3, S6, S7 per `closure_taxonomy_may30.md` Axis 2) are all instances of `native_decide` + Mathlib library lemmas + (occasionally) a residue-class enumeration. None of these constitute a "new technique" by any working mathematician's definition. Even the cleanest autonomous proof substitution today (R9 dropping S-unit theory for rad-injection) used a folklore technique that any number theory PhD student could write down.

Out of today's 22 artifacts, **at most 1** (slot 746's p-adic reduction) plausibly satisfies N4, and only because that specific p-adic application to σ₀=11 multiperfect has (per local literature search) no published prior. Even there, the underlying p-adic-valuation argument is standard.

By contrast:
- **N1** can be satisfied by careful problem selection (avoid problems with known computational frontiers).
- **N3** can be satisfied by selecting genuinely-open conjectures where any non-trivial advance is novel.
- **N5** is mostly a packaging question (combine ≥ 3 sub-claims into a family theorem).
- **N2** is partially in our control (target genuinely-hard problems).

But **N4 requires the model to invent or transfer a technique it has not been prompted with, and to apply it to a problem where that technique is not standard.** That is currently outside Aristotle's demonstrated capability profile (per A4 capability profile: Aristotle has never invented a decreasing measure for induction; has never closed a density/sieve argument with new analytic constants; has never produced a non-folklore proof technique).

---

## 6. Realistic frequency expectation

Per F4/F10 audit and today's 0/22 result, the realistic expectation for `journal_clean_novel` is:

| Pipeline state | Expected `journal_clean_novel` rate |
|---|---|
| Current (bare-gap + auto-context, no fusion lane validated) | **0–1% of attempts** (today's empirical: 0/22) |
| With fusion lane validated (subsystem #2 actively engaging on production submissions) and σ-multiplicativity family-impossibility track | **1–3% of attempts** (per `today_results_research_impact_synthesis.md` §Calibration) |
| With model upgrade (GPT-5.5 → GPT-6 / next-gen, expected Q3 2026) | **3–5% of attempts** (extrapolation, no calibration data) |

For `journal_clean_extension` the rate may be 2-3× higher with deliberate selection of problems where a structurally-new computational technique can push the published frontier (e.g., new sieves for Brocard, new descent for FT p=5).

For `journal_subclaim` the rate is higher still: σ-multiplicativity sub-claims (slot 746 template) appear to close at ~10-20% rate per family attempt, suggesting that 5-8 sub-claim closures over 4 weeks is realistic if concentrated on the right problem class.

For **everything else combined** (`journal_partial`, `infrastructure_only`, `solved_elsewhere`) the rate is high — most of today's 22 fall here — and these results are valuable for Mathlib infrastructure and pipeline calibration, but should NOT be tagged as resolving anything.

**Headline expectation:** at our current pipeline state, expect zero `journal_clean_novel` per session. Plan for the 30-day horizon assuming 0-1 hits over that period, and tag every result that doesn't pass all five N-criteria as one of the other six HM values. The honest scoreboard is `journal_clean_novel` count, period.

---

## 7. Integration with feasibility certificate

Update the per-submission `<slot>_certificate.json` schema:

```json
{
  "closure_scope": "bounded_version_closure",
  "closure_mechanism": "witness_table_chunked",
  "closure_risk_primary": "clean_decidable",
  "closure_risk_secondary": [],
  "honesty_marker": "journal_partial",
  "novelty_criteria": {
    "N1_subsumption_clean": false,
    "N2_specialist_under_1_page_proof": false,
    "N3_new_bound_or_resolution": false,
    "N4_new_technique_for_problem": false,
    "N5_journal_acceptable_as_is": false
  },
  "novelty_subsumption_citation": "Motose-Guy q < 10^14",
  "real_closure_candidate": false,
  "strategic_subclaim": false,
  "journal_clean_novel": false
}
```

The `journal_clean_novel` boolean is mechanically derived: `journal_clean_novel = ∧_{i=1..5} N_i`. Any TRUE requires the citation/specialist sketch / new-method documentation in the corresponding field.

---

## 8. Authority and supersession

- This document **refines but does not replace** `closure_taxonomy_may30.md`. Axes 1-3 are unchanged. Axis 4 (HM) is the only axis modified.
- The pre-2026-05-30 HM value `journal_clean` is deprecated. All historical rows with that tag must be re-classified to one of the seven new values.
- Closure-taxonomy decision rules (`real_closure_candidate` / `strategic_subclaim`) are unchanged; the new `journal_clean_novel` is a strictly stronger requirement than the old `journal_clean`.
- "Compiled clean ≠ resolved the gap" (CLAUDE.md rule 12) is mechanically expressed here as: `compiled_advance` requires HM ∈ {`journal_clean_novel`, `journal_clean_extension`}; HM = `journal_partial` / `journal_subclaim` may be celebrated as progress but not as gap resolution; everything else must not be marketed at all.

---

## Sources

- `docs/closure_taxonomy_may30.md` (Agent #2 — base taxonomy)
- `docs/research/today_results_research_impact_synthesis.md` (V-team — 0/22 verdict)
- `docs/research/PILOT_ERDOS850.md` (em-tautology root cause)
- `docs/research/e1003_phi_n_trick_audit.md` (R9 folklore verdict)
- `docs/research/e324_h_zero_audit.md` (R7 elementary verdict)
- `docs/research/bounded_extensions_cluster_audit.md` (R/L-cluster bounded extensions)
- `docs/research/ft_family_publishability.md` (R3 subsumed by Le 2012)
- `docs/research/asiryan_citation_audit.md` (citation gate)
- `CLAUDE.md` rules 1, 12 (gap-targeting and compiled ≠ resolved)
- `MEMORY.md` directive 4 ("Stop saying PROVEN for infrastructure that doesn't advance anything")
