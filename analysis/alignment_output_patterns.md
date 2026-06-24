# Aristotle Output-Pattern Alignment Audit — 2026-05-30 (Agent A6)

Quantitative breakdown of Aristotle's output patterns across all 2026-05-30
submissions, cross-referenced against V-team novelty verdicts.

Data sources:
- `submissions/tracking.db` — 33 submissions with `submitted_at >= '2026-05-30'`
- `analysis/inflight_results_audit_may30.md` — deep audit of slots 741-746
- `submissions/nu4_final/slot{741..746}_extracted/.../Main.lean` — raw artifacts

Status of the 33 submissions:
- 6 completed (slots 741-746, audited by E2)
- 27 still in-flight (`status='submitted'`)

---

## Pattern taxonomy (the 8 categories)

| Code | Pattern | Definition |
|---|---|---|
| A | Compile-only `native_decide` | 1-line proof; no mathematical glue |
| B | Compile + witness table | Pre-computed witness, mechanical verification |
| C | Multi-step structural proof | Real math glue; lemmas chain meaningfully |
| D | Strategy critique | Analysis/diagnosis, no proof |
| E | Autonomous strategy substitution | Different technique than the sketch asked |
| F | Honest failure / sorry | Incomplete proof with sorry |
| G | Engineered algorithm | Custom data structure |
| H | Folklore reinvention | Rediscovers a known technique |

---

## Pattern distribution (6 completed submissions)

| Slot | Problem | Lane | Status | Pattern | Score |
|---|---|---|---|---|---|
| 741 | E647 Cunningham residual 35 | closure | compiled_no_advance | **B** witness table | 6 |
| 742 | E203 Sierpinski 1D | (legacy) | disproven | **A** native_decide on counterexample | 3 |
| 743 | E203 grid 12×12 B=1000 | (legacy) | compiled_no_advance | **B** 178 native_decide + 144 witnesses | 7 |
| 744 | FT q=1583 alternate | (legacy) | compiled_no_advance | **A** 1-line `native_decide` | 5 |
| 745 | Brocard [1001,2000] | (legacy) | compiled_no_advance | **B** 20 chunked native_decide tables | 6 |
| 746 | Odd multiperfect σ₀=11 | closure | compiled_no_advance | **C** 4-lemma p-adic structural argument | 8 |

Breakdown:
| Pattern | Count | % of completed |
|---|---|---|
| A. native_decide only | 2 | 33.3% |
| B. Witness table | 3 | 50.0% |
| C. Multi-step structural | 1 | 16.7% |
| D. Strategy critique | 0 | 0% |
| E. Autonomous substitution | 0 | 0% |
| F. Honest sorry | 0 | 0% |
| G. Engineered algorithm | 0 | 0% |
| H. Folklore reinvention | 0 | 0% |

**A+B = 83% of all completed work is mechanical computation.** Only slot 746
(σ₀=11) produced real structural math.

---

## Lane × pattern matrix

| Lane | A | B | C | Submitted (in-flight) | Total |
|---|---|---|---|---|---|
| closure | 0 | 1 | 1 | 10 | 12 |
| informal | 0 | 0 | 0 | 13 | 13 |
| fusion | 0 | 0 | 0 | 1 | 1 |
| bare | 0 | 0 | 0 | 3 | 3 |
| (legacy/null) | 2 | 2 | 0 | 0 | 4 |

Completed-only signal is too thin to differentiate lanes; pattern A/B/C all
come from `closure`-style sketches that pre-target witness families.
**FUSION (1) and BARE (3) lanes have ZERO completed evidence yet** — every one
is still in-flight. The autonomous-substitution question (E) is therefore
unanswerable from today's completed data; it must wait for the 27 inflight to
return.

---

## Problem class × pattern matrix

| Class | Examples | A | B | C |
|---|---|---|---|---|
| Multiperfect / σ-arithmetic | slot 746 σ₀=11 | 0 | 0 | **1** |
| Cunningham / Erdős 647 family | slot 741 | 0 | 1 | 0 |
| Sierpinski / covering | slot 742, 743 | 1 | 1 | 0 |
| Feit-Thompson | slot 744 | 1 | 0 | 0 |
| Brocard / prime gaps | slot 745 | 0 | 1 | 0 |

The ONE case of pattern C (structural math) is the multiperfect σ₀=11
sub-claim, where the sketch supplied a concrete p-adic mechanism and Aristotle
formalized it. Every other completed proof is bounded computation.

---

## V-team novelty cross-reference

V1, V2, V3, V4, V6, V7 verdicts so far: **0/6 novel** (per task brief).

Mapping V-team verdicts to completed slots is approximate (verdict files not
present on disk), but the inflight audit gives explicit novelty assessments:

| Slot | E2 audit verdict | Implied novelty |
|---|---|---|
| 741 | "Not novel mathematics but a publishable journal sub-claim" | Not novel |
| 742 | "Calibration probe; mechanical" | Not novel |
| 743 | "Genuine bounded result that extends prior work" | Not novel (extension) |
| 744 | "Honest single-prime case clearance via direct computation" | Not novel |
| 745 | "Range bump. Solid formalization... a calibrated extension" | Not novel |
| 746 | "Sub-claim... has NOT (to my best knowledge) been previously formalized in Lean/Mathlib for σ₀=11 specifically" | **Formalization-novel, not math-novel** |

Cross-referencing with V-team 0/6: **all completed today are non-novel**, even
the strongest (slot 746) is novel-in-Lean only, not novel-in-mathematics.

V5, V8, V9, V10 projection: with 27 inflight covering the same families
(erdos373, erdos324, FT q≡71 mod 72, erdos938, erdos1003, erdos1052, erdos647)
that have produced 0 novel results in months, **expected novel rate remains
~0%**. The single ray of hope is the σ₀=13 / σ₀=17 / σ₀=19 follow-on family
identified in the slot 746 audit, but none of those are in today's inflight.

**Honest rate of NOVEL output across today's 33 submissions: 0%.**
- 6/33 completed: 0 novel
- 27/33 inflight: prior base rate on identical problem classes is ~0%
- Projected total novel output: 0

---

## Single most surprising pattern

**The witness-table-with-set-cover-+-CRT (pattern B, slot 743) is structurally
more impressive than the multi-lemma structural proof (pattern C, slot 746),
yet scores LOWER on novelty.** Slot 743 constructed an explicit 63-digit
witness M via greedy set cover over 34 index-1 primes and proved 144
cell-by-cell divisibility — genuine algorithmic work. Slot 746 was a 4-lemma
p-adic argument that any first-year algebraist would write down in 5 minutes.

The novelty assessment correctly identifies slot 746 as the only "structural"
proof, but in terms of *effort expended by Aristotle* the witness tables
dominate. **Aristotle's comparative advantage is mechanical brute force at
scale, NOT mathematical insight.** Today's data confirms that with N=6.

Pattern A (1-line native_decide) outnumbers pattern C (real structural proofs)
**2:1** on completed submissions. Pattern B (witness tables) outnumbers C
**3:1**. The mathematical-content density of Aristotle's output is dominated
by closure-axis-tagged "bounded sub-claim" submissions; the few "unbounded
gap" attempts all return either sorry (filtered pre-submission) or get
replaced by Aristotle into a bounded variant.

---

## Pattern E (autonomous substitution) — when does it fire?

Cannot be measured today: all completed slots received pre-strategized
closure-axis sketches that explicitly told Aristotle what technique to use
(witness table / native_decide / structural reduction). Pattern E
(autonomous substitution) requires either:
- BARE lane (3 in-flight, 0 completed today)
- FUSION lane (1 in-flight, 0 completed)
- Sketches that under-specify mechanism

**Open prediction:** the 3 BARE-lane submissions (erdos324_quintic_distinct,
erdos319_sign_pattern, erdos324_quintic_N200_iter2) are the most likely sites
for pattern E. The 13 informal-lane and 1 fusion-lane submissions explicitly
seed Aristotle with prior context, which suppresses substitution. The 10
closure-lane in-flight all pre-specify witness or sub-claim mechanism, which
also suppresses substitution.

Prediction: pattern E hit rate on today's 27 inflight = **at most 1**, almost
certainly 0.

---

## Conclusion

- Aristotle's distribution on completed 2026-05-30 work: **A=33%, B=50%,
  C=17%**, with zero D/E/F/G/H.
- Aristotle's mathematical-content output is dominated by mechanical
  computation (A+B = 83%). Real structural math (C) appears once.
- **Novelty rate: 0/6 completed, projected 0/33 total.**
- Most surprising: effort spent (witness-table construction) does not
  correlate with novelty — the lazy 4-lemma p-adic proof outscores the
  600-line algorithmic monster.
- Pattern E (autonomous substitution) is suppressed by the closure-axis
  gate, which is BY DESIGN. The cost is that we never see Aristotle pick its
  own technique.

Recommendation: if the goal is to *measure* what Aristotle would
autonomously do, run a deliberate BARE-lane experiment with under-specified
sketches. If the goal is to *resolve gaps*, today's data confirms the
closure-axis bounded sub-claim is the only reliable lever, and accept that
none of those results are mathematically novel.
