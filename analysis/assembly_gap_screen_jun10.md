# Assembly-Gap Screen — Ranked Shortlist (Jun 10 2026)

**Question screened:** for each candidate, is the open core exactly one *assembly gap* — a decision closable by combining known tools (published theorems + finite computation + certificates) — rather than new mathematics?

**Candidates screened:** erdos_617, erdos_647, erdos_307, erdos_850, erdos_1052.
**Adversarial verification pass:** erdos_647 only (it was the sole screen scoring above the verification threshold). Verdict: **survives**, corrected feasibility 6 → 5.5.

---

## 1. Ranked Shortlist

### #1 — erdos_647 (corrected feasibility 5.5/10, adversarially VERIFIED)

**One-liner:** The community's own definition of an assembly gap — tagged `verifiable` in teorth/erdosproblems (one of only 7 problems open-but-provable-by-finite-computation-if-true), £25 prize confirmed. Everything except the witness's existence is known machinery.

**Decisive check.** Does some n ≡ 0 (mod 420) with 10^10 < n ≤ 10^12 — whose seven associated forms n−1, (n−2)/2, (n−3)/3, (n−4)/4, (n−6)/6, (n−8)/4, (n−12)/12 are all prime — satisfy m + τ(m) ≤ n+2 for EVERY m < n (i.e., the running max of m+τ(m) over m < n equals exactly n+2)? Directly checkable by a segmented τ-sieve maintaining the running max; the range [25, 10^10] reruns as free validation against OEIS A087280 and slots 723/737 (any disagreement = halt-and-audit tripwire).

**Known tool.** OEIS A087280 (McCranie 2003) is verbatim this problem's witness sequence (5, 8, 10, 12, 24) with recorded exhaustive search to 10^10 — verified exactly via the OEIS JSON API, and teorth/erdosproblems #647 lists A087280 in its own `oeis` field (no wrong-object trap). Closing tools: (a) direct segmented divisor-count sieve with running max (~1–3·10^13 ops to 10^12, days on M-series Rust; reduction-free, trusts nothing); (b) Hardy–Littlewood/Dickson singular series for the 7-prime-form constellation as the pre-registered prior (~830 raw constellations in [10^10, 10^11]; ~0.2–0.8 expected witnesses per decade); (c) on a hit, Lean certificate via `native_decide` factor table over [n−8064, n) plus a global τ-bound. Tao–Teräväinen arXiv:2512.01739 (Dec 2025) confirms the analytic frontier — it handles ω/Ω analogues with ≪k slack only, not the exact-slack τ form; attach as F2 literature anchor.

**Kill risks.**
1. *Frontier already at 10^10* (A087280, 2003): the planned "weekend run to 10^10" produces zero new information; discovery range is [10^10, 10^12]. (Adversarial note: this is a recompute-prior mandate, not a hard kill — and the screener already recomputed.)
2. *Lottery core*: a correct assembly cannot force a hit; empty sieve at 10^12 is the realistic 40–80% outcome. Pre-registered tripwire: failed_approaches row + OEIS comment extension, no Aristotle spend, no Sophie-Germain pivot. The pre-registered empty-stop was 10^11, so the 10^12 extension needs re-registration.
3. *Certificate gap on a hit*: global "τ(m) ≤ 8064 for all m < 10^11" is not in Mathlib (and grows to 10752 by 6.7·10^12 — the window must track the actual ceiling); `native_decide` faces maximal scrutiny; false_lemmas row `hcn_tau_near_max` forbids HCN-list shortcuts. Budget 1–4 weeks Lean work.
4. *Unconfirmed claim*: the "red incorrect-work marker on Tao's wiki" could not be confirmed (0 occurrences in problems.yaml) — verify manually before publishing anything about it.
5. *Filter distrust*: slot723+737 composition is unverified (1 sorry, threshold mismatch) — use the direct unfiltered τ-sieve to 10^12; filter only beyond.
6. *Prior overstated in places* (adversarial finding): "n ≡ 0 mod 420 forced" is not exact — an n ≡ 5 mod 7 branch survives with (n−5)/7 prime, and k=10 forces an omitted (n−10)/10 prime form. Both affect only the heuristic prior (omitted form biases expected count DOWN — favorable for honesty), not sieve soundness. The 0/~224 calibrator leaves wide error bars.

**10-agent flat-squad mission spec.** One flat peer team, all ten agents doing math on #647 simultaneously in a shared workspace, no staged meta-roles. Two agents *formalize the needed statements*: lock the 647.lean faithfulness read (⨆ parses as sup ≤ n+2; Fin n boundary cases m=0, n−1; equality hit at m = n−2, n−4, n−6) and draft the witness-certificate skeleton (window factor table + parametric global τ-bound with the ceiling tracked, not hardcoded). Three agents *pull known machinery*: rebuild the segmented τ-sieve in Rust from scratch (reduction-free), independently re-derive the Hardy–Littlewood constellation prior including the omitted (n−10)/10 form and the n ≡ 5 mod 7 branch, and re-extract A087280/McCranie's method for cross-validation. Two agents *compare*: run the sieve over [25, 10^10] and diff term-by-term against A087280 and slots 723/737 — any disagreement halts the squad. Three agents *adversarially verify*: attack the certificate plan (native_decide scrutiny, hcn_tau_near_max ban), attack the prior (error-bar audit on the window-pass factor), and pre-register the [10^10, 10^12] run with explicit empty-stop criteria before the production run starts. $0 Aristotle until a hit; on a hit, lane=`informal`, Codex builds the certificate locally, Aristotle fills residual sorries via Method-1.

**Effort:** ~1 week to the no-hit decision point ($0 Aristotle). On a hit: +1–4 weeks Lean.

---

### Watch list (unverified mid-scorers, 4–5)

*Empty.* No screen scored in the 4–5 band. The nearest miss, erdos_617 (3/10), is below the band and is listed under Rejected — but see its salvageable gate below, which has standalone value.

---

## 2. Rejected

| Problem | Score | One-line reason |
|---|---|---|
| **erdos_617** (r=5/K_26) | 3/10 | Assembly fully specified and partially executed live (1.16M-clause CNF encodes, all calibration gates pass), but the computation is the bottleneck: measured hardness curve (proven r=4/K_17 undecided after 21.5 CPU-min) puts the believed-true UNSAT branch at Schur-Number-Five scale (~14 CPU-years, ~2 PB DRAT) — far outside budget — and a new Plotkin-bound lemma derived in-screen proves the planned AG(2,5) SAT warm-start family is empty (any counterexample needs a χ≥6, K_6-free Ramsey-type complement). Run only as a pre-registered lottery ticket; **salvageable gate with standalone value:** UNSAT-verify the proven r=4/K_17 case (ErGy99) with full tooling first — independent computational verification of ErGy99 either way, and if it needs more than a few hours, r=5 is definitively dead in-budget. |
| **erdos_307** (prime-reciprocal product) | 1/10 | Decisive structural finding: sums of distinct prime reciprocals never cancel, so the problem is exactly equivalent to a squarefree 2-cycle of the arithmetic derivative — which Ufnarovski–Åhlander 2003 (Conjecture 4) conjecture has NO solutions; the `verifiable` badge masks confirmed adverse selection, witness floor ≥ 10^112 with the partner set forced (all search dead), NO-direction = a 23-year-old open conjecture, and Grok's claimed partial results were verified hallucinated. File the half-day UA-equivalence memo as a durable asset; $0 Aristotle; slot closes empty. |
| **erdos_850** (Erdős–Woods k=3) | 1/10 | Both sides fail the known-tool test: impossibility is abc-hard (only Shorey–Tijdeman 2016, conditional on explicit abc; Stewart–Yu unconditional is exponentially short), and any witness is forced to be an abc triple of quality > 2 vs. the 1.6299 all-time record — while Hercher's published June 2025 GPU search already covers y < 1.4·10^12, so the proposed search is prior work with a known-empty range. 10 prior submissions, 0 advances, plus the em-tautology case study. HOLD, zero further submissions. |
| **erdos_1052** (unitary-perfect ω bound) | 1/10 | The uniform ω(n) ≤ C bound IS the open content — no published theorem touches it (verified three ways incl. Maciejewski arXiv:2605.20475, May 2026, which self-reports failure and terminates at an open cyclotomic branch); structurally isomorphic to odd-perfect finiteness (open 110+ years); the only runnable computations are F1-capped bounded extensions Aristotle already failed twice (wall_k3 rows 1282/1291 returned empty stubs); 13 DB rows, 0 advances. Also fix the local Wall-1972 misattribution before any future companion. |

---

## 3. Honest Overall Read

**The inventory is thin, and the screen worked as designed.** Of five candidates, four were rejected — three (307, 850, 1052) because the "assembly gap" framing was an illusion: their open cores are new mathematics dressed as finite checks (an expert conjecture of nonexistence, an abc-strength obstruction, a 110-year-old finiteness pattern). One (617) is a genuine assembly with the computation itself as the wall. This is the expected shape of the Erdős long tail: the `verifiable` tag is a necessary signal, not a sufficient one, and two of the three 1/10 rejections carry that tag — *adverse selection among "finitely checkable" problems is real and confirmed twice in one screen*.

**erdos_647 is a genuinely defensible next target — but it is a well-priced lottery ticket, not a promising theorem.** Its virtues are exactly what this project's post-audit doctrine asks for: every component except the witness's existence is known machinery; the decisive check is reduction-free and self-validating against published data; both outcomes are pre-registerable ($0 Aristotle on empty, a self-contained certificate on a hit); and it survived adversarial verification with only prior-sharpening corrections, every load-bearing citation checking out exactly. The honest expectation is 40–80% an empty sieve and a failed_approaches row plus an OEIS comment — a small, real, durable contribution either way. That asymmetry (bounded downside with residual value, unbounded upside if a witness lands) is the right trade at this project's measured 0.8% hit rate.

**Recommendation:** commit the ~1-week 647 sieve campaign now with re-registered stop criteria at 10^12; run the cheap 617 r=4/K_17 gate opportunistically (it has standalone value as an independent ErGy99 verification regardless of outcome); file the 307 UA-equivalence and 850 quality>2 memos into knowledge.db as durable assets; HOLD 850 and 1052 with zero further Aristotle spend. Then re-stock the screen pipeline — one survivor per five screens means the pipeline needs more candidates, not more force applied to these four.
