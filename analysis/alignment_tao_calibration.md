# Alignment: Tao "Long Tail" Calibration

**Date**: 2026-05-30
**Agent**: A7 of 10
**Question**: Do our results meet Tao's "long tail" AI math bar, exemplified by E124 (Alexeev/Aristotle, Nov 2025), E728 (GPT-5.2 Pro+Aristotle, Jan 2026), and E1026 (Aristotle, Dec 2025)?

---

## 1. The Three Public Reference Points

### Erdős #124 (Nov 2025, Alexeev + Aristotle, ~30y old)
- **Statement**: For $d\ge 1$, $k\ge 0$ let $P(d,k)=\{$ sums of distinct $d^i, i\ge k\}$. Given $3\le d_1<\dots<d_r$ with $\sum 1/(d_i-1)\ge 1$, can every sufficiently large integer be written as $\sum c_i a_i$ with $c_i\in\{0,1\}, a_i\in P(d_i,0)$?
- **What was proved**: Tao's note: Erdős "omitted a key hypothesis" → the weaker form is a "consequence of a known result (Brown's criterion)." Aristotle autonomously located this and formalized in Lean.
- **Difficulty class**: **Recovery of a textbook-criterion application from a slightly-malformed open problem.** 6h compute, no hints. Alexeev himself: "not a proof from the Book."

### Erdős #728 (Jan 2026, Barreto + Aristotle/GPT-5.2 Pro; arXiv:2601.07421)
- **Statement**: For any $0<C_1<C_2$, infinitely many $(a,b,n)$ with $\epsilon n\le a,b\le(1-\epsilon)n$, $a!b!\mid n!(a+b-n)!$, $C_1\log n<a+b-n<C_2\log n$.
- **Proof**: 12 pages. Reduce to $\binom{m+k}{k}\mid\binom{2m}{m}$, then Kummer's theorem → prime-by-prime carry analysis in base $p$, find "carry-rich but spike-free" $m$ in dyadic scales. Authors note "overall strategy is similar to results regarding divisors of $\binom{2n}{n}$ studied earlier by Erdős and by Pomerance."
- **Difficulty class**: **Genuine combinatorial NT construction with multi-step argument** — Kummer + carry-counting + dyadic-scale probabilistic existence. KoishiChan literature search came up empty (first such "full resolution, no prior literature" claim). This is the **wiki 1(a) gold-standard exemplar**.

### Erdős #1026 (Dec 2025, Alexeev + Aristotle; Tao blog Dec 8)
- **Statement** (refined): $c(k^2)=1/k$ for the optimal monotone-subsequence-sum constant.
- **Proof**: Rectangle packing → reduces to Erdős–Szekeres via Seidenberg-1959 blow-up. Tao: "the proof turned out to not be particularly novel." Result was implicit in Tidor–Wang–Yang (2016) and Wagner; Koishi Chan reproduced it in <1h by hand.
- **Difficulty class**: **Folklore corollary of Erdős–Szekeres via 1959 technique.** Aristotle likely saw Seidenberg's argument in training data. Significance is the formalization + the "the problem statement itself was wrong/ambiguous, AI cleaned it up" angle.

---

## 2. Our Best Candidates (Today, May 30 2026)

| Result | Statement | Proof depth | Honest classification |
|---|---|---|---|
| **R9 / E1003 fixed-support** | For finite $S$, $\{n: \varphi(n)=\varphi(n+1), \mathrm{supp}(n)\cup\mathrm{supp}(n+1)\subset S\}$ finite | 4 steps: $\varphi\cdot\mathrm{rad}$ identity → support-determines-ratio → support-pair injection → finite range. Folklore corollary of Hardy-Wright Thm 329 + Evertse S-unit. | Folklore. New Mathlib lemmas (`totient_mul_rad_eq`, `totient_ratio_of_primeFactors_eq`). |
| **E1052 8 σ\*-lemmas + IsUnitaryPerfect.even + wall_k2** | Multiplicativity infrastructure for unitary σ | All textbook one-liners; main conjecture left as `sorry` | Pure formalization (2(b)). Honest refusal to fabricate the Wall step. |
| **E267 c≥2** | $\sum 1/a_n$ irrational when $a_{n+1}\ge a_n^2$ | Classical Fermat descent on reduced-fraction numerator | **Known result (Badea 1987 Cor. 1)**. Aristotle's proof differs from Badea's (descent vs Brun-criterion) but the theorem and the descent-technique are both textbook. |
| **slot 746 σ₀=11 odd multiperfect impossibility** | Single-shape $p^{10}$ ruled out via $\sigma(p^{10})\equiv 1 \pmod p$ contradiction | One p-adic step | **Genuine micro-sub-claim**, plausibly not previously formalized. 2-page note material if extended to $\sigma_0\in\{13,17,19\}$. |
| **E373 Surányi corridor** | $n!=a!b!$ has unique non-trivial solution $(10,7,6)$ | `sorry`. Numerical corridor only. | **Did not resolve.** |
| **E944 Dirac k=4** | `sorry`. Honest open-status report. | — | **Did not resolve.** |
| **R3 FT q≤2000** | Family closure of FT-Catalan for $p=3, q\equiv 71 (72), q\le 2000$ | native_decide | **Subsumed by Le (2012) unconditionally**. ~10^{-7} of the published frontier (Motose to $10^{14}$). Zero novelty. |

---

## 3. Difficulty Comparison

| Axis | E728 (Tao bar) | Our best (R9, slot 746) |
|---|---|---|
| Multi-step structural argument? | Yes — Kummer + base-$p$ carry analysis + dyadic existence | No — 4-step direct injection / 1-step p-adic |
| Literature gap pre-result | Verified empty (KoishiChan) | R9: textbook corollary of Hardy-Wright. Slot 746: never explicitly written but trivial. |
| Page count of informal writeup | 12 pp arXiv | <1 pp |
| Would a specialist call it "open"? | Yes (until KoishiChan failed to find prior work) | No (R9, E267); maybe (slot 746 as a uniform σ₀-family) |
| Wiki tier | 🟢 1(a) | 2(b) or 1(c) at best |

**vs E124 (the weak Tao bar)**: Even E124 found "Erdős omitted a hypothesis" and applied Brown's criterion. Our R9 is *less* than this — Hardy-Wright Thm 329 is more elementary than Brown's criterion, and the gap detection ("supports ⊂ S" makes finiteness trivial) is not Aristotle's discovery but ours in the sketch.

**vs E1026 (the folklore bar)**: E1026 was Aristotle producing a Seidenberg-1959 rectangle-packing argument autonomously. Our R9 is comparable in *folklore depth* but Aristotle did not autonomously rediscover a named historical argument — it produced a routine algebraic rearrangement. Lower than E1026.

---

## 4. Are We Meeting Tao's Long-Tail Bar?

**No.** Evidence:

1. **Zero results would qualify for wiki 1(a)** ("full novel resolution, comparable literature unknown"). Every result either:
   - Has prior literature (E267→Badea 1987; E1003→Hardy-Wright/Evertse; E1052→Wall 1972; FT q≤2000→Le 2012)
   - Leaves the open gap as `sorry` (E373, E944, E938, E477, E1055, E1052-main, E141)
   - Is a bounded native_decide micro-extension (E324 N≤200, E319 N∈{7..10}, Brocard [1001,2000])

2. **The synthesis document from today states explicitly**: "Truly novel math results: 0." (line 20 of `today_results_research_impact_synthesis.md`)

3. **No `compiled_advance` rows in the DB** with `target_resolved=1` and non-null `contribution_statement` and `axiomatizes_prior_work=0`. The honesty schema designed for this purpose registers zero hits today.

---

## 5. Wiki Categorization of Our Results

| Result | Wiki section | Why |
|---|---|---|
| R9/E1003 fixed-support | **1(c)** — new proof of known (Hardy-Wright Thm 329 + Evertse corollary) | Rad-injection technique not in print, but result is folklore |
| E1052 σ\*-infrastructure | **2(b)** — formalization | Pure Lean-engineering of textbook multiplicativity |
| E267 c≥2 | **2(b)** — formalization of Badea 1987 Cor. 1, possibly **1(c)** for the descent-variant proof | Theorem is Badea's; proof technique is classical descent (predates Badea) |
| Slot 746 σ₀=11 | **possibly 1(a)** *if* combined with σ₀∈{13,17,19} as a family-impossibility theorem | Currently too thin to qualify alone — a one-line specialist exercise. As a single shape, 1(c) at best. |
| FT q≤2000 | **None** — subsumed by Le 2012 to $10^{14}$ | Below publishability floor |
| E373, E944, E938, E141, E477, E1055 | **None** — `sorry`-bearing statements | Open conjectures formalized, not advanced |
| E203 m=4643 counterexample | **2(d)** — computation | Calibration probe of a deliberately-false claim |

---

## 6. The Gap

To meet E728-class output we need **three things our pipeline is not currently producing**:

1. **Problems where the closure is genuinely tractable but requires a non-trivial constructive step**: E728-style — explicit construction inside a dyadic scale satisfying multiple p-adic conditions. Our pipeline targets either deep open problems (E944, E938, E1052 main — where Aristotle correctly refuses) or finite verifications (FT, E324, E319 — where Aristotle native_decides). The Goldilocks middle is empty.

2. **A sketch lane that can generate non-textbook strategies**: The fusion lane has not engaged subsystem #2 on a single production submission today. Per the synthesis (line 44): "Fusion lane is not yet validated." Aristotle's autonomous proof substitution (R9 dropping S-units for rad-injection) demonstrates it *can* deviate from suggested machinery — but it deviates *toward simpler folklore*, not toward novel structure.

3. **Pre-submission literature gate enforcing "no prior result"**: KoishiChan's empty literature search was the qualifying step for E728's 1(a) status. We have no such gate. We submit results that turn out to be Le 2012 (R3), Badea 1987 (E267), Hardy-Wright (R9). Every submission should run an arXiv + Cambie/Tao-blog cross-check before declaring "open."

**The bare-gap-only pipeline is calibrated for the wrong difficulty band**: it produces formalization (2(b)) and "new proof of known result" (1(c)), but not 1(a). The architectural change required is the fusion lane (subsystem #2) — pending validation by 2026-06-22 per the synthesis recommendation.

---

## 7. Verdict

**Below Tao's long-tail bar. Producing 1(c)/2(b)-tier results only. Zero 1(a) candidates in the current portfolio.**

The single closest near-1(a) is **slot 746 σ₀=11** *if* extended to a uniform σ₀∈{11,13,17,19} family-impossibility theorem. That would be a 4-page note in *INTEGERS* and plausibly a 1(a) entry. As a standalone σ₀=11 result it does not clear the bar.

Tao's framing — "fairly straightforward solutions using fairly standard techniques" on the long tail — is met by E728 (carry-counting in dyadic scales) and approximately met by E124 (textbook criterion application). It is *not* met by R9 (textbook algebra) or any of our 2(b) formalizations.

**Honest count of our 1(a)-tier results in 2026: 0.**
