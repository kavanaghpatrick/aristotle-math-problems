# Bounded-Extensions Cluster Audit

**Date:** 2026-05-30
**Cluster:** R3 + R4 + R5 + R10 — bounded computational verification via `native_decide`
**Question:** Publishable in their own right? Individually? Together as a Lean-formalization paper?

---

## 1. The Four Submissions

| ID | Problem | Bound | Method | UUID |
|----|---------|-------|--------|------|
| R3 | Feit-Thompson p=3, q≡71 (mod 72) | q ≤ 2000 (14 primes) | enumerated `Fin`/`native_decide` | 09a5b938 |
| R4 | Erdős 324 — quintic distinctness | N=200 (20,100 sums) | `Fin 201` + `native_decide` | 8294964d |
| R5 | Erdős 319 — c(N)≥4 explicit witness | N∈{7,8,9,10} | brute-force scan | 33c46b5d |
| R10 | Erdős 647 — divisor-σ₀ residual | n∈[3000, 10⁶] | enumerated arithmetic family | 9c30dee3 |

**Pattern:** Each takes a previously-unverified bounded range of an open Erdős/Feit-Thompson question and discharges it with a finite `decide`/`native_decide`/`Fin n` enumeration in Lean.

---

## 2. Existence Proof — Bounded-Verification Papers Are a Real Venue Category

Three concrete precedents establish that bounded numerical verification IS publishable on its own:

### Helfgott & Platt 2013 — *Experimental Mathematics* 22(4), 406–409
- **Title:** "Numerical Verification of the Ternary Goldbach Conjecture up to 8.875·10³⁰"
- **Length:** ~4 pages
- **Content:** Bounded computational verification (Proth-prime sieve), no asymptotic theorem
- **DOI:** 10.1080/10586458.2013.831742; arXiv:1305.3062
- **Standalone value:** Published *before* Helfgott's main proof (arXiv:1312.7748) and serves as a load-bearing citation, but is its own peer-reviewed paper.

### Berndt & Galway 2000 — *Ramanujan Journal* 4(1), 41–42
- **Title:** "On the Brocard–Ramanujan Diophantine Equation n!+1=m²"
- **Length:** 2 pages
- **Content:** No solutions for n ≤ 10⁹; sketch of Legendre-symbol heuristic
- Subsequent extensions (Matson n<10¹², Epstein–Glickman n<10¹⁵) were *also* published in their own right.

### Hercher 2024 — *On the Sum of Squarefree Integers and a Power of Two* (arXiv:2411.01964)
- Extends Erdős "squarefree + power of 2" verification from 1.4·10⁹ (McCranie) to 2⁵⁰. Pure bounded computation. Standalone preprint.

### Mihnea & Dumitru 2025 — arXiv:2509.00128
- Extends Erdős–Straus to 10¹⁸ + evaluates f(p). Bounded verification, standalone paper.

**Conclusion:** Bounded computational extensions ARE publishable; *Experimental Mathematics*, *Ramanujan Journal*, *INTEGERS*, and *Math of Computation* all carry such notes when (a) the bound is a meaningful improvement, and (b) some new technique is introduced.

---

## 3. Per-Submission Standalone Assessment

| ID | Bound novelty | Method novelty | Standalone publishable? |
|----|---------------|----------------|--------------------------|
| R3 | q≤2000 — micro-extension of prior slot720/736/744 (q≤1500, q=1583) | None (same `native_decide` template) | **No.** A 14-prime extension does not clear the bar Helfgott/Berndt/Hercher cleared. |
| R4 | N=200, 20,100 sums (max 6.32·10¹¹) | None — extension of L3 iter1 N=50 | **No.** Trivially eclipsed by any future N=10⁴ run. |
| R5 | c(N)≥4 for N∈{7,8,9,10} | None — same witness {1,2,3,6} as the c(6) case | **No.** Bound is 4 integers wide. |
| R10 | n∈[3000, 10⁶] residual closure | Mild — Cunningham-chain fusion + dossier offset table | **Borderline.** σ₀ residual technique has some structure; bound is non-trivial but residual class is engineered. |

**None of the four individually crosses the Helfgott–Platt bar** (8.875·10³⁰ was a 30-orders-of-magnitude jump using a new Proth sieve). They are micro-extensions, not breakthroughs.

---

## 4. The Cluster as a Lean-Formalization Paper

This is the more interesting framing. The relevant venue category is the *Lean formalization short paper*:

| Venue | Fit | Notes |
|-------|-----|-------|
| **ITP (LIPIcs)** | Possible | Recent ITP'23 (Best/Birkbeck/Brasca on FLT regular primes) and ITP'25 papers accept short formalization notes. Bar is "non-trivial Mathlib contribution + interesting formalization story." |
| **CICM / Calculemus** | Possible | Same niche. Intelligent Computer Mathematics conference accepts short tool/library papers. |
| **JFR (Journal of Formalized Reasoning)** | Weak fit | JFR has been mostly dormant; few recent submissions. |
| **Lean Workshop / Lean Together** | Strong fit (informal) | A 5-min talk + short writeup is exactly this category. Lean Together 2026 (Jan), FMPSI'26 (Jun), Bridging Lean/LMFDB (Jun) are obvious venues. |
| **JoMA (Journal of Mathlib Authors)** | N/A | Not an established journal (does not exist as a peer-reviewed venue). |
| **Mathlib PR** | Direct fit | Each result, if cleaned up, is a candidate PR. |

### Does the cluster cohere as a paper?

**The cluster's unifying theme:** "Closure of bounded subranges of four open Erdős/Feit-Thompson questions via `native_decide` + targeted reductions, formalized in Lean 4."

**For/against:**
- **For:** Each contribution is small, but a *bundle of four* with a common methodology (Lean + native_decide + Aristotle-assisted closure) and common authorship narrative is more interesting than any one alone. Real precedent: Loeffler-Stoll "Formalizing zeta and L-functions" bundled multiple Mathlib results.
- **Against:** (a) The math content is shallow — there's no new theorem, no new technique that survives outside Lean; (b) Three of the four are micro-extensions of *already-formalized* prior Aristotle results; (c) Lean Workshop/ITP short-paper reviewers want either (i) a Mathlib-worthy general-purpose contribution or (ii) a substantively new mathematical result. The cluster offers neither.

---

## 5. Honest Classification

**TOO SMALL (individually).** No single submission crosses the bar for *Experimental Mathematics*, *Ramanujan J.*, or *INTEGERS*. The bounds (2000 primes, N=200, N=10, n=10⁶) are too modest, and the methods are reuse of `native_decide` rather than new sieving / interval-arithmetic / SAT-encoding technique.

**MATHLIB-WORTHY (collectively, with work).** The four results, *if* the proofs are sorry-free, axiom-clean, and the bounds correspond to anything anyone is likely to need, are each candidate Mathlib PRs into the relevant `FormalConjectures.ErdosProblems.*` files. This is the highest-confidence pathway.

**LEAN WORKSHOP / TALK (cluster level).** Submitting all four as a Lean Together 2026 lightning talk or FMPSI'26 short paper is realistic — *if* framed as "AI-driven bounded-range closure of Erdős conjectures" rather than as a math paper. The contribution is *the workflow*, not the bounds.

**NOT ITP/CICM short paper.** ITP/CICM expect substantive formalization stories (a new Mathlib library, a non-trivial dependency reorganization, a methodological insight). Four `native_decide` calls do not clear that bar.

---

## 6. Realistic Publication Path

**Recommended (in priority order):**

1. **Mathlib PRs.** Open one PR per result against the corresponding `formal-conjectures` file (FT, E324, E319, E647). Acceptance is a real, citable record of work. Estimated effort: low if proofs are already sorry-free; medium if cleanup needed.
2. **Lean Together 2026 lightning talk + writeup.** Bundle all four into one 10-page note titled e.g. "Aristotle-Assisted Bounded Closure of Four Open Erdős Conjectures in Lean 4." This is a realistic deliverable for January 2026.
3. **arXiv preprint of (2).** Once the lightning-talk note exists, posting it to arXiv.math.NT is a low-cost step that creates a citable artifact.
4. **Do NOT submit to *Experimental Mathematics* / *Ramanujan J.* / *INTEGERS* as a math paper.** The bounds are not competitive with existing literature in those venues, and reviewers will (correctly) reject as not advancing the math state-of-the-art.

**Do NOT pursue:** JFR, JoMA (does not exist), ITP/CICM full paper.

---

## 7. Cluster Value vs Individual Value

- **Individual value:** ~0. Each submission is a 2-page note that no mathematics journal would accept.
- **Cluster value (as Mathlib PRs):** Real but modest. Four `FormalConjectures` files closed for a bounded range each. This is a citable contribution to the Mathlib ecosystem.
- **Cluster value (as Lean Workshop note):** Real and worth pursuing. The story is "Aristotle-driven semi-autonomous bounded closure of open Erdős conjectures in Lean 4," and it sits in a niche (AI + formalization + Erdős problems) that the community is actively interested in (cf. DeepMind Formal Conjectures project, Alexeev et al. OpenAI Erdős proofs, Xena blog Dec 2025 on Erdős formalization).
- **Cluster value (as research paper):** ~0. There is no underlying mathematical theorem to publish.

---

## 8. Citations

- Helfgott & Platt 2013, *Experimental Mathematics* 22(4):406–409 — https://www.tandfonline.com/doi/full/10.1080/10586458.2013.831742 / arXiv:1305.3062
- Helfgott 2013, "The ternary Goldbach conjecture is true," arXiv:1312.7748
- Berndt & Galway 2000, *Ramanujan Journal* 4(1):41–42 — https://link.springer.com/article/10.1023/A:1009873805276
- Hercher 2024, "On the Sum of Squarefree Integers and a Power of Two," arXiv:2411.01964
- Mihnea & Dumitru 2025, "Further verification and empirical evidence for the Erdős–Straus conjecture," arXiv:2509.00128
- Best, Birkbeck, Brasca 2023, "Fermat's Last Theorem for regular primes," ITP 2023 short paper, DOI:10.4230/LIPIcs.ITP.2023.36
- Loeffler & Stoll 2025, "Formalizing zeta and L-functions in Lean," arXiv:2503.00959
- Xena Project, "Formalization of Erdős problems," 2025-12-05
- DeepMind Formal Conjectures project (launched May 2025)
- ITP 2025 (LIPIcs vol. 352), Reykjavik, Sep–Oct 2025
- Lean Together 2026, virtual, Jan 19–23
- FMPSI'26, Orsay, Jun–Jul 2026
- Bridging Lean and the LMFDB, UEA Norwich, Jun–Jul 2026
