# Literature Freshness Audit — Closure Candidates

**Date:** 2026-05-30
**Agent:** C6 (retry after rate-limit on initial attempt)
**Inputs:** `codex_closure_candidates.md` (10 candidates) + `grok_closure_candidates.md` (10 candidates). Gemini's file (`gemini_closure_candidates.md`) did not materialize within the 10-min poll window; proceeded with Codex+Grok union as protocol allows (≥2 of 3).
**Total distinct candidates audited:** 22 (after de-dup; includes E672 split into k=4 powerful AP and k=4,ℓ=3 AP per Codex/Grok framings, plus E1 bonus check).

---

## Status counts

| Status | Count | % |
|---|---:|---:|
| STILL_OPEN | 13 | 59% |
| SOLVED_SINCE | 4 | 18% |
| STILL_OPEN_BUT_TRIVIAL | 1 | 5% |
| AMBIGUOUS | 1 | 5% |
| Confirmed SOLVED (Erdős 1 bonus) | 1 | 5% |
| Already excluded by proposer | 2 | 9% |

---

## TOP 3 SOLVED-SINCE MISFIRES (would have wasted compute)

### 1. **Casas-Alvero degree 12** (Grok #4) — DOUBLE EMBARRASSMENT
- Grok stated "open for n=12 over Q". Reality:
  - **Castryck, Laterveer, Ounaïes (2012)** settled degree 12 specifically (it was the smallest open case at that time).
  - **Ghosh (Jan 2025, arXiv:2501.09272)** claims a FULL proof of the conjecture for all degrees d≥3 via Koszul homology.
- Submitting this as a counterexample search is searching for something whose non-existence is already proven (modulo peer review of the Jan 2025 paper).
- **REMOVE from closure lane.**

### 2. **Lehmer totient ω(n)=7** (Grok #5)
- Grok stated "current literature stops at ω(n)≤6". Reality:
  - **Cohen-Hagis (1980)** proved ω(N)≥14 for any solution.
  - Current bound is ω(N)≥15 with N>10^30.
- The ω=7 case has been ruled out for **46 years**.
- **REMOVE.**

### 3. **Primitive weird numbers ω=6** (Grok #6)
- Grok stated "the ω=6 case was explicitly listed as open by Melfi". Reality:
  - **Amato-Hasler-Melfi-Parton (J. Number Theory v201, 2019)** found PWNs with up to 16 prime factors, and 12 PWNs with exactly ω=6 were known by 2018.
  - Melfi himself co-authored the paper that closed this.
- The 2015 Melfi paper Grok references is about **infiniteness** (conditional on Cramér), not existence at ω=6.
- **REMOVE: Grok misread the open question.**

### Honorable mention — **Erdős #307** (Codex #7)
- Codex framed as "finite prime sets P,Q with (Σ 1/p)(Σ 1/q)=1".
- Note: erdosproblems.com #307 is about **sum** = 1 (not product), and the sum-version of the problem (subsets S⊆{1,..,n} with Σ 1/s=1) saw **major resolution in 2024** by Steinerberger, Liu-Sawhney, Bloom et al.
- If Codex meant the product version (which is a different open question), framing is ambiguous; if it meant the sum version, it's solved.
- **AMBIGUOUS — flag for manual disambiguation before submission.**

---

## TOP 3 STILL-OPEN CONFIRMED (closure-grade)

### 1. **Erdős #64 — Erdős-Gyárfás 2^k cycles** (Codex AND Grok mention)
- Status: **OPEN** for min-degree 3 case despite Liu-Montgomery 2023 (avg-degree) and 2024-2025 P_k-free extensions.
- Counterexample must have >17 vertices total; cubic counterexample >30 vertices.
- Closure mechanism: SAT/extremal search produces candidate, Aristotle verifies adjacency on `Fin N`.
- **Strong match to S6 DNA (slots 114/131/250/267).**

### 2. **Erdős #672 powerful AP** (Codex + Grok, complementary framings)
- Codex: positive witness for k≥35 (l=2 closed by Marszalek up to k≤34).
- Grok: explicit k=4, ℓ=3 AP of 3-powerful numbers.
- Status: **OPEN**; abc-conditional bounds only; Springer book "Perfect Powers — An Ode to Erdős" (2025) treats the conjecture as live.
- Closure: explicit witness via CRT embedding, native_decide verifier.
- **Matches slot712 DNA directly.**

### 3. **Erdős #647 existential** (Codex)
- Status: **OPEN**; Erdős offered £25 (≈$44 in 1992 USD) for a single n>24 example.
- Erdős's stated conjecture is that no such n exists; problem is "extremely doubtful" per Erdős.
- Closure: either a single explicit n (positive resolution + prize) OR proof of non-existence via σ₀ multiplicativity (matches slot737 DNA).
- **Highest publishability/compute ratio.**

---

## EMBARRASSMENTS / GAPS

### Grok's "Erdős #137 k=4" is trivially implied
- Grok #1 proposes "four consecutive powerful integers (k=4) — k=3 solved 1980s, k=4 open."
- Two errors:
  1. **k=3 is NOT solved** — Erdős-Mollin-Walsh conjecture is OPEN as of 2025 (Chan 2025 only resolves a subcase).
  2. **k=4 is trivially implied by k=3** — any 4 consecutive powerful integers contain 3 consecutive powerful integers. So either:
    - k=3 stays open → k=4 is the same problem dressed up
    - k=3 gets solved → k=4 inherits automatically
- **Closure of k=4 = closure of k=3 = ~$1M conjecture-grade target, not a side problem.**
- This is the Leinster slot739 antipattern: a problem-shape that LOOKS like a smaller subcase but is logically the same problem.

### Grok's "covering systems with squarefree odd moduli >40"
- Grok #3 proposes "disprove by explicit construction" of a distinct squarefree odd cover with moduli >40.
- **BBMST22** proved: NO distinct odd squarefree covering system exists, full stop. The >40 condition is irrelevant — Grok's target was already disproved on a stronger hypothesis.
- **Closure here = formalize BBMST22**, which is formalization-not-novel. Falls into the snipe_list KnownCliff zone.

### Codex's "Erdős #7 = covering DNA match"
- Codex says E#7 is the cleanest match to Aristotle's S7 covering DNA. True in principle, but the actual open problem is **DISCOVERING** a cover (Selfridge $2000 prize) — Aristotle only VERIFIES.
- The mathematical content is in the cover construction (unsolved since 1950 despite massive search). Aristotle's role is downstream.
- **Closure-grade IF an external search finds a candidate cover. Otherwise: not Aristotle's job.**
- Same shape as Sierpinski/Riesel candidates.

### Codex's E#647 framing is sharper than snipe_list's
- snipe_list_may30 treats E647 as a σ₀ generalization template.
- Codex points out the live closure is finding the explicit n>24 witness with prize attached.
- **Codex is more honest** about what constitutes closure here.

---

## RECOMMENDATIONS

**Strip from closure lane (waste compute):**
- Casas-Alvero deg 12 (Grok #4) — SOLVED 2012/2025
- Lehmer ω=7 (Grok #5) — SOLVED 1980
- Primitive weird ω=6 (Grok #6) — SOLVED 2019
- Covering squarefree odd >40 (Grok #3) — REFUTED by BBMST22
- Erdős #137 k=4 (Grok #1) — TRIVIALLY = k=3 (Leinster antipattern)

**Manual review (clarify framing):**
- Erdős #307 (Codex #7) — sum vs product disambiguation
- Kotzig P_k (Codex #10) — Xing-Hu 1990 proof gap; verify status

**Closure-grade green-lit:**
- E#647 existential (Codex #1) — highest publishability
- E#64 Erdős-Gyárfás counterexample (Codex #5 + Grok #1 dressed up) — S6 DNA match
- E#672 powerful AP witness (Codex #8 + Grok #8) — slot712 DNA match
- E#835 k-subset coloring (Codex #6) — narrow scope, k=9..12 attackable
- Tuza ν=5 on 13 vertices (Grok #7) — small graph counterexample search
- Reconstruction Conjecture counterexample (Codex #9) — high difficulty but S6 in principle
- Riesel/Sierpinski smaller-k disproofs (Codex #3,4) — requires external cover search; closure = verification only

**Bound-bumping aliases (likely F7 leak, not closure):**
- Pillai 5^x−3^y=2 to 2000 (Grok #9) — extends slot676 but bound-only
- Goormaghtigh (5,3) at 10^9 (Grok #2) — Grantham 2024 already at 10^700
- Brocard (Grok excluded explicitly)
- Odd multiperfect σ₀=11 (Grok #10) — narrow but verification cost

---

## Data quality note

Without Gemini's candidate list, the union is smaller than ideal (~20 distinct candidates vs estimated 20-30). If a literature-fresh sweep matters for Gemini's picks, re-run when `gemini_closure_candidates.md` materializes. The Grok+Codex union already exposes the dominant failure mode (Grok proposes things that are decades-solved or trivially implied by a bigger problem), which is the main signal the audit was designed to surface.

## Net signal

**5 of 10 Grok candidates fail the literature-freshness check.** Grok hallucinated currency on:
- Casas-Alvero deg 12 (solved 2012)
- Lehmer ω=7 (solved 1980)
- Primitive weird ω=6 (solved 2019)
- Squarefree odd covers (refuted 2022)
- Erdős #137 k=4 (logically = k=3)

**Codex's failures are subtler:** Mostly correct status but framing as "verification" when the actual open problem is **discovery** (E#7, Sierpinski, Riesel). Codex's closure-grade picks (#1, #5, #8) align with the actual open math.

**Net advisory: trust Codex >> Grok on closure candidate identification. Grok's confidence outruns its literature recall.**
