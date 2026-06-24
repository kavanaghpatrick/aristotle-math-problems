# Research Fusion Analysis: Erdős 267 (Lacunary Fibonacci Reciprocals)

**Agent:** S6 of 10 (technique-scouting round 1) | **Date:** 2026-05-30
**Problem:** For which c > 1 is Σ_{k≥0} 1/F_{n_k} irrational, where (n_k) is any sequence of positive integers with n_{k+1}/n_k ≥ c eventually?
**Source:** erdosproblems.com/267 ; Codex F8 marked as top fusion candidate (Pisot β-shift target).
**Status:** OPEN in the range 1 < c < 2. Closed for c ≥ 2 (Badea-style) and for c > 2 (Nguyen 2022, transcendence).

---

## A. What is known (as of 2026)

### A1. Closed cases
- **Good (1974)** — the doubling case n_k = 2^k is not just irrational but algebraic:
   Σ_{m≥0} 1/F_{2^m} = (7 - √5) / 2.
- **André-Jeannin (1989)** — Σ 1/F_n is irrational (general full sum, not lacunary). Uses full recurrence structure.
- **Badea (1987)** — sufficient irrationality criterion: a_{k+1} > a_k^2 - a_k + 1 eventually. For Fibonacci, F_{2m} = F_m(2F_{m+1}-F_m) > F_m^2 - F_m + 1, so n_{k+1} ≥ 2 n_k eventually suffices. Closes c ≥ 2.
- **Nguyen (2022, Trans. AMS)** — transcendence when liminf n_{k+1}/n_k > 2. Closes c > 2 strongly.
- **Duverney-Kurosawa-Shiokawa (2020)** — refinement of Badea-type fast-convergence criterion.

### A2. The exact open interval
**1 < c < 2** is the precise open range.

The methodological barrier is **quadratic growth**: every existing general tool (Badea, Duverney, Subspace-theorem) requires denominator growth at least like a_k^2. For c < 2 we only have a_k^c — subquadratic — and existing criteria fail.

## B. Codex F8's analysis (cross-domain pull)

**Top candidate framing: Pisot / β-shift dynamics.**

Fibonacci numbers F_n satisfy F_{n+1}/F_n → φ = (1+√5)/2, a Pisot number (algebraic integer >1 with all other conjugates of modulus <1). The "β-shift" associated with φ is a symbolic dynamical system whose admissible sequences encode β-expansions of reals.

Heuristic: 1/F_n ≈ φ^{-n} · √5. So Σ 1/F_{n_k} ≈ √5 · Σ φ^{-n_k}. The latter is a β-power-series in β = 1/φ.

**Why 1<c<2 is hard:** The β-shift has finite-type symbolic complexity, but the irrationality of Σ φ^{-n_k} with n_{k+1}/n_k ≥ c subquadratic is *exactly* the kind of question that fails the standard transcendence/subspace technology and is conjecturally related to **normality of β-expansions on lacunary subsequences**.

## C. Adjacent-domain analogs

### C1. Mahler functions / Mahler's method (transcendence)
The series Σ 1/F_{2^m} (Good's algebraic case) is a Mahler function:
  f(z) satisfying f(z^p) = R(z, f(z)) for polynomial R.
Mahler's theorem gives transcendence of f(α) for algebraic α (under conditions). The c=2 (doubling) case is a "p=2" Mahler series. For 1<c<2, the Mahler equation is missing.

### C2. Subspace theorem (Schmidt 1972)
Schmidt's subspace theorem and its p-adic extensions (Evertse-Schlickewei) close many Diophantine series, but always require denominators growing at least as fast as a_k^{2+ε}. Same threshold as Badea.

### C3. β-expansions and dynamics (Parry, Schmidt)
Parry's theorem characterizes β with finite β-expansion of 1. For φ (Fibonacci β), the β-expansion of 1 is finite: 1 = 1·φ^{-1} + 1·φ^{-2}. So φ-β-shifts have rigid structure. Open question: when does the lacunary subseries Σ φ^{-n_k} hit a "rational column" of the β-shift?

### C4. Normality / continued fractions
1/F_n has continued fraction structure F_{n-1}/F_n = [0; 1, 1, ..., 1] (n-1 ones). Crude bounds on truncations of S = Σ 1/F_{n_k}:
  q_N R_N ≈ φ^{(1/(c-1) - 1) · n_{N+1}}.
For c>2: truncations directly rule out rationality. For 1<c<2: too weak.

### C5. Schmidt-Spiro / Hancl-type criteria
Hancl-style irrationality criteria for "fast positive series" exist, but they all reduce to the quadratic threshold.

## D. The exact methodological gap (Codex F8's framing)

> The cleanest single missing lemma would be a **multi-step Brun/Badea criterion** for Fibonacci reciprocals — something that can use n_{k+r} ≥ 2 n_k for a fixed r=r(c) even when n_{k+1} < 2 n_k. I.e., a criterion stable under amortizing growth over finitely many steps rather than one step.

Current proofs are one-step. Open range needs a **genuinely multi-step irrationality criterion** tailored to Fibonacci denominators.

## E. Adjacent open problems with similar shape

- **Cantor-set irrationality** (Mahler 1929): irrationality of digit-set series at irrational base.
- **Bugeaud's conjecture on stammering sequences** — partial results via subspace theorem.
- **Skolem-Mahler-Lech** at irrational base — closed in characteristic 0 but the analogous "lacunary subseries" question is open.

## F. Status assessment

OPEN since 1976 (Erdős posed). c=2 closed by Badea 1987, c>2 closed by Nguyen 2022. The remaining sliver 1<c<2 has resisted all "fast-convergence" technology because the methods are inherently quadratic. **High-quality candidate for technique-scout debate**: a sharp, isolated open problem with a clearly-named methodological obstruction (quadratic threshold). Pisot dynamics is the Codex F8 conjectured unlocker.

**This is potentially a fusion-lane candidate** if the debate identifies a workable multi-step criterion or β-shift bridge lemma.
