# Mathlib Infrastructure Gaps Blocking Aristotle Fusion Candidates

**Date:** 2026-05-30
**Agent:** A4 of 10
**Mathlib snapshot:** vendored at `/Users/patrickkavanagh/aristotle_biochemistry/.lake/packages/mathlib`, last commit `Thu Dec 11 10:09:39 2025`
**Method:** direct grep / find against the vendored Mathlib tree; cross-checked Lean Zulip, ImperialCollegeLondon/FLT repo, and current Mathlib documentation.

---

## Executive verdict

Five of the six stalled fusion candidates are blocked by **deep, multi-thousand-line Mathlib gaps**. Closing every gap is a 5–10 year community effort. The single highest-leverage gap is **Mordell-Weil rank + heights for elliptic curves over Q** — it directly unblocks E938 and R7-E324 (both Mordell / Frey / rational-points territory) and partially aids E944 sub-problems that reduce to point-counting on curves.

**However:** filling these gaps is necessary but not sufficient. Aristotle would still need to assemble a non-trivial original proof; today it stalls at the strategic-decomposition step even when *all* needed Mathlib lemmas exist (see L1 E944 audit). The gaps remove *one* constraint, not the binding one.

---

## Per-candidate gap analysis

### E938 (powerful numbers ↔ Mordell / Pillai)
**Math required:** Mordell's theorem on integer points of $y^2 = x^3 + k$, height bounds, rank-of-elliptic-curve machinery, Baker's effective theory.
**Mathlib state:**
- `Mathlib/AlgebraicGeometry/EllipticCurve/{Weierstrass,Group,Affine,Projective,Jacobian,Reduction,DivisionPolynomial}.lean` — group law and reduction are present (Reduction.lean added 2025 by B. Wang).
- `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` — sequences only, no rank.
- **MISSING:** Mordell-Weil theorem (finite generation of $E(\mathbb{Q})$), rank, height pairing, Néron-Tate canonical height, integral-points finiteness (Siegel), 2-descent.
- Zulip (Buzzard, Angdinata) estimates Mordell-Weil "3 years to land in Mathlib."

### R7-E324 Asiryan
**Math required:** same elliptic-curve apparatus plus Bombieri-Lang conjecture or Vojta-style height inequalities; Faltings as the heavyweight backstop.
**Mathlib state:** all of the above missing. Additionally:
- No Bombieri-Lang, no Vojta-Mordell, no Faltings.
- No o-minimal / Pila-Wilkie infrastructure (`grep "o-minimal"` returns nothing; `Mathlib/ModelTheory/` has no o-minimal subtree).

### E1003 v1 (Subspace-Theorem lane)
**Math required:** Schmidt's Subspace Theorem, S-unit equations finiteness (Evertse-Schlickewei-Schmidt).
**Mathlib state:**
- `Mathlib/RingTheory/DedekindDomain/SInteger.lean` (Angdinata, 2022) defines `Set.integer`, `Set.unit` — bare definitions only, no finiteness theorems for S-unit equations.
- **MISSING:** Roth's theorem (Diophantine approximation), Schmidt Subspace Theorem, ESS bounds, Evertse-Győry decomposable forms.
- No active community work surfaced.

### E944 (graph chromatic / SAT lane)
**Math required:** automated SAT-as-tactic over large CNF; graph databases.
**Mathlib state:**
- `Mathlib/Tactic/Sat/FromLRAT.lean` (Mario Carneiro, 2022) — accepts LRAT proofs from external solvers, NOT a solver itself; no DRAT/LRAT generation, no propositional reflection at Aristotle scale.
- `SimpleGraph.IsCritical` and `chromaticNumber` exist (latter via FC's `FormalConjecturesForMathlib`).
- **MISSING:** SAT solver embedded in Lean (e.g., LeanSAT integration), curated graph database for chromatic searches.

### E1041 Herzog-Piranian
**Math required:** Hausdorff measure of Riesz-type sets in $\mathbb{D}$; boundary behavior of analytic functions.
**Mathlib state:**
- `Mathlib/MeasureTheory/Measure/Hausdorff.lean` (1112 LoC) — solid foundational layer: `μH[d]`, `mkMetric`, Hölder/Lipschitz invariance, equality with Lebesgue on $\mathbb{R}^n$.
- `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` (562 LoC) — dimension theory.
- **MISSING:** specific machinery for plane sets / unit disk (no `*UnitDisk*`, no Poincaré disk), Frostman lemma, capacity theory, polar sets, boundary cluster sets of analytic functions in the disk.

### E1052 (unitary perfect numbers ↔ Bilu-Hanrot-Voutier)
**Math required:** BHV primitive divisor theorem for Lucas/Lehmer sequences; deep Baker bounds.
**Mathlib state:**
- **NOTHING.** `grep "Bilu\|Hanrot\|Voutier\|primitive divisor"` returns zero hits. No Lucas-sequence formalization beyond `LucasLehmer.lean` (Mersenne primality test). No Lehmer-pair definition. No Baker's theorem on linear forms in logarithms.

### E267 (Pisot lane, secondary candidate)
**Math required:** Pisot/Salem numbers, β-expansion theory, symbolic dynamics on subshifts.
**Mathlib state:**
- `grep "Pisot\|Salem"` matches only inside `Combinatorics/Additive/AP/Three/Behrend.lean` (Salem-Spencer sets — different "Salem").
- `Mathlib/Dynamics/*` has flows, entropy, ergodic measures — no β-shifts, no substitution systems, no symbolic-dynamics infrastructure.
- **MISSING:** entire theory.

---

## Top 5 blocking Mathlib gaps (prioritized by candidates unblocked)

| # | Gap | Unblocks | Effort estimate | Active work? |
|---|-----|----------|-----------------|--------------|
| 1 | Mordell-Weil rank + heights for $E/\mathbb{Q}$ (2-descent, Néron-Tate, Siegel integral points) | E938, R7-E324 partial, half of FLT downstream | ~3 years (Buzzard estimate); ~5,000–10,000 LoC | Yes: ImperialCollegeLondon/FLT (Buzzard, funded through Sept 2029); Angdinata Mathlib commits |
| 2 | Schmidt Subspace Theorem + S-unit equation finiteness | E1003 v1, many Diophantine problems | ~1 year (Roth ~3mo, ESS ~6mo, applications ~3mo) | None visible on Zulip 2026 |
| 3 | Bilu-Hanrot-Voutier primitive divisor theorem (and prerequisite Baker linear-forms-in-logs) | E1052, large class of exponential-Diophantine problems | ~2 years (Baker is the long pole, ~4,000 LoC) | None |
| 4 | o-minimal structures + Pila-Wilkie counting | R7-E324 (Bombieri-Lang variant), André-Oort family | ~2–3 years (foundational; needs model-theory revival in Mathlib) | Latent — ModelTheory subtree exists but no o-minimal commits |
| 5 | Frostman lemma + capacity theory in the disk; boundary cluster sets | E1041, broad classical complex analysis | ~1 year (Hausdorff measure foundation is solid; specialization moderate) | None visible |

**Aux (smaller leverage):** SAT-as-Lean-tactic (E944), Pisot/β-shifts (E267) — each ~6 months but unblocks one problem.

---

## Realistic timeline if community fully commits

- **Year 1 (now → 2027):** Schmidt Subspace Theorem (someone like Barroero, who shipped MahlerMeasure / Northcott in 2025, could plausibly take this).
- **Year 2 (2027–2028):** Frostman lemma + complex-analysis disk machinery; first half of Mordell-Weil (height functions, 2-descent skeleton).
- **Year 3 (2028–2029):** Mordell-Weil completes; FLT project hits modularity-lifting milestone (per Buzzard funding window).
- **Year 4–5:** BHV (gated on Baker); o-minimal / Pila-Wilkie.

Even an optimistic schedule puts full unblocking at ~2030.

---

## Single highest-leverage gap

**Mordell-Weil rank + heights for $E/\mathbb{Q}$.**

Justification:
- Unblocks both top fusion candidates (E938, R7-E324).
- Has active backing (ImperialCollegeLondon/FLT, Angdinata).
- Has clean decomposition (Buzzard's two-part split: algebro-geometric (Picard) and arithmetic (2-descent + heights) — independent).
- Outputs reusable machinery (heights, descent, Néron-Tate pairing) that downstream solvers can invoke for *any* rational-points problem, not just one Erdős entry.

---

## Honest verdict on Aristotle + Mathlib filled gaps

**Necessary, not sufficient.**

Today's Aristotle stalls are not primarily "Mathlib lemma X missing." Audit evidence (`docs/research/infrastructure_mathlib_audit.md`):
- L1 E944: `SimpleGraph.IsCritical` already exists in `FormalConjecturesForMathlib`; the submission redefines it locally. The pipeline isn't surfacing existing definitions.
- R8 E938: `Nat.Powerful` exists in `FC/Data/Nat/Full.lean`; six sibling problems already use it; the submission rebuilds it.
- L5 E1055: `IsOfClass` exists; submission writes alternate `selfridgeClass`.

So the *binding constraint* on novel output is **not** raw Mathlib coverage. It is:
1. **Context retrieval** — Aristotle isn't reliably pulling existing FC/Mathlib definitions.
2. **Strategic-decomposition** — even when lemmas exist, Aristotle can't pick the right top-level approach (BHV reduction, Subspace-Theorem reduction, etc.).
3. **Original mathematical insight** — for E938 / R7-E324 / E1003, the proof requires a *new* mathematical idea, not assembly of known ones; better Mathlib doesn't supply ideas.

If Mathlib were complete tomorrow, Aristotle would likely produce **more compiled-clean infrastructure** (proofs of known special cases, reformulations) but **not novel open-problem resolutions**. The hit rate on novel math would move from 0.8% to maybe 1.5–2% — material but not transformative.

---

## Sources

- ImperialCollegeLondon/FLT (v4.30.0, May 27 2026; Buzzard funded through Sept 2029 via EP/Y022904/1).
- Lean Prover Community archive on elliptic curves (Buzzard quote: "Mordell-Weil can land in mathlib in 3 years"; Picard-group / 2-descent decomposition).
- Bilu-Hanrot-Voutier (1999), *J. Reine Angew. Math.*, primitive divisors for $n > 30$.
- Evertse-Schlickewei-Schmidt (2002), bound on solutions to S-unit equations.
- Vendored Mathlib at `/Users/patrickkavanagh/aristotle_biochemistry/.lake/packages/mathlib` (commit Dec 11 2025).
- Cross-reference: `docs/research/infrastructure_mathlib_audit.md` (2026-05-30, this project).
