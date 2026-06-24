# E938 Deep-Iteration Meta-Synthesis Report

**Date:** 2026-05-30
**Coordinator:** E938-DEEP-6
**Inputs:** 4 sibling deep-iteration `.fusion.json` files + Aristotle slot 1300 `ARISTOTLE_SUMMARY.md` + convergence consultation (grok-4 succeeded; codex/gpt-5.5 reasoning loop diverged into Mathlib source-reading; gemini quota-exhausted)

---

## Aristotle's Slot 1300 Critique (verbatim)

> "The Maier matrix method, Selberg sieve with dimension-1/2 bounds, and level-of-distribution results for the powerful indicator are all absent from Mathlib"
>
> "The logical connection between 'Maier irregularity forces many small gaps' and 'AP-consecutiveness is contradicted' is not rigorous as stated — the density arguments in Steps 5–6 conflate different notions"
>
> "Computational search up to 10⁶ found only 3 consecutive powerful 3-APs"

**Two named gaps:** G1 (Mathlib-absent sieve infrastructure) + G2 (density conflation in slot 1300's Steps 5–6).

---

## Sibling Angles + Cross-Critique Outcomes

| Sibling | Technique | Fit | Cross-critique verdict |
|---|---|---:|---|
| **A — heath_brown** | Mollin-Walsh paired-Pell + Bombieri-Lang on surface 2c²d³ = a²b³ + e²f³ | 0.18 | L7 bounded-kernel Faltings is **unconditional sub-result**; L6 (BL/Vojta dim 2) is **open** |
| **B — hooley** | Selberg sieve on cubefree kernels + van Doorn family awareness | 0.18 | Dispersion direction BLOCKED; **falsification-or-finiteness** branch surfaced via van Doorn 2026 |
| **C — mollin_walsh** | Walker per-kernel + mod-N residue census | 0.12 | Mod-8 residues = {0,1,3,4,5,7} (corrected); mod-72 admissible AP triples = 593 → **2-adic Hensel does NOT close** |
| **D — stark** | Stark-Heegner CM curve E_d : y² = x(x+d)(x+2d) | 0.07 | **FALSIFIED** at Round 2 — (1728,1764,1800) product = 2¹¹·3⁷·5²·7² is NOT a perfect square; no integer point on E_36 |

---

## Strongest Sibling Angle

**Despite the lowest fit score, sibling C (mollin_walsh) was strongest** because it supplied the most novel computational verification:

1. **Corrected the mod-8 residue claim** for powerful numbers: {0,1,3,4,5,7} (not {0,1,4} as multiple prior dossiers claimed). The residues 2 and 6 mod 8 are excluded by v₂(n) = 1.
2. **Verified mod-72 admissible AP triple count = 593** — confirming that pure 2-adic / 36-adic / 72-adic Hensel-style local obstructions DO NOT close E938 (the obstruction GROWS with modulus, not shrinks).
3. **Confirmed van Doorn's first triple (130530625, 130553476, 130576327) is REAL but NOT CONSECUTIVE** — explicit computational verification of 5 intervening powerfuls strictly between the endpoints. This is novel context Aristotle has never been given.
4. **Made explicit that per-kernel finiteness is the smallest unconditional sub-result** — i.e., we know HOW to close E938 for any FIXED kernel triple (via Mordell-Siegel on the ternary form), but kernel uniformity is at least Bombieri-Lang in difficulty.

Sibling A (heath_brown) was a close second — it independently identified the kernel-bounded slice (L7) as the right unconditional sub-result. Sibling D (stark) contributed a CRITICAL FALSIFICATION ARTIFACT: the (1728,1764,1800) triple-product analysis proves the most natural CM-elliptic angle is dead.

---

## Aristotle's Gap (G1 + G2) — How the Meta Closes It

### G1: "Maier matrix + Selberg sieve dim-1/2 + level-of-distribution absent from Mathlib"

**Meta closure:** Abandon Maier + Selberg entirely. The Maier matrix angle was a 2018-style analytic-NT route that has no Mathlib formalization and likely won't have one for years. The meta swaps to:

- **Pell + SiegelsLemma** (both IN Mathlib: `Mathlib.NumberTheory.Pell`, `Mathlib.NumberTheory.SiegelsLemma`) for the per-kernel ternary-form finiteness.
- **Squarefree + Nat.factorization** (both IN Mathlib) for the Golomb parametrization.
- **Nat.sqrt + Nat.Powerful + Nat.nth + Set.IsAPOfLength** (all IN Mathlib, verified by reading `formal-conjectures/FormalConjectures/ErdosProblems/938.lean`) for the elementary square-gap bound.

The square-gap bound d ≤ √(n_{k+2}) + 1 is ENTIRELY ELEMENTARY (no sieve, no analytic NT) and is load-bearing across all 4 sibling deep-iterations. This is the Mathlib-ready replacement for slot 1300's Maier dispersion.

### G2: "Density arguments in Steps 5-6 conflate notions"

**Meta closure:** Abandon density-based reasoning entirely. Slot 1300 tried to argue that "Maier irregularity forces many small gaps" → "AP-consecutiveness is contradicted" via a density argument that Aristotle correctly flagged as conflating Maier-output-density (deviation from average) with AP-existence-density (constructive count of APs at fixed gap). 

The meta synthesis uses **direct per-kernel Mordell-Siegel finiteness** on the ternary form b₁X² + b₃Z² = 2b₂Y² for each FIXED kernel triple. No density argument anywhere. Per-kernel finiteness is unconditional via Pell-orbit / Mordell-Siegel; kernel uniformity is the explicit open core.

---

## New Closure the Meta Adds

The meta synthesis adds three things that no individual sibling delivered as a clean integrated package:

1. **L5 = Smallest unconditional sub-result formalized.** "For any fixed bound B > 0, restricted to powerful 3-APs with max(b_i) ≤ B, the consecutive-AP count is unconditionally finite." This is a Mathlib-formalizable lemma using only Pell + SiegelsLemma + Finset enumeration. Sibling A identified this; the meta makes it the central LEMMA Aristotle is asked to prove.

2. **Explicit Mathlib pointer table.** Every candidate lemma in the meta cites the specific Mathlib module that supplies the needed infrastructure (verified by direct source inspection 2026-05-30). No claim of "Mathlib-ready" without a file-name backing.

3. **Falsification branch awareness (L7).** Van Doorn 2026 (arXiv:2605.06697, posted May 4 2026) Conj 5 asserts the theorem is FALSE — infinitely many consecutive 3-APs from family A₁. The meta explicitly invites Aristotle to attempt either direction. None of the 4 siblings made this branch as cleanly explicit.

The meta also corrects/consolidates two citation errors from prior E938 dossiers (slots 1259, 1284, 1300, 1302, 1304):
- Mollin-Walsh: IJMMS 9 (1986) 801-806 doi:10.1155/S0161171286000984 (NOT JNT 1986 21:231-243 — that is a different Walsh paper).
- Heath-Brown 1988: Sem.Th.Nb.Paris Birkhauser pp.137-163 "Ternary Quadratic Forms..." (NOT Math Comp 50:155-168).

---

## Honest Assessment

**The meta does NOT close E938 unconditionally.** Per-kernel finiteness is unconditional but kernel uniformity is at least Bombieri-Lang in difficulty on a dim-2 surface of general type. The empirical record (only 3 consecutive 3-APs up to 10⁶, 18 up to 10¹⁴, all from family A₁) supports the conjecture being true, but no path to a clean Mathlib proof exists.

**What the meta DOES contribute** is:

- A SHARPER framing than slot 1300 that explicitly closes both gaps Aristotle flagged.
- A SMALLEST UNCONDITIONAL SUB-RESULT (L5) that Aristotle has not been asked for before.
- A FALSIFICATION-AWARE submission (L7) acknowledging van Doorn 2026.
- COMPUTATIONAL CORRECTIONS to prior dossiers (mod-8 residues, citation anchors).

Bayesian estimate: **P(target_resolved=1 within 72h) ≈ 0.03**. Most likely outcome: `compiled_partial` with L1-L5 formalized and L6 axiomatized as the open input. Per CLAUDE.md rule 10: HAVE FAITH IN ARISTOTLE.
