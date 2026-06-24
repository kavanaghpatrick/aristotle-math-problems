# Aristotle Smoke Test — Euclid's Infinitude of Primes

**Date:** 2026-05-30
**Aristotle Project UUID:** `8d500201-0786-4bb2-8489-2f6aad91be91`
**Submitted by:** I9 informal-mode adapter (`scripts/aristotle_informal.py`)
**Endpoint:** `https://aristotle.harmonic.fun`
**SDK:** `aristotlelib 0.7.0`
**Status:** Compiled clean. No `sorry`. Standard axioms only.

---

## Canonical Reference Status

This document is the **canonical "what informal-mode output looks like"** reference for the Aristotle pipeline. Promoted from `submissions/nu4_final/i9_extracted/f9e23cf2-55f2-4eab-940c-6c06e79f54e5_aristotle/` (the I9 smoke-test extraction directory). Any future ambiguity about whether a submission engaged Aristotle's lemma-based informal reasoner (subsystem #2) versus its MCGS formalizer (subsystem #1) should be resolved by comparing the result format to this artifact.

---

## What This Demonstrates

**Empirical confirmation of W8's hypothesis that bare-Lean submissions only invoke subsystem #1; informal-mode prompts engage subsystem #2.**

The I9 adapter (`scripts/aristotle_informal.py`) constructs an informal-mode prompt at submission time from a `.fusion.json` companion. When that prompt has no Lean tarball and is framed as a natural-language problem statement (per W8 §3, arXiv:2510.01346 §3), Aristotle routes through its lemma-based informal-reasoning system rather than running MCGS goal search against a `theorem ... := by sorry` skeleton.

The output below is **qualitatively different** from typical BARE-mode submissions:

- BARE-mode output: a single `.lean` file with `theorem name : type := by <tactic>` and possibly some comments. No separate informal narrative. No "Informal proof:" section. No "Formalization:" section explaining the choice of Mathlib lemmas.
- This informal-mode output: an `ARISTOTLE_SUMMARY.md` file with explicit sections — an **"Informal proof"** section stating Euclid's argument in English, followed by a **"Formalization"** section explaining how the Lean proof maps onto Mathlib (`Nat.exists_infinite_primes`). The `.lean` file itself is a minimal wrapper.

This two-channel response — formal Lean + informal strategic narrative — is the canonical fusion-lane / informal-lane payload signature.

---

## Provenance Chain

```
Sketch:        /tmp/i9_smoke_sketch.txt              (bare gap, ≤30 lines)
Companion:     /tmp/i9_smoke_sketch.fusion.json      (informal proof outline)
Adapter:       scripts/aristotle_informal.py         (assembles informal-mode prompt)
SDK call:      Project.create(prompt=<assembled>, tar_file_path=None)
                                                     ^^^^^^^^^^^^^^^^^^^
                                                     no Lean tarball
Project UUID:  8d500201-0786-4bb2-8489-2f6aad91be91
Result tarball: submissions/nu4_final/i9_extracted/
               └─ f9e23cf2-55f2-4eab-940c-6c06e79f54e5_aristotle/
                  ├─ ARISTOTLE_SUMMARY.md            (informal proof + formalization)
                  └─ RequestProject/Main.lean        (Lean source)
```

The `f9e23cf2-...` directory inside `i9_extracted/` is the Aristotle-side result-bundle UUID for the response artifact; `8d500201-...` is the project UUID. They are distinct identifiers.

---

## Verbatim ARISTOTLE_SUMMARY.md

```markdown
# Summary of changes for run f9e23cf2-55f2-4eab-940c-6c06e79f54e5
## Infinitude of Primes — Proved ✓

**Theorem:** For every natural number `n`, there exists a prime `p > n`.

**Informal proof (Euclid's argument):**
Given `n`, consider `N = n! + 1`. Since `N ≥ 2`, it has a prime factor `p`. Since every prime `≤ n` divides `n!`, none of them can divide `n! + 1 = N` (as that would force `p | 1`). Hence `p > n`.

**Formalization:**
The proof leverages Mathlib's `Nat.exists_infinite_primes` (which provides a prime `p ≥ n+1`) and wraps it to match the required signature `∃ p, n < p ∧ Nat.Prime p`.

**File:** `RequestProject/Main.lean`

```lean
theorem i9_smoke_infinitude_primes (n : ℕ) : ∃ p, n < p ∧ Nat.Prime p := by
  exact Exists.imp ( by tauto ) ( Nat.exists_infinite_primes ( n + 1 ) )
```

The proof compiles successfully with no `sorry`, and depends only on standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
```

---

## Verbatim Main.lean

```lean
import Mathlib

theorem i9_smoke_infinitude_primes (n : ℕ) : ∃ p, n < p ∧ Nat.Prime p := by
  exact Exists.imp ( by tauto ) ( Nat.exists_infinite_primes ( n + 1 ) )
```

---

## What This Output Format Tells Us

1. **Two distinct artifacts.** `ARISTOTLE_SUMMARY.md` is not a comment block inside the `.lean` file; it is a standalone Markdown document. The informal reasoner produced it.
2. **Explicit "Informal proof:" header.** This is the literal subsystem-#2 signature. Bare-mode submissions never produce this header.
3. **Explicit "Formalization:" header.** The reasoner explains its choice of Mathlib lemma (`Nat.exists_infinite_primes`) in natural language, then provides the wrapped Lean form. This is the autoformalization step Harmonic describes in arXiv:2510.01346 §3.
4. **Minimal Lean wrapper.** Only 2 lines of proof. MCGS could have produced this, but the surrounding narrative is the load-bearing evidence that the informal reasoner was engaged first.
5. **Standard axioms only.** No new axiomatization smuggled in. The proof depends on `propext`, `Classical.choice`, `Quot.sound` only — the Mathlib defaults.

---

## How to Use This Reference

When auditing a future submission:

- **Look for `ARISTOTLE_SUMMARY.md` in the result tarball.** If present with "Informal proof:" + "Formalization:" sections, subsystem #2 was engaged.
- **Look for two-channel output.** Standalone Markdown + Lean file = informal mode. Lean file only = bare/MCGS mode.
- **Use the four S10 validation criteria** (per `docs/e938_fusion_validation_watch.md`) to determine whether the strategic content from the companion JSON actually drove the reasoner's decomposition.

This Euclid result is the **calibration baseline**. Future fusion / informal lane submissions should produce output of this same shape (or better — with richer NL trace, cross-domain citations, lemma decomposition) for the lane to be considered validated.

---

## Cross-References

- I9 infrastructure note: `docs/infrastructure_changes_may30/I9_informal_mode.md`
- W8 finding (Aristotle subsystems): `analysis/web_research_synthesis.md`
- Harmonic paper §3: arXiv:2510.01346
- S10 four-criteria pivot rule: `docs/e938_fusion_validation_watch.md` §106–113
- Lane usage matrix: `docs/lane_routing_matrix.md`
- Aristotle usage guide: `docs/aristotle_usage_guide.md`
- E938 fusion validation watch: `docs/e938_fusion_validation_watch.md`
