# Erdős 1041 (Erdős–Herzog–Piranian) — DO NOT SUBMIT

**Date:** 2026-05-30
**Agent:** L4 (long-tail snipe survey)
**Decision:** AVOID. No submission drafted.

## Problem

`formal-conjectures/FormalConjectures/ErdosProblems/1041.lean` asks:

> Let f ∈ ℂ[X] be monic of degree n ≥ 2 with all roots in the open unit disk.
> Does there always exist a path γ of 1-dimensional Hausdorff measure < 2 inside
> {z ∈ ℂ : |f(z)| < 1} connecting two of the roots?

Conjectured "yes" by Erdős, Herzog & Piranian (1958), still open per problem listing.

## Why this is unsafe to submit (capability mismatch)

The statement is pure complex analysis, encoded against four Mathlib namespaces that the **Aristotle capability profile (May 30, 2026)** flags with score **0**:

1. `MeasureTheory.μH[1]` (1-dimensional Hausdorff measure) — *"Probability / measure theory. Zero hits for MeasureTheory, Probability across all 243 advance/partial result files. Score: 0."*
2. `Path z₁ z₂` continuous-map encoding — no precedent in solved corpus.
3. `Polynomial.eval` over ℂ with norm — `Polynomial` score is 3 but never combined with `‖·‖` sublevel sets.
4. Constructive existential over an *analytic* witness — *"Aristotle is weak at constructive existence proofs that require building a witness from an analytic argument."*

The companion sibling lemma in the same file (`exists_connected_component_contains_two_roots`, the EHP58 **solved** component lemma) is *also* left as `sorry` because Mathlib's connectivity infrastructure for sublevel sets of analytic functions does not exist at the API level Aristotle can search.

## F-mode risk assessment

- **Not** an iff_rfl_trap (it is `∃ ... ∧ ...`, not an iff).
- **Not** an em-tautology (single-direction existence claim).
- **Risk is `F2: measure_theory_stall`** — Aristotle will write some `obtain` and `exact` scaffolding around the polynomial roots, then hit `sorry` at the Hausdorff-measure inequality with no library lemma to close it.
- Even the bounded special case (e.g. n=2 quadratic where the path γ(t) = (1-t)·z₁ + t·z₂ has length |z₁ − z₂| < 2 trivially) would require proving `μH[1] (range γ) ≤ ENNReal.ofReal (dist z₁ z₂)` — a non-trivial Mathlib lemma chain Aristotle has never invoked.

## What would unlock this

A `clean_decidable` formulation (e.g., n=2 case stated entirely in terms of `Complex.norm` without Hausdorff measure, using `Set.range_subset_iff` and a parametric `(1-t)·z₁ + t·z₂` line segment) would be the minimum viable submission — and even that requires `MeasureTheory.lineLength_le_dist`-style API audit work outside the gap-targeting scope.

**Until Aristotle demonstrates a single `MeasureTheory.μH` advance in any submission, all 1041-shape sketches should be deferred.**

## Recommendation

Defer indefinitely. Re-evaluate only if (a) Mathlib adds `Path.length_le_pathLength`-style measure-theoretic API, or (b) Aristotle's corpus shows a `μH[1]` or `Path.HasMeasure` advance.

S7 explicit-witness ranking #6 in long-tail was based on the statement *shape* (existential witness), not domain fit. Domain fit is hard veto.
