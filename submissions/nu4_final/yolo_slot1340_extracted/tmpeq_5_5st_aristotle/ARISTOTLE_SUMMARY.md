# Summary of changes for run a8561426-86aa-42c0-ab51-b5344e9a488f
## Erdős 142 — Quantitative Roth Bound: Results

### What was accomplished

The sorry in the slot-1320 formalization has been **partially closed** — the core mathematical argument is now fully formalized, conditional on the Bloom–Sisask bound.

### Key theorem proved

**`rothNumberNat_times_log_eventually_lt_of_bloomSisask`** — Fully proven (no sorry, standard axioms only):
```
BloomSisakBound → ∃ N₁, ∀ N ≥ N₁, r₃(N) · log(N) < N
```

This takes the Bloom–Sisask 2020 bound (r₃(N) ≤ C·N/(log N)^{1+c} for absolute c, C > 0) as an explicit hypothesis and derives the target inequality via real-analysis asymptotics:
- Since c > 0, (log N)^c → ∞, so eventually C/(log N)^c < 1
- Multiplying the Bloom–Sisask bound by log N gives r₃(N)·log(N) ≤ C·N/(log N)^c < N

### Remaining sorry

The unconditional statements `rothNumberNat_times_log_eventually_lt` and `erdos_142_quantitative_roth_lever` retain a single `sorry` — this sorry is **isolated to instantiating the `BloomSisakBound` hypothesis**, i.e., the Bloom–Sisask 2020 bound itself (arXiv:2007.03528, Thm 1.1), which is not formalized in Mathlib.

### Design choice: hypothesis instead of axiom

Rather than introducing an `axiom` declaration (which would compromise proof soundness and introduce non-standard axioms into `#print axioms`), the Bloom–Sisask bound is stated as a `def BloomSisakBound : Prop` and passed as an explicit hypothesis. This cleanly separates the formalized deduction (fully verified) from the unformalized deep result (marked with sorry), and ensures the conditional theorem depends only on standard axioms (propext, Classical.choice, Quot.sound).

### File structure

- `Main.lean` — Contains all definitions, the conditional theorem (proven), and the unconditional statements (1 sorry marking the Bloom–Sisask gap)

# Summary of changes for run 7353e4d7-230f-49b6-9849-a4c508c830dc
## Erdős Problem 142 — Formalization Results

### What was accomplished

The file `RequestProject/Main.lean` contains a complete formalization of Erdős Problem 142 (finite threshold version), with the proof structure cleanly separated into:

1. **Definition of `Set.IsAPOfLengthFree.maxCard`** — defined as `rothNumberNat N` for k=3 (the standard additive Roth number from Mathlib's `Combinatorics.Additive.AP.Three.Defs`).

2. **Main theorem `erdos_142_finite_threshold`** — fully proven, assuming the deep bound below. The deduction is verified by Lean: given the deep bound, we obtain N₁ and take N₀ = N₁; for every N ∈ [N₀, N₀ + 10⁶] we have N ≥ N₁, so the bound applies.

3. **One remaining sorry: `rothNumberNat_times_log_eventually_lt`** — states that ∃ N₁, ∀ N ≥ N₁, r₃(N) · log(N) < N.

### Why the sorry cannot be eliminated with current Mathlib

This sorry encapsulates a deep result in additive combinatorics that is **not yet formalized in Mathlib**:

- **What Mathlib has:** `rothNumberNat_isLittleO_id` proves r₃(N) = o(N) via the corners theorem and Szemerédi regularity. This only gives r₃(N)/N → 0, which is strictly weaker than what's needed.

- **What's needed:** r₃(N) = o(N/log N), which requires a *quantitative* upper bound like:
  - Bloom–Sisask (2020): r₃(N) ≤ C·N/(log N)^{1+c} for some c > 0
  - Kelley–Meka (2023): r₃(N) ≤ C·N·exp(-c·(log N)^{1/12})
  
  Either bound implies r₃(N)·log(N) < N for large N, but neither is formalized.

- **Why the existing quantitative bound fails:** The Szemerédi regularity approach in Mathlib (`roth_3ap_theorem_nat` via `cornersTheoremBound`) gives tower-type thresholds. For any density parameter ε, the threshold `cornersTheoremBound(ε/3)` is a tower of exponentials of height ~1/ε⁵, which vastly exceeds e^{1/ε}. This makes it impossible to find an interval where both ε·N < N/log(N) and N ≥ cornersTheoremBound(ε/3) hold simultaneously.

### Summary

The formalization is as complete as current Mathlib allows. The main theorem's proof is verified, and the single sorry is isolated to exactly the deep analytic number theory result (Bloom–Sisask / Kelley–Meka upper bound on the Roth number) that Mathlib lists as a TODO.