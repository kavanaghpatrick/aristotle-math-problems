# Summary of changes for run 7b17dcd4-de9e-4fa2-b28c-fac0e6a5fcbf
## Erdős 124 — (3,4,7) case for k=2: status and contribution

**This is an open problem, and it remains open.** The requested theorem `erdos124_347_k2` (every `n > 3 982 888` lies in `3²·B₃ + 4²·B₄ + 7²·B₇`) is stated faithfully in `RequestProject/Main.lean` against the exact requested signature, with `sumsOfDistinctPowers d k` defined as the sums of distinct powers `d^j` with exponents `j ≥ k`. It is left as `sorry`.

### What I established (genuine results, no `sorry`, only standard axioms)
I reduced the tail theorem to a single arithmetic inequality and machine-verified the finite crux:

- `baseCovered31_true` (`native_decide`, 34M-entry reachability check): with the atom set `{3²..3¹⁵, 4²..4¹¹, 7²..7⁸}` (sum `33 841 349`), **every `n ∈ [3 982 889, 29 858 460]` is a subset sum** — i.e. the symmetric gap-free middle `(N₀, Σ_base − N₀)` of the base case holds.
- `gapLemma_verified_1e30` (`native_decide`): the **gap lemma** `atomSum(<v) ≥ v + 2·N₀` holds for every atom `v > 3¹⁵` up to `10³⁰` (the margin is positive throughout, minimised at `7⁹`).

### The reduction (documented in `PROOF_NOTES.md`)
1. **Symmetry**: for any finite atom set, the subset-sum set is symmetric about its total, so its gap-free region is exactly `(N₀, Σ − N₀)`.
2. **Symmetric interval-doubling induction**: adding the next atom `v` extends gap-freeness precisely when `v ≤ Σ_{<v} − 2N₀` (the gap lemma). The base case is `baseCovered31_true` (the base must include `3¹⁵`, the unique atom that would otherwise violate the condition).
3. Together these give `(N₀, ∞) ⊆ R`.

Everything except the gap lemma is elementary and (for the base) machine-verified.

### Why it stays open
The gap lemma's tail is the genuine kernel. Elementary bounds give only `atomSum(<v) ≥ v − 18`; the missing slack `+2N₀` is the weighted distance from `v` to the next powers of the other two bases, which collapses at power near-coincidences `3^p ≈ 4^q ≈ 7^r`. Bounding these away requires **effective lower bounds for linear forms in logarithms (Mignotte–Waldschmidt)** — the same tool BEGL96 used for the `k=1` value `581`. This machinery is neither elementary nor present in Mathlib, so a complete formal proof is not currently attainable. An automated proof attempt confirmed the gap-lemma inequality is exactly the blocking step.

### Files
- `RequestProject/Main.lean` — definitions, the two verified computational facts, and the stated (open) theorem.
- `PROOF_NOTES.md` — the full reduction, the symmetry/doubling argument, the base-case choice, and the precise open kernel.

The project builds successfully (the only `sorry` is the open main theorem).