# Summary of changes for run 73bbf0d0-012f-44bf-8b66-a190be1f15ec
I proved the scaling identity for `sumsOfDistinctPowers` (Erdős 124 structural reduction).

**What was done:**
- Created `RequestProject/Erdos124.lean` containing the definition `Erdos124.sumsOfDistinctPowers d k = {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d^i = x}` and the target theorem.
- Proved `erdos124_scaling (d k x : ℕ)`: `x ∈ sumsOfDistinctPowers d k ↔ d^k ∣ x ∧ (x / d^k) ∈ sumsOfDistinctPowers d 0`.

**Proof idea (verified and formalized):**
- *Forward:* if `x = ∑_{i∈s} d^i` with all `i ≥ k`, then using `d^i = d^k · d^(i-k)` and re-indexing via the injective map `i ↦ i - k` (`Finset.sum_image`), we get `x = d^k · y` with `y = ∑_{j} d^j ∈ sumsOfDistinctPowers d 0`, giving `d^k ∣ x` and `x / d^k = y`. The edge case `d^k = 0` (i.e. `d = 0`, `k ≥ 1`) forces `x = 0` and is handled separately via the empty Finset.
- *Backward:* if `d^k ∣ x` and `y = x/d^k = ∑_{j∈s'} d^j`, re-index via `j ↦ j + k` to obtain `∑_{i} d^i = d^k · y = x` with all exponents `≥ k`.

**Verification:** The file builds cleanly with no warnings, contains no `sorry`, and `#print axioms` shows it depends only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

This is the elementary reduction that rewrites the pointwise sumset `∑_{d∈D} sumsOfDistinctPowers d k` into the canonical form `∑_{d∈D} d^k · B_d` underlying the open BEGL96 case.