# Summary of changes for run 4066c8ad-eadd-4fba-ad9e-5d3d5167d6ca
## Erdős Problem 251: Irrationality of Σ p_n / 2^n

### Status
This is an **open conjecture** (Erdős 1988). The main irrationality statement remains as `sorry` since no valid proof is known.

### Critical Analysis of the Proposed Proof Outline

I carefully analyzed the proposed proof outline (digit periodicity + Guth-Maynard). The outline has **fundamental flaws**:

1. **Step 3 (carry analysis) is incorrect**: The tail R_N · 2^N = p_{N+1} + p_{N+2}/2 + p_{N+3}/4 + ... has a secondary sum ≈ p_{N+1} (not ≪ p_{N+1}), so ⌊R_N · 2^N⌋ ≈ 2p_{N+1}, not p_{N+1}. The binary digits of S are NOT simply the binary digits of individual primes.

2. **Step 6 (Guth-Maynard application)**: The result on primes in short intervals does not directly yield the claimed "binary pattern diversity" bound, and in any case is not formalized in Mathlib.

3. **Finite-state predictor argument**: Eventual periodicity of binary digits does not translate into a finite-to-one map on primes in the clean way claimed.

### What Was Proved (in `Erdos251.lean`)

I developed substantial new mathematical infrastructure:

1. **Chebyshev-type lower bound on π(x)** via the central binomial coefficient:
   - `centralBinom_le_pow_primeCounting`: C(2n,n) ≤ (2n)^{π(2n)} — each prime power factor of C(2n,n) is ≤ 2n
   - `four_pow_le_pow_primeCounting_succ`: 4^n ≤ (2n)^{π(2n)+1} — combining with Mathlib's 4^n ≤ 2n·C(2n,n)

2. **Exponential vs polynomial growth**:
   - `sq_lt_two_pow_pred`: n² < 2^{n-1} for n ≥ 7 (by induction)
   - `pow_lt_two_pow_sq_pred`: n^{2(n+1)} < 2^{n²-1} for n ≥ 7

3. **Prime counting lower bound**:
   - `primeCounting_sq_ge`: π(n²) ≥ n+1 for n ≥ 7 (by contradiction using the Chebyshev bound)

4. **Polynomial bound on the n-th prime**:
   - `nthPrime_le_sq`: p_n ≤ n² for n ≥ 6

5. **Summability of the series**:
   - `summable_nthPrime_div_two_pow`: Σ p_n/2^n converges (by comparison with Σ n²/2^n)

The summability result is particularly notable — previous attempts (slots 699, 704, 1219) all failed to prove it, managing only the weaker Bertrand-based bound p_n ≤ 2^{n+1} which is insufficient. The key innovation here was developing a Chebyshev-type lower bound on π(x) from scratch using Mathlib's central binomial coefficient infrastructure, yielding the polynomial bound p_n ≤ n² that makes summability provable.

### Files
- `Erdos251.lean` — Main development with all proofs (only `erdos_251` itself uses `sorry`)
- `slot699_result.lean`, `slot704_result.lean` — Previous partial attempts (unchanged)