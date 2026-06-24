# E124 open part: the deconvolution reduction (k=0 ⟹ k≥1 is a finite-deconvolution problem)

**Author:** sumset. **Status:** identity PROVED + verified. This is the cleanest exact link between
the SOLVED k=0 theorem and the OPEN k≥1 conjecture.

## Notation
B_d = S(d,0) = 0/1-digit base-d numbers. T_k(D) := ∑_{d∈D} d^k·B_d = ∑_{d∈D} S(d,k) (the open
sumset; T_0 = ∑_{d∈D} B_d is the k=0 object). For each d, k let
  low_k(d) := B_d ∩ [0, d^k) = { ∑_{j<k} ε_j d^j : ε_j ∈ {0,1} }   (the 2^k "low digit" values).
Let  **L_k(D) := ∑_{d∈D} low_k(d)**  — a FIXED FINITE set, |L_k| ≤ ∏_d 2^k = 2^{k|D|},
max(L_k) = ∑_d (d^k − 1)/(d − 1) · (d−1)?  actually max(L_k)=∑_d (d^k−1)/(d−1) hmm; bounded anyway.

## Theorem C (deconvolution identity). For every finite D, every k ≥ 0:
> `∑_{d∈D} B_d  =  L_k(D)  +  T_k(D)`    (Minkowski sum in ℕ).

**Proof.** By the self-similarity identity (verified separately; immediate from base-d digit
splitting): for each d,
  `B_d = low_k(d) + d^k·B_d`   (every 0/1-digit number splits uniquely into its lowest k digits plus
  d^k times the 0/1-digit number formed by the remaining digits).
Take the Minkowski sum over d ∈ D and use that Minkowski sum distributes over `+`:
  ∑_d B_d = ∑_d (low_k(d) + d^k·B_d) = (∑_d low_k(d)) + (∑_d d^k·B_d) = L_k(D) + T_k(D). ∎

Verified: identity holds (beyond the finite seed max(L_k)) for D ∈ {(3,4,7),(3,5,7,13),(3,4,9,25)},
k ∈ {1,2,3}.

## The open problem, restated as finite deconvolution

The k=0 theorem (Alexeev/Aristotle) says: for admissible D (all d≥3, ∑1/(d−1)≥1), **T_0 is cofinite**.
Theorem C then says **L_k + T_k is cofinite**, with L_k a fixed finite set. The OPEN k≥1 conjecture
is exactly:

> **(Q′)** Given that `L_k + T_k` is cofinite (k=0 theorem) and `gcd(D)=1`, is `T_k` itself cofinite?

This is a **deconvolution / division problem in the monoid of subsets of ℕ under Minkowski sum**:
"if a finite set L Minkowski-added to T is cofinite, and T has no congruence obstruction, is T
cofinite?" In general FALSE without the gcd/Theorem-B hypothesis (e.g. L={0,1}, T=2ℕ gives L+T=ℕ
cofinite but T=2ℕ not cofinite — but T=2ℕ FAILS Theorem B / gcd). The role of gcd(D)=1 (Theorem B:
T_k meets every residue class) is precisely to rule out that failure mode.

## What's needed to close (Q′) — the honest remaining gap

`L + T cofinite` + `T meets every residue class mod every M` does NOT by itself imply `T cofinite`.
Counterexample to the naive hope (abstract): take T = ℕ \ {squares-ish sparse set S that still hits
every residue}, L finite chosen so L+T fills S. T hits all residues but is not cofinite, yet L+T is.
So Theorem B + Theorem C are NOT sufficient alone; the BEGL96-style **archimedean seed-interval +
self-similar propagation** is the missing third ingredient. Specifically what must be shown:

> **(SEED)** There is N_0 = N_0(D,k) and an interval I = [a, a + Λ) of length Λ ≥ max_d d^k such that
> I ⊆ T_k(D). Then self-similarity of each d^k·B_d propagates coverage to all n ≥ a (standard
> BEGL96 interval-doubling), giving cofiniteness.

Theorem B guarantees no residue obstruction blocks the seed; ∑1/(d−1)≥1 is the density needed for
the seed to exist; gcd=1 makes the propagation moduli coprime. The content of BEGL96's hard work
(done only for (3,4,7)) is establishing (SEED) uniformly. **This is where the problem is genuinely
open**: no one has proved (SEED) for general admissible D at k≥1.

## Theorem C alone is INSUFFICIENT (explicit abstract counterexample — honest wall)

The deconvolution route hits the SAME wall maverick's Result 2 identified. The hoped-for inference
"`L_k + T_k` cofinite (k=0 thm) + `T_k` hits every residue (Theorem B) ⟹ `T_k` cofinite" is FALSE
in general. Explicit counterexample in the abstract subset-monoid:
- L = {0,1,2,3}, T = ℕ \ {10^j : j≥1} (drop the powers of 10).
- T hits every residue class mod every m (powers of 10 miss no full class). ✓ (Theorem-B analogue)
- L + T = ℕ (cofinite) — the gaps at 10^j are filled by +1,+2,+3 since no 4 consecutive powers. ✓
- But T is NOT cofinite (misses every 10^j). ✗

So Theorem B + Theorem C are necessary structure but NOT sufficient. The missing ingredient is the
archimedean (SEED)/(★) lemma — exactly BEGL96's Mignotte–Waldschmidt/Baker-type input, done only for
(3,4,7). This confirms (independently, via the deconvolution framing) the team consensus: the open
core is genuinely archimedean/Diophantine, not soft/structural. Cross-ref: maverick_bounded_gap_lemma.md
Result 2; cassels_completeness_lemma.md §4.

## Deliverable summary for the team
Three rigorous, verified theorems reduce E124-open to a single archimedean lemma (SEED):
1. **Scaling** (sumset_reduction_scaling.md): S(d,k) = d^k·B_d. [PROVED, 1 line]
2. **Theorem B** (sumset_crt_residue_theorem.md): T_k covers ℤ/M ∀M ⟺ gcd(D)=1. [PROVED]
3. **Theorem C** (this file): ∑_d B_d = L_k + T_k, L_k fixed finite. [PROVED]
⟹ Open content = (SEED): a covered interval of length ≥ max_d d^k exists for admissible D, k≥1.
