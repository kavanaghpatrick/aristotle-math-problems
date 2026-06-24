# maverick: the self-similar recursion engine T_k = C_k + T_{k+1} (VERIFIED)

Builds on [[sumset_reduction_scaling]] (sumset) and [[modular_local_coverage]] (modular).
Notation: `T_k := ∑_{d∈D} d^k·B_d` (the level-k sumset; the open question is whether T_k is
cofinite for every k≥1 when D admissible, gcd(D)=1).

## THE RECURSION (verified exactly, D={3,4,5}, k=1,2 on [0,~2950])

The base-d digit recursion `B_d = d·B_d ⊔ (1 + d·B_d)` (lowest base-d digit is 0 or 1) lifts to
the sumset. Multiply by d^k and sum over D:

> **(R)**  `T_k = C_k + T_{k+1}`,  where  `C_k := { ∑_{d∈D} e_d·d^k : e_d ∈ {0,1} }`
> is a set of **2^|D| offsets** (the choice of lowest digit per base).

For D={3,4,5}: C_1 = {0,3,4,5,7,8,9,12}, C_2 = {0,9,16,25,34,41,50} (25=16+9 collides → 7 elts).

**Verified:** T_k = C_k + T_{k+1} as sets on [0, N−max C_k], exactly, for k=1,2.

## CONSEQUENCE 1 — monotonicity (verified). Since 0 ∈ C_k:
> `T_{k+1} ⊆ T_k`  ⟹  `n₀(k) ≤ n₀(k+1)` is FALSE direction; correctly **n₀ is non-decreasing in k**.

Verified T_{k+1} ⊊ T_k for k=1,2,3 (D={3,4,5}). So **cofiniteness gets HARDER as k grows.**
This is the precise reason the k=0 theorem (Alexeev) does NOT imply k≥1, and why n₀(k)→∞
(empirically 79, 77613, 4.3M, 69M). **No finite-N computation can settle the conjecture.**

## CONSEQUENCE 2 — unrolling. For every L ≥ 1:
> `T_0 = C_0 + C_1 + ⋯ + C_{L-1} + T_L`.
Since 0 ∈ T_L, `T_0 ⊇ C_0+⋯+C_{L-1}` = the "low-digit truncation" of T_0. (Consistency check, ✓.)

## THE OPEN STEP this isolates (hardest sub-lemma)

(R) reduces "T_k cofinite" to a **fixed-point / self-similar covering** problem:
T_k is the union of 2^|D| shifted copies of the SAME-SHAPE sparser set T_{k+1}.
This is exactly an **affine IFS (iterated function system) / self-similar set on ℤ**, with maps
x ↦ x + c for c ∈ C_k feeding T_{k+1}. Cofiniteness of T_k ⟺ the IFS attractor (run forward
through scales) tiles a cofinite set.

Two ingredients must combine (matches modular's split):
1. **LOCAL (residue):** modular's (L) — gcd(D)=1 ⟹ T_k ≡ ℤ/m for all m. [verified by me]
2. **GLOBAL (density/size):** ∑1/(d−1) ≥ 1 ⟹ the offset sets C_k are "dense enough" that the
   shifted copies of T_{k+1} overlap to fill intervals (no asymptotic density gap). This is the
   Pomerance density side; it's the carry-debt control modular flagged.

The clean target lemma I'm now chasing:
> **(★)** ∃ finite L and threshold such that C_0 + C_1 + ⋯ + C_{L-1} already covers a full
> residue system mod (something) AND has bounded gaps ⟹ adding the tail T_L (which contains 0
> and is cofinite mod every m) closes every interval. I.e. a quantitative "covering + density"
> bound uniform in k via the self-similar (R).

Status: (R), monotonicity, both consequences VERIFIED computationally. (★) in progress.
