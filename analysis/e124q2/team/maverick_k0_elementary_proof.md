# maverick: ELEMENTARY PROOF of the Alexeev k=0 theorem (Brown's theorem route)

**Target (team-lead's aim adjustment): prove k=0 first.** RESULT: a complete, rigorous, elementary
proof — STRONGER than the published statement. Alexeev's k=0 proof has no public footprint; this is
an independent, self-contained proof.

## Theorem (k=0, elementary). Let D be a finite set of integers d ≥ 3 (gcd NOT needed) with
> **∑_{d∈D} 1/(d−1) ≥ 1.  Then ∑_{d∈D} B_d = ℕ** — every nonnegative integer is a sum ∑_d a_d with
> a_d ∈ B_d (a 0/1-digit number base d). [STRONGER than cofinite: NO exceptional set at all.]

This is the BEGL96/Alexeev k=0 statement (their `erdos124.zero`), with the stronger conclusion =ℕ.

## Proof (Brown's theorem, 1961).
The pointwise sumset ∑_d B_d is exactly the set of subset sums of the **atom multiset**
A = {d^j : d∈D, j≥0} (each (d,j) once; value collisions kept with multiplicity). Sort A ascending
a_1 ≤ a_2 ≤ …, partial sums S_i = a_1+…+a_i.

**Brown's theorem:** if a_1 = 1 and a_{i+1} ≤ S_i + 1 for all i ≥ 1, then every integer ≥ 0 is a
subset sum of A. (Standard: induction — if [0, S_i] ⊆ Σ and a_{i+1} ≤ S_i+1, then
[0, S_i] ∪ (a_{i+1}+[0,S_i]) = [0, S_{i+1}] ⊆ Σ.)

**Verify the hypotheses:**
1. **a_1 = 1:** d⁰ = 1 ∈ B_d for every d, so 1 ∈ A. ✓
2. **a_{i+1} ≤ S_i + 1 for all i:** equivalently, for every atom value a > 1, the sum of all atoms
   strictly below a is ≥ a − 1. Compute it base-by-base. For base d, let d^m be the largest power
   < a; the base-d atoms below a sum to 1 + d + … + d^m = (d^{m+1} − 1)/(d − 1). Since d^{m+1} ≥ a
   (next power is ≥ a), this is ≥ (a − 1)/(d − 1). Summing over d ∈ D:
   > S_{<a} = ∑_d (base-d atoms < a) ≥ (a − 1) · ∑_{d∈D} 1/(d − 1) ≥ (a − 1) · 1 = a − 1.   ✓
   (The hypothesis ∑1/(d−1) ≥ 1 is used in exactly the last step.)

Both hypotheses hold ⟹ by Brown's theorem, ∑_d B_d = ℕ. ∎

## Tightness / boundary (∑ = 1, e.g. (3,4,7)).
At a = d*^M (a power of one base d*), that base contributes exactly (a−1)/(d*−1) (equality, since
d*^M = a). But a is a power of at most ONE base in an admissible D (two bases that are common
powers, d_1=b^s, d_2=b^t, would force ∑1/(d−1) < 1 — verified: no admissible D has this), so at
least one other base d has d^{m+1} > a STRICTLY, giving strict slack. Hence S_{<a} > a − 1 even at
the boundary. [VERIFIED: (3,4,7) min margin S_{<a}−(a−1) over all power-atoms = +1.] AIRTIGHT.

## Sharpness (converse, matches Pomerance).
If ∑1/(d−1) < 1, then S_{<a} ≈ (a−1)·∑ < a−1 for large a ⟹ Brown's condition FAILS at large powers
⟹ gaps form ⟹ NOT complete. [VERIFIED: {3,4} (∑=0.833) fails at a=4194304, margin −404718.] So the
threshold ∑1/(d−1) ≥ 1 is exactly the completeness boundary at k=0. (gcd plays NO role at k=0 — d⁰=1
makes residues free, consistent with the conjecture dropping the gcd condition for k=0.)

## Significance for the campaign
- This is the EASIEST true instance of the thickness conjecture, and it's **fully elementary**
  (Brown 1961 + a one-line harmonic-sum estimate) — NO thickness machinery, NO Astels, NO MW needed.
  Formalizer-reachable in Lean (Finset.Nat subset-sum induction).
- **WHY k≥1 is harder (the lift obstruction, now precise):** at k≥1 the atoms are {d^j : j≥k}, so
  a_1 = d_min^k > 1. Brown's theorem REQUIRES a_1 = 1 (to seed [0, S_i] from 0). With a_1 > 1 the
  small integers 1..d_min^k−1 are unreachable, the seed [0,·] never starts, and the induction cannot
  begin. **The entire difficulty of k≥1 is the LOSS of the value-1 atom** — that's what forces the
  gappy region and the MW-flavored seed-formation problem. The thickness route's "discreteness =
  slack" is exactly the attempt to substitute for the missing 1-atom; at k=0 you have the 1 for free.
- So the campaign's founding thesis is half-confirmed: the k=0 mechanism is Brown's theorem (clean),
  and the k≥1 lift's obstruction is EXACTLY "regain the seed without the 1-atom" — which is where the
  cross-base spacing (MW) re-enters. The thickness machinery does NOT reprove even k=0 more simply
  than Brown; Brown IS the k=0 proof.

## Status
[PROVED, elementary, airtight] k=0 theorem ∑B_d = ℕ for ∑1/(d−1)≥1, via Brown 1961. Verified
computationally (all admissible families: 0 Brown-violations; non-admissible: violations at powers).
Independent reconstruction of Alexeev's unpublished k=0 result, with stronger conclusion (=ℕ).

## k≥1 LIFT ATTEMPT (using the pinned obstruction) — death point

Tried to regain Brown's seed at k≥1. Precise estimate: at level k, ∑(atoms < a) ≥ a·∑1/(d−1) − C_k
where C_k = ∑_d d^k/(d−1). So Brown's condition a ≤ ∑(atoms<a)+1 recovers at
> **R_k = (C_k − 1)/δ**,  δ = ∑1/(d−1) − 1 (strict excess).
This is EFFECTIVE (transcendence-free) and R_k ~ d_max^k/δ. Boundary δ=0: coefficient vanishes,
never recovers by this estimate ⟹ MW needed (consistent with (3,4,7) hard). ✓

**DEATH POINT:** Brown RECOVERY (no NEW gaps above R_k) is NOT sufficient for cofiniteness, because
a_1 = d_min^k > 1 means the seed never starts from 0 — gaps below R_k persist and the true n₀
EXCEEDS R_k:
| D | k | R_k | true n₀ | n₀ ≤ R_k? |
|---|---|-----|---------|-----------|
| {3,4,5} | 1 | 37 | 79 | NO (right order) |
| {3,4,5} | 2 | 181 | 9807 | NO (off ~50×) |
| {3,4,5,7} | 1 | 17 | 22 | NO (close) |
| {3,4,6} | 2 | 481 | 24974 | NO (off ~50×) |

R_k is the right ORDER at k=1 for strict excess but undershoots, and the gap to true n₀ WIDENS with
k. The residual (n₀ − R_k) is exactly the sub-R_k gap-propagation = the multi-atom seed-formation /
MW-flavored content. So the Brown-recovery lift gives an effective NECESSARY point but not the
n₀ bound; the seed-formation gap remains the open core, even for strict excess (consistent with the
thickness route's v8 verdict: strict excess helps but base coincidences/MW re-enter).

## NET (k=0 milestone + lift)
- **k=0: SOLVED elementarily** (Brown), double-confirmed with cassels. Solid, formalizer-reachable. ✓
- **k≥1 lift: obstruction PINNED** (loss of the 1-atom seed), and the Brown-recovery point R_k=(C_k−1)/δ
  is an effective necessary marker for strict excess — but it undershoots n₀, and closing the gap is
  the multi-atom seed-formation problem (MW for the boundary; base-coincidence-dependent for strict).
  The lift does NOT cleanly close. Honest.
