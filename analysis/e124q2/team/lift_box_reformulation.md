# The box/counting reformulation — average #reps provably →∞; the open kernel is min vs avg

**Author:** lift | **Status:** clean reformulation of the open kernel (both (BRIDGE) and Lemma A'),
with one ELEMENTARY half PROVEN-able and the hard half precisely isolated. Verified computations.

## The elementary half (provable): the AVERAGE representation count → ∞

Let r_D(n) = #{ (b_d)_{d∈D} : b_d ∈ B_d, ∑_d d^k b_d = n } be the representation count (k=1 here).
The counting exponent of B_d (the digit set, 0/1 base d) is e_d = log 2 / log d. By a box/convolution
count, the average of r_D over [X, 2X] is ~ X^{(∑_d e_d) − 1}.

> **Key inequality (PROVED, elementary):** e_d = log2/log d > 1/(d−1) for every d ≥ 3 (term-by-term,
> verified d=3..11 and provable by convexity). Hence **∑_d e_d > ∑_d 1/(d−1) ≥ 1** for EVERY
> admissible D. So the box-exponent ε := ∑e_d − 1 > 0 — even at the boundary ∑1/(d−1)=1
> ((3,4,7): ε=0.487; (3,5,7,13): ε=0.688). `/tmp/e124_box_exponent.py`.

So **the AVERAGE r_D(n) → ∞ for every admissible D** — this is elementary and uniform, no MW. (Note:
the relevant exponent for #reps is the COUNTING exponent log2/log d, which is strictly bigger than the
DENSITY/threshold invariant 1/(d−1) — that gap is why the average is comfortably supercritical even
when the threshold invariant is exactly critical.)

## The hard half (the open kernel): minimum vs average

Cofiniteness needs min_n r_D(n) ≥ 1 for large n, i.e. **min r_D ≥ 1**, not just avg → ∞. Measured
ratio min/avg over dyadic windows:
- (3,4,5): 0.26 → 0.40 (stable/growing).
- (3,4,7) boundary: 0.248 → 0.239 → 0.446 → 0.263 → **0.130** at [4·10⁶,6·10⁶] — it DIPS.
  (`/tmp/e124_minavg_trend.py`.) The dip is near the (3,4,7) k=2-threshold region (~4·10⁶) — exactly
  the straggler regime, exactly where the power-coincidence structure bites.

**So min/avg does NOT stay cleanly bounded below at the boundary — it dips at structured points.**
The dips are at the cross-base power near-coincidences (the MW spacing). Bounding min r_D away from 0
= controlling these dips = the equidistribution/MW content. NOT bypassed by the box average.

## Why this is the right reformulation

This recasts BOTH open kernels in one clean, fully-explicit form:
> **(KERNEL).** For admissible D, the explicit counting function r_D(n) satisfies r_D(n) ≥ 1 for all
> n > N₀ — equivalently, min_{n∈[X,2X]} r_D(n) / avg_{[X,2X]} r_D stays bounded below as X→∞.

- The AVERAGE → ∞ is PROVEN (box, elementary, ε>0 from the log2/logd > 1/(d−1) inequality).
- The MIN ≥ 1 is the open core. At ∑>1+δ (comfortably strict, no clustering) the dips are shallow and
  min/avg stays bounded (⟹ the winnable tier). At the boundary / clustered D, the dips reach toward 0
  at power-coincidences (⟹ MW/(BRIDGE)).

This is a cleaner statement of the open problem than "seed interval" or "+M-closure": it's the
minimum of one explicit, elementary counting function, with the average provably divergent. It also
makes the MW role transparent — MW controls how deep the dips go at power-coincidences.

## Honest takeaway (no breakthrough, but a clean frame)

The box argument does NOT bypass MW — it isolates exactly what MW must do (bound the min-to-avg dips
at coincidences), and proves the easy half (avg→∞) cleanly and uniformly. It does NOT give k=1
unconditionally (the dips are real, e.g. (3,4,7) min/avg=0.13 at 4·10⁶). So my earlier hope that the
box count closes k=1 is REFUTED by its own data — recorded honestly. The kernel (min r_D ≥ 1) is the
same difficulty as (BRIDGE)/(Lemma A'), now in its sharpest elementary form.

Cross-refs: lift_bridge_quantified.md (density-overlap = the min-coverage view), lift_classwise_seed_lemma.md
(the +M-closure view), cassels_strict_excess_theorem.md (Lemma A / m₀), lift_boundary_criticality.md.
