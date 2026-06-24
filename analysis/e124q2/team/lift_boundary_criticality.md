# E124: the boundary ∑1/(d−1)=1 is a CRITICAL regime — why it's hard, and where slack lives

**Author:** lift | **Status:** Computational characterization (validated framework). Sharpens the
location of the open difficulty and informs strategy for the whole team.

## The representation-count measurement

Define r(n) = number of distinct subset-sum representations of n by the atom multiset
A(D,k) = {d^j : d∈D, j≥k}. (Each atom usable once; this is exactly "n ∈ T(D,k)" with multiplicity.)
Computed via standard subset-sum DP (`/tmp/e124_selfsim.py`, `/tmp/e124_supercrit.py`).

For large n (~3000), k=1, the MINIMUM of r(n) over a 500-wide window:

| D | ∑1/(d−1) | min r(n), n~3000 | median r(n) | regime |
|---|----------|------------------|-------------|--------|
| (3,4,7) | **1.000** | **3** | 12 | CRITICAL (boundary) |
| (3,4,5) | 1.083 | 7 | 18 | slightly super |
| (4,5,6,7,8) | 1.093 | **208** | 235 | robustly super |

Note (3,4,5) and (4,5,6,7,8) have nearly identical harmonic sums (1.083 vs 1.093) but wildly
different min-rep (7 vs 208): having MORE bases (5 vs 3) — i.e. more independent "coins" — also
fattens the representation count even at similar harmonic sum.

## Interpretation: ∑1/(d−1)=1 is a phase-transition boundary

The harmonic sum ∑1/(d−1) = ∑_d ∑_{j≥1} d^{−j} is the expected number of atoms in a "random" dyadic
window, i.e. the branching ratio of the representation process. At ∑=1 the process is **critical**:
the count of representations of a large n neither grows nor dies on average, and the MINIMUM over
windows stays O(1) — some n are barely (singly) representable arbitrarily far out. Above 1, the
process is supercritical and r(n) → ∞, giving slack.

**This is the precise reason the boundary case is genuinely hard:**
- A SOFT argument (second-moment / density / counting) needs r(n) > 0 to be *robust* — it proves
  "most n are representable" or "r(n) is large." At the boundary r(n) can dip to 1, so soft methods
  cannot rule out a SINGLE missed value; they leave an unbounded set of potential exceptions.
- To close the boundary case you must rule out near-misses EXACTLY. For (3,4,7) BEGL96 did this with
  the Mignotte–Waldschmidt lower bound on |3^p − 4^q| — a HARD transcendence input that controls the
  finest spacing of atoms. There is no soft substitute at criticality.

## Strategic consequences for the team

1. **Two genuinely different sub-regimes of the open conjecture:**
   - **∑1/(d−1) > 1 (strict):** supercritical, r(n)→∞. A density/counting proof should work and is
     the realistic target for a GENERAL theorem. This is the softer, more attackable half.
   - **∑1/(d−1) = 1 (exact boundary):** critical. Requires transcendence/Baker-type per-base-pair
     gap bounds (generalizing MW |3^p−4^q|). This is the genuinely hard half; even (3,4,7) only fell
     to a specialized 2-logs estimate, and only for k=1 in print.

2. **The conjecture's `≥ 1` (not `> 1`) is what makes it deep.** If the conjecture were stated with
   strict `> 1`, it would likely be provable by density methods (and liftable to k≥1 via sumset's
   Theorem B for residues + supercritical density). The closure of the boundary is the real prize.

3. **For Aristotle / a formalization attempt:** the supercritical case (∑ > 1) is the tractable lane.
   The boundary case (∑ = 1) needs Mathlib's transcendence machinery (linear forms in logarithms /
   Baker's theorem), which is largely absent from Mathlib — a serious formalization obstacle
   independent of whether the math is known.

## Relation to k≥1 (the lift)

The criticality phenomenon is k-UNIFORM: the branching ratio ∑1/(d−1) does not depend on k (the d^k
scaling multiplies all atoms but preserves their relative density / the harmonic sum). So the
critical-vs-supercritical dichotomy is the SAME at every k. What k changes is only the modulus in the
residue-covering step (sumset Theorem B: need gcd(D)=1) and the seed-interval length (∼ d_max^k).
**Net:** the k≥1 difficulty = (k=0 boundary difficulty) + (residue covering, which gcd=1 fully
solves). The boundary density argument is the shared hard core at every k.

## Files / cross-refs
- lift_gcd_necessity.md (gcd=1 necessary), lift_sufficiency_mechanism.md (residue lemma / 2-ingredient),
  lift_347_allk_and_validation.md (BEGL96 only proves k=1; 4 published constants reproduced).
- sumset_crt_residue_theorem.md (Theorem B — residue covering ⟺ gcd=1, the general form).
- scholar_BEGL96_proof_dissected.md (Theorem 1 needs β>2 + positive upper density; boundary uncovered).
