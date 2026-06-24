# maverick: the box-counting density heuristic is WRONG; harmonic ∑1/(d−1) is the true threshold

This is a structural warning + diagnostic. It explains WHY the problem resists counting arguments
and confirms the harmonic condition is the genuine invariant (not a proxy).

## The wrong heuristic (do not use)
The "obvious" density count: |d^k·B_d ∩ [0,N]| ≈ N^{log2/log d}, so the sumset's box-counting
density exponent is ≈ min(1, ∑_d log2/log d). One might guess: cofinite ⟺ ∑_d log2/log d ≥ 1.

**This is FALSE.** Counterexamples (verified):

| D | ∑1/(d−1) | ∑ log2/log d | cofinite? (computed) |
|---|----------|--------------|----------------------|
| {3,4} | 0.833 (<1) | 1.131 (>1) | **NO** — missing set has POSITIVE density (~124k missing in (N/2,N] at N=10⁶) |
| {3,4,9} | 0.958 (<1) | 1.446 (>1) | **NO** — sparse persistent gaps, largest ~0.98N tracking N |
| {3,4,7} | 1.000 (=1) | 1.487 (>1) | YES (581) |
| {3,4,5} | 1.083 (>1) | 1.562 (>1) | YES (79) |

Both {3,4} and {3,4,9} have box-density exponent > 1 yet are NOT cofinite (Pomerance converse,
`erdos124.converse` in the Lean file). So the box-counting exponent **over-predicts** completeness.

## Why: the digit sets are CORRELATED
A naive sumset-density estimate assumes the three 0/1-digit sets behave like independent random
sets of their stated densities. They do NOT — base-d 0/1-digit numbers are the deterministic
Cantor-type set `B_d`, and the cross-base correlations (especially when bases share structure,
e.g. 4 and 9 = 2²,3²; or 3 and 9) suppress the effective density well below the box-counting value.
**The harmonic sum ∑1/(d−1) = ∑_d ∑_{j≥1} d^{−j} is the correct invariant** because it is the exact
"reciprocal-mass" that controls the Cassels/Birch filling condition (see [[maverick_bounded_gap_lemma]],
Lemma BG: the ratio ∑_{atoms<a}/a → ∑1/(d−1), and ≥1 is exactly the filling threshold). The
box-counting exponent is a red herring.

## Diagnostic value for the FALSIFICATION lane
Two distinct failure signatures when ∑1/(d−1) < 1:
- **{3,4}-type (positive-density complement):** missing set has positive density — gaps everywhere.
- **{3,4,9}-type (sparse-persistent complement):** few but unboundedly-large gaps (largest ~N).
Both are NOT-cofinite, but the second looks deceptively "almost cofinite" at small N. **Any team
member running a falsification search must check the complement's density in the UPPER half of the
window, not just "largest miss," and must push N well past d_max^k** (cf. breaker's stragglers
warning [[breaker_engine_and_347anomaly]]). A largest-miss ≈ N is the non-termination signal.

## Take-away for the proof
A pure counting/density argument CANNOT prove the conjecture (it would also "prove" {3,4} and
{3,4,9}, which are false). The proof must use the harmonic invariant + the gcd=1 residue structure
TOGETHER — exactly the two-engine synthesis in [[maverick_synthesis_two_engines]]. This is consistent
with scholar's finding that BEGL96's positive-density Theorem 1 does NOT reach the finite harmonic-
boundary regime.
