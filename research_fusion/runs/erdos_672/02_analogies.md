# Erdős 672 — Stage 2 Analogies (k = 4, ℓ = 3)

## Cross-domain hooks explored

### Hook A: Extremal set theory / EKR-shifted-AP transplant (REJECTED)

The original moonshot prompt suggested replacing the Mordell-Weil rank step
with an Erdős-Ko-Rado intersection bound on shifted-AP families.

**Verdict (Grok, May 30 2026)**: Not viable. The obstruction in E672 is
*arithmetic*, not combinatorial. The condition "n(n+d)(n+2d)(n+3d) is a cube"
is not monotone, EKR-style intersection bounds do not control the 3-adic
valuation vector `(v_3(n+id))_{i=0..3}` required for a cube, and there is no
existing density-bound transplant strong enough to dominate the
`max(d,N)^{3/7-eps}` window from Bajpai-Bennett-Chan 2023.

Tokushige's 2021 hypergraph-Hoffman framework (intersection density on shifted
families) does not extend to non-monotone arithmetic conditions.
Reference: Tokushige, "Application of hypergraph Hoffman's bound to
intersecting families" (2021/2022).

### Hook B: Thue + Frey curve + Bennett-Skinner level-lowering (LOAD-BEARING)

This is the actual published proof technique chain, transplanted across
several papers (BBGH 2006, GHP 2009, HTT 2009). The structure for `(k=4, l=3)`:

1. Reduce `prod_{i=0..3}(n + i*d) = y^3` with `gcd(n,d) = 1` to a finite
   list of *ternary equations* of the form `A*X^3 + B*Y^3 = C*Z^l`
   where `A, B, C` are smooth (supported on `{2, 3}`) and `(X, Y, Z)`
   are coprime.

2. Attach to each ternary equation a Frey curve, which is modular
   (Wiles-Taylor) of some computable level.

3. Apply Bennett-Skinner level-lowering to land in `S_2(Gamma_0(N))`
   for `N` divisible only by primes in `{2, 3}` plus controlled factors.

4. Verify computationally that the newform space at the target level is
   trivial (using LMFDB or Magma).

5. Conclude no solution exists.

For `(k=4, l=3)` specifically, HTT 2009 carry out steps 1-5 in detail.
The exact list of ternary equations is small enough to enumerate.

### Hook C: Hypergeometric method / Baker linear forms (BACKUP)

Bilu-Hanrot-Voutier's primitive-divisor result and Baker's linear-forms-in-logs
machinery give an effective version of step 1: the Thue equations have at most
a known bounded number of solutions, and the bounds are explicit. For
`(k=4, l=3)` the bounds are well below `10^4` and a finite enumeration closes
the remaining case after step 3.

## Why Hook B is right for (k=4, l=3)

- The proof is *published*. We are not asking Aristotle to find a new proof;
  we are asking it to formalize a known proof.
- The required Mathlib infrastructure (Frey curves, modularity statements,
  Galois representations) is partially present and growing.
- Aristotle's informal reasoner has been documented (Boris Alexeev's E124
  experience) to perform well when the named-technique chain is provided
  and the proof is "lowest hanging fruit" relative to the technique.

## Why Hook A is the wrong shape

Extremal-combinatorics methods *count* configurations. The (k=4, l=3) problem
asks for *non-existence*, not bounded density. An EKR-style upper bound on
counting cube-product APs to height `X` would saturate at `O(X^0)` only after
the arithmetic constraints close the geometry, which is the very step we
were trying to replace.
