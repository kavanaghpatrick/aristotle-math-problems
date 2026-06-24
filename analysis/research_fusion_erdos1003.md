# Research Fusion Analysis: Erdős 1003 (φ(n) = φ(n+1) Infinitely Often)

**Agent:** S6 of 10 (technique-scouting round 1) | **Date:** 2026-05-30
**Problem:** Are there infinitely many n such that φ(n) = φ(n+1)?
**Source:** erdosproblems.com/1003 ; formal-conjectures/FormalConjectures/ErdosProblems/1003.lean
**Status:** OPEN. C1 (D-team) flagged this as "slot737 DNA candidate" — high cross-domain unlocker potential.

---

## A. What is known (as of 2026)

1. **Erdős-Pomerance-Sárközy (1992)** — the count of n ≤ x with φ(n)=φ(n+1) is O(x · (log log x / log x)). So density is 0, but the upper bound does not rule out infinitude.
2. **Graham-Holt-Pomerance (1998)** — *Solutions to φ(x)=φ(x+k)*. For *general* shift k, most solutions come from a rigid prime-tuple construction. **Critical fact for E1003:** the construction is IMPOSSIBLE for k=1 (no j with rad(j) = rad(j+1) past trivial cases). So consecutive equal totients, if infinite, must come from an EXCEPTIONAL MECHANISM, not the standard family.
3. **Ford (1998 onward)** — *Distribution of totients*. V(x) = x/(log x)^{1+o(1)}. Globally, totient values are sparse, but this gives no adjacency control.
4. **Carmichael's conjecture** (still open) — every totient has ≥2 preimages. E1003 asks for adjacency-1 preimages infinitely often — strictly stronger and more local.
5. **Pollack (2024, arXiv:2406.12296)** — recent work supports view that "singleton" totients are extremely rare, but does not manufacture adjacency.
6. **Known small solutions** — n = 1, 3, 15, 104, 164, 194, 255, 495, 584, 975, ... — list extends to ~10^11 (Sloane A001274). All known solutions found by computer search; no infinite family known.

## B. Known partial structure (from Codex F8 / D-team)

**The 2^(2^r)-1 family.** For r ≥ 0:
  n = 2^(2^r) - 1 = F_0 F_1 ... F_{r-1}  where F_i = 2^(2^i)+1 are Fermat primes.
  Then φ(n) = ∏_{i<r}(F_i-1) = 2^(2^r-1) = φ(2^(2^r)) = φ(n+1).
  Gives n = 3, 15, 255, 65535, 4294967295. STOPS at r=5 because F_5 is composite.

This is the only known infinite-family-shaped construction. No analog identity is known.

**Why "twin-prime-like" route is wrong:** If n+1 = q prime > 2, then φ(n+1) = q-1 = n while φ(n) < n for n > 1. So we can't have prime n+1 except q=2,3. Prime-tuple constructions for general k don't apply at k=1.

**n = 2p ansatz constraint:** If n=2p, p odd prime, then φ(n) = p-1. For φ(2p+1) = p-1, the odd m = 2p+1 must satisfy m/φ(m) = 2 + 3/(p-1) > 2. But m/φ(m) = ∏_{q|m} q/(q-1), so m must be composite with ≥3 distinct odd prime factors, every q|m satisfying q-1 | p-1. Forces 2p+1 into rigid inverse-totient shape — sporadic at best.

## C. Adjacent-domain analogs

### C1. Inverse totient problem (number theory, adjacent)
The set φ^{-1}(m) is finite but can be large; the structure is sparse and irregular. Adjacency in domain is unrelated to adjacency in range. Methods: combinatorial sieves on prime tuples.

### C2. Prime gap problems (additive number theory)
The Erdős-Pomerance estimate uses similar sieve technology to twin-prime upper bounds. But twin primes get a positive-density-style result via Zhang-Maynard-Tao. E1003 has no analog of the GPY sieve because there's no "prime-tuple" generating set.

### C3. Singular Mahler measures / heights (Diophantine)
The 2^(2^r)-1 family is reminiscent of Lehmer's Mahler-measure problem: small heights are rare. Both feature a "Fermat-prime tower" rigidity. But Mahler measure is heights-based, totient is multiplicative — no direct map.

### C4. Random multiplicative functions
Bourgain-Sarnak-Ziegler / Tao have studied logs of random multiplicative functions. Heuristics for the count of pairs (n, n+1) with same arithmetic invariant.

## D. Where bare-gap attempts have failed (prior pipeline history)

Several Codex/v2/v3 attempts at slot737/slot~. Codex F8's analysis correctly diagnoses that:
- Bare submission of "∃^∞ n : φ(n)=φ(n+1)" gives Aristotle no fulcrum.
- A bounded statement "∃ n ∈ [N, 2N], φ(n)=φ(n+1)" can be verified by `native_decide` for any fixed N (trivially) but does not advance the gap.
- The gap is the *infinitude*, which requires structure not currently in Mathlib.

## E. Open methodological questions

- Is there a "multi-step" identity in inverse-totient theory that would give a new infinite family beyond 2^(2^r)-1?
- Can ergodic theory (Furstenberg correspondence) be applied to the indicator function 1_{φ(n)=φ(n+1)}? — note: the set has zero density.
- Could a *Diophantine* parametrization (e.g., polynomial identity that forces φ-equality) be discovered?

## F. Status assessment

OPEN since at least 1965 (Erdős posed it). Resisted attack for 60+ years. Plausibility of resolution in next 10 years: low (5-15% per our optimistic estimate) without a NEW STRUCTURAL IDEA.

**This is a high-quality candidate for technique-scout debate**: number-theoretic, deeply studied, with multiple identifiable obstructions, and a tantalizing single-family hint (Fermat tower) that does not generalize.
