---
spec: erdos389-850-assessment
phase: research
created: 2026-03-13
---

# Research: Erdos 389 and 850 Tractability Assessment

## Executive Summary

**Erdos 389 is a brick wall. Erdos 850 has produced real infrastructure but cannot be resolved without ABC-conjecture-level machinery. Both are likely intractable for Aristotle.** The evidence from 10+ submissions and 3 Aristotle runs per problem is overwhelming: Aristotle builds impressive scaffolding but cannot close the core gap. Recommend deprioritizing both.

## Erdos 389 — Consecutive Product Divisibility

### The Problem
For every n >= 1, does there exist k >= 1 such that n(n+1)...(n+k-1) | (n+k)...(n+2k-1)?

### What Aristotle Has Done (3 runs)

| Run | Result | Key Output |
|-----|--------|------------|
| 275128cf (bare) | sorry on main thm | Computational verification n=1..6, tried Kummer's theorem, failed |
| d2b51fe4 (with context) | sorry on main thm, 18 proven | Reduction to binomial ratios, Legendre sum framework, `exists_k_for_small_primes` for primes <= P |
| 3b112ef3 (corrected) | Pending | Just submitted today |

### Why It's Intractable

1. **The core difficulty is explicit**: Aristotle's own summary (d2b51fe4) identifies it precisely: "satisfying the condition for all gap primes simultaneously while maintaining the divisibility conditions for small primes appears to require sieve-theoretic arguments not available in Mathlib."

2. **k grows as ~3^n**: OEIS A375071 shows k(12) = 3,648,830 and k(18) = 255,278,294. This isn't a problem with a nice closed-form construction.

3. **The existential "for all n, exists k" structure is the hardest kind**: You need to construct k as a function of n. The problem *asks* whether such a construction exists. There's no known constructive proof strategy.

4. **Prior submission had WRONG formulation**: The earlier 344-line, 18-theorem result was for an incorrect statement. Codex caught this. All that infrastructure is wasted.

5. **Kummer's theorem approach failed**: Aristotle tried choosing k = p^m for primes p > n, analyzing base-p carries. Partial progress for individual primes, but cannot handle all primes simultaneously.

6. **The problem "cannot be resolved by finite computation"** — erdosproblems.com states this explicitly. It's a universal statement over all n.

### Verdict: DROP

This is a genuinely hard open problem that professional number theorists haven't cracked in 46+ years. The gap between "controlling small primes" and "controlling all primes simultaneously" requires sieve theory that isn't in Mathlib. Aristotle cannot invent new sieve methods.

## Erdos 850 — Three Consecutive Same-Radical Pairs

### The Problem
Do distinct x, y exist with rad(x)=rad(y), rad(x+1)=rad(y+1), rad(x+2)=rad(y+2)?

### What Aristotle Has Done (6+ runs)

| Run/Slot | Result | Key Output |
|----------|--------|------------|
| slot614 | compiled_clean, 12 proven | First attempt: `exact em _` (P or not P) — trivial tautology |
| slot693 | "disproven", 51 proven | Extensive infrastructure: no solutions x < 10, |x-y| >= 30, 6 | (y-x), same parity, smoothness |
| slot702 | compiled_clean, 42 proven | Case-by-case proofs for x=0 through x=9. Exponential Diophantine for each case |
| slot705 | compiled_clean, 13 proven | Resub with slot702+614 context |
| slot706 | compiled_clean | Resub with more context |
| slot714 | budget exhausted | Computational search in Lean (brute force, found nothing to 5000) |

### The P-or-not-P Trap

The first formulation `(exists x y ...) or not (exists x y ...)` is trivially `em _`. Aristotle solved it instantly — but proved nothing. This happened **twice** (slot614, 887a188c). The `exact em _` proof is a tautology.

### The Nonexistence Reformulation Risk

The latest submission (erdos850_nonexistence.txt) commits to proving `not exists x y ...`. Evidence for this:
- Computational search to 10^8: zero witnesses (Codex search)
- k=2 family x=2^n-2, y=2^n(2^n-2) cannot extend: y+2=(2^n-1)^2+1 always has odd prime factor
- Shorey-Tijdeman: nonexistence follows from Baker's strong ABC conjecture

Evidence against committing:
- **Codex/GPT-5.2 leans toward existence** in the debate (S-unit reformulation argument)
- **Grok-4 leans toward nonexistence**
- No modular obstruction has been proven
- Search to 10^8 is tiny in number theory — counterexamples could be huge

### What Aristotle Actually Proved (Useful Infrastructure)

The slot702 result is genuinely impressive — sorry-free proofs that no solution exists for each specific x from 0 to 9, using exponential Diophantine arguments. For example:
- x=5: requires solving 7^b - 5^a = 2, proved unique solution a=1, b=1
- x=6: requires solving 2^k - 7^m = 1, proved unique solution k=3, m=1
- x=9: requires solving 11^c - 3^a = 2, proved unique solution c=1, a=2

But **this per-case approach cannot scale**. Each new x introduces different primes and different exponential Diophantine equations. There's no general argument.

### The ABC Connection

Shorey and Tijdeman [ShTi16] proved: under Baker's strong form of ABC, the answer is NO. This means:
1. A proof of nonexistence is conditional on unproven conjectures
2. An unconditional proof would essentially require proving a special case of ABC
3. Aristotle cannot prove ABC or its consequences

### Verdict: DROP (or severely deprioritize)

The per-case approach hit a wall after x=9. Scaling requires either:
- A modular obstruction covering all x (not found)
- ABC-conjecture-level machinery (not in Mathlib)
- A witness (not found to 10^8)

## Side-by-Side Comparison

| Factor | Erdos 389 | Erdos 850 |
|--------|-----------|-----------|
| Open since | 1980 | 1963 |
| Direction | Existence (for all n, exists k) | Unknown (exists or not exists) |
| Aristotle runs | 3 | 6+ |
| Best result | Legendre framework + sorry | Case-by-case x=0..9 + constraints |
| Blocking obstacle | Sieve theory for gap primes | ABC conjecture dependency |
| Formulation issues | Had wrong statement initially | P-or-not-P trap (twice) |
| Computational evidence | k grows as 3^n | No witness to 10^8 |
| Community status | Firmly open, no near-miss | Conditionally resolved under strong ABC |
| Tractability | Near zero | Very low |

## Answers to Specific Questions

### 1. Are these genuinely tractable?

**No.** Both problems have resisted professional mathematicians for decades. Aristotle's best work is infrastructure and per-case verification — it hasn't come close to the core arguments needed.

### 2. For Erdos 389: is the existential provable without constructing k?

**Probably not in any practical sense.** The statement "for all n, exists k" inherently requires either:
- A constructive function n -> k (not known, grows as 3^n)
- A non-constructive existence proof (would likely require deep analytic number theory)

Aristotle builds infrastructure toward construction but hits the wall at "controlling all primes simultaneously." The gap is not a formalization issue — it's a genuine mathematical barrier.

### 3. For Erdos 850: is committing to nonexistence justified?

**Weakly justified, but risky.** Evidence for nonexistence:
- Shorey-Tijdeman conditional result under strong ABC
- No witness to 10^8
- k=2 family cannot extend
- Debate: Grok-4 favors nonexistence

Evidence it could be wrong:
- Codex/GPT-5.2 argues S-unit systems could have multiple solutions
- 10^8 is small in number theory
- No unconditional modular obstruction proven
- Committing wrongly wastes all submissions

**The bigger problem**: even if nonexistence is correct, proving it appears to require ABC-level arguments. Aristotle can't access those.

### 4. Should we drop one or both?

**Drop both.** The submission-to-progress ratio is terrible:
- Erdos 389: 3+ submissions, zero progress on core gap
- Erdos 850: 6+ submissions, impressive infrastructure but no path to resolution

### 5. What would be better candidates?

Based on the one success (ArithmeticSumS — falsification, 5 proven theorems), good candidates share these traits:
- **Falsifiable by computation or counterexample** (ArithmeticSumS was disproved)
- **Small search space** where Aristotle can test exhaustively
- **Finite/bounded problems** rather than universal quantifiers over all naturals
- **Problems where Mathlib already has the relevant theory**
- **Problems from combinatorics or discrete math** (less reliance on analytic methods)

Candidates from the existing pipeline:
- **Erdos 672** (107 proven theorems in one run — Aristotle is productive here)
- **Agoh-Giuga** (48 proven, but may have same scaling issue)
- **Problems with decidable finite cases** that native_decide can handle

## Pitfalls to Avoid

1. **The P-or-not-P formulation**: Never submit `A or not A`. Always commit to one side.
2. **Wrong statement**: Verify the exact formulation against erdosproblems.com before submitting.
3. **Sunk cost fallacy**: 6+ submissions on Erdos 850 doesn't mean the 7th will crack it.
4. **"compiled clean" excitement**: Aristotle often produces large files with many helper lemmas but sorry on the main theorem. This isn't progress on the gap.
5. **Infrastructure ≠ resolution**: The slot702 per-case proofs are beautiful Lean code, but they don't advance toward the general problem.

## Sources

| Source | Key Finding |
|--------|-------------|
| erdosproblems.com/389 | Open, cannot be resolved by finite computation |
| erdosproblems.com/850 | Open, conditional on strong ABC |
| OEIS A375071 | Minimal k for Erdos 389 grows roughly as 3^n |
| Aristotle summary d2b51fe4 | "sieve-theoretic arguments not available in Mathlib" |
| Aristotle summary 1f5b8c9e | `exact em _` — trivial tautology |
| slot702_result.lean | 624 lines of per-case proofs, cannot scale |
| codex_results/erdos389_solve.md | Confirmed wrong formulation in prior submission |
| codex_results/erdos850_solve.md | k=2 family cannot extend to k=3, structural obstruction |
| debate_erdos850_feb18.md | Grok-4: likely false; Codex: likely true; no consensus |
| submissions/tracking.db | 0 resolutions from 9+ submissions across both problems |
