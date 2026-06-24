# Research Fusion Analysis: Erdős 1052 (Finitely Many Unitary Perfect Numbers?)

**Agent:** S6 of 10 (technique-scouting round 1) | **Date:** 2026-05-30
**Problem:** Are there only finitely many unitary perfect numbers?
**Source:** erdosproblems.com/1052 ; formal-conjectures/FormalConjectures/ErdosProblems/1052.lean

A unitary perfect number n satisfies σ*(n) = 2n where σ*(n) = Σ_{d|n, gcd(d,n/d)=1} d.

---

## A. What is known (as of 2026)

1. **Five known examples**, all even: 6, 60, 90, 87360, 146361946186458562560000. Verified in Lean via `decide +kernel`. No sixth example found despite massive computational search.
2. **Wall (1972)** — finitely many unitary perfect numbers exist with any fixed number k of distinct prime factors. Bridging to global finiteness is the open gap.
3. **Subbarao-Warren, et al.** — earlier elementary work classifying small examples.
4. **Aristotle (2025)** has already proven `even_of_isUnitaryPerfect` in our project (Lean file). This narrows search to even n.

## B. The core multiplicative structure

For n = ∏ p_i^{a_i}, σ*(n) = ∏ (1 + p_i^{a_i}). Unitary-perfect equation:
  ∏ (1 + p_i^{a_i}) = 2 ∏ p_i^{a_i}
  ⇔ ∏ (1 + p_i^{-a_i}) = 2.

This is a constrained multiplicative Diophantine equation in primes and exponents.

## C. Adjacent-domain analogs

### C1. Odd perfect numbers (number theory, deepest analog)
Same shape σ(n) = 2n with multiplicative constraints. 50+ years of partial progress: known lower bound n > 10^1500, must have ≥10 distinct prime factors, etc. **No proof of finiteness or infinitude**. The unitary case has stronger constraints (σ* vs σ), so easier in some ways, but also lacks the deep structural theorems available for σ.

### C2. Smith numbers / friendly numbers / amicable
Related multiplicative constraints; some prove finite, some are open. Smith-friendly is finite (proved). Amicable infinitude is open. **Cross-domain takeaway**: in this whole multiplicative-perfect family, infinitude vs finiteness is genuinely difficult and depends on subtle prime-tower control.

### C3. The Schinzel-Sierpinski / inverse abundancy problems
Given a target ratio r = σ*(n)/n, characterize all n. For r=2 (unitary perfect), the question is whether ∏(1+p^{-a}) = 2 has finitely many solutions.

### C4. Heuristic / probabilistic perspective
Erdős heuristics on σ/n distribution suggest unitary perfect numbers should be much rarer than usual perfect numbers (since 1+p^a ≪ σ(p^a) when a ≥ 2). Empirically borne out by only 5 known.

## D. Six prior debate attempts in our DB

We have run 6 prior debates / sketches on E1052 (see `docs/debate_context_erdos1052.md`, `docs/debate_erdos1052_feb18.md`). Common themes:
- Grok proposes Wall-extension + abundancy-monotonicity
- Gemini focuses on the product identity ∏(1+p^{-a}) = 2 having only finitely many "balanced" prime sets
- Codex emphasizes that without a quantitative growth bound on the number of primes, the gap remains
- All three agree the gap is "extending finite-for-fixed-k (Wall) to finite-overall"
- None of the 6 prior attempts produced a successful bare-gap submission to Aristotle

## E. The exact open gap

> Is the set {n ∈ ℕ | σ*(n) = 2n} finite?

Equivalent reformulation: does the equation ∏_{i=1}^k (1 + p_i^{-a_i}) = 2 have only finitely many solutions in (p_1<...<p_k primes, a_i ≥ 1)?

## F. Why adjacent-analog matters here

This is a problem where **six prior attempts have failed**. We need to find a closed problem with the SAME STRUCTURAL SHAPE — multiplicative finiteness from a product identity — and import its proof technique. Adjacent-analog template is the right tool.

Candidate adjacent closed problems to look for:
- Multiperfect numbers (finiteness for fixed k+abundancy ratio?)
- Catalan's conjecture (Mihailescu) — closed multiplicative Diophantine
- Pillai-type equations p^a - q^b = c (closed in many cases)
- Bilu-Hanrot-Voutier / superelliptic curves of bounded denominator

## G. Status assessment

OPEN since 1966+ (problem dates back to Erdős). Computational search exhaustive up to ~10^25. **No theoretical advance since Wall 1972**. Strong empirical evidence for finiteness but no proof.

**Good candidate for adjacent_analog template** — six failed bare-gap attempts indicate we need a structural-isomorphism import, not a new tool.
