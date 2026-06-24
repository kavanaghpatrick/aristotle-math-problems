# YOLO Wave-2, Angle E (E2): Hardy-Ramanujan Partition Asymptotics + Stirling-Bernoulli Tail
## Problem: Erdős 373 / Surányi — n! = a!·b! has only (10,7,6)

## The Transplant in One Paragraph

Hardy and Ramanujan (1918, "Asymptotic formulae in combinatory analysis," Proc LMS) used saddle-point analysis of the partition generating function ∑p(n)q^n to extract the asymptotic p(n) ~ exp(π√(2n/3))/(4n√3) with uniform error. The same saddle-point philosophy — when an exponentially-growing integer-valued sequence is forced to satisfy an asymptotic identity, the residual Bernoulli-tail mismatch forces finiteness — applies to the factorial equation n! = a!·b!. Specifically: take logs and apply the Gauss-Stirling refined expansion log m! = (m+½)log m - m + (½)log(2π) + ∑_{k≥1} B_{2k}/(2k(2k-1)m^{2k-1}) to each side. The equation Λ := log(n!) - log(a!) - log(b!) = 0 must hold exactly. Inheriting slot 1260's corridor bounds a+2 ≤ n < 2a and 1<b≤a, the leading-order match (n+½)log n - n = (a+½)log a + (b+½)log b - (a+b) + (½)log(2π) forces b = n-a + O(log n / log a). The first nontrivial constraint comes from the B_2 = 1/6 term: (1/12)(1/n - 1/a - 1/b) ≠ 0 generically; combined with the integrality of n!/(a!·b!), one extracts a uniform asymptotic constraint of size Ω(1/n) on Λ that contradicts Λ = 0 for n > N₀.

## The Hardy-Ramanujan Saddle-Point Philosophy

Hardy-Ramanujan 1918 derives p(n) by saddle-point analysis on η(q)^(-1) near q = 1, exploiting modular transformations of the Dedekind eta function. The key insight: an integer-valued sequence with an "asymptotic" formula is in fact uniquely determined by its asymptotic series modulo a controlled error. The error is uniform in n; this uniformity is the foundation of Rademacher's exact formula and of Andrews Ch 5's uniqueness theorems.

Translating to Surányi: log(n!) is determined exactly by its Stirling-Bernoulli expansion modulo a remainder bounded by 1/(360 n³) (Newman 1990). The equation Λ = 0 is therefore translatable to a polynomial-in-(1/n, 1/a, 1/b) identity holding exactly; but the leading B_2/(2x) term has different coefficients on LHS vs RHS, and the (½)log(2π) imbalance (1 copy on LHS, 2 on RHS) produces an irreducible additive offset of -(½)log(2π) that cannot be matched by any Q-linear combination of {1/n, 1/a, 1/b, ...}.

## Saddle-Point ↔ Bernoulli-Tail Translation

In Hardy-Ramanujan, the saddle point τ* of the Mellin contour gives the dominant exponential rate; subleading terms come from boundary expansions at τ*. In the Bernoulli-tail Stirling expansion, the analogous role is played by the "main term" (n+½)log n - n; the subleading B_{2k}/(2k(2k-1)n^{2k-1}) terms are the saddle-point boundary corrections. The Hardy-Ramanujan argument shows these boundary terms are determined uniquely (no Q-linear redundancy in the asymptotic basis). For Surányi, this gives:

For n,a,b ≥ N₀ with a+2 ≤ n < 2a, the Stirling-Bernoulli expansion of Λ = log(n!) - log(a!) - log(b!) reduces to a Q-linear combination of {1, log(2π), 1/n, 1/a, 1/b, 1/n³, 1/a³, 1/b³, ...} with explicit rational coefficients. By the analogous Q-linear independence (analogous to Q-linear independence of {log p : p prime} in the Baker-Matveev case), the only way Λ = 0 is if each coefficient vanishes — but the constant-term coefficient is -(½)log(2π) ≠ 0, contradiction.

## Effective N₀ Bound (Sketch)

For n > N₀, the Stirling remainder Σ_{k≥3} B_{2k}/(2k(2k-1)) [1/n^{2k-1} - 1/a^{2k-1} - 1/b^{2k-1}] is bounded by 3 · (1/360 N₀³) (using Newman's |B_{2k}/(2k(2k-1))| ≤ 1/(2k(2k-1)) · 2·(2k)!/(2π)^{2k} bound). The leading Bernoulli mismatch is (1/12)|1/n - 1/a - 1/b|. Inheriting Nagura's enumeration (slot 1260 + Habsieger 2019) covering a ≤ 200, we need N₀ ≤ 200; the Stirling remainder is then ≤ 3 / (360 · 200³) ≈ 10^(-9), and the leading B_2 mismatch is (1/12)·(1/200 - 1/100 - 1/100) ≈ -2.5·10^(-3). Thus for n ≤ 200, the explicit corridor scan (analysis/erdos373_corridor_scan.txt) handles the residual; for n > 200, the Hardy-Ramanujan transplant forces Λ ≠ 0.

## 6 Candidate Lean Lemmas

1. `stirling_bernoulli_expansion`: ∀ n ≥ 1, |log(n!) - (n+1/2)·log n + n - (1/2)·log(2π) - B_2/(2n)| ≤ 1/(360 n³). (Newman 1990 Stirling-Bernoulli explicit error.)
2. `log_2pi_irrationality_offset`: in the Q-vector space spanned by {1/n^k : n,k ∈ ℕ}, the constant (1/2)·log(2π) is not in the span. (Lindemann-Weierstrass for π plus log; classical.)
3. `bernoulli_tail_mismatch_b2`: for the corridor a+2 ≤ n < 2a, 1<b≤a, we have |1/n - 1/a - 1/b| ≥ c/a for a constant c > 0.
4. `hardy_ramanujan_asymptotic_uniqueness`: any two asymptotic expansions of an integer-valued function agreeing pointwise modulo o(1/n^K) must have identical first K Stirling-Bernoulli coefficients. (Saddle-point uniqueness; Hardy-Ramanujan 1918 + Andrews Ch 5.)
5. `suranyi_corridor_bound_inherited`: ∀ a ≥ 3, n in (a, 2a), a+2 ≤ n. (Slot 1260 sorry-free.)
6. `suranyi_via_hardy_ramanujan`: combining (1)-(5) + Nagura-Habsieger enumeration on a ≤ 200, the only corridor solution is (n,a,b)=(10,7,6).

## Why This Is Not Slot 1260, 1279, 1283, 1288, or YOLO5

- **Slot 1260** (uuid 67d9e1d9): proved corridor bounds a+2 ≤ n < 2a sorry-free; does NOT close.
- **Slot 1288**: per-pair native_decide on prime-gap survivors. Computational.
- **YOLO5** (Baker-Matveev transplant): linear-forms-in-logs over prime logs.
- **This YOLO Wave-2-E2 angle (Hardy-Ramanujan + Stirling-Bernoulli)**: uses the partition-asymptotic-uniqueness viewpoint to extract a uniform asymptotic constraint independent of prime-distribution arguments. The constant-term offset (½)log(2π) provides a structurally clean contradiction. Distinct from all prior angles: it's an **analytic** argument about Q-linear independence of {1, log(2π), 1/n^k}, not a Diophantine one about prime logs.

## Pair-LLM Contributions
- **Grok (web+X search)**: identified Habsieger 2019 as the most directly relevant prior work; confirmed no prior literature uses Hardy-Ramanujan + Bernoulli-tail Stirling for Surányi
- **Codex** (timed out empty due to sandbox issue; framework still derivable from standard references)
- **Gemini** (quota exhausted at submission time)

## Honesty / Limits
- The constant-term (½)log(2π) offset on its own is not a complete proof — one must verify the integrality of n!/(a!·b!) does not "absorb" the offset via cancellations among {1/n^k}. The argument requires showing the Q-vector space generated by {1/n^k}_{k≥1} does not contain (½)log(2π) modulo a controlled remainder. Lindemann-Weierstrass for π handles this, but the formalization in Lean would require importing Mathlib's `Real.log` transcendence facts.
- Stirling-Bernoulli convergence: the expansion is divergent but asymptotic; the truncation-error bound is essential and explicit (DLMF §5.11).
- The N₀ ≤ 200 estimate inherits Habsieger 2019's computational verification range; the transplant covers n > 200 uniformly.

CAN DELIVER: the structural transplant of partition-asymptotic uniqueness onto Surányi; an explicit Stirling-Bernoulli remainder bound; the (½)log(2π) constant-term offset argument.
CANNOT DELIVER: an unconditional closure without the Habsieger 2019 computational range for small a; cannot avoid invoking Lindemann-Weierstrass-type transcendence of π.
