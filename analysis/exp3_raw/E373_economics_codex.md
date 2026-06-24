# EXP3 — E373 × economics × codex
Prompt date: 2026-05-31  Elapsed: 136.4s  Bytes: 3202

## Prompt

```
You are a cross-domain mathematician searching for DEEP STRUCTURAL ANALOGS — not surface keyword matches.

PROBLEM:
Erdős/Surányi conjectured (Problem 373) that the only solution in integers ≥ 2 to the equation n! = a! · b! (with n > a ≥ b ≥ 2) is (n,a,b) = (10,7,6) — i.e., 10! = 7! · 6!. The conjecture predicts finiteness; only one solution is known. Habsieger 2019 verified up to C ≤ 10^3000. Luca 2007 gives conditional finiteness on ABC. The Stirling–Bernoulli expansion of log Γ provides a high-order analytic constraint, but turning it into a finite check requires bounding (n - a) uniformly (Erdős 1993 gives a_1 ≥ n - 5 log log n).

STRUCTURE: A Diophantine equation in 3 variables (n, a, b) where both sides are EXPONENTIALLY-GROWING multiplicative objects (factorials). The equation forces a near-cancellation between log Γ(n+1) and log Γ(a+1) + log Γ(b+1). Asymptotic expansion produces a finite-dim constraint, but it lives in real coordinates while solutions live in integers. The TENSION is: continuous near-cancellation must support an integer-valued exact identity at exactly one (n,a,b). The known solution (10,7,6) is a tiny isolated exceptional case.

TASK: Find the deepest structural analog to this problem in economics (auction theory, equilibrium, mechanism design, game theory, financial markets).

CRITICAL: Do NOT propose mathematical analogs (no Roth, no cap-set, no Szemerédi, no removal lemmas, no slice-rank, no Bombieri-Lang, no ABC, no L-functions, no sieve methods, no Mordell-Weil). These have already been mined. Your job is to find the OFF-DOMAIN analog.

For your chosen analog, give:

(i) THE ANALOG PROBLEM: Name and one-sentence statement of the problem in the target domain that has the SAME structural shape (sparse deterministic set + second-order pattern, or near-cancellation of multiplicative quantities). Be specific — name researchers, papers, equations.

(ii) THE TECHNIQUE THAT SOLVED IT THERE: The named method/argument (e.g., "renormalization group flow with relevant operator analysis at the Wilson-Fisher fixed point"). If unsolved in the target domain, name the most successful partial result.

(iii) THE OBSTRUCTION TO DIRECT TRANSPLANT: What property of the original problem fails the precondition of the technique? Be precise about the failure mode.

(iv) THE BRIDGE: A SPECIFIC modification of either the technique or the problem reformulation that bridges the obstruction. This must be CONCRETE — a defined object, a measurable parameter, a function to compute. Not "consider an analogous structure" — produce a named construction with explicit ingredients.

FORMAT: 4 numbered paragraphs (i)-(iv), 100-200 words each. Be terse and technical. If no genuine analog exists in this domain, say so directly with one sentence of explanation — do NOT fabricate.

REMEMBER: The user knows the standard mathematical analogs. We are searching for a NON-OBVIOUS bridge. Surprise us, or admit there is no bridge here.

```

## Response

1. **(i) THE ANALOG PROBLEM:** Border’s reduced-form implementability problem in auction theory: given interim winning probabilities \(q_i(t_i)\), decide whether they are the projection of some ex-post feasible deterministic single-item allocation rule. Border’s theorem says feasibility is equivalent to the cut inequalities  
\[
\sum_i\sum_{t_i\in S_i} f_i(t_i)q_i(t_i)\le 1-\prod_i\left(1-\sum_{t_i\in S_i}f_i(t_i)\right)
\]
for all type subsets \(S_i\). This is the closest structural analog: a continuous low-dimensional object must lift to a sparse deterministic/integer allocation set, and the obstruction is encoded by multiplicative product terms from independent type profiles. See Border 1991, “Implementation of Reduced Form Auctions” [Econometrica](https://ideas.repec.org/a/ecm/emetrp/v59y1991i4p1175-87.html).

2. **(ii) THE TECHNIQUE THAT SOLVED IT THERE:** Border’s geometric separation argument: characterize the convex hull of ex-post feasible allocation incidence vectors by all subset-cut inequalities. The modern constructive form is Cai-Daskalakis-Weinberg’s “ironed hierarchy” decomposition: they identify a sufficient subset of Border constraints and implement any feasible reduced form as a distribution over ironings of a common ordering [arXiv:1112.4572](https://arxiv.org/abs/1112.4572). For richer capacity constraints, Che-Kim-Mierendorff replace the geometry by a feasible-circulation/network-flow formulation with paramodular capacity constraints, again turning interim real feasibility into exact ex-post implementability [Econometrica 2013](https://www.econometricsociety.org/publications/econometrica/2013/11/01/generalized-reduced%E2%80%90form-auctions-network%E2%80%90flow-approach).

3. **(iii) THE OBSTRUCTION TO DIRECT TRANSPLANT:** Border works because randomization convexifies deterministic mechanisms: implementability is membership in a polytope, and violations have separating hyperplanes with one-sided, monotone cut structure. The factorial problem has no such convexification. A convex mixture of \((n,a,b)\) triples or factorial products is meaningless for the exact identity. Worse, the Stirling constraint is only a scalar real projection of the true integer condition: equality requires matching every prime valuation, not merely \(\log n!-\log a!-\log b!=0\). Thus small analytic slack gives no separation oracle unless it is lifted back to prime-exponent coordinates.

4. **(iv) THE BRIDGE:** Use a “Legendre-Border separator.” Put \(d=n-a\) and define, for cutoff \(Y\),
\[
\Delta_p(a,b,d)=\sum_{k\ge1}\left(\left\lfloor\frac{a+d}{p^k}\right\rfloor-\left\lfloor\frac{a}{p^k}\right\rfloor-\left\lfloor\frac{b}{p^k}\right\rfloor\right),\quad p\le Y.
\]
Then \(n!/a!=b!\) implies \(\Delta_p=0\) for every prime \(p\). Define the computable cut defect  
\[
B_Y(a,b,d)=\max_{|\lambda_p|\le1}\sum_{p\le Y}\lambda_p\Delta_p=\sum_{p\le Y}|\Delta_p|.
\]
This is the exact analog of a Border separation oracle: the real Stirling tube proposes candidates, while \(B_Y\) tries to separate them in finite prime-coordinate cuts. A finite-check strategy would prove that for all large \(d\), every integer point in the Stirling tube has \(B_{Y(d)}(a,b,d)>0\).
