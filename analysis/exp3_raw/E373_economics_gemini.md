# EXP3 — E373 × economics × gemini
Prompt date: 2026-05-31  Elapsed: 44.9s  Bytes: 5380

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

[model=gemini-2.5-flash]

I am now starting to research potential economic analogs for the given mathematical problem. My strategic intent is to identify a problem that shares the core structural tension of continuous near-cancellation resolving to sparse, discrete integer solutions, and then to develop a concrete bridge. I will use web search to identify relevant economic theories and researchers.
I have completed the research phase and identified "Discrete Arbitrage" or "Combinatorial Arbitrage" as a suitable structural analog in economics. My strategic intent for the next steps is to formulate the four required sections: (i) The Analog Problem, (ii) The Technique That Solved It There, (iii) The Obstruction to Direct Transplant, and (iv) The Bridge, ensuring each adheres to the specified word count and technical depth. I will now proceed to write these sections.
(i) THE ANALOG PROBLEM:
The deepest structural analog to the Erdős/Surányi conjecture in economics lies within **Combinatorial Arbitrage** in markets with discrete asset units and transaction costs. This problem, exemplified by prediction markets or cross-exchange trading, seeks to identify an exact, risk-free profit opportunity by executing a specific, finite sequence of discrete trades in assets whose prices, while appearing continuous, are subject to discrete tick sizes, bid-ask spreads, and integer quantity constraints. The challenge is that fundamental asset pricing models often derive continuous "no-arbitrage" conditions (e.g., using martingales or linear pricing rules), yet the actual market allows for discrete transactions. The "near-cancellation" is the expectation of zero profit in an efficient, continuous market, but specific, sparse configurations of discrete prices and trade sizes can create an exact profit identity, akin to the isolated (10,7,6) solution. Relevant works include those by Chen et al. (2013) on arbitrage in prediction markets using integer programming and efforts to detect triangular arbitrage in FX markets.

(ii) THE TECHNIQUE THAT SOLVED IT THERE:
The primary technique for identifying and verifying combinatorial arbitrage opportunities in financial markets is **Integer Linear Programming (ILP)** or more generally, **Mixed-Integer Programming (MIP)**. Given a set of available assets, their bid/ask prices, transaction costs, and minimum/maximum trade sizes (all discrete or convertible to discrete units), an ILP model formulates the problem of maximizing profit subject to budget constraints, position limits, and the requirement that all trade quantities must be integers. The "solution" is a specific vector of integer trade quantities across various assets that yields a positive, risk-free profit. This technique explicitly handles the discreteness that continuous optimization methods (like standard linear programming for no-arbitrage bounds) abstract away, enabling the precise identification of sparse, exact profit identities that satisfy all real-world trading constraints.

(iii) THE OBSTRUCTION TO DIRECT TRANSPLANT:
The main obstruction to directly transplanting the "continuous near-cancellation, discrete identity" resolution from the Erdős/Surányi conjecture to discrete arbitrage lies in the **nature of the underlying continuous approximation**. For n! = a!b!, the Stirling–Bernoulli expansion of log Γ provides a high-order, analytic, asymptotic approximation that effectively collapses the search space for integer solutions. This approximation explicitly encodes the continuous behavior of the factorial function. In discrete arbitrage, while continuous asset pricing models provide no-arbitrage bounds, there isn't an equivalent *analytic expansion* for the profit function that smoothly bridges continuous mispricings to *exact integer profits* while also accounting for discrete transaction costs and quantities. The "near-cancellation" in finance is often statistical or econometric, not a direct analytic consequence of the fundamental objects themselves, making the continuous-to-discrete transition less elegant and more computationally intensive.

(iv) THE BRIDGE:
To bridge this obstruction, one could develop a **"Discretized Profit Manifold" (DPM)**, constructed by applying a **lattice reduction algorithm** to the residuals of a continuous no-arbitrage pricing model.
First, define a continuous "no-arbitrage hyperplane" in a high-dimensional space where each dimension represents an asset's log-price or return. Calculate the **mispricing vector** for observed discrete market prices relative to this hyperplane.
Second, construct a high-dimensional lattice where basis vectors represent feasible discrete trades (e.g., buying 1 unit of asset A, selling 1 unit of asset B, incurring their respective costs).
The "bridge" is then to use a **generalized Lenstra-Lenstra-Lovász (LLL) algorithm**, or a more specialized variant for approximate shortest vector problem (SVP) in specific lattices, to find short, non-zero integer vectors within this lattice that, when combined with the mispricing vector, fall within a predefined "profit cone" (determined by transaction costs and desired minimum profit). This provides a computationally tractable way to search for sparse integer trade combinations that turn continuous "near-arbitrage" into discrete, exact profit identities, making the analytical transition concrete.