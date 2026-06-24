# EXP3 — E373 × biology × codex
Prompt date: 2026-05-31  Elapsed: 172.7s  Bytes: 3309

## Prompt

```
You are a cross-domain mathematician searching for DEEP STRUCTURAL ANALOGS — not surface keyword matches.

PROBLEM:
Erdős/Surányi conjectured (Problem 373) that the only solution in integers ≥ 2 to the equation n! = a! · b! (with n > a ≥ b ≥ 2) is (n,a,b) = (10,7,6) — i.e., 10! = 7! · 6!. The conjecture predicts finiteness; only one solution is known. Habsieger 2019 verified up to C ≤ 10^3000. Luca 2007 gives conditional finiteness on ABC. The Stirling–Bernoulli expansion of log Γ provides a high-order analytic constraint, but turning it into a finite check requires bounding (n - a) uniformly (Erdős 1993 gives a_1 ≥ n - 5 log log n).

STRUCTURE: A Diophantine equation in 3 variables (n, a, b) where both sides are EXPONENTIALLY-GROWING multiplicative objects (factorials). The equation forces a near-cancellation between log Γ(n+1) and log Γ(a+1) + log Γ(b+1). Asymptotic expansion produces a finite-dim constraint, but it lives in real coordinates while solutions live in integers. The TENSION is: continuous near-cancellation must support an integer-valued exact identity at exactly one (n,a,b). The known solution (10,7,6) is a tiny isolated exceptional case.

TASK: Find the deepest structural analog to this problem in biology (evolutionary dynamics, network theory, ecology, population genetics, protein folding).

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

1. **(i) The Analog Problem:** Wegscheider/Haldane thermodynamic loop consistency in biochemical reaction networks: for every closed metabolic/enzyme cycle \(c\in\ker N\), the product of equilibrium constants must cancel, \(\prod_r K_r^{c_r}=1\), equivalently \(\sum_r c_r\log K_r=0\). This is the biological analog I’d choose. It is explicit in Wegscheider’s detailed-balance conditions and modern metabolic energy-balance work by Beard, Babson, Curtis, and Qian (2004) on thermodynamic constraints from stoichiometric cycle space ([PubMed](https://pubmed.ncbi.nlm.nih.gov/15135031/)); enzyme-kinetic versions appear as Haldane relationships and Wegscheider conditions in modular rate laws ([Liebermeister et al.](https://academic.oup.com/bioinformatics/article/26/12/1528/281177)). Same shape: huge multiplicative pathway weights look locally plausible, but exact biology permits only zero-affinity products on discrete cycles.

2. **(ii) The Technique That Solved It There:** The successful method is log-affinity/cycle-space reduction: transform products of rate constants into linear affinities, impose \(A=N^T\mu\), and test flux signs against internal cycles. In CRNT language this is detailed/complex balance plus cycle balance; Müller and Joshi prove “detailed balance = complex balance + cycle balance” graph-theoretically, with formal balance \(\prod_{ij\in C}k_{ij}=\prod_{ij\in C}k_{ji}\) for every directed cycle ([Müller–Joshi 2020](https://link.springer.com/article/10.1007/s11538-020-00792-1)). In metabolic modeling, the practical solver is energy balance analysis: parameterize equilibrium constants by chemical potentials so Wegscheider constraints become automatic. The key move is not estimating products; it re-coordinates the problem into potentials plus a finite cycle basis.

3. **(iii) The Obstruction To Direct Transplant:** The factorial equation fails the fixed-network precondition. In metabolism, \(N\) is fixed, cycles are a finite lattice basis, and \(K_r\) are independent positive parameters or potentials-derived quantities. Here the “cycle” itself moves with \((n,a,b)\):  
\[
\sum_{m=a+1}^n \log m-\sum_{m=2}^b\log m=0.
\]
The coefficient vector is an interval-difference vector over an unbounded alphabet of primes/integers, not a fixed stoichiometric kernel. Also, CRNT certifies thermodynamic possibility, not integer realization: zero affinity in \(\mathbb R\) is easy once potentials exist, while the Erdos-Suranyi obstruction is exactly that the real zero must land on integer endpoints.

4. **(iv) The Bridge:** Use a “factorial affinity network.” Fix \(d=n-a\) and define  
\[
\mathcal A_d(x,b)=\log\Gamma(x+d+1)-\log\Gamma(x+1)-\log\Gamma(b+1).
\]
This is the cycle affinity of a two-path biochemical loop: forward path rates \(x+1,\dots,x+d\), reverse path rates \(2,\dots,b\). For each \((d,b)\), compute the unique real zero \(x_{d,b}\), its lattice defect \(\Delta_{d,b}=\operatorname{dist}(x_{d,b},\mathbb Z)\), and elasticity  
\[
E_{d,b}(x)=\partial_x\mathcal A_d=\sum_{i=1}^d (x+i)^{-1}.
\]
Then the CRNT-style finite-cycle test becomes an interval exclusion certificate: a candidate survives only if the Stirling-Bernoulli error window around \(x_{d,b}\) intersects \(\mathbb Z\). This bridges thermodynamic zero-affinity to integer endpoint rigidity.
