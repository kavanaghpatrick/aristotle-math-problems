# EXP3 — E373 × physics × codex
Prompt date: 2026-05-31  Elapsed: 174.1s  Bytes: 2748

## Prompt

```
You are a cross-domain mathematician searching for DEEP STRUCTURAL ANALOGS — not surface keyword matches.

PROBLEM:
Erdős/Surányi conjectured (Problem 373) that the only solution in integers ≥ 2 to the equation n! = a! · b! (with n > a ≥ b ≥ 2) is (n,a,b) = (10,7,6) — i.e., 10! = 7! · 6!. The conjecture predicts finiteness; only one solution is known. Habsieger 2019 verified up to C ≤ 10^3000. Luca 2007 gives conditional finiteness on ABC. The Stirling–Bernoulli expansion of log Γ provides a high-order analytic constraint, but turning it into a finite check requires bounding (n - a) uniformly (Erdős 1993 gives a_1 ≥ n - 5 log log n).

STRUCTURE: A Diophantine equation in 3 variables (n, a, b) where both sides are EXPONENTIALLY-GROWING multiplicative objects (factorials). The equation forces a near-cancellation between log Γ(n+1) and log Γ(a+1) + log Γ(b+1). Asymptotic expansion produces a finite-dim constraint, but it lives in real coordinates while solutions live in integers. The TENSION is: continuous near-cancellation must support an integer-valued exact identity at exactly one (n,a,b). The known solution (10,7,6) is a tiny isolated exceptional case.

TASK: Find the deepest structural analog to this problem in physics (statistical mechanics, gauge theory, condensed matter, phase transitions, renormalization group).

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

(i) **THE ANALOG PROBLEM:** Borgs–Kotecký / Biskup–Borgs–Chayes–Kleinwaks–Kotecký partition-function zeros at first-order phase transitions: locate finite-volume zeros of \(Z_L^{\mathrm{per}}(z)\) when
\[
Z_L^{\mathrm{per}}(z)\approx \sum_m q_m\,\zeta_m(z)^{L^d},
\]
so zeros require exact cancellation of exponentially large phase weights. In two-phase regions the zeros satisfy
\[
q_m^{1/L^d}|\zeta_m|=q_n^{1/L^d}|\zeta_n|,\qquad
L^d\Arg(\zeta_m/\zeta_n)=\pi \bmod 2\pi .
\]
This is the same structural shape: a continuous coexistence condition plus a discrete quantization condition. See Biskup et al., *Commun. Math. Phys.* 251 (2004), and the Pirogov–Sinai companion paper covering Ising/Potts/Blume-Capel cases: [arXiv:math-ph/0304007](https://arxiv.org/abs/math-ph/0304007), [arXiv:math-ph/0312041](https://arxiv.org/abs/math-ph/0312041).

(ii) **THE TECHNIQUE THAT SOLVED IT THERE:** Complex Pirogov–Sinai theory plus Rouché localization. One first proves a contour expansion giving finitely many metastable free energies \(\zeta_m(z)\), then replaces \(Z_L\) by the finite exponential sum above, solves the phase-coexistence equations, and uses Rouché’s theorem to put true zeros within exponentially small error of those model equations. Borgs–Janke also used the finite-size form
\[
Z_{\rm per}=\sum_m \exp(-\beta f_m V)
\]
for first-order transition point extraction: [Phys. Rev. Lett. 68, 1738](https://doi.org/10.1103/PhysRevLett.68.1738).

(iii) **THE OBSTRUCTION TO DIRECT TRANSPLANT:** The factorial problem has no thermodynamic volume \(L^d\), no analytic coupling \(z\), no contour representation, and no finite stable phase set whose remainders are \(O(e^{-cL})\). Stirling–Bernoulli gives an asymptotic expansion, not a convergent low-temperature expansion with a spectral gap between phases. Also the desired zero is on a real integer lattice:
\[
\Delta_k(a,b)=\log\Gamma(a+k+1)-\log\Gamma(a+1)-\log\Gamma(b+1)=0,
\]
with \(k=n-a\), rather than in a complex parameter plane where phase arguments supply quantization automatically.

(iv) **THE BRIDGE:** Introduce the exact two-phase “factorial Lee–Yang twist”
\[
Z_k(a,b;\theta)=\frac{\Gamma(a+k+1)}{\Gamma(a+1)}+e^{i\theta}\Gamma(b+1).
\]
Then \(n!=a!b!\), \(n=a+k\), is exactly \(Z_k(a,b;\pi)=0\). Its zero in \(\theta\) is
\[
\theta_k(a,b)=\pi+i\Delta_k(a,b)\pmod{2\pi}.
\]
So the conjecture becomes: the lattice-indexed Lee–Yang zero hits the physical anti-phase line only at \((k,a,b)=(3,7,6)\). Compute the coexistence root
\[
\alpha_k(b):\quad \sum_{j=1}^k\log(\alpha_k(b)+j)=\log\Gamma(b+1)
\]
and the measurable gap
\[
\delta_k(b)=\operatorname{dist}(\alpha_k(b),\mathbb Z).
\]
Exact solutions are precisely \(\delta_k(b)=0\). This is the concrete transplant target.
