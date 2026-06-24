# EXP3 — E373 × cs × codex
Prompt date: 2026-05-31  Elapsed: 163.8s  Bytes: 2895

## Prompt

```
You are a cross-domain mathematician searching for DEEP STRUCTURAL ANALOGS — not surface keyword matches.

PROBLEM:
Erdős/Surányi conjectured (Problem 373) that the only solution in integers ≥ 2 to the equation n! = a! · b! (with n > a ≥ b ≥ 2) is (n,a,b) = (10,7,6) — i.e., 10! = 7! · 6!. The conjecture predicts finiteness; only one solution is known. Habsieger 2019 verified up to C ≤ 10^3000. Luca 2007 gives conditional finiteness on ABC. The Stirling–Bernoulli expansion of log Γ provides a high-order analytic constraint, but turning it into a finite check requires bounding (n - a) uniformly (Erdős 1993 gives a_1 ≥ n - 5 log log n).

STRUCTURE: A Diophantine equation in 3 variables (n, a, b) where both sides are EXPONENTIALLY-GROWING multiplicative objects (factorials). The equation forces a near-cancellation between log Γ(n+1) and log Γ(a+1) + log Γ(b+1). Asymptotic expansion produces a finite-dim constraint, but it lives in real coordinates while solutions live in integers. The TENSION is: continuous near-cancellation must support an integer-valued exact identity at exactly one (n,a,b). The known solution (10,7,6) is a tiny isolated exceptional case.

TASK: Find the deepest structural analog to this problem in computer science (complexity theory, algorithms, distributed systems, formal languages, automata).

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

1. **(i) The Analog Problem.** Abelian-square avoidance in morphic words: given a deterministic infinite word `w = g^ω(a)`, decide whether it contains a factor `UV` with equal Parikh vectors `Ψ(U)=Ψ(V)`. The sharp landmark is Veikko Keränen, “Abelian Squares Are Avoidable on 4 Letters,” ICALP 1992: he constructed an 85-uniform morphism on four letters whose fixed point has no abelian square ([OpenAIRE](https://explore.openaire.eu/search/publication?pid=10.1007%2F3-540-55719-9_62)). The factorial equation becomes this shape after prime factorization: let `W = pf(2)pf(3)pf(4)...` over the prime alphabet, with multiplicity. Then `n! = a!b!` iff the Parikh vector of blocks `a+1,...,n` equals that of blocks `2,...,b`.

2. **(ii) Technique Solved There.** The method is finite template/desubstitution verification for abelian powers in morphic fixed points. Keränen used an explicit uniform morphism plus finite computer checks; Currie and Rampersad later abstracted this into a decidability theorem for fixed points avoiding abelian `k`-powers when the morphism’s frequency matrix is invertible and contracting in a suitable norm ([arXiv:1106.1842](https://arxiv.org/abs/1106.1842)). A forbidden equality `Ψ(U)=Ψ(V)` is represented as a zero-difference template. Uniformity lets one pull any large occurrence back through the morphism to a smaller “parent” template. Contraction bounds all possible ancestors, reducing an infinite search over positions and lengths to a finite graph of Parikh-difference templates.

3. **(iii) Obstruction To Direct Transplant.** The factorial word is not a fixed point of a finite uniform morphism. Its alphabet is the primes, hence unbounded; its block `pf(m)` has length `Ω(log m / log log m)` irregularly; and the prime-support dimension grows with `n`. The Currie-Rampersad contraction precondition fails twice: there is no fixed frequency matrix `M`, and no inverse contraction on Parikh differences. Analytically, Stirling gives a real near-cancellation, but the formal-language method needs exact finite-state self-similarity. Prime factorization supplies exact Parikh vectors, but not a morphic desubstitution map that turns every large candidate into a smaller candidate from a finite ancestor set.

4. **(iv) The Bridge.** Build a finite-prime factorial-template system. For cutoff `y`, define `V_y(t)=(v_p(t!))_{p≤y}` and discrepancy `D_y(n,a,b)=V_y(n)-V_y(a)-V_y(b)`. A true solution has `D_y=0` for every `y≥n`. Compute `V_y` using Legendre digit sums: `v_p(t!)=(t-s_p(t))/(p-1)`. The concrete object is the directed “Legendre ancestor graph” whose state is `(n,a,b,D_y)` modulo base-`p` digit carries for `p≤y`, with transition `(n,a,b) ↦ (⌊n/p⌋,⌊a/p⌋,⌊b/p⌋)`. The measurable defect is `ρ_y=log(n!/(a!b!))-Σ_{p≤y}D_p log p`. This imports template checking as finite-prime desubstitution; the missing theorem is a uniform `y` forcing `ρ_y=0`.
