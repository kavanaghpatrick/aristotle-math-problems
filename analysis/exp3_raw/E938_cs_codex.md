# EXP3 — E938 × cs × codex
Prompt date: 2026-05-31  Elapsed: 286.8s  Bytes: 3585

## Prompt

```
You are a cross-domain mathematician searching for DEEP STRUCTURAL ANALOGS — not surface keyword matches.

PROBLEM:
Let A = {n_1 < n_2 < ...} be the sequence of powerful numbers (integers n such that if a prime p divides n, then p^2 divides n). Erdős conjectured (Problem 938) that there are only finitely many three-term arithmetic progressions of CONSECUTIVE terms n_k, n_{k+1}, n_{k+2}. Powerful numbers have density 0; classical Roth-type density results do not apply. The gap sequence (n_{k+1} - n_k) is irregular. Known: Habsieger 2019 verified no solutions exist for small ranges; van Doorn 2026 found very-large non-consecutive AP triples among powerful numbers.

STRUCTURE: A combinatorial problem about a deterministic zero-density sequence defined by a MULTIPLICATIVE predicate (prime-squarefull). The target is a SECOND-ORDER pattern (consecutiveness of an AP) — distinct from finding any AP. The gap function is shaped by additive interactions between multiplicative shells (kernel/squarepart factorization). Known tools (Roth, Szemerédi, cap-set slice-rank) all require positive density or finite-field structure. Local-global obstructions (mod 72) do not close because admissible AP triples mod-N GROWS with N.

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

1. **(i) THE ANALOG PROBLEM:** The closest CS analog is the **Skolem-gap problem for linear recurrence sequences / linear loops**: given \(a_t=u^\top M^t v=\sum_j P_j(t)\lambda_j^t\), let \(Z=\{t:a_t=0\}\); decide whether the increasing enumeration of \(Z\) has three consecutive elements \(z_i,z_{i+1},z_{i+2}\) with \(z_{i+1}-z_i=z_{i+2}-z_{i+1}\). This is the Skolem Problem plus a second-order gap predicate, and appears as point-to-hyperplane reachability in linear dynamical systems, adjacent to Kannan-Lipton’s **“The Orbit Problem is Decidable”** ([dblp.org](https://dblp.org/db/conf/stoc/stoc80)). The match is structural: \(Z\) is a deterministic sparse hit set; membership is near-cancellation among multiplicative modes \(\lambda_j^t\), not density; the target is not “some AP in \(Z\)” but a statement about adjacent hits.

2. **(ii) THE TECHNIQUE THAT SOLVED IT THERE:** General Skolem remains open, so the best partial result is **Skolem-Mahler-Lech plus effective low-order Skolem algorithms**. SML says the zero set of a characteristic-zero LRS is a finite set plus finitely many arithmetic progressions ([cambridge.org](https://www.cambridge.org/core/journals/journal-of-the-london-mathematical-society/article/a-generalised-skolemmahlerlech-theorem-for-affine-varieties/CFB1881CDB67C479CA15E0950C2D37FE)); once such a representation is effective, the consecutive-gap query is a Presburger formula:
\[
Z(x)\wedge Z(x+d)\wedge Z(x+2d)\wedge \forall w\,(x<w<x+2d\Rightarrow w=x+d\vee \neg Z(w)).
\]
Effectivity is known in low order: Mignotte-Shorey-Tijdeman and Vereshchagin handled major order-\(\le4\) cases, and Bacik completed algebraic order \(4\) decidability ([arxiv.org](https://arxiv.org/abs/2409.01221)). The working method is spectral decomposition, multiplicative-relation lattices among characteristic roots, Baker/separation bounds, and semialgebraic invariant certificates in linear-loop verification ([arxiv.org](https://arxiv.org/abs/1701.02162)).

3. **(iii) THE OBSTRUCTION TO DIRECT TRANSPLANT:** The LRS method assumes a fixed finite-dimensional dynamical system: finitely many characteristic roots, one clock \(t\), and a finite-rank multiplicative relation lattice. Powerful numbers have none of that. Writing \(n=b^3m^2\) with \(b\) squarefree, an AP triple satisfies
\[
b_1^3u^2-2b_2^3v^2+b_3^3w^2=0,
\]
but \((b_1,b_2,b_3)\) ranges over unbounded squarefree kernels, and consecutiveness quantifies over every other shell \(b^3m^2\) inside the interval. Thus there is no single recurrence, no fixed torus, no eventual semilinear zero set, and no finite automaton state space. The exact failure mode is unbounded prime-support rank: the “characteristic roots” are effectively all primes, activated witness-by-witness.

4. **(iv) THE BRIDGE:** Use a **shell-intrusion counter**, replacing semilinear zero-set decomposition by an explicit adjacency certificate. For \(x<z\), define
\[
J(x,z)=\sum_{\substack{\mu^2(b)=1\\ b\le (z-1)^{1/3}}}
\max\!\left(0,\left\lfloor\sqrt{(z-1)/b^3}\right\rfloor-\left\lfloor\sqrt{x/b^3}\right\rfloor\right).
\]
This counts powerful numbers in the open interval \((x,z)\). Hence \(x,y,z\) is a consecutive AP iff \(x,y,z\in A\), \(x+z=2y\), and \(J(x,z)=1\). For each fixed kernel triple \(\beta=(b_1,b_2,b_3)\), parameterize integer points on \(b_1^3u^2-2b_2^3v^2+b_3^3w^2=0\), giving \((x_\beta(t),y_\beta(t),z_\beta(t))\). The transplanted invariant task is concrete: prove eventual safety \(J(x_\beta(t),z_\beta(t))>1\), with computable threshold \(T_\beta\) and an explicit intruding shell \(b=b_\beta(t)\).
