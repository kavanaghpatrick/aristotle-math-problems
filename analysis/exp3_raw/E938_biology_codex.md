# EXP3 — E938 × biology × codex
Prompt date: 2026-05-31  Elapsed: 284.9s  Bytes: 3305

## Prompt

```
You are a cross-domain mathematician searching for DEEP STRUCTURAL ANALOGS — not surface keyword matches.

PROBLEM:
Let A = {n_1 < n_2 < ...} be the sequence of powerful numbers (integers n such that if a prime p divides n, then p^2 divides n). Erdős conjectured (Problem 938) that there are only finitely many three-term arithmetic progressions of CONSECUTIVE terms n_k, n_{k+1}, n_{k+2}. Powerful numbers have density 0; classical Roth-type density results do not apply. The gap sequence (n_{k+1} - n_k) is irregular. Known: Habsieger 2019 verified no solutions exist for small ranges; van Doorn 2026 found very-large non-consecutive AP triples among powerful numbers.

STRUCTURE: A combinatorial problem about a deterministic zero-density sequence defined by a MULTIPLICATIVE predicate (prime-squarefull). The target is a SECOND-ORDER pattern (consecutiveness of an AP) — distinct from finding any AP. The gap function is shaped by additive interactions between multiplicative shells (kernel/squarepart factorization). Known tools (Roth, Szemerédi, cap-set slice-rank) all require positive density or finite-field structure. Local-global obstructions (mod 72) do not close because admissible AP triples mod-N GROWS with N.

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

1. **(i) The Analog Problem:** RNA stem-pair compensatory evolution. In Kimura’s compensatory-neutral model, developed for RNA secondary-structure covariation by Stephan/Kirby and later Chen et al., the viable genotypes are sparse sequence-space points whose paired nucleotides preserve a fold; the target pattern is not “any viable sequence,” but a second-order event `AB -> ab` where `Ab` and `aB` are deleterious while the double mutant restores fitness. Formally the cancellation is epistasis: `epsilon = log w_AB + log w_ab - log w_Ab - log w_aB`. Wilke, Lenski, and Adami studied this in RNA folding via neutral-mutant decay `w(d)=exp(-alpha d^beta)`, where compensatory mutations drive antagonistic epistasis. Sources: [Stephan & Kirby 1993](https://pubmed.ncbi.nlm.nih.gov/8224831/), [Chen et al. 1999](https://pubmed.ncbi.nlm.nih.gov/10791023/), [Wilke-Lenski-Adami 2003](https://bmcecolevol.biomedcentral.com/articles/10.1186/1471-2148-3-3).

2. **(ii) The Technique That Solved It There:** The successful tool is Kimura-Stephan two-locus compensatory fixation theory plus stochastic tunneling. The four-state system is `AB, Ab, aB, ab`, with endpoint fitness `1` and single-mutant fitnesses `1-s_1, 1-s_2`; Stephan interprets the inverse fixation time of `ab` as the compensatory substitution rate. Iwasa, Michor, and Nowak’s “stochastic tunnel” computes the rate of reaching type `2` without fixation of type `1`, exactly the biological version of crossing an invisible intermediate layer. Empirical RNA work then adds measurable covariates: nucleotide distance, helix length, position in helix, substitution rate, GC content. See [Iwasa-Michor-Nowak 2004](https://academic.oup.com/genetics/article/166/3/1571/6050386) and [Piskol-Stephan 2008](https://academic.oup.com/mbe/article/25/11/2483/1093346).

3. **(iii) The Obstruction To Direct Transplant:** The RNA method assumes a stochastic population process with parameters `N_e, mu, s, r` and a mutation graph whose local branching makes “tunneling rate” meaningful. Powerful numbers have no population clock, no mutation supply, no selection coefficient, and no independence of neighboring states. The obstruction is sharper: RNA compensation is a local two-locus defect repaired by a second local change, while a powerful AP triple requires exact global shell alignment  
`2 a_1^2 q_1^3 = a_0^2 q_0^3 + a_2^2 q_2^3`,  
with `q_i` squarefree, plus the induced-order condition that no other `a^2 q^3` lies in either gap. Stochastic tunneling estimates passage probability; Erdős’s problem asks for deterministic zero-temperature existence of induced equal-gap motifs.

4. **(iv) The Bridge:** Use a zero-temperature tunneling partition function. Let `P(n)=1` iff `n=a^2 q^3` with `q` squarefree, and define  
`I(x,d)=sum_{x<y<x+d} P(y)+sum_{x+d<y<x+2d} P(y)`.  
For dyadic scale `X`, compute  
`Z_X(lambda)=sum_{X<=x<2X} sum_{d>=1} P(x)P(x+d)P(x+2d) exp(-lambda I(x,d))`.  
Then `lim_{lambda->infty} Z_X(lambda)` counts exactly consecutive powerful AP triples in `[X,2X]`. Refine it by kernels: `Z_X(lambda; q_0,q_1,q_2)` restricts to `x+jd=a_j^2 q_j^3`. The measurable “compensation coefficient”  
`C_X(q_0,q_1,q_2)=E[I(x,d) | q_0,q_1,q_2]`  
identifies shell triples whose AP alignments are least blocked by intervening powerful numbers.
