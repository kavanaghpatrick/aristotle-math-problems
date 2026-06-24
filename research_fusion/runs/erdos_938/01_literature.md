# Literature breadth — erdos_938
Date: 2026-05-30  Stage: 1
Domains queried: nt, analytic_nt, additive_combinatorics, diophantine, arithmetic_geometry, combinatorics
Keywords used: powerful numbers, arithmetic progression, squarefull, consecutive integers
Papers retrieved: 7
Lean source: `formal-conjectures/FormalConjectures/ErdosProblems/938.lean`

## External references
- https://www.erdosproblems.com/938

## erdosproblems.com excerpt
```
938 | Erdős Problems Forum Inbox Favourites Tags More FAQ Prizes Problem Lists Definitions Links Forum Menu Inbox Favourites Tags FAQ Prizes Problem Lists Definitions Links Go Go Dual View Random Solved Random Open OPEN This is open, and cannot be resolved with a finite computation. Let $A=\{n_1&#60;n_2&#60;\cdots\}$ be the sequence of powerful numbers (if $p\mid n$ then $p^2\mid n$). Are there only finitely many three-term progressions of consecutive terms $n_k,n_{k+1},n_{k+2}$? #938 : [Er76d] number theory | powerful The open status of this problem reflects the current belief of the owner of this website. There may be literature on this problem that I am unaware of, which may partially or completely solve the stated problem. Please do your own literature search before expending significant effort on solving this problem. If you find any relevant literature not mentioned here, please add this in a comment. Comment activity that has not yet been incorporated into the remarks None Partial Solution There are claims of partial results and/or a path to a solution in the comments. Erdős also conjectured (see [364] ) that there are no triples of powerful numbers of the shape $n,n+1,n+2$.
```

## Domain: nt (4/8)
### Mixed thresholds in the Lonely Runner Conjecture (arxiv:2605.27941)
- Authors: Alathea Jensen
- Year: 2026
- Abstract: The Lonely Runner Conjecture states that if $k+1$ runners start at the same point on a unit-length circular track and run with distinct constant speeds, then each runner is at some time at least $1/(k+1)$-distant from every other runner. Equivalently, for every tuple of $k$ distinct positive integer speeds $s_1,\ldots,s_k$, there is a real number $t$ such that $\|s_i t\|\geq \frac{1}{k+1}$ for all $i$. We introduce and study a version of the conjecture in which the required distances may vary with $i$. For $\mathbf d=(d_1,\ldots,d_k)\in(0,1/2]^k$, let $\mathsf{MLPS}_k$ be the set of vectors such that, for every choice of distinct positive integer speeds $s_1,\ldots,s_k$, there is a real number $t$ with $\|s_i t\|\geq d_i$ for all $i$. We give an exact characterization of $\mathsf{MLPS}_2$. We also use Fourier series for distance-threshold indicator functions to obtain an arithmetic progression summation formula and an exact two-function integral formula for unequal thresholds.
- Relevance: Mentions arithmetic progression; potential structural overlap.

### Linnik's problem for multiplicative functions (arxiv:2605.27833)
- Authors: Kaisa Matomäki, Joni Teräväinen
- Year: 2026
- Abstract: We study a multiplicative function analogue of Linnik's problem on the least prime in an arithmetic progression. Let $h\colon \mathbb{N}\to\mathbb{R}\setminus\{0\}$ be a multiplicative function, and let $a \pmod q$ be a reduced residue class. We ask how far one must go before finding square-free integers $n_1,n_2\equiv a \pmod q$ with $h(n_1)<0<h(n_2)$. We show that one can always find such integers with $n_1,n_2\le q^{2+o(1)}$, unless the sign of $h$ strongly pretends to be a real Dirichlet character modulo $q$. Thus, apart from this natural character obstruction, sign changes of a multiplicative function occur in every reduced residue class at a scale corresponding essentially to the square root barrier. In the special case of the Liouville function $λ$ this improves on a recent result of Ford and Radziwiłł and matches, up to $q^{o(1)}$ factors, what was previously known conditionally under the generalized Riemann hypothesis.
- Relevance: Mentions arithmetic progression; potential structural overlap.

### A proof of the $4,7$ cases of Sylvester's conjecture on cube sums (arxiv:2605.25917)
- Authors: Hongbo Yin
- Year: 2026
- Abstract: In this paper, we prove that every prime $p$ which is congruent to $4,7$ modulo $9$ is the sum of two rational cubes. This is $2/3$ of Sylvester's conjecture which has a history of nearly 150 years since 1879. In the proof, we use recent progress on Full BSD conjecture of rank $0$ elliptic curves in \cite{BF} to deduce that the Manin-Stevens constants of some families of elliptic curves are units. We also use recent solutions of Unbounded Denominators Conjecture in \cite{CDT} to prove that some cubic roots of modular functions are invariant under some congruence subgroups. Instead of using the Unbounded Denominators Conjecuture, we also give another conditional proof assuming the GRH for number fields or Artin's primitive root conjecture for arithmetic progressions.
- Relevance: Mentions arithmetic progression; potential structural overlap.

### On the binary digits of the Erdős-Borwein constant (arxiv:2605.24160)
- Authors: John M. Campbell
- Year: 2026
- Abstract: In a landmark paper on arithmetical properties of Lambert series, Erdős proved that $\sum_{n=1}^{\infty} \frac{1}{2^{n} - 1}$ is irrational. This value $E$ is now referred to as the Erdős-Borwein constant. Crandall, in 2012, studied properties of the base-2 expansion of this constant, and left the following as an open problem: Does the string $11$ occur infinitely often in the base-2 expansion of $E$? This open problem was also subsequently noted by Shallit. We succeed in introducing a full proof that solves Crandall's problem in the affirmative. Our proof combines a congruence construction in the spirit of Erdős and an estimate due to Alford, Granville, and Pomerance for the counting function for primes in arithmetic progressions. Our argument was developed through extensive interactions with GPT-5.5 Pro.
- Relevance: Mentions arithmetic progression; potential structural overlap.

## Domain: analytic_nt (0/8)
No 2020-2026 papers found for this domain.

## Domain: additive_combinatorics (1/8)
### Pairs of square-free arithmetic progressions in infinite words (arxiv:2605.29853)
- Authors: Thomas Delépine, Pascal Ochem, Matthieu Rosenfeld
- Year: 2026
- Abstract: We study a question of Harju from 2019 regarding the existence of infinite ternary square-free words whose subsequences modulo $p$ and $q$ are also square-free for relatively prime integers $p$ and $q$. Among such pairs $(p, q)$ with $p, q \geq 3$, the only two pairs with this property known prior to this work were $(3, 11)$ and $(5, 6)$. We prove that there are finitely many pairs $(p, q)$ of relatively prime integers with $p, q \geq 3$ for which there is no infinite ternary square-free word whose subsequences modulo $p$ and $q$ are square-free. To prove our result, we combine different techniques, including the construction of words from multi-valued square-free morphisms and circular square-free morphisms. We also introduce the notion of square-free transducers, a generalization of square-free morphisms that may be of independent interest.
- Relevance: No direct keyword match; flagged as adjacent.

## Domain: diophantine (0/8)
No 2020-2026 papers found for this domain.

## Domain: arithmetic_geometry (0/8)
No 2020-2026 papers found for this domain.

## Domain: combinatorics (2/8)
### Finding a Solution to the Erdős-Ginzburg-Ziv Theorem in Linear Time (arxiv:2605.21753)
- Authors: Sunghyeon Jo
- Year: 2026
- Abstract: The Erdős-Ginzburg-Ziv theorem states that every sequence of 2n - 1 integers contains a subsequence of length n whose sum is divisible by n. Choi, Kang, and Lim gave a simple deterministic O(n log n) algorithm for finding such a subsequence, and Leung recently improved this to O(n log log log n). We give a deterministic linear-time algorithm. The core is a linear-time algorithm for the following prime target subset-sum problem: given p - 1 nonzero residues in Z_p and a target residue, find a subset with the prescribed sum. Our algorithm maintains a compact arithmetic-progression representation of reachable sums. When two progressions intersect, a bounded Frobenius interval in their sum allows them to be merged into one longer progression, with enough growth to pay for the update. When the representation either contains a full progression or covers all nonzero residues, the target residue is recovered constructively. The standard multiplicative reduction then extends the prime algorithm
- Relevance: No direct keyword match; flagged as adjacent.

### Box Progressions, Abelian Power-Free Morphisms and A Sieve Technique for the Template Method (arxiv:2605.20504)
- Authors: Sadık Eyidoğan, Haydar Göral, Nihan Tanısalı
- Year: 2026
- Abstract: Given balls and boxes both enumerated by the positive integers, we consider a sequential allocation of the balls into the boxes. We fix $\ell \ge 2$. Proceeding in increasing order of box labels, assign to each box the next $r$ smallest balls for some $ 1\leq r\leq\ell$. Given an integer $k\ge 3$, is there a natural number $N$ such that in any placement of $N$ balls into boxes, there exist $k$ balls whose labels and box labels each form a $k$-term arithmetic progression? We address this question by identifying abelian power-free fixed points of morphisms over a binary alphabet. We present sufficient conditions under which a morphism is abelian $k$-power-free. Our conditions extend Dekking's result over a binary alphabet and offer a weaker, yet more effective alternative to Carpi's. Combining Dekking's result with the template method of Currie and Rampersad, we develop a sieve technique that significantly reduces the number of parents that must be examined to establish abelian power-fre
- Relevance: Mentions arithmetic progression; potential structural overlap.
