# Strategy Document: Pursuing Novel Mathematical Results with Aristotle

## Purpose
This document analyzes what Aristotle is good at, what it's bad at, and identifies the highest-value open problems where we can make genuinely novel contributions. It serves as context for a multi-AI debate on our next research direction.

---

## Part 1: What Aristotle Actually Does (Evidence-Based)

### Performance by Mode
| Mode | Success Rate | Evidence |
|------|-------------|----------|
| INFORMAL (.txt sketch → proof) | **100%** (10/10) | Constructs entire proofs from 50-100 line natural language |
| FORMAL sorry=0 (verification) | **100%** (6/6) | Pure rubber-stamping, no novel content |
| FORMAL sorry=1+ (NT/algebra) | ~70-80% | Works when Mathlib API is rich (slot572 from scratch) |
| FORMAL sorry=1+ (combinatorics) | **0%** (0/183) | Never succeeds. Do not attempt. |

### Performance by Domain
| Domain | Success Rate | Notes |
|--------|-------------|-------|
| Number Theory | **85-100%** | Rich Mathlib: ZMod, totient, Jacobi, primes, divisibility |
| Algebra (groups) | **85-100%** | Group theory, cyclic, dihedral, subgroup lattice |
| Analysis | 25-100% | Varies wildly; real analysis OK, functional analysis harder |
| Combinatorics | **7-50%** | Only succeeds on concrete Fin n; abstract graph theory fails |

### What Aristotle Excels At
1. **Structural lemmas of open problems** (not full resolutions)
   - FT p=3: 14 lemmas from one sketch (slot560, 345 lines)
   - Lehmer totient: 7 structural constraints on counterexamples (slot591)
   - These are REAL MATH — constraints any counterexample must satisfy

2. **5:1 expansion from natural language**
   - 53-line sketch → 117-line proof (slot562, Leinster cyclic)
   - 47-line sketch → 345-line proof (slot560, Feit-Thompson)
   - Aristotle discovers Mathlib APIs, invents proof structures, fills logical gaps

3. **Bounded/computational + structural combinations**
   - slot581: No 4 consecutive powerful numbers + modular constraints
   - slot559: All 28 prime pairs (p,q) with p,q < 20 verified for FT

4. **Iterative deepening on a problem**
   - FT p=3: slot560 → slot590-615 = 20+ submissions, 6000+ lines of proven infrastructure
   - Each continuation references prior lemma names, building scaffolding

### What Aristotle Cannot Do
1. **Prove genuinely open conjectures outright** — it proves structural lemmas, not full resolutions
2. **Abstract combinatorics** — graph theory without concrete vertices fails
3. **Assembly of multiple sub-cases** — slot549 had 4 sub-cases proven, assembly still had 12 sorry
4. **Existence proofs for open problems** — slot597 (Erdős 307) likely to fail on existence claim

---

## Part 2: Honest Assessment of Our 50 Recent Submissions

### What We Actually Did (slots 565-621)
| Category | Count | Value |
|----------|-------|-------|
| Formalizing known results (Euler form, Ryavec, etc.) | ~30 | LOW — re-proving what's known |
| FT p=3 infrastructure (known QR/CR techniques) | ~14 | MEDIUM — deep but uses standard methods |
| Counterexamples (Casas-Alvero, Erdős 137) | ~4 | MEDIUM — useful falsification |
| Genuinely novel mathematical contributions | **0** | **ZERO** |

### The Problem
We've been feeding Aristotle known results and calling the proofs "novel" because they're newly formalized. But formalization of known math is not novel math. The user directive is clear: **"I don't think anyone cares about formalization — we care about NOVEL solutions."**

### What "Novel" Means
A genuinely novel result is one that:
1. Proves something not previously known to be true (or false)
2. Establishes new structural constraints on open problems
3. Closes a gap between known bounds
4. Discovers a new connection between known results
5. Extends a solved case to the next unsolved case

**FT slot560 (14 structural lemmas) was our closest to genuine novelty** — those constraints on p=3 case are new mathematical content. But slot590-615 largely applied known techniques (QR, cubic characters) to cases where the answer was predictable.

---

## Part 3: Where Novel Contributions Are Possible

### Strategy: "Gap-Closing" on Partially Solved Problems

The highest-value approach is finding problems where:
- **Part A is solved** (gives us proof techniques and confidence)
- **Part B is open** (but close enough that the solved techniques might extend)
- **The gap is small** (one parameter change, one hypothesis weakened, one bound tightened)

### TIER S: Tiny Gap — Direct Extension of Proven Results

**1. Erdős 257: Lambert Series Subsums** (NT, irrationality)
- **SOLVED**: ∑_{n≥1} d(n)/2^n is irrational (Erdős 1948)
- **OPEN**: For ANY infinite A ⊆ ℕ, is ∑_{n∈A} 1/(2^n - 1) irrational?
- **Gap**: Full sum → arbitrary infinite subsum
- **Approach**: The full sum identity ∑ 1/(2^n-1) = ∑ d(n)/2^n gives us the tool. For infinite A, the subseries still has enough irrationality structure. Lambert series irrationality criteria (Erdős 1948, Bundschuh-Väänänen) apply to subsums. Key: show partial sums approximate badly by rationals.
- **Aristotle task**: Prove irrationality of ∑_{n∈A} 1/(2^n-1) for specific infinite A (e.g., A = primes, A = squares), then attempt general case.
- **Formal-conjectures file**: `ErdosProblems/257.lean`

**2. Erdős 258: Divisor Function Series — Drop Monotonicity** (NT, irrationality)
- **SOLVED**: Erdős-Straus proved ∑ d(n)/(a₁···aₙ) irrational for MONOTONE a_n → ∞
- **OPEN**: Same result without monotonicity (just a_n → ∞)
- **Gap**: Remove one hypothesis
- **Approach**: The Erdős-Straus proof uses the asymptotic dominance of denominators. Without monotonicity, subsequences can temporarily shrink. Need: show the irrationality measure is preserved under reorderings, or use a different irrationality criterion that doesn't need monotonicity.
- **Aristotle task**: Prove the monotone case (slot604 already proved Erdős-Straus). Then prove a weakened version (e.g., eventually monotone, or bounded oscillation).
- **Formal-conjectures file**: `ErdosProblems/258.lean`

**3. Erdős 1052: Unitary Perfect Finiteness** (NT, arithmetic functions)
- **SOLVED**: All unitary perfect numbers are EVEN (we proved this in slot567!)
- **OPEN**: Are there finitely many unitary perfect numbers?
- **Gap**: Parity → finiteness
- **Approach**: We proved evenness. The 5 known unitary perfects are 6, 60, 90, 87360, 146361946186458562560000. The largest has 24 prime factors. Finiteness would follow from: (a) showing the number of prime factors is bounded, (b) showing each prime power in the factorization is bounded, (c) using the ABC conjecture to bound solutions. Wall's 1972 result: no odd unitary perfect exists. So finiteness reduces to bounding even unitary perfects.
- **Aristotle task**: Prove upper bounds on number of prime factors of unitary perfect numbers. Prove any unitary perfect n satisfies n < f(ω(n)) for some explicit f.
- **Formal-conjectures file**: `ErdosProblems/1052.lean`

### TIER A: Small Gap — Bounded Case to General

**4. Erdős 1107: Sums of r-Powerful Numbers** (NT, additive)
- **SOLVED**: Heath-Brown proved r=2 (every large n = sum of 3 square-full numbers)
- **OPEN**: For all r ≥ 2, every large n = sum of ≤ (r+1) r-powerful numbers
- **Gap**: r=2 → general r
- **Approach**: Heath-Brown's method uses lattice point counting in the cube root. For general r, need r-th root lattice counting. The density of r-powerful numbers is n^(1/r), so heuristically (r+1) summands should suffice by Waring-type arguments.
- **Aristotle task**: Prove r=3 case (every large n = sum of 4 cube-full numbers), or prove general bound assuming r=2 case.
- **Formal-conjectures file**: `ErdosProblems/1107.lean`

**5. Erdős 141: Consecutive Primes in AP** (NT, primes)
- **SOLVED**: Verified for k ≤ 10 (computational witnesses exist)
- **OPEN**: k=11 (first unknown case), general k
- **Gap**: k=10 → k=11 (or arbitrary k)
- **Approach**: Green-Tao proves arbitrary-length APs in primes, but not CONSECUTIVE primes. Maynard-Tao proves bounded prime gaps. The consecutive constraint makes this fundamentally harder. For k=11, a computational search would be massive but feasible with enough compute. For general k, conditional on Dickson's conjecture.
- **Aristotle task**: Prove structural results about consecutive prime APs (e.g., common difference must satisfy certain divisibility conditions). Prove conditional results assuming Dickson's.
- **Formal-conjectures file**: `ErdosProblems/141.lean`

**6. Leinster: Infinitely Many Leinster Groups** (Algebra, group theory)
- **SOLVED**: 8 structural results (cyclic ↔ perfect, no p-group, no semisimple, no symmetric, no p²q², dihedral ↔ odd perfect, nonabelian exist, abelian ↔ cyclic perfect)
- **OPEN**: Are there infinitely many non-isomorphic Leinster groups?
- **Gap**: Classification → counting
- **Approach**: If there are infinitely many perfect numbers, then infinitely many cyclic Leinster groups exist (we proved this conditionally in slot575). For unconditional result: Tóth (2009) found non-nilpotent Leinster groups for each of the first 11 primes. The question is whether the construction generalizes.
- **Aristotle task**: Prove that for each prime p, there exists a non-nilpotent Leinster group of order divisible by p (generalizing Tóth). Or prove unconditionally that infinitely many non-isomorphic Leinster groups exist using the known examples.
- **Formal-conjectures file**: `Wikipedia/LeinsterGroup.lean`

### TIER B: Medium Gap — Structural Understanding → Open Case

**7. Erdős 123: d-Complete Sequences** (NT, additive)
- **SOLVED**: 2^k · 3^l is d-complete (Gross). 3^k · 5^l · 7^m is d-complete (Erdős-Lewin).
- **OPEN**: For pairwise coprime a,b,c, is {a^k · b^l · c^m} always d-complete?
- **Gap**: Two special cases → general coprime triples
- **Approach**: Both proofs use different techniques (binary representation vs modular arithmetic). A unified approach using the coprimality condition would generalize. The key property: coprime generators create dense enough representation via Chinese Remainder.
- **Aristotle task**: Prove d-completeness for a third triple (e.g., 2^k · 5^l · 7^m). Then attempt the general coprime result.
- **Formal-conjectures file**: `ErdosProblems/123.lean`

**8. Erdős 1148: Difference of Squares Representation** (NT, additive)
- **SOLVED**: Every large n = x² + y² - z² with max(x²,y²,z²) ≤ n + 2√n (trivial)
- **OPEN**: Can we get max(x²,y²,z²) ≤ n?
- **Gap**: Tighten bound by 2√n
- **Approach**: The trivial bound uses z=0, x²+y²=n (Fermat). To beat n, need cancellation: x²+y² slightly larger than n, z² absorbs the excess. Lattice point counting near the circle x²+y²=n+z² with z small.
- **Aristotle task**: Prove bound n + c√n for explicit c < 2. Or prove the exact bound for n in certain residue classes.
- **Formal-conjectures file**: `ErdosProblems/1148.lean`

**9. Andrica's Conjecture: Bounded Case** (NT, prime gaps)
- **SOLVED**: Ferreira (2023) proved √p_{n+1} - √p_n < 1 for all sufficiently large n
- **OPEN**: Prove for ALL n (finitely many small cases remain)
- **Gap**: "Sufficiently large" → explicit constant
- **Approach**: Ferreira's proof gives an effective constant N₀ beyond which the result holds. For n < N₀, computational verification. If N₀ is reasonable (say < 10^12), this is checkable.
- **Aristotle task**: Prove Ferreira's result (asymptotic). Then prove for n < 10^6 computationally. The gap is the intermediate range.
- **Formal-conjectures file**: `Wikipedia/Andrica.lean`

**10. Erdős 364: Consecutive Powerful Numbers** (NT)
- **SOLVED (by us!)**: No 4 consecutive powerful numbers (slot581). Bounded verification. Modular constraints.
- **OPEN**: No 3 consecutive powerful numbers.
- **Gap**: k=4 → k=3
- **Approach**: We proved k=4 using pigeonhole on residues mod small primes. For k=3, the constraint is tighter. Among n, n+1, n+2, at least one is ≡ 2 mod 4 (hence not powerful if 4 ∤ that number). But this only works if the number has an odd prime factor to the first power. Need: among any 3 consecutive, find one that must have a prime to the first power.
- **Aristotle task**: Prove modular constraints that rule out 3 consecutive powerful numbers modulo specific primes. Build toward full k=3 case.
- **Formal-conjectures file**: `ErdosProblems/364.lean` (variant in `137.lean`)

### TIER C: Higher Risk / Higher Reward

**11. Odd Perfect Numbers: Strengthen Euler's Form** (NT)
- **SOLVED (by us!)**: n = p^α · m², p ≡ α ≡ 1 mod 4 (slot619)
- **OPEN**: Prove n > 10^1500 (current best: 10^1500 by Ochem-Rao 2012)
- **Gap**: Structure → size bounds
- **Approach**: Use Euler's form plus divisibility constraints. Each prime factor of m must satisfy p ≡ 1 mod 4. The number of prime factors ω(n) ≥ 10 (Hare-Nielsen). Component analysis: if p^α is the special prime, then σ(p^α) = (p^{α+1}-1)/(p-1) must be 2m² times a coprime factor.
- **Aristotle task**: Prove ω(n) ≥ 10 for odd perfect n (Nielsen 2015). Prove further constraints on the exponents.
- **Formal-conjectures file**: `Wikipedia/OddPerfectNumber.lean`

**12. Erdős 413: Omega Barriers** (NT, arithmetic functions)
- **SOLVED**: Erdős proved analogous result for expProd has positive density
- **OPEN**: Infinitely many n where m + Ω(m) ≤ n for all m < n
- **Gap**: expProd → Ω barrier
- **Approach**: expProd barriers are n where m · rad(m) ≤ n fails. Ω barriers are about additive structure. The techniques differ but the philosophy is similar: find n that are "unreachable" by smaller numbers.
- **Aristotle task**: Prove infinitude of Ω-barriers conditional on known results about Ω distribution. Prove structural properties of Ω-barriers.
- **Formal-conjectures file**: `ErdosProblems/413.lean`

**13. Feit-Thompson p=3, q ≡ 71 mod 72** (NT, character theory)
- **SOLVED**: All other mod-8 residue classes for q (slots 590, 598, 599, 601-603, 608, 610-613)
- **OPEN**: q ≡ 71 mod 72 (the hardest subcase)
- **Gap**: This is the LAST remaining case for p=3
- **Approach**: All character methods (QR, CR, QR4) give trivial results (χ_d(3) = 1 for all d | 12). Need fundamentally new approach: perhaps p-adic analysis, Eisenstein integers, or class field theory over Q(ζ₃). The Kummer symbol is circular. The Eisenstein reciprocity formula exists but is not simpler.
- **Aristotle task**: Prove new structural constraints on q ≡ 71 mod 72. Use Z[ω] arithmetic to derive non-trivial congruences. Explore sextic character approach.
- **This is the HIGHEST NOVELTY target if successful** — would complete the p=3 case of a famous theorem.

**14. Singmaster's Conjecture** (NT/Combinatorics)
- **SOLVED**: Kane (2007) proved multiplicity ≤ 8 for sufficiently large values
- **OPEN**: Global bound, or sharper bound
- **Gap**: Asymptotic → explicit
- **Approach**: Repeated binomial coefficients C(n,k) = C(m,j) where (n,k) ≠ (m,j). Known: C(n,2) = C(m,2) has infinitely many solutions (Pell equation). Multiplicity 6 achieved by C(3003,1) = C(78,2) = C(15,5) = C(14,6). Upper bound: Abbott-Erdős-Hanson proved O(n^{2/3+ε}).
- **Aristotle task**: Prove Kane's result (multiplicity ≤ 8 for large values). Prove multiplicity ≤ 6 for C(n,k) with k ≥ 3.
- **Formal-conjectures file**: `Wikipedia/Singmaster.lean`

**15. Gilbreath's Conjecture: Bounded Verification** (NT)
- **SOLVED**: Verified computationally to very large k
- **OPEN**: Prove for all k (or even for all k ≤ 10^10)
- **Gap**: Computational → formal proof
- **Approach**: The recursive definition d^0(n) = p_n, d^{k+1}(n) = |d^k(n+1) - d^k(n)| has d^k(0) = 1 for all computed k. The connection to prime gaps is deep: Gilbreath follows from sufficiently uniform prime gaps.
- **Aristotle task**: Prove Gilbreath for k ≤ 100 via bounded computation. Prove conditional results: Gilbreath follows from Andrica's conjecture (or from bounded prime gaps).
- **Formal-conjectures file**: `Wikipedia/Gilbreath.lean`

---

## Part 4: The Novel Contribution Taxonomy

### What counts as "genuinely novel"?

**TIER 1 — First-Ever Proofs** (highest value)
- Proving something that was OPEN (sorry in formal-conjectures, not in Mathlib)
- Examples: Closing Erdős 257, proving k=3 for Erdős 364, completing FT p=3

**TIER 2 — New Structural Results** (high value)
- Constraints on hypothetical counterexamples that weren't known before
- Examples: New bound on ω(odd perfect), new modular constraint on unitary perfects

**TIER 3 — Gap Closures** (medium-high value)
- Tightening bounds, extending from case k to case k+1
- Examples: Erdős 1148 (tighten to n), Erdős 1107 (r=3 case)

**TIER 4 — Conditional Results** (medium value)
- Proving A → B where A is open but the implication is new
- Examples: Gilbreath conditional on Andrica, Leinster infinitude conditional on perfect numbers

**TIER 5 — Re-formalizations** (low value — what we've been doing)
- Proving known results in Lean that weren't in Lean before
- This is where 90%+ of our 50 recent submissions fall

---

## Part 5: Recommended Strategy

### The "Structural Lemma" Approach
Instead of trying to prove open conjectures outright (which Aristotle can't do), we should:

1. **Pick an open problem** with partial progress
2. **Identify the specific gap** between known and unknown
3. **Design structural lemmas** that constrain the solution space
4. **Write INFORMAL sketches** proposing these lemmas
5. **Let Aristotle prove the lemmas** (its sweet spot)
6. **Iterate** — each proven lemma informs the next sketch

This is exactly what worked for Feit-Thompson (20+ submissions, 6000+ lines). We need to do it for OTHER problems, not just FT.

### The "Computational-First" Approach
For problems with computational leverage:

1. **Compute** witnesses, patterns, counterexamples in Rust/Python
2. **Identify** structure in the computational data
3. **Conjecture** structural results based on patterns
4. **Sketch** the conjectured structure for Aristotle
5. **Prove** (or disprove) via INFORMAL

### Priority Order for Next Submissions
1. **Erdős 364 k=3** (we already proved k=4, techniques in hand)
2. **Erdős 1052 finiteness** (we already proved evenness, structure understood)
3. **Erdős 257 subsums** (direct extension of solved irrationality result)
4. **FT p=3 q≡71 mod 72** (highest impact if solved, but hardest)
5. **Leinster infinitely many** (unconditional approach, group theory domain)
6. **Odd perfect ω ≥ 10** (extend our Euler form result)
7. **Erdős 258 non-monotone** (weaken one hypothesis)
8. **Erdős 1107 r=3** (extend from r=2)
9. **Erdős 1148 tight bound** (tighten by 2√n)
10. **Andrica bounded** (close the gap between asymptotic and all n)

---

## Part 6: Questions for Debate

1. **Which problem has the highest probability of yielding a genuinely novel result** given Aristotle's capabilities?
2. **Should we focus depth (many submissions on one problem) or breadth (one submission each on many problems)?**
3. **Is the "structural lemma" approach the right one, or should we try something fundamentally different?**
4. **Which of the 15 candidates is most likely to succeed in 5-10 Aristotle submissions?**
5. **Are there approaches besides Aristotle that would be more productive for novel results?**
6. **What computational explorations should we run BEFORE writing sketches?**
