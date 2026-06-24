# Cross-Domain Fusion Breakthroughs in Mathematics — Ground Truth Catalog

**Author:** Agent F4 of 10
**Date:** 2026-05-30
**Purpose:** Catalog famous math breakthroughs that came from cross-domain fusion, extract the recipe, and check whether our 30-problem shortlist contains analogous opportunities.

---

## 1. The 13-Breakthrough Catalog

| # | Breakthrough | Year | Domains Fused | Key Technique Transferred | Obvious? | Insight→Proof | Lit-search role |
|---|---|---|---|---|---|---|---|
| 1 | **Wiles + FLT** | 1995 | Diophantine NT × elliptic curves × modular forms × Galois reps | Modularity lifting; Hellegouarch–Frey curve attaches a Galois rep to a hypothetical FLT solution | NOT OBVIOUS (Frey's 1985 idea was a leap; Ribet 1986 verified the bridge) | ~10 years from Frey (1985) to Wiles–Taylor (1995) | Heavy: required absorbing Mazur's deformation theory, Hida theory, Tate twists |
| 2 | **Perelman + Poincaré** | 2003 | 3-manifold topology × geometric analysis × PDE × statistical mechanics | Ricci flow (Hamilton) + entropy functional (analogy to statistical mechanics) | NOT OBVIOUS (Hamilton had Ricci flow for 20 years; entropy was Perelman's leap) | ~21 years (Hamilton 1982 → Perelman 2003) | Moderate; Perelman synthesized Hamilton, Cheeger-Gromov, Aleksandrov geometry |
| 3 | **Atiyah-Singer Index Theorem** | 1963 | Algebraic topology × elliptic PDEs × differential geometry × K-theory | Equate analytic index (dim ker − dim coker) to topological index (characteristic classes) | OBVIOUS in hindsight (genus formula, Riemann-Roch, Hirzebruch suggested it) | ~5 years from precursor (Hirzebruch 1956) | Heavy: cobordism, K-theory, characteristic classes all pre-existed |
| 4 | **Faltings + Mordell** | 1983 | Arithmetic geometry × Arakelov theory × moduli spaces × p-adic Hodge | Arakelov height + Tate conjecture for abelian varieties | NOT OBVIOUS (Mordell open 60 years; Parshin's reduction step was the key linkage) | ~60 years (Mordell 1922 → Faltings 1983) | Heavy: Parshin's trick, Arakelov 1974, Tate 1966 — Faltings glued |
| 5 | **Maynard-Tao bounded gaps** | 2013 | Sieve theory × multidimensional optimization × linear algebra | Multidimensional sieve weight (vs. GPY one-dimensional) | NOT OBVIOUS (GPY had a wall; Maynard saw "score each variable separately") | ~8 years (GPY 2005 → Maynard 2013) | Moderate: built directly on GPY |
| 6 | **Zhang bounded gaps** | 2013 | Analytic NT × algebraic geometry (Deligne's Weil II) × spectral theory (Kuznetsov) | Smooth-modulus restriction of Bombieri-Vinogradov + Deligne's bounds for Kloosterman sums | NOT OBVIOUS (everyone thought BV was the wall; Zhang found a side door) | ~2 years (Zhang isolated 2011 → 2013) | Heavy: synthesized Bombieri/Friedlander/Iwaniec/Fouvry/Deligne |
| 7 | **Green-Tao primes in AP** | 2004 | Additive combinatorics × ergodic theory × sieve theory × harmonic analysis | Transference principle: extend Szemerédi from dense → pseudorandom-dense sets | NOT OBVIOUS (primes have density 0; Szemerédi inapplicable; Goldston-Yildirim sieve gave the pseudo-random envelope) | ~28 years (Szemerédi 1975 → Green-Tao 2004), but the fusion was ~3 years | Heavy: Furstenberg correspondence, Goldston-Yildirim, Gowers norms all pre-existed |
| 8 | **Helfgott + ternary Goldbach** | 2013 | Circle method (Hardy-Littlewood-Vinogradov) × explicit computation × GRH verification | Optimized large sieve + explicit constants + computer verification up to 10^27 | OBVIOUS in hindsight (Vinogradov 1937 had the asymptotic; just needed to make every constant effective) | ~76 years (Vinogradov 1937 → Helfgott 2013) | Heavy: 80 years of explicit-bound improvements |
| 9 | **Hough + Erdős minimum modulus** | 2015 | Analytic NT × probability (sequential probability measures) | "Distortion method" — reveal congruences in stages, each adds bounded entropy | NOT OBVIOUS (open 65 years; novel proof method invented) | ~65 years (Erdős 1950 → Hough 2015) | Light: novel method, not lit-search-derivable |
| 10 | **Ellenberg-Gijswijt cap set** | 2016 | Additive combinatorics × commutative algebra (polynomial method) | Croot-Lev-Pach polynomial method (rank of slice rank tensor) | NOT OBVIOUS (polynomial method was tried for ~10 years before correct variant found) | ~3 weeks after Croot-Lev-Pach (May 2016) | Heavy: built directly on Croot-Lev-Pach |
| 11 | **Perelman entropy** see #2 | — | — | — | — | — | — |
| 12 | **Hales + Kepler conjecture** | 1998 (formal 2017) | Discrete geometry × linear programming × interval arithmetic × graph theory | Reduce to 100,000 LP problems on tame planar graphs | OBVIOUS (L. Fejes Tóth proposed in 1953) | ~45 years (Tóth 1953 → Hales 1998) | Heavy: built on Tóth's program |
| 13 | **Polymath1 (Density Hales-Jewett)** | 2009 | Combinatorics × ergodic theory (replaced) | Replace ergodic Furstenberg-Katznelson with combinatorial proof providing explicit bounds | OBVIOUS in retrospect (everyone wanted elementary proof) | 37 days collaborative | Heavy: open problem, 38 years of context |
| 14 | **AlphaProof IMO 2024** | 2024 | Reinforcement learning × Lean formal verification × LLM × autoformalization | AlphaZero search over Lean proof states + LLM proposal distribution | NOT OBVIOUS (RL+formal math was tried for years, breakthrough was scale + autoformalizer) | ~5 years (early formal RL → AlphaProof 2024) | N/A — AI system, not human |
| 15 | **Scholze perfectoid spaces** | 2012 | p-adic Hodge × adic spaces × characteristic-p geometry (Fontaine-Wintenberger) | "Tilting": functorial bridge between char-0 and char-p perfectoid algebras | NOT OBVIOUS (Fontaine-Wintenberger 1979 had the local case; Scholze globalized) | ~33 years (FW 1979 → Scholze 2012) | Heavy: built on Faltings almost mathematics, Fontaine-Wintenberger |

---

## 2. The Recipe for Cross-Domain Fusion (What Mathematicians Actually Do)

Pattern observed across all 15 breakthroughs:

### Step 1 — IDENTIFY A WALL
Researcher confronts a problem where the natural method *almost* works but has a quantifiable obstruction. Examples:
- GPY (2005): sieve gives `liminf p_{n+1} − p_n < ∞` *if* Elliott-Halberstam beyond ½ holds — but EH is open.
- Furstenberg-Katznelson (1991): density Hales-Jewett proved but no quantitative bound (axiom of choice).
- FLT pre-1985: no known link to anything tractable.

### Step 2 — IMPORT A FOREIGN OBJECT
Look in an *adjacent* (NOT distant) domain for an object whose structure resolves the wall. The import is usually NOT random; it is suggested by:
- A formal analogy (Frey's elliptic curve mirrors Fermat solution structure)
- A weaker version solved by foreign method (Hamilton's Ricci flow for ≥0 Ricci → Perelman generalizes)
- An old conjecture re-read in new framework (Tate conjecture → Faltings)

### Step 3 — BUILD THE BRIDGE LEMMA
The *single* technical innovation that links the two sides. This is where the breakthrough lives:
- Wiles: modularity lifting theorem
- Maynard: multidimensional sieve weight
- Zhang: smooth-modulus restriction of BV
- Croot-Lev-Pach: polynomial vanishes on diagonal → slice-rank bound
- Hough: distortion method (sequential probability measures)

### Step 4 — VERIFY (often by exhaustion or computation)
Many modern fusion proofs end with:
- 100,000 LP verifications (Hales)
- 10^27 computational checks (Helfgott)
- Numerical witness tables (Polymath bounded gaps → 246)
- AlphaProof: lake build verifies the Lean term

### Step 5 — REFORMULATE (post-hoc)
Once a proof works, the community reformulates in cleaner language:
- Tao reformulated Croot-Lev-Pach via slice rank
- Atiyah-Bott-Patodi reproved Index Theorem via heat kernel
- Morgan-Tian rewrote Perelman's three papers

### The Honest Pattern
**~95% of the "fusion" is dependent on a 5-50 year body of prior work.** The breakthrough is usually a SINGLE bridge lemma plus the courage to attempt the synthesis. The two domains were already "talking" through earlier results; the fusion crystallized something already in the air.

---

## 3. Do Any of Our 30 Shortlist Problems Match a Known Fusion Pattern?

Our 30 candidates (`snipe_list_may30.md`) cluster into 5 archetypes:
- **C1** — Bounded-range bump (Brocard, Pollock)
- **C2** — Residue narrowing (Erdős 647 Cunningham, σ₀ multiplicativity)
- **C3** — E203/Sierpiński covering family
- **C4** — Greedy-CRT existence (Egyptian, Romanoff, Sidon)
- **C5** — FT diagnostic (Feit-Thompson p=3 q≡71 mod 72)

### Map to Known Fusion Patterns

| Our cluster | Known fusion analog | Plausibility |
|---|---|---|
| **C1 (Brocard bounded)** | Hales/Kepler: reduce to finite LP problems. *Pattern match: yes, both are "compress infinite into bounded native_decide".* | HIGH — but this is computation, not fusion of mathematical ideas |
| **C2 (Erdős 647 Cunningham)** | Heath-Brown three cubes: p-adic local solubility + analytic NT + numerics. *Pattern match: moderate — residue class narrowing is shared with class field theory questions.* | MODERATE — could plausibly find a Galois-side observation that closes more residues |
| **C3 (E203 / Sierpiński)** | Erdős covering systems → Hough's distortion method. *Pattern match: direct lineage; Sierpiński problems live in same family.* | HIGH-but-HARD — Hough's distortion is the *only* method that's broken these problems and it took 65 years |
| **C4 (Greedy-CRT existence)** | Maynard-Tao multidimensional sieve + Croot-Lev-Pach polynomial method. *Pattern match: weak — our problems are mostly bounded-decidable, not the dense-combinatorial regime where these methods fire.* | LOW |
| **C5 (Feit-Thompson p=3 q≡71)** | Class field theory + Galois cohomology + explicit Kummer extensions. *Pattern match: direct — this IS algebraic NT, and prior failed approaches (memory file) listed Kummer symbol, Eisenstein reciprocity, all standard approaches.* | LOW — already tried all known fusion patterns |

### Specific Problem-Level Findings

1. **Rank 17 (Sierpiński 78557 / Erdős 203 1D)** — has a known fusion analog: Selfridge's 8-prime covering set is a classical construction. This is NOT a novel-fusion target; it's a known-result formalization.

2. **Rank 22 (Erdős 647 lim variant)** — Erdős explicitly called this "extremely doubtful". This means **the natural fusion would be DISPROOF via σ₀-multiplicativity + counting** — a pattern analogous to Erdős' own probabilistic method. PLAUSIBLE.

3. **Rank 9 (Erdős 938 powerful 3-term APs)** — has a structural cousin in the abc conjecture and Schinzel's hypothesis H. A fusion target *might* exist via Vojta-style height bounds, but this is far above Aristotle's reach.

4. **Rank 10 (FT q=1583)** — pure computation; no fusion needed (the diagnostic file confirms single mod-exp). Not a fusion target.

5. **None of our 30** matches the "FLT-class" or "Maynard-class" pattern of bringing genuinely foreign machinery to bear. All 30 are within a narrow band of "bounded native_decide + small structural lemma".

---

## 4. Critical Analysis: What Fraction Are Findable By Our Tools?

### LLM Doing Literature Search

**Estimate: ~50-60% of these breakthroughs would have been *anticipated* by lit-search.**

Reasoning:
- For Wiles/FLT: literature already had Frey curves (1985), Ribet's theorem (1986). An LLM in 1990 reading the right papers would *recognize* the convergence — but the modularity lifting theorem itself required new mathematics.
- For Maynard: GPY was on every analytic NT person's desk. Lit-search would surface it. The "multidimensional" insight was a small leap — an LLM with strong analogical reasoning could plausibly suggest it.
- For Hough's distortion method: NO. Genuinely novel proof technique.
- For Perelman's entropy: NO. The cross-domain analogy (statistical mechanics) is loose; lit-search would not surface it.
- For Croot-Lev-Pach: BORDERLINE. The polynomial method had been tried for ~10 years on cap set; the specific variant was a 6-page novel construction.

**Score: ~40% lit-search would surface the connection; ~10-20% would actually find the bridge lemma; net ~25-30% findable.**

### LLM Doing Technique-Transfer Suggestion

**Estimate: ~15-25%.**

LLMs *can* suggest "try ergodic theory for combinatorics" or "try polynomial method here" — these are common-knowledge transfer suggestions. They CANNOT identify which specific bridge lemma is the right one. The work is in Step 3 (build the bridge lemma).

DeepMind's 2021 work on knots+Kazhdan-Lusztig showed an ML system *can* identify novel cross-domain connections (algebraic↔geometric knot invariants), but this is a different regime: ML finds *patterns* in computed data, not *proof bridges*.

### Aristotle (Lean-native, computational)

**Estimate: ~5%.**

Aristotle is fundamentally a verification + tactic-search engine. Looking at the 15 breakthroughs:
- **None** were closed by a tactic-level search. The bridge lemma in each case is a *named, definitionally non-trivial object* (modularity lifting, multidimensional sieve, perfectoid space, distortion method).
- Aristotle's success template (per A4 capability profile) is "bounded native_decide over precomputed witness table". This matches Hales' LP verification step and AlphaProof's IMO problems, but those are the *last 5%* of the breakthrough, after the human/AI has constructed the framework.
- The single case Aristotle could plausibly handle end-to-end is something like Polymath1 (density Hales-Jewett bound) IF given the elementary proof skeleton — but that proof is 50+ pages and requires non-trivial combinatorial intermediates.

**Honest answer: Aristotle is a verifier, not a discoverer of cross-domain fusion. Our pipeline pattern (bare-gap + auto-context) makes Aristotle a probabilistic completion engine for bridges Aristotle has *previously seen* (auto-context). It cannot invent the Frey curve.**

---

## 5. The Honest Bottom Line — Can Our Tools Plausibly DO Research Fusion?

**Verdict: NO at the breakthrough level; YES at the "next bump" level.**

### What our tools CAN do
1. Verify bounded computations (Hales/Helfgott-style "exhaust the residues")
2. Mechanically extend a previously successful template (Brocard 738 → 745 → 750)
3. Synthesize prior Aristotle results as scaffolding (auto-context) — this is genuinely useful inside a narrow corridor
4. Run RL-style proof search on problems with short proofs (AlphaProof-style; but we don't have AlphaProof)
5. Surface candidate connections via Grok/Gemini/Codex external models

### What our tools CANNOT do
1. Invent a Frey-style "attach a curve to a Diophantine solution" leap
2. Generalize a 1D method to nD without explicit human structural insight (Maynard's leap)
3. Recognize when a foreign technique applies (polynomial method on cap set took ~10 years post-availability)
4. Build the bridge lemma — this is where 100% of the math sits, and our tools don't generate it
5. Move outside the bounded-decidable corridor

### Implication for Strategy

Per CLAUDE.md PRIME DIRECTIVE: "We do NOT develop proof strategies. We state the open gap and let Aristotle find the path."

**This catalog confirms the directive is correct — but with a critical caveat:**
- Aristotle finds paths *within* known territory (variants of templates it has seen)
- Aristotle does NOT find paths *across* domains
- Therefore, "submitting bare conjectures aggressively" works for **mechanical extension** (C1 cluster, ~85% of advances) but cannot produce a Wiles-class breakthrough
- The 30-shortlist is correctly weighted toward C1/C2/C3 (bounded-decidable) and we should NOT expect cross-domain miracles

The realistic Aristotle pipeline output is "many small wins via mechanical extension and witness verification". The breakthroughs in this catalog all required human cross-domain insight; assuming Aristotle replicates that pattern is unfounded.

---

## Sources

### Wiles + FLT
- [Wiles's proof of Fermat's Last Theorem - Wikipedia](https://en.wikipedia.org/wiki/Wiles's_proof_of_Fermat's_Last_Theorem)
- [Modularity theorem - Wikipedia](https://en.wikipedia.org/wiki/Modularity_theorem)
- [The Core of Fermat's Last Theorem Just Got Superpowered - Quanta Magazine](https://www.quantamagazine.org/the-core-of-fermats-last-theorem-just-got-superpowered-20250602/)

### Perelman + Poincaré
- [Ricci Flow and the Poincaré Conjecture - Clay Math monograph](https://www.claymath.org/library/monographs/cmim03.pdf)
- [The Poincaré Conjecture--Proved - Science](https://www.science.org/doi/10.1126/science.314.5807.1848)
- [Hamilton-Perelman's Proof - arXiv](https://arxiv.org/abs/math/0612069)

### Atiyah-Singer
- [Atiyah–Singer index theorem - Wikipedia](https://en.wikipedia.org/wiki/Atiyah%E2%80%93Singer_index_theorem)
- [The Atiyah-Singer index theorem - arXiv](https://arxiv.org/abs/2107.03557)

### Faltings + Mordell
- [Faltings's theorem - Wikipedia](https://en.wikipedia.org/wiki/Faltings's_theorem)
- [Gerd Faltings Proves Mordell's Conjecture (1983) - Encyclopedia.com](https://www.encyclopedia.com/science/encyclopedias-almanacs-transcripts-and-maps/gerd-faltings-proves-mordells-conjecture-1983)

### Maynard-Tao / Zhang / Polymath
- [Together and Alone, Closing the Prime Gap - Quanta Magazine](https://www.quantamagazine.org/mathematicians-team-up-on-twin-primes-conjecture-20131119/)
- [The "bounded gaps between primes" Polymath project - arXiv](https://ar5iv.labs.arxiv.org/html/1409.8361)
- [Yitang Zhang's Spectacular Mathematical Journey - IAS](https://www.ias.edu/ideas/2014/zhang-breakthrough)

### Green-Tao
- [Green–Tao theorem - Grokipedia](https://grokipedia.com/page/Green%E2%80%93Tao_theorem)
- [The Green-Tao Theorem on Arithmetic Progressions - AMS](https://www.ams.org/journals/bull/2006-43-01/S0273-0979-05-01086-4/S0273-0979-05-01086-4.pdf)

### Helfgott + Goldbach
- [The ternary Goldbach conjecture is true - arXiv](https://arxiv.org/abs/1312.7748)
- [Goldbach's conjecture - Grokipedia](https://grokipedia.com/page/Goldbach's_conjecture)

### Hough + covering systems
- [On covering systems of integers - arXiv](https://arxiv.org/pdf/1705.04372)
- [Erdős covering systems - arXiv](https://arxiv.org/pdf/2211.01417)

### Heath-Brown + cubes
- [Sums of three cubes - Grokipedia](https://grokipedia.com/page/Sums_of_three_cubes)
- [On a question of Mordell - PNAS](https://www.pnas.org/doi/pdf/10.1073/pnas.2022377118)

### Scholze + perfectoid
- [Perfectoid Spaces and their Applications - ICM](https://www.math.uni-bonn.de/people/scholze/ICM.pdf)
- [The Work of Peter Scholze - arXiv](https://arxiv.org/pdf/1909.07222)

### Hales + Kepler
- [Kepler conjecture - Wikipedia](https://en.wikipedia.org/wiki/Kepler_conjecture)
- [Sphere packings I - arXiv](https://arxiv.org/pdf/math/9811073)

### Polymath
- [Polymath Project - Wikipedia](https://en.wikipedia.org/wiki/Polymath_Project)
- [Polymath and The Density Hales-Jewett Theorem - ResearchGate](https://www.researchgate.net/publication/225842260_Polymath_and_The_Density_Hales-Jewett_Theorem)

### Cap set
- [Cap set - Wikipedia](https://en.wikipedia.org/wiki/Cap_set)
- [The Polynomial Method and the Cap Set Problem - MIT LIDS](https://lids.mit.edu/news-and-events/events/polynomial-method-and-cap-set-problem)

### AlphaProof
- [AI achieves silver-medal standard solving IMO problems - DeepMind](https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/)
- [Olympiad-level formal mathematical reasoning with RL - Nature](https://www.nature.com/articles/s41586-025-09833-y)

### Furstenberg / Szemerédi
- [Szemerédi's theorem - Wikipedia](https://en.wikipedia.org/wiki/Szemer%C3%A9di's_theorem)
- [Ergodic Methods in Additive Combinatorics - arXiv](https://arxiv.org/pdf/math/0608105)

### Erdős-Selberg PNT
- [The Elementary Proof of the Prime Number Theorem - Goldfeld](https://www.math.columbia.edu/~goldfeld/ErdosSelbergDispute.pdf)

### AI-assisted knot theory
- [Machine learning helps mathematicians make new connections - ScienceDaily](https://www.sciencedaily.com/releases/2021/12/211201111925.htm)
