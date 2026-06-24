As of today, this is no longer open: Hough’s paper was received December 22, 2013, accepted August 19, 2014, and published in 2015, proving an upper bound of `10^16` using Lovasz-local-lemma machinery. I’ll still answer in the requested 2014 scouting frame. ([annals.math.princeton.edu](https://annals.math.princeton.edu/2015/181-1/p06))

### Technique 1: Lopsided Lovasz Local Lemma via CRT dependency graphs

1. **Seminal source:** Erdős-Lovász 1975, local lemma; Moser-Tardos 2010 constructive LLL and witness trees. Hough 2015 is the actual covering-system unlock. ([page.math.tu-berlin.de](https://page.math.tu-berlin.de/~felsner/Lehre/SemProbMeth/01a-Moser%2BTardos.pdf)) ([annals.math.princeton.edu](https://annals.math.princeton.edu/2015/181-1/p06))  
2. **Structural analog:** Hypergraph coloring and bounded-occurrence SAT: many individually rare bad events with sparse dependency. Here, a residue class `a mod n` is a bad event on the prime-power CRT coordinates dividing `n`.  
3. **Why it fits:** Large minimum modulus makes each bad event small; the real issue is not total density but local dependency through shared prime factors.  
4. **Why default tools failed:** Inclusion-exclusion and large sieve hit a **dependency/correlation barrier**: they see aggregate density but cannot exploit that most bad events are locally dependent only through a controlled prime support.  
5. **Lean/Mathlib:** Infrastructure sits in `ProbabilityTheory`, `MeasureTheory`, `ZMod`, `Finset`, `Nat`. Missing: a formal asymmetric/lopsided LLL, witness-tree calculus, CRT product probability spaces over prime powers, and Hough-style bias statistics.

### Technique 2: Hypergraph Containers via the Saxton-Thomason / Balogh-Morris-Samotij scythe algorithm

1. **Seminal source:** Balogh-Morris-Samotij, *Independent sets in hypergraphs*, arXiv 2012/revised 2014, JAMS 2015; independently Saxton-Thomason, *Hypergraph containers*, Inventiones 2015. ([arxiv.org](https://arxiv.org/abs/1204.6530)) ([arxiv.org](https://arxiv.org/abs/1204.6595?utm_source=openai))  
2. **Structural analog:** Sparse Ramsey theory, sum-free sets, and independent-set enumeration were unlocked by replacing brute-force enumeration with a small family of structured containers.  
3. **Why it fits:** A covering system in `Z/LZ` can be encoded as a set-cover/transversal problem over residue-class hyperedges. Containers could compress the universe of possible high-minimum-modulus covers into structured candidate families.  
4. **Why default tools failed:** Computer enumeration hits a **solution-space explosion**; sieve estimates do not classify near-covers. Containers attack exactly that missing structural classification.  
5. **Lean/Mathlib:** Base pieces: `Finset`, `Fintype`, `Combinatorics.SetFamily`, `SimpleGraph`. Missing: a serious `Hypergraph` API, uniform hypergraph codegrees, container lemmas, and the scythe algorithm.

### Technique 3: Alon-Furedi Finite-Grid Covering Lemma + Combinatorial Nullstellensatz

1. **Seminal source:** Alon-Furedi, *Covering the Cube by Affine Hyperplanes*, 1993; Alon, *Combinatorial Nullstellensatz*, 1999. ([colab.ws](https://colab.ws/articles/10.1006%2Feujc.1993.1011)) ([ftp.math.utah.edu](https://ftp.math.utah.edu/pub/tex/bib/toc/combinprobabcomput.html))  
2. **Structural analog:** Hyperplane covers of finite grids and finite-field Kakeya: convert a combinatorial cover into a polynomial vanishing statement, then contradict degree/support constraints.  
3. **Why it fits:** After passing to squarefree or prime-power CRT coordinates, residue classes become algebraic cylinders/subspaces in a finite grid. A full cover says a product polynomial vanishes everywhere.  
4. **Why default tools failed:** Sieve methods face an **algebraic-rank blind spot**: they count densities but cannot detect polynomial degree obstructions or coordinate-rank constraints.  
5. **Lean/Mathlib:** `Mathlib.Combinatorics.Nullstellensatz`, `MvPolynomial`, `Polynomial`, `ZMod`, `LinearAlgebra`. Missing: Alon-Furedi grid-cover corollaries, CRT-to-grid normalization, and polynomial-cover results over mixed prime-power rings.

### Technique 4: Green Arithmetic Regularity Lemma and Density-Increment Decomposition

1. **Seminal source:** Green, *A Szemeredi-type regularity lemma in abelian groups, with applications*, 2005. ([research-information.bris.ac.uk](https://research-information.bris.ac.uk/en/publications/a-szemeredi-type-regularity-lemma-in-abelian-groups-with-applicat/))  
2. **Structural analog:** Almost sum-free-set structure and Roth/Szemeredi-style density increments: decompose a bounded function on a finite abelian group into structured plus Fourier-uniform parts.  
3. **Why it fits:** Work in `G = Z/LZ`; the uncovered-set indicator should be zero for a cover. A structure/randomness decomposition could force any successful high-modulus cover to concentrate on a low-complexity Bohr/coset factor, implying a small modulus.  
4. **Why default tools failed:** Large sieve is mainly `U^2`/mean-square information. The obstruction is a **missing inverse theorem/structure-vs-randomness bridge** for the cover indicator.  
5. **Lean/Mathlib:** `ZMod`, `AddChar`, `MeasureTheory`, `Finset`, finite abelian groups. Missing: robust finite Fourier analysis, Gowers norms, Bohr sets, arithmetic regularity, and density-increment machinery.

### Technique 5: Permutation-Character Method for Finite Coset Covers

1. **Seminal source:** B. H. Neumann, *Groups covered by finitely many cosets*, 1954; Herzog-Schönheim coset-partition conjecture, 1974. ([publi.math.unideb.hu](https://publi.math.unideb.hu/paper/2620)) ([erdosproblems.com](https://www.erdosproblems.com/history/274))  
2. **Structural analog:** Exact covering systems and coset partitions: exact distinct-index covers are impossible in abelian/subnormal settings; the character-ring view records coset incidence more rigidly than scalar density.  
3. **Why it fits:** A covering system becomes a coset cover of the finite cyclic group `Z/LZ`. The incidence function is a sum of induced trivial permutation characters `Ind_H^G 1`; exact covers give character identities, and non-exact covers give inequalities.  
4. **Why default tools failed:** Inclusion-exclusion collapses everything to scalar overlap counts. The obstruction is a **nonuniform multiplicity barrier**: arbitrary covers leak multiplicity, while group characters may retain index/subgroup information.  
5. **Lean/Mathlib:** `GroupTheory.Coset`, `Subgroup`, `Fintype`, `ZMod`, `Representation`. Missing: finite group character theory at this level, induced permutation characters, and formal Herzog-Schönheim/coset-cover APIs.

## Ranking

1. **Lopsided LLL**: prior `0.35` from adjacent sparse-avoidance successes × likelihood `0.80` from exact CRT-local dependency structure = `0.28`. With hindsight, this is the actual unlock.
2. **Hypergraph containers**: prior `0.30` × likelihood `0.45` = `0.135`. Strong because the problem has a hidden family-classification/enumeration shape.
3. **Arithmetic regularity**: prior `0.25` × likelihood `0.35` = `0.0875`. Plausible if the right object is the uncovered-set indicator on `Z/LZ`.
4. **Polynomial method**: prior `0.22` × likelihood `0.30` = `0.066`. Good on squarefree/grid reductions, weaker on mixed prime powers.
5. **Permutation characters**: prior `0.18` × likelihood `0.28` = `0.050`. Very structurally relevant, but arbitrary non-exact covers weaken the character identities that make the method powerful.