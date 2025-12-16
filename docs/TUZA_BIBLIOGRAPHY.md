# Bibliography: Tuza's Conjecture on Triangle Packing and Covering

## Executive Summary

**Tuza's Conjecture (1981)**: For any graph G, τ(G) ≤ 2ν(G), where:
- ν(G) = maximum number of edge-disjoint triangles (triangle packing number)
- τ(G) = minimum number of edges needed to hit all triangles (triangle covering number)

**Current Status**:
- **Open for general graphs** (44+ years)
- Best known general bound: τ(G) ≤ (66/23)ν(G) ≈ 2.87ν(G) [Haxell]
- Trivial bounds: ν(G) ≤ τ(G) ≤ 3ν(G)
- Proven for many special graph classes
- The factor of 2 is **tight** (Baron-Kahn construction shows families where τ ~ 2ν asymptotically)

---

## 1. Original Paper

### Tuza, Zsolt (1981)
**Title**: "Conjecture"
**Publication**: In A. Hajnal, L. Lovász, and V. T. Sós (eds.), *Finite and Infinite Sets*, Proc. Colloq. Math. Soc. János Bolyai, Vol. 37, page 888. North-Holland, Amsterdam.
**Context**: Sixth Hungarian Combinatorial Colloquium, Eger, Hungary, July 6-11, 1981
**Main Result**: Conjectured that τ(G) ≤ 2ν(G) for all graphs G
**Significance**: Initiated 40+ years of research; listed in Bondy-Murty's "100 open problems"

---

## 2. General Upper Bounds

### Haxell, Penny (1999)
**Title**: "Packing and covering triangles in graphs"
**Publication**: *Discrete Mathematics* 195 (1999), pp. 251-254
**Main Result**: τ(G) ≤ (66/23)ν(G) for all graphs G
**Technique**: Combinatorial argument
**Significance**: **Best known general bound** (≈ 2.87, between conjectured 2 and trivial 3)

---

## 3. Special Graph Classes - Planar and Sparse

### Tuza, Zsolt (1985)
**Title**: [Planar graphs result]
**Main Result**: Proved the conjecture for **planar graphs**
**Significance**: First major special case

### Haxell, Penny; Kostochka, Alexandr; Thomassé, Stéphan
**Title**: "Packing and Covering Triangles in K₄-free Planar Graphs"
**Publication**: *Graphs and Combinatorics*
**ArXiv**: Available on personal pages
**Main Result**: For K₄-free planar graphs: τ(G) ≤ (3/2)ν(G)
**Additional**: Equality holds only for edge-disjoint unions of 5-wheels
**Technique**: Structural analysis of planar graphs
**Significance**: **Stronger bound** than Tuza's conjecture for this class

### Puleo, Gregory J. (2015)
**Title**: "Tuza's Conjecture for graphs with maximum average degree less than 7"
**Publication**: *European Journal of Combinatorics* 49 (2015), pp. 134-152
**ArXiv**: arXiv:1308.2211
**Main Result**: Proved conjecture for all graphs with maximum average degree < 7
**Technique**: **Discharging method** with reducible configurations
**Key Innovation**: Introduced "reducible sets" and "weak König-Egerváry graphs"
**Significance**: Generalizes planar graph case (planar graphs have degeneracy ≤ 5)

---

## 4. Special Graph Classes - Structured Graphs

### Haxell, Penny (1993)
**Title**: "Packing and Covering Triangles in Tripartite Graphs"
**Publication**: *Discrete Mathematics*
**Main Result**: Proved conjecture for **tripartite graphs**
**Significance**: First result for a dense graph class

### Krivelevich, Michael (1995)
**Title**: "On a conjecture of Tuza about packing and covering of triangles"
**Publication**: *Discrete Mathematics* 142 (1995), 281-286
**Main Result**: Proved conjecture for graphs with **no K₃,₃-subdivision**
**Additional**: Also proved the **fractional version** holds (when ν or τ replaced by fractional relaxation ν* or τ*)
**Significance**: First fractional result; uses weight functions instead of sets

### Bonamy, Marthe et al. (2021)
**Title**: "Tuza's Conjecture for Threshold Graphs"
**Publication**: *EUROCOMB 2021*, also in *Discrete Mathematics & Theoretical Computer Science*
**ArXiv**: arXiv:2105.09871
**Authors**: Ł. Bożyk, A. Grzesik, M. Hatzel, T. Masařík, J. Novotná, K. Okrasa
**Main Result**: Proved conjecture for **threshold graphs** (graphs that are both split graphs and cographs)
**Significance**: First dense hereditary superclass of cliques where conjecture is confirmed

### Botler et al.
**Title**: [K₈-free chordal graphs]
**Main Result**: Proved conjecture for **K₈-free chordal graphs**
**Status**: Conjecture remains **open for general chordal graphs, split graphs, and interval graphs**

---

## 5. Dense Graphs

### Yuster, Raphael (2012)
**Title**: "Dense Graphs with a Large Triangle Cover Have a Large Triangle Packing"
**Publication**: *Combinatorics, Probability & Computing* 21(6):952-962
**Main Result**: If τ(G) ≥ bn² for fixed b > 0, then τ(G) < (2+o(1))ν(G) (asymptotic)
**Conjecture (Later Disproved)**: Factor of 2 is not optimal for dense graphs
**Significance**: Established asymptotic result for very dense graphs

### Baron, Jake D.; Kahn, Jeff (2016)
**Title**: "Tuza's Conjecture is Asymptotically Tight for Dense Graphs"
**Publication**: *Combinatorics, Probability & Computing* 25(5): 645-667
**ArXiv**: arXiv:1408.4870
**Main Result**: For any α > 0, there exist arbitrarily large graphs G with:
  - τ(G) > (1-o(1))|G|/2
  - ν(G) < (1+α)|G|/4
**Technique**: Partly random construction
**Significance**: **Disproved Yuster's conjecture**; showed factor 2 is **best possible asymptotically**

---

## 6. Random Graphs

### Bennett, Patrick; Dudek, Andrzej; Zerbib, Shira
**Title**: [Gap in random graph result]
**Main Result**: Proved conjecture for G(n,p) when p < c₁n^(-1/2) or p > c₂n^(-1/2)
**Gap**: Left open the regime c₁n^(-1/2) < p < c₂n^(-1/2) (c₁ ≈ 0.48, c₂ ≈ 4.25)

### Kahn, Jeff; Park, Jinyoung (2022)
**Title**: "Tuza's Conjecture for random graphs"
**Publication**: *Random Structures & Algorithms* 61(2): 235-249
**ArXiv**: arXiv:2007.04351
**DOI**: 10.1002/rsa.21057
**Main Result**: For any p = p(n), τ(G_{n,p}) ≤ 2ν(G_{n,p}) with high probability
**Technique**: Probabilistic method
**Significance**: **Closed the gap** in Bennett-Dudek-Zerbib; resolved conjecture for **all** Erdős-Rényi random graphs

### Bennett, Patrick; Cushman; Dudek, Andrzej (2020)
**Title**: "Closing the Random Graph Gap in Tuza's Conjecture through the Online Triangle Packing Process"
**Publication**: *SIAM Journal on Discrete Mathematics*
**ArXiv**: arXiv:2007.04478
**Main Result**: Independent proof of conjecture for random graphs G(n,m) for all ranges of m
**Technique**: **Online triangle packing process** analyzed via differential equations method
**Significance**: Concurrent with Kahn-Park result

---

## 7. Algorithmic and Sufficient Conditions

### Various Authors (2016)
**Title**: "Sufficient Conditions for Tuza's Conjecture on Packing and Covering Triangles"
**Publication**: Conference proceedings / *SpringerLink*
**ArXiv**: arXiv:1605.01816
**Main Results**: For graphs where triangles cover all edges, polynomial-time algorithm finds triangle cover of size ≤ 2ν(G) if:
  - ν(G)/|T_G| ≥ 1/3, OR
  - ν(G)/|E| ≥ 1/4, OR
  - |E|/|T_G| ≥ 2
**Technique**: Hypergraph approach, polynomial-time combinatorial algorithms
**Significance**: Provides verifiable sufficient conditions and efficient algorithms

---

## 8. Multi-transversals and Generalizations

### Various Authors (2020)
**Title**: "Multi-transversals for Triangles and the Tuza's Conjecture"
**Publication**: *Proceedings of the Thirty-First Annual ACM-SIAM Symposium on Discrete Algorithms (SODA)*
**ArXiv**: arXiv:2001.00257
**Main Result**: Results on multi-transversals strengthen Krivelevich's fractional version
**Significance**: Extends fractional relaxation results

---

## 9. Related Graph Classes

### Chahua, Luis Eduardo; Gutierrez, Juan et al.
**Title**: "On Tuza's conjecture in co-chain graphs"
**Publication**: ArXiv
**ArXiv**: arXiv:2211.07766
**Main Result**: Proved conjecture for co-chain graphs (subclass of unit-interval graphs) when both partition sizes are multiples of 2
**Significance**: Step toward attacking conjecture for (mixed) unit interval graphs

---

## 10. Recent Developments (2024-2025)

### Dense Graphs (2025)
**Title**: "On Tuza's conjecture in dense graphs"
**Publication**: *Discrete Applied Mathematics* (to appear)
**Main Result**: Progress on dense split graphs
**Status**: Split graphs and interval graphs remain open

### Generalized Tuza's Conjecture
**Title**: "New bounds on a generalization of Tuza's conjecture"
**ArXiv**: arXiv:2406.06501 (June 2024)
**Main Result**: Bounds for hypergraph generalizations

---

## 11. Survey and Reference Sources

### Bondy, J. Adrian; Murty, U. S. R.
**Title**: *Graph Theory* (textbook)
**Publisher**: Springer
**Editions**: 1976 (original), later editions updated
**Relevance**: Includes Tuza's conjecture in "100 open problems" list; standard reference for graph theory

### Open Problem Garden
**URL**: http://www.openproblemgarden.org/op/triangle_packing_vs_triangle_edge_transversal
**Content**: Community-maintained status updates and references

### Douglas West's Problem List
**URL**: https://faculty.math.illinois.edu/~west/regs/jones.html
**Content**: "Ryser, Jones, and Tuza Conjectures" - regularly updated survey

### Wikipedia
**URL**: https://en.wikipedia.org/wiki/Tuza's_conjecture
**Content**: Comprehensive overview with current status of special cases

---

## 12. Connection to Erdős Problems (Recent)

### Erdős Problem #124 and Brown's Criterion
**Context**: AI system "Aristotle" (Harmonic) solved Erdős Problem #124 in 2024
**Connection**: The problem as formalized was accidentally weaker than intended, becoming a **consequence of Brown's criterion** (a result on complete sequences)
**Relevance to Tuza**: Shows how formalization gaps can make "hard" problems tractable; Brown's criterion relates to packing/covering problems
**Key Insight (Terence Tao)**: "Erdős omitted a key hypothesis which made the problem a consequence of a known result"
**Sources**:
- https://www.erdosproblems.com/124
- https://news.ycombinator.com/item?id=46094037

---

## Key Techniques Summary

| Technique | Representative Papers | Graph Classes |
|-----------|----------------------|---------------|
| **Combinatorial arguments** | Haxell (1999) | General bounds |
| **Discharging method** | Puleo (2015) | Sparse graphs (mad < 7) |
| **Structural decomposition** | Haxell-Kostochka-Thomassé | K₄-free planar |
| **Fractional relaxation** | Krivelevich (1995) | General |
| **Probabilistic method** | Kahn-Park (2022) | Random graphs |
| **Hypergraph approach** | Sufficient Conditions (2016) | Algorithmic |
| **Random construction** | Baron-Kahn (2016) | Tightness examples |

---

## Current Research Frontiers (as of 2025)

### Still Open:
1. **General graphs** - close gap from 66/23 to 2
2. **Chordal graphs** (general case)
3. **Split graphs**
4. **Interval graphs**
5. **Mixed unit interval graphs**

### Recently Resolved:
- ✅ Random graphs (all densities) - Kahn-Park (2022)
- ✅ Threshold graphs - Bonamy et al. (2021)
- ✅ Asymptotic tightness for dense graphs - Baron-Kahn (2016)
- ✅ Graphs with mad < 7 - Puleo (2015)

### Related Open Questions:
- Hypergraph generalizations
- Weighted variants
- Directed triangle packing/covering
- Computational complexity of triangle packing (polynomial-time via matroid parity)

---

## Key ArXiv Papers (Sorted by Date)

1. **arXiv:1308.2211** (2013/2015) - Puleo: Maximum average degree < 7
2. **arXiv:1408.4870** (2014/2016) - Baron-Kahn: Asymptotically tight for dense graphs
3. **arXiv:1605.01816** (2016) - Sufficient conditions and algorithms
4. **arXiv:2001.00257** (2020) - Multi-transversals
5. **arXiv:2007.04351** (2020/2022) - Kahn-Park: Random graphs
6. **arXiv:2007.04478** (2020) - Bennett-Cushman-Dudek: Random graphs
7. **arXiv:2105.09871** (2021) - Bonamy et al.: Threshold graphs
8. **arXiv:2211.07766** (2022) - Chahua-Gutierrez: Co-chain graphs
9. **arXiv:2406.06501** (2024) - Generalization bounds

---

## Recommended Reading Order

### For Quick Understanding:
1. Wikipedia article (overview)
2. Bondy-Murty textbook (context)
3. Haxell (1999) - general bound

### For Technical Depth:
1. Tuza (1981) - original conjecture
2. Haxell (1999) - best general bound
3. Puleo (2015) - discharging method (arXiv:1308.2211)
4. Kahn-Park (2022) - random graphs (arXiv:2007.04351)
5. Baron-Kahn (2016) - tightness (arXiv:1408.4870)

### For Specific Graph Classes:
- **Planar**: Haxell-Kostochka-Thomassé (K₄-free planar)
- **Sparse**: Puleo (2015)
- **Dense**: Yuster (2012), Baron-Kahn (2016)
- **Structured**: Haxell (1993) tripartite, Krivelevich (1995) K₃,₃-free
- **Random**: Kahn-Park (2022)

---

## Sources

- [Wikipedia: Tuza's conjecture](https://en.wikipedia.org/wiki/Tuza's_conjecture)
- [Sufficient Conditions for Tuza's Conjecture (SpringerLink)](https://link.springer.com/content/pdf/10.1007/978-3-319-44543-4_21.pdf)
- [Closing the Random Graph Gap - ArXiv](https://arxiv.org/abs/2007.04478)
- [Ryser, Jones, and Tuza Conjectures](https://faculty.math.illinois.edu/~west/regs/jones.html)
- [Tuza's Conjecture for Threshold Graphs - ArXiv](https://arxiv.org/abs/2105.09871)
- [Puleo: Maximum Average Degree < 7 - ArXiv](https://arxiv.org/abs/1308.2211)
- [Kahn-Park: Random Graphs](https://onlinelibrary.wiley.com/doi/am-pdf/10.1002/rsa.21057)
- [Baron-Kahn: Asymptotically Tight - ArXiv](https://arxiv.org/abs/1408.4870)
- [DIMACS: Tuza's Conjecture in Dense Graphs](http://dimacs.rutgers.edu/news_archive/tuza-conjecture)
- [Multi-transversals - ArXiv](https://arxiv.org/abs/2001.00257)
- [Co-chain Graphs - ArXiv](https://arxiv.org/abs/2211.07766)
- [Erdős Problem #124](https://www.erdosproblems.com/124)
- [Open Problem Garden](http://www.openproblemgarden.org/op/triangle_packing_vs_triangle_edge_transversal)
