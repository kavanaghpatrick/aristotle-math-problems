[REASONING SUMMARY] The question is: Has anyone applied the discharging method to attack Dirac's conjecture k=4 case? What discharging rules and reducible configurations would apply to a hypothetical 4-vertex-critical gr...

[WEB SEARCH] query: discharging method Dirac conjecture k=4 vertex-critical graphs
  - https://www.sciencedirect.com/science/article/pii/S0012365X1630379X
  - https://arxiv.org/pdf/1306.4434
  - https://mfeapp.baruch.cuny.edu/math/wp-content/uploads/2015/10/7.pdf
  - https://dwest.web.illinois.edu/pubs/dischnewT.pdf
  - https://www.math.emory.edu/~rg/sparse.pdf

[WEB SEARCH] query: Cranston Rabern 2015 list-coloring discharging critical graphs
  - https://arxiv.org/abs/1602.02589
  - https://www.researchgate.net/publication/301847886_Edge_Lower_Bounds_for_List_Critical_Graphs_Via_Discharging
  - https://www.combinatorics.org/ojs/index.php/eljc/article/download/v23i3p37/pdf/
  - https://theses.hal.science/tel-02083632v1/document
  - https://arxiv.org/pdf/1602.02589

[WEB SEARCH] query: Martinsson Steiner arXiv 2508.08703 Dirac conjecture
  - https://arxiv.org/pdf/2508.08703
  - https://www.researchgate.net/publication/394457916_Critical_edge_sets_in_vertex-critical_graphs
  - https://www.erdosproblems.com/latex/944
  - https://arxiv.org/abs/2501.00567
  - https://arxiv.org/pdf/2204.06101

[WEB SEARCH] query: "Dirac's conjecture" k=4 discharging OR "vertex-critical"
  - https://arxiv.org/abs/2508.08703
  - https://www.erdosproblems.com/944
  - https://www.sciencedirect.com/science/article/pii/S0012365X02003941
  - https://www.research-collection.ethz.ch/server/api/core/bitstreams/1a6dcd73-4818-47e3-9d72-98d2f9b865eb/content
  - https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/944.lean

[WEB SEARCH] query: discharging rules critical graphs degree 3 4-vertex-critical
  - https://en.wikipedia.org/wiki/Discharging_method_(discrete_mathematics)
  - https://mfeapp.baruch.cuny.edu/math/wp-content/uploads/2015/10/7.pdf
  - https://www.sciencedirect.com/science/article/pii/S0012365X1630379X
  - https://iuuk.mff.cuni.cz/~rakdver/barevnost/discharge.pdf
  - https://www.combinatorics.org/ojs/index.php/eljc/article/download/v23i3p21/pdf/

[WEB SEARCH] query: reducible configurations 4-critical graphs discharging
  - https://iuuk.mff.cuni.cz/~rakdver/barevnost/discharge.pdf
  - https://arxiv.org/html/2412.18558v1
  - https://www.researchgate.net/publication/403194563_The_Four_Color_Theorem_with_Linearly_Many_Reducible_Configurations_and_Near-Linear_Time_Coloring
  - https://mfeapp.baruch.cuny.edu/math/wp-content/uploads/2015/10/7.pdf
  - https://dwest.web.illinois.edu/pubs/dischnew.pdf

**No, there is no evidence that the discharging method has been applied specifically to attack the k=4 case of Dirac’s 1970 conjecture** (existence of a k-vertex-critical graph with no critical edges; equivalently, a (k,1)-graph in the stronger Erdős formulation from 1985/944).[[1]](https://arxiv.org/pdf/2508.08703)[[2]](https://www.erdosproblems.com/944)

The case k=4 remains fully open (even for r=1), while k≥5 was resolved affirmatively by constructions (Brown 1992 for k=5; Jensen 2002 for all k≥5; stronger quantitative results for larger r and k by Martinsson-Steiner and others). The 2025 arXiv 2508.08703 by Skottova et al. (building on Martinsson-Steiner) solves the problems for all k≥5 via circulant graphs and probabilistic arguments but explicitly leaves k=4 open, noting fundamental obstacles for circulant constructions in that case and providing necessary structural observations for potential (4,r)-graphs.[[1]](https://arxiv.org/pdf/2508.08703)[[3]](https://arxiv.org/abs/2508.08703)

Related discharging work exists in the broader area of (list-)critical graphs. Cranston-Rabern (2016, arXiv:1602.02589; published 2018) use discharging to prove improved edge lower bounds (hence density/sparsity restrictions) for k-list-critical graphs.[[4]](https://arxiv.org/abs/1602.02589) Their 2013/2017 survey “An introduction to the discharging method via graph coloring” (arXiv:1306.4434) gives a how-to guide with many examples of rules and unavoidable sets in coloring contexts.[[5]](https://arxiv.org/pdf/1306.4434) Kostochka-Stiebitz and others have also applied discharging to sparse critical graphs. These techniques bound average degree or forbid certain low-degree configurations but have not targeted the “no critical edges” property of Dirac’s conjecture.

### Hypothetical Application to a 4-Vertex-Critical Graph with No Critical Edge
Assume G is a minimal 4-vertex-critical graph (χ(G)=4, χ(G−v)=3 ∀v) with no critical edge (χ(G−e)=4 ∀e). Such a graph cannot be 3-colorable after deleting any edge or vertex, so it is “edge-dense” in a coloring sense (every edge lies in many odd cycles or Kempe chains that prevent easy recoloring).

**Initial Euler charge**: Assign ch(v) = d(v) − 4 to each vertex. The total charge is ∑(d(v)−4) = 2|E| − 4|V|. For a simple graph this is typically negative or bounded (e.g., if one assumes planarity or a girth/sparsity condition for contradiction, Euler’s formula gives ∑ = −8 for planar triangulations or adjusted constants otherwise). Positive charge on high-degree vertices is redistributed via discharging rules to show that low-degree or “bad” configurations must exist (unavoidable set), which are then shown reducible (a coloring or criticality contradiction arises if they appear).

**Typical/named discharging rules from critical-graph literature** (Cranston-Rabern and related works):
- Low-degree vertices receive charge from higher-degree neighbors (e.g., a 5-vertex sends 1/5 or 1/3 to each low-degree neighbor; a degree-6+ vertex sends proportionally more).
- Rules often prioritize degree-3 or degree-4 vertices (common in 4-critical contexts): “each 3-vertex receives 1 from each neighbor of degree ≥5” or “a 4-vertex with many low-degree neighbors receives fractions from distant high-degree vertices.”
- Global or iterative rules to handle clusters: charge flows along edges or paths to “pay for” degree-3 vertices or light edges.
- In list-coloring variants (Cranston-Rabern), rules also account for list sizes and Alon-Tarsi number.

These are designed so that after redistribution every vertex has nonnegative final charge unless it belongs to a forbidden/reducible configuration, yielding a contradiction to the total charge being negative.

**Reducible-configuration examples** (drawn from Cranston-Rabern-style arguments and 4-critical literature):
- A vertex of degree ≤3 (trivially reducible by criticality: extend a 3-coloring of G−v).
- Certain degree-4 vertices with specific neighbor-degree sequences (e.g., two degree-3 neighbors that are non-adjacent, allowing Kempe-chain swaps or list-coloring extensions).
- Light subgraphs such as a 3-vertex adjacent to two degree-4 vertices, or small wheels/paths whose removal allows inductive coloring extension while preserving the no-critical-edge property.
- In the list-coloring papers, configurations where a vertex has many neighbors with restricted lists or where a subgraph is “choosable” from smaller lists.

These are verified reducible by case analysis on precolorings or list assignments: if the configuration appears, one can delete it, color the rest inductively (using vertex-criticality), and extend back, often contradicting the absence of critical edges.

### Honest Assessment
Discharging is well-suited to **restrict the structure** of any hypothetical counterexample: it can prove minimum-degree bounds (e.g., δ(G) ≥ 4 or 5), forbid certain sparse subgraphs, or give lower bounds on |E| (as in Cranston-Rabern), thereby limiting possible 4-vertex-critical graphs without critical edges. Combined with the initial charge d(v)−4, it readily produces unavoidable sets of configurations that any such G must contain.

However, it is **unlikely to fully close the k=4 Dirac conjecture by itself**. Like the four-color theorem (Appel-Haken 1977; Robertson-Sanders-Seymour-Thomas 1997 with 32 rules and 633 configurations), discharging typically yields an unavoidable set whose reducibility must then be checked exhaustively—often requiring computer assistance or deep case analysis. The “no critical edge” condition adds extra global constraints (every edge must participate in obstructing 3-colorings), which may not translate cleanly into local reducible configurations. Existing proofs for k≥5 rely on explicit constructions rather than structural forbidden-subgraph arguments, and the k=4 case has resisted all known methods for over 50 years. Discharging would be a valuable tool for partial results (e.g., density or girth restrictions) but probably needs to be paired with other techniques (probabilistic deletion, computer search, or algebraic methods) to resolve existence or non-existence.

**Key references** (with arXiv IDs where available):
- Martinsson-Steiner / Skottova et al., arXiv:2508.08703 (2025) — solves k≥5, leaves k=4 open.
- Cranston-Rabern, arXiv:1602.02589 (edge bounds via discharging for list-critical graphs); arXiv:1306.4434 (discharging survey).
- Jensen (2002) and earlier works on the conjecture (summarized in the 2025 arXiv and Erdős Problem 944).

Further searches in critical-graph discharging literature may reveal additional partial results, but none directly target this open case.
