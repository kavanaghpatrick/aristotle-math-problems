# Martinsson–Steiner 2025 — FULL extraction (the most recent + most relevant paper)

**arXiv:2310.12891v1 [math.CO] 19 Oct 2023.** Published: Combinatorics, Probability and Computing, vol. 34 (2025), pp. 151–157. Authors at ETH Zürich. PDF retrieved + full text in /tmp/ms2310.txt (514 lines, 6 pages). VERIFIED via pdftotext on the arXiv PDF.

## Status confirmation (PRIMARY SOURCE for "k=4 open")
The paper itself states (line 53): "This leaves only the case k = 4 of Dirac's conjecture open today, which remains an intriguing open problem." And (lines 78-79): "Our result still leaves open Erdős' question when k ≥ 4 is fixed as a small value and r tends to infinity." So as of late 2023 / 2025 publication, **k=4 is the sole open case**. Grok live-search (June 2026) confirms no later resolution; erdosproblems.com/944 still lists k=4, r=1 open.

## Main theorem (verbatim, line 75-77)
**Theorem 1.** For every r ∈ ℕ there is some k₀ ∈ ℕ such that for every k ≥ k₀ there exists a k-chromatic vertex-critical graph G such that χ(G − R) = k for every R ⊆ E(G) with |R| ≤ r.

This is the r-generalized Dirac / Erdős-1985 problem (Erdős #944 full form). r=1 recovers "no critical edge."

## THE CONSTRUCTION (complete, this is reusable as a toolkit)
Given r ≥ 1:
1. Set **s := r + 3** and **m := 2^(s+1)**.
2. (Lemma 3) For n ≡ 1 (mod s), n large, obtain an **s-uniform hypergraph H on n vertices** with:
   - (i) For every vertex v, **H − v has a perfect matching** (partition of the other n−1 vertices into (n−1)/s hyperedges).
   - (ii) **Local sparsity**: every F ⊆ E(H) with |F| ≤ m spans ≥ (s−1)|F| vertices (i.e. ∪_{e∈F} e ≥ (s−1)|F|).
   Built RANDOMLY via Shamir's hypergraph perfect-matching threshold (Johansson–Kahn–Vu 2008; Kahn 2023).
3. Take n := s(k−1) + 1.  Define **G := complement of the 2-section of H** (2-section = clique on each hyperedge; complement of that).

Why it works:
- **Vertex-critical, χ ≤ k−1 after deleting v**: H−v has a perfect matching into (n−1)/s = k−1 hyperedges → each hyperedge is an independent set in G (complement of 2-section) → proper (k−1)-coloring of G−v. So χ(G−v) ≤ k−1.
- **χ(G) ≥ k and no small critical edge-set**: For |R| ≤ r, show α(G−R) ≤ s. An independent set of size s+1 in G−R = a set X, |X|=s+1, with G[X] having ≤ r edges, i.e. the 2-section G₂^H[X] having ≥ C(s+1,2) − r = C(s,2) + 3 edges. But Lemma 5 (from local sparsity ii) bounds |E(G₂^H[X])| ≤ C(s,2) + 2. Contradiction. So α(G−R) ≤ s ⟹ χ(G−R) ≥ n/s > k−1 ⟹ ≥ k. Since this holds for ALL R with |R| ≤ r, removing any ≤ r edges keeps χ = k.

## ★★ WHY THIS METHOD CANNOT REACH k=4 (the central obstruction insight) ★★
The construction's chromatic number is **k = (n−1)/s + 1** where n = s(k−1)+1. The independence number is forced to be exactly **α(G) = s = r + 3**. So χ ≈ n/s. To get a SMALL k (like k=4), you need n small (n = s·3 + 1 = 3s+1 for k=4). But:
- Lemma 3's hypergraph existence is **asymptotic** ("for every sufficiently large n"). The probabilistic Shamir-threshold argument (perfect matching after any single vertex deletion + local sparsity) only kicks in for large n.
- For k=4 you'd need s-uniform H on n = 3s+1 vertices with the matching+sparsity properties. With s = r+3 ≥ 4 (even at r=1, s=4), n=13. The random construction gives NO guarantee at such tiny n; the union-bound probabilities (1/n², etc.) are vacuous.
- More fundamentally: the method produces α(G) = s = r+3. For r=1 that's α = 4. With χ=4 and α=4 you need ≥ 16 vertices (n ≥ χ·α). The construction naturally lives at LARGE k where n/s = k is large. **The whole architecture trades "large k" for the probabilistic existence of the sparse-matchable hypergraph.** It is intrinsically an asymptotic-in-k method.

**Takeaway for the squad:** Martinsson–Steiner is a LARGE-k probabilistic existence result. It gives ZERO direct leverage on k=4 (they say so explicitly, line 78). It does NOT provide an obstruction to k=4 either — it's simply silent. The k=4 case needs an explicit/small construction OR an impossibility proof, neither of which this paper addresses.

## REUSABLE TOOL (master-list candidate)
- **2-section + complement trick**: vertex-critical graphs with controlled α arise as complements of 2-sections of s-uniform hypergraphs whose vertex-deleted subhypergraphs have perfect matchings. A k=4 attempt could ask: is there a SMALL s-uniform hypergraph (s=4? s=3?) on n=3s+1 vertices with H−v perfect-matchable for all v AND the local-sparsity bound — found by EXHAUSTIVE search rather than probabilistically? This is a concrete computational target for hunter/forge. NOTE: s=r+3 was chosen to make α=s and the arithmetic χ=(n−1)/s+1 land; for k=4, r=1 you want χ=4 ⟹ need (n−1)/s = 3 ⟹ n = 3s+1, and α=s. A 4-chromatic graph with α=s needs ≥ 4s vertices but n=3s+1 < 4s for s≥2 — **arithmetic clash**: complement-of-2-section construction gives χ ≤ n/α = (3s+1)/s < 4 for s ≥ 2. So the EXACT MS construction can NEVER yield χ=4 (it would force χ ≤ 3). This is a clean reason the MS template fails at k=4 — not just "probabilities too weak" but an arithmetic wall: their χ = (n−1)/s + 1 with α = s forces the graph to be very dense relative to its independence number only at large k. **The MS construction structurally cannot produce a 4-chromatic example.**

## NEW PAPER FOUND IN REFS — Wang 2009 (NOT in squad-lead's list!)
Ref [11]: **J. Wang, "Infinite family from each vertex k-critical graph without any critical edge."** In: Combinatorial Optimization and Applications (COCOA 2009), LNCS 5573, 238–248 (2009).
- This says: given ONE vertex-k-critical graph with no critical edge, you can build an INFINITE FAMILY. Relevant: a single k=4 example would immediately yield infinitely many. Also possibly a tool for going k → k+1 or building families. WORTH RETRIEVING. Flag to forge (constructions).

## Full reference list from MS paper (citations to chase)
- [1] Brown 1992, Discrete Math 102(1) 99–101 (note: MS cite vol 102, squad-lead said 99-101 — consistent).
- [2] Chung–Graham, "Erdős on graphs: His legacy of unsolved problems", CRC 1998.
- [3] Chung, "Vertex-critical graphs with many extra edges", online Erdős DB (mathweb.ucsd.edu/~erdosproblems/...NoncriticalEdges.html) — THE canonical online problem page predating erdosproblems.com.
- [4] Erdős 1985/1989, "On some aspects of my work with Gabriel Dirac", Ann. Discrete Math 41, 111-116 — the SOURCE of the r-generalization (p.113).
- [5] Lattanzio 2002, Discrete Math 258(1-3) 323–330.
- [6] Jensen 2002, Discrete Math 258, 63–84.
- [7] Jensen 1996 PhD thesis "Structure of critical graphs", Odense.
- [8] Jensen–Toft, "Graph coloring problems", Wiley 1995 — Problem 5.14 is exactly this.
- [9] Johansson–Kahn–Vu 2008, "Factors in random graphs", RSA 33(1) 1–28.
- [10] Kahn 2023, "Asymptotics for Shamir's problem", Adv. Math 422, 109019.
- [11] Wang 2009 (above).
