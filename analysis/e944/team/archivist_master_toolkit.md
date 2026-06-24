# E944 — Master Tool List + Known Walls (the squad's reference)

All theorems stated precisely with citations. "★" = directly load-bearing for k=4.

## A. NECESSARY CONDITIONS any (4,1)-graph MUST satisfy (★ feeds search + impossibility)
Source: Skottová–Steiner 2025 (arXiv:2508.08703), Proposition 5.1 + remarks. VERIFIED in /tmp/skottova.txt lines 1295-1334.
Let G be a (4,1)-graph (= our IsErdos944 4 1 target: 4-vertex-critical, no critical edge), n = |V(G)|.
1. **Edge-connectivity ≥ 6** (hence min degree δ ≥ 6).  [general (4,r): ≥ 3r+3]
   Proof idea: random 3-coloring of two sides of any cut, S₃ permutation; expected monochromatic cross-edges = x/3; need ≥ r+1=2 monochromatic edges in EVERY 3-coloring ⟹ x/3 ≥ 2 ⟹ x ≥ 6.
2. **Max degree Δ ≤ n − 5.**  [general (4,r): ≤ n−(2r+3)]
3. **n ≥ 11.**  [general (4,r): ≥ 5r+6]  ⟹ NO (4,1)-graph on ≤ 10 vertices. (Computational floor below confirms even higher.)
4. **Sparsest candidate is 6-REGULAR.** Open Problem 5.2 (S–S): "Does there exist a 6-regular (4,1)-graph?" Authors recommend searching 6-regular graphs first.

## B. NON-EXISTENCE / dead-end families (★ walls)
1. **Circulant graphs CANNOT be (4,1)-graphs.** Skottová–Steiner §5, lines 1283-1292. For k=4 the distance set D₂=D₃=∅; only D₁ (odd distances) survives → χ=3 (odd-cycle-like). Authors "lean towards thinking circulant (4,1)-graphs do not exist." STRONG WALL — exclude all circulants.
2. **Lattanzio tensor-product family cannot reach k=4.** k−1=3 prime ⟹ no nontrivial factorization ⟹ product mechanism inapplicable. [La02]
3. **Jensen color-pattern circulants degenerate at k=4** (same as B1; Jensen's Table-2 pattern forbids distances >1, leaving odd cycle).
4. **Martinsson–Steiner hypergraph-2-section-complement cannot be 4-chromatic.** Arithmetic: χ=(n−1)/s+1, α=s, n=3s+1 ⟹ χ ≤ (3s+1)/s < 4 for s≥2. (archivist derivation.)
5. **k=3 baseline:** the only 3-vertex-critical graphs are odd cycles, which ARE edge-critical. (S–S line ~72.) So k≥4 is genuinely necessary; k=4 is the first nontrivial case.

## C. POSITIVE TOOLS (★ if a k=4 example is found, or to build one)
1. **Gluing / bootstrapping (Skottová–Steiner Lemma 2.1), holds for k≥4.** Given (k,r)-graphs of orders n₁..n_t AND a k-critical graph of order h with exactly t edges, get a (k,r)-graph of order h+Σ(nᵢ−1). Hajós-style wiring (uᵢ→Aᵢ, wᵢ→Bᵢ via color classes). ⟹ ONE (4,1)-graph ⟹ infinitely many (combined with Lemma 2.2). The amplification is FREE; the bottleneck is finding one seed.
2. **Sparse k-critical graphs of every order (Skottová–Steiner Lemma 2.2), k≥4.** For n≥k+3, a k-critical graph of order n with ≤ (k−2)n edges exists, via Hajós joins of wheels / K₄. Gives the "h, t edges" input to Lemma 2.1.
3. **Hajós construction / Hajós join.** Standard: builds k-critical (k-edge-critical) graphs. Used inside Lemma 2.2. NOTE: produces EDGE-critical graphs (every edge critical) — the OPPOSITE of what we want for the seed, but useful as the "frame" H in gluing.
4. **de Bruijn–Erdős:** χ(G) ≤ k (finite) iff every finite subgraph is k-colorable. ⟹ WLOG the (4,1)-graph target is FINITE. (Lean def allows infinite V but IsCritical forces χ=4 finite; vertex-criticality of every vertex on an infinite graph is degenerate — intended object is a finite Fintype graph.)
5. **Jensen–Siggers partial k=4 result** [JS, Sib. Èlektron. Mat. Izv.]: ∀ε>0 ∃ 4-vertex-critical graph with < ε-fraction of edges critical. CLOSEST anyone got to k=4. The remaining gap: drive that fraction to ZERO. Retrieve this paper (Siberian Electronic Math Reports — likely OPEN ACCESS, see To-Retrieve).

## D. STRUCTURAL THEORY of 4-critical graphs (for impossibility direction)
WARNING (gallai): these are mostly EDGE-critical theory; vertex-critical ≠ edge-critical. Use with care.
1. **Kostochka–Yancey 2014:** every k-EDGE-critical graph has ≥ ((k+1)(k−2)n − k(k−3))/(2(k−1)) edges; for k=4: e ≥ (5n−2)/3. Applies to edge-critical, NOT directly to our vertex-critical-no-critical-edge target. (gallai's domain.)
2. **Gallai (1963):** structure of low-degree vertices in k-edge-critical graphs (Gallai trees / Gallai forest of (k−1)-degree vertices). Again EDGE-critical. (gallai's domain.)
3. **Brooks' theorem:** χ ≤ Δ unless complete or odd cycle. A 4-chromatic graph with Δ=6 (the 6-regular candidate) is consistent with Brooks (6 ≥ 4).
4. **Dirac (1974) / general:** k-vertex-critical graphs have δ ≥ k−1 = 3; our Prop 5.1 sharpens to δ ≥ 6 for the no-critical-edge case.

## E. THE r-generalization landscape (context)
- f_k(n) = largest r s.t. a (k,r)-graph of order n exists. Erdős 1985 asked f_k(n)→∞.
- Skottová–Steiner: f_k(n)=Ω(n^{1/3}) for all k≥5 (Ω(n^{1/2}) along a subsequence); upper bound f_k(n)=O(n/(log n)^c) for all k≥4 (via Conlon–Fox regularity).
- f_4(n) → ∞ is OPEN; even f_4(n) ≥ 1 for some n (= existence of a (4,1)-graph) is OPEN.
- Trivial: f_k(n) < (n−1)/(k−1); for k=4, f_4(n) < (n−1)/3.

---
## F. 2025-2026 COLLISION SCAN (archivist, June 2026)
k=4 is OPEN, area is ACTIVE-but-not-crowded. Moderate collision risk on adjacent questions only.
- Only active group: **Raphael Steiner + Ema Skottová (ETH)** — produced the two directly-relevant 2025 papers (Martinsson–Steiner; Skottová–Steiner). Steiner's research page lists the Skottová collab as ongoing. Note: Martinsson–Steiner also has a **Forum of Math Sigma 2025** journal version (in addition to CPC 34:151-157).
- NO 2026 preprints on the pure k=4 existence problem. NO talk/seminar abstracts on k=4 existence. NO published computational/SAT/AI attack on a (4,1)-graph. NO resolution of the Jensen–Siggers "E* connected/spanning?" question.
- erdosproblems.com/944: no 2025-2026 comments or partial-progress notes.
- COLLISION RISK: highest if the squad overlaps Steiner-group techniques (edge-set criticality, coloring-uniqueness-after-deletion, f_k(n) bounds). LOW for a pure computational search for a k=4 example (nobody is doing that publicly) and for the impossibility/E*-structure direction (untouched since J–S 2012). ⟹ hunter's SAT/CEGAR existence search and count/wall's E*-impossibility route are the LEAST-contested angles.

---
## CALIBRATION on negative computational evidence
Per squad protocol + squad-1 lesson: absence in a small search ≠ nonexistence. Prop 5.1 forces n≥11 and δ≥6 — a (4,1)-graph, if it exists, is NOT tiny and could require large n (the r-version examples have order growing with parameters). Phrase any "not found up to n=N" as a verified lower bound on the smallest example, never as nonexistence.
