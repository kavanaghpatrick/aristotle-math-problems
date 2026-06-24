# Jensen–Siggers 2012 — the CLOSEST anyone has gotten to k=4 (FULL extraction)

**T. Jensen & M. Siggers, "On a question of Dirac on critical and vertex critical graphs", Siberian Electronic Mathematical Reports 9 (2012), 156–160.** OPEN ACCESS. PDF: http://semr.math.nsc.ru/v9/p156-160.pdf. FULL TEXT extracted → /tmp/jensen_siggers.txt (254 lines, 4 pages, pdftotext-verified). This is the ONLY published quantitative result on k=4.

## Main result (Theorem 1, verbatim)
There exist c₁, c₂ > 0 such that for infinitely many n there is a **4-vertex-critical** graph H on n vertices with |E(H)| > c₁n² but |E*(H)| < c₂n, where E* = the set of CRITICAL edges. Explicit constants: c₁ = 12/21², c₂ = 1+ε.
⟹ The fraction of critical edges → 0 as n → ∞ (Θ(n) critical edges among Θ(n²) total). They do NOT reach E* = ∅ (Dirac k=4 still open).

## The construction (EXPLICIT, non-circulant — a concrete near-miss blueprint)
Fix integer m ≥ 3.
1. **B = B(m)**: complete tripartite graph K_{2m,2m,2m} (three parts S₁,S₂,S₃ of 2m vertices). KEY (Lemma 1): B has a UNIQUE 3-coloring up to color permutation — φ(v)=i iff v∈Sᵢ — AND this remains the unique coloring after removing ANY single edge (works until m−2 edges removed). So **none of B's 12m² edges is critical**: removing one edge leaves the same forced coloring, χ stays 3 locally, and in H stays 4.
2. **T = T(m)** (Construction 2): from a path x₀x₁…x_{2m+1} plus independent y₁,…,y_m, add edges yᵢx_{2i−1}, yᵢx_{2i}. A "color-transfer gadget." Lemma 2: a 3-coloring of the boundary Y⁺={x₀,x_{2m+1}}∪Y extends to T iff [φ(x₀)=φ(x_{2m+1})=c₀ ⟹ some yᵢ has color c₀] or [φ(x₀)≠φ(x_{2m+1}) always extends]. Plus item (iii): any boundary coloring missing one vertex extends to T minus that vertex (this is what makes it vertex-critical-friendly).
3. **T' = T'(m)** (Construction 3): T plus a leaf zᵢ on each yᵢ. Lemma 3 = Lemma 2 with the condition flipped to φ(zᵢ)≠c₀.
4. **G = G(m)** (Construction 4): a star (center v₀, leaves v₁,v₂,v₃) glued to copies T₁,T₂,T₃ (and T'₁,T'₂,T'₃) by identifying the vᵢ with the x₀/x_{2m+1} boundary vertices in a cyclic pattern. Sᵢ := copy of Y in Tᵢ ∪ copy of Z in T'ᵢ. G has n = 21m+4 vertices, 21m+6 edges. Lemma 4: (i) under ANY 3-coloring of G at least one Sᵢ is NOT monochromatic (because two of v₁,v₂,v₃ share a color, forcing a bichromatic Sᵢ); (ii) for any vertex v* ∈ S₁∪S₂∪S₃, G\v* HAS a 3-coloring making each Sᵢ\{v*} monochromatic.
5. **H' = B ∪ G** glued by identifying B's Sᵢ with G's Sᵢ (Sᵢ is independent in G). Lemma 1 + Lemma 4(i) ⟹ H' is NOT 3-colorable (χ≥4). Let H = a 4-critical subgraph (remove vertices while staying non-3-colorable). Lemma 4(ii) forces all of S₁∪S₂∪S₃ ⊆ V(H). Lemma 1 ⟹ none of B's edges critical ⟹ E*(H) ⊆ E(G), which has only 21m+6 = Θ(n) edges. Done.

## ★★ THE STRATEGIC INSIGHT (Concluding Remarks, verbatim) ★★
"In our construction, E* was **connected, and even a spanning subgraph** of H. We cannot see how to avoid this. If Dirac's Question has a negative answer for k=4, it does not seem unlikely that one could further say that the graph E* of critical edges is connected, or even spanning. We think it would be interesting to investigate even questions such as this."

⟹ TWO directions for the squad:
- **(Construction direction)** The whole architecture works EXCEPT the leftover ~21m+6 critical edges in G. To resolve k=4 positively, modify G so that those Θ(n) critical edges also become non-critical, WITHOUT collapsing χ to 3. The bottleneck is concentrated entirely in the "color-disagreement transfer" gadget G — B contributes ZERO critical edges. This is a SHARP, LOCALIZED target: kill the criticality inside G(m).
- **(Impossibility direction)** Jensen–Siggers CONJECTURE that for k=4 the critical-edge set E* may be FORCED to be connected/spanning. If one proves "every 4-vertex-critical graph has a connected (or spanning) E* of positive size," that would REFUTE Dirac k=4 (show E* ≠ ∅ always). This is a concrete impossibility lemma to target. → forward to count/skeptic/wall.

## LITERATURE CORRECTION (important, from J–S intro, more authoritative than Grok)
J–S intro states (line ~50): "[3] Jensen showed that for each k≥5 there are infinitely many examples, and [5] Lattanzio showed further constructions for ODD values of k≥5."
So the precise division of labor:
- **Jensen 2002 [3]: ALL k≥5** (this is the real "solves k≥5" result; state of the art).
- **Lattanzio 2002 [5]: ODD k≥5** per J–S (the formal-conjectures repo + MS paper say "k−1 not prime"; these are consistent-ish: odd k means k−1 even = composite for k≥5, but "k−1 not prime" is broader, covering e.g. k=10 with k−1=9). The repo's Lean statement uses "k−1 not prime" — TRUST THE REPO STATEMENT for our formalization target. The nuance: different sources summarize Lattanzio's coverage slightly differently; the SOLE open case k=4 is unaffected (k−1=3 prime AND k=4 even, excluded by both characterizations).
- **Problem 5.14 in Jensen–Toft "Graph Coloring Problems" (Wiley 1995), pp.105-106** = the canonical textbook statement of this exact problem. [ref [4] in J–S]

## Why k=4 resists, in J–S's own framing
For k=3: 3-vertex-critical = 3-critical = odd cycles, all edge-critical, E* = everything. The jump to k=4 is the FIRST place vertex-critical can diverge from edge-critical, and J–S's construction shows the divergence can be made ALMOST total (only Θ(n) of Θ(n²) edges critical) but a positive linear core survives. Closing that core is the open problem.
