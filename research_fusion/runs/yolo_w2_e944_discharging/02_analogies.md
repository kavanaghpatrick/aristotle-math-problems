# Analogies — discharging-based attacks on critical-graph problems

## 4-Color Theorem (Appel-Haken 1976; Robertson-Sanders-Seymour-Thomas 1997)
Setup: planar graph G, minimum counterexample (smallest 5-chromatic planar simple graph).
- Initial charge: c(v) = d(v) - 6 for vertices, c(f) = 2·d(f) - 6 for faces. Sum = -12 by Euler.
- 32 discharging rules redistribute charge from positive-charge high-degree vertices/faces to negative-charge low-degree ones.
- 633 reducible configurations: subgraphs that can't appear in a minimum counterexample (via Kempe-chain arguments).
- After discharging, every vertex has non-negative charge unless it lies in a reducible config; but sum is negative; contradiction.

## Cranston-Rabern 2017 edge bounds (arXiv:1602.02589)
Setup: k-list-critical graph G.
- Initial charge: c(v) = d(v) - (k-1) - ε for some ε.
- Discharging rules send charge from higher-degree to lower-degree neighbors based on Alon-Tarsi/list-color properties.
- Reducible configurations: f-Alon-Tarsi colorable subgraphs.
- Conclusion: bound on |E(G)| in terms of |V(G)| and k.

## Transplant to Dirac k=4 no-critical-edge

The KEY INSIGHT from the analogy: in 4CT and Cranston-Rabern, discharging works because there is a global topological/list constraint (planarity / list assignment) that limits the *high-degree* side too — high-degree vertices appear in bounded patterns.

For Dirac k=4 with no-critical-edge, we have NO such global constraint on high-degree side. The no-critical-edge condition imposes constraints PRIMARILY on the low-degree side: it forces δ(G) ≥ 6 (codex consultation, May 30 2026).

**Adapted strategy**: Two-phase discharging.
- Phase 1: Use the no-critical-edge condition to force δ(G) ≥ 6 as a *reducible-configuration* result, not as a discharging contradiction. This is a clean lemma.
- Phase 2: With δ(G) ≥ 6 established, use Kostochka-Stiebitz density |E(G)| ≥ (15/7)|V(G)| (k=4 case) plus Stiebitz's critical-colouring hypergraph H_chr(G) to look for a quantitative obstruction. Initial charge c(v) = d(v) - α for α tuned to make the sum vanish — α = 2|E|/|V| ≈ 4.28; choose α ∈ {5, 6} to push positive vertices into being "few".
- Phase 3: Identify reducible configurations involving degree-6 vertices and their second-neighborhood structure (no-critical-edge propagates through second-neighborhoods via Kempe-chain swaps).

**Honest assessment from codex consultation**: Pure discharging via c(v) = d(v) - 4 does not close k=4. It yields δ(G) ≥ 6 cleanly. To close k=4, the discharging must be coupled with (a) finite structural enumeration on small graphs with δ ≥ 6, OR (b) a Kempe-chain / Alon-Tarsi argument that finds a critical edge in any graph with δ ≥ 6.

## Related Aristotle-tractable sub-goals
1. Lean formalize the lemma: G 4-vertex-critical and no-critical-edge ⟹ δ(G) ≥ 6.
2. Lean formalize: under δ(G) ≥ 6, |E(G)| ≥ 3|V(G)|, hence |V(G)| ≥ 7.
3. Combine with Kostochka-Stiebitz density to push |V(G)| ≥ N₀ for some N₀, then a SAT/finite-enumeration step handles |V(G)| ≤ N₀ + structure.

Step 1 is the cleanest Aristotle-formalizer-friendly subgoal (pure structural lemma, no extremal counting, ~1 page of Lean).
