# Codex W3 Erdős 944 DP-coloring transplant (May 30 2026)

codex
I’ll verify the exact DP-coloring facts and density theorem before compressing this into the requested argument, since the conclusion depends on theorem hypotheses.
web search: 
web search: Bernshteyn 2017 DP-coloring edge deletion theorem correspondence chromatic number edge deletion
web search: 
web search: https://arxiv.org/abs/1609.09122
web search: 
web search: site:epubs.siam.org Bernshteyn Kostochka DP-critical graphs 2019 SIAM Journal on Discrete Mathematics
web search: 
web search: "Sharp Dirac" "SIAM Journal on Discrete Mathematics" "DP-Critical"
web search: 
web search: "DP-critical" "density" "Bernshteyn"
web search: 
web search: 
web search: 
web search: https://arxiv.org/pdf/1609.09122
web search: 
web search: https://arxiv.org/pdf/1609.09122
web search: 
web search: "On DP-coloring of graphs and multigraphs" Bernshteyn Kostochka Pron edge deletion theorem
web search: 
web search: https://arxiv.org/pdf/1609.00763
web search: 
web search: https://arxiv.org/pdf/1609.00763
web search: 
web search: "Bernshteyn" "Kostochka" "SIAM Journal on Discrete Mathematics" "critical graphs"
web search: 
web search: "The asymptotic behavior of the correspondence chromatic number" "edge" "deletion"
web search: 
web search: "rigid" "DP-coloring" "edge" Bernshteyn
codex
(i) **Precise DP Transplant.**  
For a finite simple graph `G`, use a `3`-fold DP cover `𝓗`; an `𝓗`-coloring is an independent transversal of the cover. `χ_DP(G) ≥ 4` means: there exists a `3`-fold cover of `G` with no coloring. This is the right transplant of “not 3-colorable.” Ordinary `χ(G)=4` implies `χ_DP(G)≥4`, since ordinary/list colorings embed into DP-coloring. Dvořák-Postle introduced this correspondence-coloring framework; Bernshteyn-Kostochka-Pron use the same cover/independent-transversal language. Sources: Dvořák-Postle JCTB 2018, and B-K-P 2017. [DP definition](https://arxiv.org/pdf/1609.09122), [B-K-P](https://arxiv.org/pdf/1609.00763).

(ii) **Restriction Obtained.**  
Assume `G` is a hypothetical Dirac `k=4` counterexample:

`χ(G)=4`, every `G-v` is 3-colorable, and every `G-e` still has chromatic number `4`.

Then for every edge `e`, `χ_DP(G-e) ≥ 4`. Choose an inclusion-minimal subgraph `H_e ⊆ G-e` with `χ_DP(H_e) ≥ 4`. Then:

`H_e` is DP-4-critical.

By DP edge-deletion rigidity, deleting any edge of `H_e` lowers `χ_DP` exactly to `3`, not below and not staying `≥4`.

By DP-critical density, if `H_e ≠ K4`, then

`2|E(H_e)| ≥ (40/13)|V(H_e)|`.

Sharper: if `H_e` is controlled by the sharp DP-Dirac theorem and is not the exceptional 3-Dirac graph, then

`2|E(H_e)| > 3|V(H_e)| + 1`.

So any hypothetical no-critical-edge `G` must have the following strong “edge-avoidable DP-core” property:

For every edge `e ∈ E(G)`, `G-e` contains a DP-4-critical subgraph `H_e`, avoiding `e`, with DP-critical density at least `40/13`, usually above the Dirac line `3n+1`.

If one additionally assumes the stronger DP-vertex-critical transplant `χ_DP(G-v) ≤ 3` for all `v`, then each `H_e` must be spanning, giving the global restriction

`2|E(G)| - 2 ≥ 2|E(H_e)| ≥ (40/13)|V(G)|`

and usually

`2|E(G)| > 3|V(G)| + 3`.

But that stronger DP-vertex-critical hypothesis is **not implied** by ordinary 4-vertex-criticality.

(iii) **Four Lean Lemma Candidates.**

1. `ordinary_chromatic_le_dp_chromatic`  
   `χ G ≤ χ_DP G`.

2. `no_critical_edge_gives_dp_core`  
   If `χ(G-e)=4`, then there exists `H ⊆ G-e` minimal with `χ_DP H ≥ 4`.

3. `minimal_dp_non3_is_dp4_critical`  
   Inclusion-minimal `χ_DP ≥ 4` subgraph is DP-4-critical; edge deletion gives `χ_DP(H-f)=3`.

4. `dp4_critical_density_k4`  
   DP-4-critical `H ≠ K4` satisfies `2|E H| ≥ (40/13)|V H|`; optionally add the sharper non-Dirac branch.

(iv) **Open-Question Assessment.**  
This does **not** solve Erdős 944 / Dirac `k=4`. It gives a clean obstruction: every edge of a counterexample must be avoidable by a dense DP-4-critical core. The missing bridge is exactly the dangerous one: ordinary vertex-criticality does not force DP-vertex-criticality, and DP cores inside `G-e` need not be spanning. The DP machinery is useful structure, not a proof of nonexistence or existence.
tokens used
110,629
(i) **Precise DP Transplant.**  
For a finite simple graph `G`, use a `3`-fold DP cover `𝓗`; an `𝓗`-coloring is an independent transversal of the cover. `χ_DP(G) ≥ 4` means: there exists a `3`-fold cover of `G` with no coloring. This is the right transplant of “not 3-colorable.” Ordinary `χ(G)=4` implies `χ_DP(G)≥4`, since ordinary/list colorings embed into DP-coloring. Dvořák-Postle introduced this correspondence-coloring framework; Bernshteyn-Kostochka-Pron use the same cover/independent-transversal language. Sources: Dvořák-Postle JCTB 2018, and B-K-P 2017. [DP definition](https://arxiv.org/pdf/1609.09122), [B-K-P](https://arxiv.org/pdf/1609.00763).

(ii) **Restriction Obtained.**  
Assume `G` is a hypothetical Dirac `k=4` counterexample:

`χ(G)=4`, every `G-v` is 3-colorable, and every `G-e` still has chromatic number `4`.

Then for every edge `e`, `χ_DP(G-e) ≥ 4`. Choose an inclusion-minimal subgraph `H_e ⊆ G-e` with `χ_DP(H_e) ≥ 4`. Then:

`H_e` is DP-4-critical.

By DP edge-deletion rigidity, deleting any edge of `H_e` lowers `χ_DP` exactly to `3`, not below and not staying `≥4`.

By DP-critical density, if `H_e ≠ K4`, then

`2|E(H_e)| ≥ (40/13)|V(H_e)|`.

Sharper: if `H_e` is controlled by the sharp DP-Dirac theorem and is not the exceptional 3-Dirac graph, then

`2|E(H_e)| > 3|V(H_e)| + 1`.

So any hypothetical no-critical-edge `G` must have the following strong “edge-avoidable DP-core” property:

For every edge `e ∈ E(G)`, `G-e` contains a DP-4-critical subgraph `H_e`, avoiding `e`, with DP-critical density at least `40/13`, usually above the Dirac line `3n+1`.

If one additionally assumes the stronger DP-vertex-critical transplant `χ_DP(G-v) ≤ 3` for all `v`, then each `H_e` must be spanning, giving the global restriction

`2|E(G)| - 2 ≥ 2|E(H_e)| ≥ (40/13)|V(G)|`

and usually

`2|E(G)| > 3|V(G)| + 3`.

But that stronger DP-vertex-critical hypothesis is **not implied** by ordinary 4-vertex-criticality.

(iii) **Four Lean Lemma Candidates.**

1. `ordinary_chromatic_le_dp_chromatic`  
   `χ G ≤ χ_DP G`.

2. `no_critical_edge_gives_dp_core`  
   If `χ(G-e)=4`, then there exists `H ⊆ G-e` minimal with `χ_DP H ≥ 4`.

3. `minimal_dp_non3_is_dp4_critical`  
   Inclusion-minimal `χ_DP ≥ 4` subgraph is DP-4-critical; edge deletion gives `χ_DP(H-f)=3`.

4. `dp4_critical_density_k4`  
   DP-4-critical `H ≠ K4` satisfies `2|E H| ≥ (40/13)|V H|`; optionally add the sharper non-Dirac branch.

(iv) **Open-Question Assessment.**  
This does **not** solve Erdős 944 / Dirac `k=4`. It gives a clean obstruction: every edge of a counterexample must be avoidable by a dense DP-4-critical core. The missing bridge is exactly the dangerous one: ordinary vertex-criticality does not force DP-vertex-criticality, and DP cores inside `G-e` need not be spanning. The DP machinery is useful structure, not a proof of nonexistence or existence.
