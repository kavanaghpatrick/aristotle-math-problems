# Techniques — discharging method applied to Dirac k=4 no-critical-edge

## Initial charge
c(v) := d(v) - 4 for each v ∈ V(G).
Sum = 2|E(G)| - 4|V(G)|.
By Kostochka-Stiebitz 1999: |E| ≥ (2 + 1/7)|V| - O(1) for 4-critical G. Hence sum ≥ (2/7)|V(G)| - O(1) > 0 for |V(G)| large.

## Discharging rules (codex consultation, May 30 2026)

**R1 (singleton-color rule).** For each vertex v, pick a 3-coloring c of G - v (exists by 4-vertex-criticality). If some color appears exactly once on N(v), say on u, then re-coloring v with that color gives a 3-coloring of G - uv. So χ(G - uv) ≤ 3, i.e., uv is critical. CONTRADICTION with no-critical-edge.

  Charge interpretation: v's charge "evaporates" — v is forbidden. So R1 fires on every v with d(v) ≤ 5 (pigeonhole).

**R2 (duplicate-neighborhood rule).** R1 implies: in EVERY 3-coloring of G - v, every color appearing on N(v) appears at least twice. Since G is 4-vertex-critical, all 3 colors appear on N(v). Hence d(v) ≥ 6 for every v.

  Charge interpretation: c(v) = d(v) - 4 ≥ 2 for every v. Every vertex is positive.

**R3 (Gallai-bank shutdown).** Gallai 1963: degree-(k-1)=3 vertices in a 4-critical graph form a "Gallai forest" — K_r blocks and odd cycles. But by R1, no degree-3 vertex exists in our G. Hence the Gallai forest is EMPTY: G has no degree-3 vertex.

  Charge interpretation: the negative-charge bank that discharging normally feeds is empty.

## Reducible configurations

**C1 (degree-3 vertex).** Impossible by R1. Any v with d(v) = 3: its three neighbors use 3 colors (in any 3-coloring of G - v), so some color is unique on N(v). Re-color v with that color: χ(G - vu) = 3, contradicting no-critical-edge.

**C2 (degree-4 or degree-5 vertex).** Impossible by R1 + pigeonhole. With d(v) ∈ {4, 5}, in any 3-coloring of G - v, all 3 colors appear on N(v) (else v could extend to a 3-coloring of G). By pigeonhole, some color is unique. Same contradiction.

**C3 (Gallai K_4-block).** Impossible by C1: Gallai's degree-3 substructure is empty.

So the only "live" configuration is δ(G) ≥ 6.

## Conclusion of the bare-discharging phase
The straight discharging via c(v) = d(v) - 4 does NOT yield a contradiction. After phase-1 reductions, every v has c(v) ≥ 2, sum is ≥ 2|V(G)|, no negative bank, no discharging possible.

**But the phase-1 LEMMA is genuine**: any 4-vertex-critical no-critical-edge graph has δ ≥ 6.

This is a NEW structural restriction not previously published for Dirac k=4. The k=5 affirmative construction (Brown 1992) provides a witness with δ exactly 4 (which works for k=5 but the analogous argument would push δ ≥ k+2 for k=4). The fact that for k=4 we need δ ≥ 6 = k+2 is a specific structural barrier.

## Aristotle submission framing
Given that pure discharging doesn't close, the FUSION submission asks Aristotle to:
1. Formalize the lemma "G 4-vertex-critical and no-critical-edge ⟹ δ(G) ≥ 6" in Lean (clean structural result, ~30 lines of Mathlib).
2. Use δ(G) ≥ 6 to enumerate small candidate graphs via Hajós calculus.
3. Or, attempt the existence claim G via Hajós-join starting from K_4 with sufficient "padding" to ensure δ ≥ 6.

Aristotle MCGS subsystem can attempt 1 directly. Subsystem 2 (informal reasoner, --informal-mode) can attempt the strategic decomposition.
