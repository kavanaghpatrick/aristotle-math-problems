import Mathlib

set_option maxHeartbeats 8000000

/-!
# Erdős Problem 944 — Dirac's Conjecture, k = 4 Case

## The Problem

Dirac (1970) asked: for every k ≥ 4, does there exist a finite simple graph G
with chromatic number k such that every vertex is critical (removing any vertex
strictly drops χ) yet every single edge is non-critical (no single-edge deletion
drops χ)?

## Known Results

- **k ≥ 5**: Resolved positively. Brown (1992) gave the first construction for
  k = 5; Lattanzio (2002) extended to k = 6,7; Jensen (2002) handled all k ≥ 5.
- **k = 4**: **OPEN** as of 2025. No 4-vertex-critical graph with no critical
  edges has been found, and non-existence has not been proved.

## Proof Approaches Considered

### 1. Brute-force small graph search
Any 4-vertex-critical graph on n vertices has at least ⌈(5n-2)/4⌉ edges
(Dirac's theorem for 4-critical graphs). The smallest candidates have ≥ 6
vertices (since K₄ is both vertex- and edge-critical). Exhaustive computational
searches on small graphs (n ≤ 12) have not yielded examples.

### 2. DP-coloring / correspondence-coloring approach
The DP-chromatic number χ_DP(G) ≥ χ(G). For a 4-vertex-critical G with no
critical edges, each edge e has χ(G-e) = 4, so G-e contains a DP-4-critical
subgraph H_e with edge density ≥ 40/13 · |V(H_e)| (Bernshteyn–Kostochka–Pron
2017). This gives density constraints but does not resolve existence.

### 3. Hajós construction / Ore composition
Standard constructions from K₄ (Hajós join, Ore composition) produce
4-critical graphs, but these constructions inherently create critical edges.
No known modification avoids this for k = 4.

## Conclusion
The problem remains genuinely open. The `sorry` below reflects the current state
of mathematical knowledge, not a limitation of the proof assistant.
-/

namespace SimpleGraph

/-- A graph `G` is *k-critical* if its chromatic number equals `k` and removing
    any single vertex strictly decreases the chromatic number. -/
def IsCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧
  ∀ v : V, (G.induce ({v}ᶜ : Set V)).chromaticNumber < k

/-- An edge `e` is *critical* for `G` if removing it strictly decreases the
    chromatic number. -/
def IsCriticalEdge {V : Type*} (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  (G.deleteEdges {e}).chromaticNumber < G.chromaticNumber

end SimpleGraph

/--
Erdős 944 / Dirac's conjecture, k = 4 case:
There exists a finite 4-vertex-critical simple graph in which no edge is critical.

**Status: OPEN.** This is an unsolved problem in combinatorics (open since 1970).
The cases k ≥ 5 were resolved positively by Brown (1992), Lattanzio (2002),
and Jensen (2002), but the k = 4 case remains open as of 2025.
-/
theorem yolo_w3_erdos_944_dp_coloring :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.IsCritical 4 ∧
      (∀ e : Sym2 V, ¬ G.IsCriticalEdge e) := by
  sorry
