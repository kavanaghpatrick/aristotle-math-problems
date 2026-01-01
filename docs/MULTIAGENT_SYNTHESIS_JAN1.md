# Multi-Agent Synthesis: Exchange Argument for ν* = 4

**Date**: January 1, 2026
**Agents**: Grok-4, Gemini, Codex
**Problem**: Prove packingWeight ≤ 4 for any fractional packing when ν = 4

---

## Executive Summary

Three AI agents independently analyzed the exchange argument gap. Key findings:

1. **ν* = ν is NOT automatic** (Gemini) - The fractional packing number can exceed integer packing
2. **Naive Fubini fails** (All) - Gives 3×M.sum + ext.sum ≤ 12, not packingWeight ≤ 4
3. **Correct approach: Dual Certificate** (Codex) - Covering Selection proves packingWeight ≤ |M|

---

## Agent Reports

### Grok: Exchange Argument Analysis

**Key Insight**: The exchange argument works via slack consumption.

- Define slack(m) = 1 - w(m) for each m ∈ M
- Each external shares an M-edge with unique owner m
- w(external) ≤ slack(owner) by edge constraint
- Total: externals.sum ≤ totalSlack = |M| - M.sum

**Problem**: This gives ext.sum ≤ 3 × totalSlack (each m owns 3 edges), not ext.sum ≤ totalSlack.

**Recommendation**: Use indicator saturation argument - when M is saturated (all w(m) = 1), externals must be 0.

### Gemini: LP Duality Research

**Critical Finding**: ν* = ν is NOT automatically true!

> "Haxell and Rödl showed that ν*(G) - ν(G) = o(n²) for all graphs G...
> Yuster showed ν*(G) - ν(G) = Ω(n^1.5) for infinitely many G."

**LP Framework**:
- Primal: max Σ w(t) s.t. Σ_{t ∋ e} w(t) ≤ 1
- Dual: min Σ y(e) s.t. Σ_{e ∈ t} y(e) ≥ 1

**Failed Dual Construction**: y(e) = 1/3 for M-edges doesn't work - externals sharing only 1 M-edge get coverage 1/3 < 1.

**Recommendation**: Construct a proper dual certificate or prove τ ≤ 8 directly.

### Codex: Lean Formalization Strategy

**Correct Approach: Covering Selection**

```lean
def IsCoveringSelection (G M S) : Prop :=
  S ⊆ M_edges G M ∧
  S.card = M.card ∧
  ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ S, e ∈ t.sym2
```

**Why This Works**:
1. Each edge e ∈ S has constraint: (triangles ∋ e).sum w ≤ 1
2. Every triangle contains ≥ 1 edge from S (covering property)
3. Summing: packingWeight ≤ |S| = |M| = 4

**Key Lemma Needed**: `covering_selection_exists` - For maximal M, we can select |M| edges that cover all triangles.

---

## Proof Outline (Consensus)

### Step 1: Indicator Achieves 4 ✓ PROVEN
The indicator 1_M is a valid fractional packing with weight |M| = 4.

### Step 2: No Packing Exceeds 4 ← THE GAP

**Approach A: Covering Selection (Recommended)**
1. Prove: For maximal M with |M| = 4, ∃ S ⊆ M_edges with |S| = 4 covering all triangles
2. By weak duality: packingWeight ≤ |S| = 4

**Approach B: Case Analysis**
- For each M structure (star, path, cycle, scattered), prove bound directly
- Tedious but concrete

**Approach C: Hall's Theorem**
- Model as bipartite matching: M-elements ↔ externals
- Show Hall's condition satisfied

---

## Remaining Work

### Primary Target: `covering_selection_exists`

```lean
lemma covering_selection_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    ∃ S, IsCoveringSelection G M S := sorry
```

**Proof Sketch**:
1. For each external t, it shares edge e_t with some m_t ∈ M (by maximality)
2. Define assignment: t ↦ m_t
3. For each m ∈ M, pick edge that covers the most externals assigned to m
4. Verify: every M-element has picked edge, every triangle is covered

**Case Analysis** (if needed):
- **Star (all share 1 vertex)**: Central vertex's edges cover everything
- **Path/Cycle**: Careful selection along the structure
- **Scattered**: Independent, trivially works

---

## Files Created

- `slot174_dual_certificate.lean` - Main formalization with CoveringSelection approach
- 1 sorry on `covering_selection_exists`

---

## References

- Krivelevich (1995): τ ≤ 2ν*
- Haxell-Rödl: Integrality gap bounds
- Yuster: Counterexamples to ν* = ν
