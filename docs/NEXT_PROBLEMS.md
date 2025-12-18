# Next Problems for Aristotle (Post-Tuza)

Based on Grok-4's analysis of what worked for Tuza, these are the recommended next targets.

## What Works for Aristotle

| Strength | Example from Tuza |
|----------|-------------------|
| Local structure reasoning | Triangles, cliques, edge-disjointness |
| Induction on parameters | Induction on ν, graph size |
| Case analysis | Small configurations (K₄, bowtie) |
| Counterexample discovery | TuzaReductionProperty, NearbyTriangles |
| Boris pattern | Minimal prompts, let AI explore |

## What Doesn't Work

| Weakness | Why |
|----------|-----|
| Probabilistic arguments | Can't discover Lovász Local Lemma applications |
| Complex weighting schemes | Too many degrees of freedom |
| "Insight leaps" | Can't jump to non-obvious approaches |

---

## Problem 1: Mantel's Theorem ⭐ RECOMMENDED FIRST

**Statement:** In any graph with n vertices and more than ⌊n²/4⌋ edges, there exists a triangle.

**Why Good Target:**
- Same local structure as Tuza (triangles)
- Induction on n with degree case analysis
- Tight examples are explicit (complete bipartite K_{n/2,n/2})
- EXACT result (not just a bound)

**Difficulty:** 4/10

**Lean Approach:**
```lean
theorem mantel (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (h : G.edgeFinset.card > Fintype.card V ^ 2 / 4) :
    ∃ t ∈ G.cliqueFinset 3, True := by
  sorry
```

**Submission Strategy:** "Prove Mantel by induction on n, case analysis on high-degree vertices; generate counterexamples for tightness."

---

## Problem 2: Ramsey Number R(3,3) = 6

**Statement:** Every 2-coloring of K₆ edges contains a monochromatic triangle. R(3,3) ≤ 5 is false (5-cycle is counterexample).

**Why Good Target:**
- Pure case analysis on small configurations
- Triangle/clique local structure
- Explicit counterexamples (C₅)
- FINITE - can verify exhaustively

**Difficulty:** 3/10

**Lean Approach:**
```lean
theorem ramsey_3_3 :
    ∀ (f : Sym2 (Fin 6) → Bool),
    (∃ t : Finset (Fin 6), t.card = 3 ∧ ∀ e ∈ t.sym2, ¬e.IsDiag → f e = true) ∨
    (∃ t : Finset (Fin 6), t.card = 3 ∧ ∀ e ∈ t.sym2, ¬e.IsDiag → f e = false) := by
  sorry
```

**Submission Strategy:** "Verify R(3,3)=6 by case analysis; find C₅ counterexample for R(3,3)≤5."

---

## Problem 3: Turán's Theorem for K₃

**Statement:** The maximum edges in an n-vertex triangle-free graph is ⌊n²/4⌋, achieved by K_{⌊n/2⌋,⌈n/2⌉}.

**Why Good Target:**
- Builds on Mantel (converse direction)
- Triangle local structure
- Induction with bipartition cases
- Extremal graph theory foundation

**Difficulty:** 5/10

**Lean Approach:**
```lean
theorem turan_k3 (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (h : G.CliqueFree 3) :
    G.edgeFinset.card ≤ Fintype.card V ^ 2 / 4 := by
  sorry
```

**Submission Strategy:** "Prove Turán for K₃ by induction on n with bipartition; show bound is tight via complete bipartite."

---

## Problem 4: Friendship Theorem (Weak Version)

**Statement:** If every pair of vertices has exactly one common neighbor, the graph is a "windmill" (triangles sharing one central vertex).

**Why Good Target:**
- Local structure (common neighbors, triangles)
- Case analysis on vertex pairs
- Small counterexamples to false claims
- Similar reasoning to Tuza ν=1 case

**Difficulty:** 6/10

**Lean Approach:**
```lean
def FriendshipGraph (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → ∃! w, G.Adj u w ∧ G.Adj v w

theorem friendship_windmill (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (h : FriendshipGraph G) :
    ∃ c : V, ∀ t ∈ G.cliqueFinset 3, c ∈ t := by
  sorry
```

**Submission Strategy:** "Explore friendship condition via case analysis on vertex pairs; prove windmill structure by induction."

---

## Problem 5: Dirac's Theorem (Lower Bound)

**Statement:** If min degree ≥ n/2 in an n-vertex graph (n ≥ 3), then it's Hamiltonian.

**Why Good Target:**
- Induction on graph size
- Case analysis on path extensions
- Local structure via degrees
- Counterexamples for weaker bounds

**Difficulty:** 7/10

**Lean Approach:**
```lean
theorem dirac (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (hn : Fintype.card V ≥ 3)
    (hdeg : ∀ v : V, G.degree v ≥ Fintype.card V / 2) :
    G.IsHamiltonian := by
  sorry
```

**Submission Strategy:** "Prove Dirac by induction on n with path endpoint cases; counterexamples for degree n/2-1."

---

## Recommended Order

1. **Mantel's Theorem** - Natural next step, same local structure as weak Tuza
2. **R(3,3) = 6** - Finite case analysis, good test of exhaustive search
3. **Turán K₃** - Builds on Mantel
4. **Friendship** - More complex case analysis
5. **Dirac** - Hardest, requires path reasoning

## Boris Pattern Template

For each problem, submit:

**Formal (minimal):**
```lean
import Mathlib
-- Minimal definitions
-- Theorem statement with sorry
```

**Informal:**
```
Problem: [one line]
Known: [what's in Mathlib]
Goal: [exact theorem]
```

Let Aristotle explore freely. The weak Tuza success came from 47 lines, not 160.
