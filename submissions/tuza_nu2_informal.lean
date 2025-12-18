/-
TUZA'S CONJECTURE ν=2: INFORMAL REASONING MODE

=== TASK ===
We need to prove: When ν(G) = 2, then τ(G) ≤ 4.

The approach via exists_reducing_edges has FAILED 8+ times in formal mode.
Before trying more formal proofs, let's reason INFORMALLY about:

1. WHY might exists_reducing_edges be true?
2. WHY might it be FALSE? (Is there a counterexample?)
3. What's the INTUITION behind Tuza's conjecture?
4. What makes ν=2 harder than ν=1?

=== INFORMAL REASONING REQUESTED ===

Please reason through this problem step by step in natural language.
Output your reasoning as comments. Then, if you find a path forward,
attempt to formalize it.

KEY QUESTIONS:

Q1: Given two edge-disjoint triangles t1, t2 in G with ν(G)=2,
    if we delete one edge from each (e1 ∈ t1, e2 ∈ t2),
    why should ν(G \ {e1,e2}) ≤ 1?

    Informal argument attempt:
    - t1 and t2 are no longer triangles in G'
    - Any triangle t3 in G' was also in G
    - t3 must have shared an edge with t1 or t2 (else ν(G) ≥ 3)
    - But wait... t3 could share an edge with t1 that ISN'T e1
    - So t3 might still be a triangle in G'
    - Could there be TWO such triangles t3, t4 that are edge-disjoint?

    THIS IS THE GAP. Explain why t3, t4 can't both exist.

Q2: The counterexample to vertex_disjoint_unique_packing showed:
    - t1 = {0,1,2}, t2 = {3,4,5} vertex-disjoint
    - t3 = {0,1,6} forms alternative packing {t2, t3}

    Does this counterexample also break exists_reducing_edges?
    What if we delete edge {0,1} from t1 and {3,4} from t2?
    Is ν(G') ≤ 1? Or can {t3, some t4} form a packing in G'?

Q3: What's special about K₅?
    - K₅ has ν=2, τ=4 (extremal)
    - Every pair of triangles in K₅ shares exactly one vertex
    - Deleting any edge kills exactly 3 triangles
    - Does this structure help?

=== YOUR INFORMAL ANALYSIS ===
Write your reasoning below as comments, then formalize if possible.

-/

import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Definitions -/

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

/-! ## INFORMAL REASONING SECTION

Please write your informal mathematical reasoning here as comments.
Explain your thought process, identify the key difficulties,
and propose approaches before formalizing.

YOUR ANALYSIS:

-/

/-
STEP 1: Understanding the problem structure

Let G have ν(G) = 2. This means:
- There exist two edge-disjoint triangles t1, t2
- There do NOT exist three pairwise edge-disjoint triangles

Let t1 = {a, b, c} and t2 = {d, e, f}.

Case A: t1 and t2 are vertex-disjoint (share 0 vertices)
Case B: t1 and t2 share exactly 1 vertex (e.g., c = d)
Case C: t1 and t2 share exactly 2 vertices - IMPOSSIBLE (would share an edge)

STEP 2: The reduction argument

We want to find edges e1, e2 such that ν(G \ {e1, e2}) ≤ 1.

Natural choice: e1 = {a,b} ∈ t1, e2 = {d,e} ∈ t2.

After deletion:
- t1 is destroyed (missing edge {a,b})
- t2 is destroyed (missing edge {d,e})

For ν(G') ≥ 2, we'd need two edge-disjoint triangles T1, T2 in G'.

STEP 3: Why can't T1, T2 exist?

Key constraint: T1 and T2 were triangles in G, and must have been
"connected" to t1 or t2 (else ν(G) ≥ 3 with {t1, t2, T1}).

Specifically:
- T1 shares an edge with t1 or t2
- T2 shares an edge with t1 or t2

If T1 shares edge with t1: T1 uses two vertices from {a,b,c}
If T1 shares edge with t2: T1 uses two vertices from {d,e,f}

THE DIFFICULTY: T1 could share edge {a,c} with t1 (not the deleted {a,b}).
So T1 survives in G'. Similarly T2 could share {d,f} with t2 and survive.

Could T1 (sharing {a,c}) and T2 (sharing {d,f}) be edge-disjoint?

T1 = {a, c, x} for some x
T2 = {d, f, y} for some y

These are edge-disjoint if:
- {a,c} ∩ {d,f} = ∅ ✓ (already true)
- {a,x}, {c,x} don't equal {d,y}, {f,y}
- This requires x ∉ {d,f} and y ∉ {a,c}

So IF x ∉ {d,e,f} and y ∉ {a,b,c}, we get edge-disjoint T1, T2 in G'.

But wait - in the original G, would {t1, T2} be edge-disjoint?
T2 = {d, f, y} with y ∉ {a,b,c}.
t1 = {a, b, c}.
These share no edges! So {t1, T2} would be edge-disjoint.
And {t2, T2} share edge {d,f}.
And {t1, t2} are edge-disjoint.

Hmm, {t1, T2} edge-disjoint means ν(G) ≥ 2 (which we know).
But can we have {t1, t2, T1} edge-disjoint?
T1 = {a, c, x} shares {a,c} with t1. Not edge-disjoint with t1. ✓

STEP 4: The actual constraint

For ν(G) = 2 exactly, every triangle T shares an edge with t1 OR t2.

If T shares edge with t1: T ∈ {{a,b,?}, {a,c,?}, {b,c,?}}
If T shares edge with t2: T ∈ {{d,e,?}, {d,f,?}, {e,f,?}}

Delete e1 = {a,b}, e2 = {d,e}.

Surviving triangles share: {a,c}, {b,c}, {d,f}, or {e,f} with t1/t2.

Could {a,c,x} and {d,f,y} both survive and be edge-disjoint?

Actually YES if x,y are chosen right. This seems like a problem...

STEP 5: Wait - reconsider

{a,c,x} shares {a,c} with t1, so was "forced" to share with t1.
{d,f,y} shares {d,f} with t2, so was "forced" to share with t2.

In G, these were both triangles. Are they edge-disjoint with each other?

{a,c,x} has edges: {a,c}, {a,x}, {c,x}
{d,f,y} has edges: {d,f}, {d,y}, {f,y}

Disjoint if {a,c,x} ∩ {d,f,y} has ≤ 1 element.

If vertex-disjoint t1, t2: {a,b,c} ∩ {d,e,f} = ∅.
So {a,c} ∩ {d,f} = ∅. Good.
Need x ∉ {d,f,y} or y ∉ {a,c,x} to avoid edge overlap.

This CAN happen! So ν(G') could be 2!

CONCLUSION: The naive edge choice {a,b}, {d,e} might NOT reduce ν.

STEP 6: Better edge choice?

What if we're smarter about which edges to delete?

If there's a vertex v that's in MANY triangles, deleting edges at v might help...

Or: Use blocking_number_le_2 result. There exist ≤2 edges that hit ALL maximum packings.
These might be different from "one edge per triangle".

FORMALIZATION ATTEMPT BASED ON THIS ANALYSIS:

-/

/-! ## Formalization Attempts -/

-- The naive approach that might fail
lemma exists_reducing_edges_naive (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ S : Finset (Sym2 V), S.card ≤ 2 ∧ S ⊆ G.edgeFinset ∧
      trianglePackingNumber (G.deleteEdges S) ≤ 1 := by
  sorry

-- Alternative: use blocking edges instead of "one per triangle"
-- The blocking_number_le_2 theorem says there exist ≤2 edges hitting all max packings
-- Can we show these edges actually REDUCE ν, not just block packings?

-- Key insight: blocking all max packings might not reduce ν if
-- new triangles become available. But new triangles don't appear
-- when we delete edges - only disappear. So blocking should work!

lemma blocking_implies_reducing (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (S : Finset (Sym2 V))
    (hS : ∀ P : Finset (Finset V), P ⊆ G.cliqueFinset 3 → IsEdgeDisjoint P →
          P.card = 2 → ∃ t ∈ P, (triangleEdges t ∩ S).Nonempty) :
    trianglePackingNumber (G.deleteEdges S) ≤ 1 := by
  sorry

-- Main theorem via blocking
theorem tuza_case_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4 := by
  sorry

end
