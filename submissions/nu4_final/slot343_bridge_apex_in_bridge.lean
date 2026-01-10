/-
  slot343: Test if apex is ALWAYS in the bridge

  Grok Strategy (Option B): Modify edge selection to hit bridges.

  KEY QUESTION: Is the universal apex of X always in B when B is a bridge
  sharing edges with X and Y?

  If YES: Apex-based edges automatically hit bridges (no modification needed)
  If NO: Need coordinated selection or bridge assignment

  ANALYSIS:
  - B ∩ X ∩ Y has vertex v (by bridge_inter_nonempty)
  - X = {v, x, z} where B ∩ X = {v, x}
  - B = {v, x, y} where y ∈ Y

  Universal apex for X-externals: all externals of X share a common vertex.

  Question: Is this apex necessarily in {v, x} (the shared edge with B)?

  If apex = v or x, then edges from apex include s(v,x) which is in B.
  If apex = z (the "third" vertex of X not in B), then edges s(z,v), s(z,x)
  are NOT in B.sym2 = {s(v,x), s(v,y), s(x,y)}.

  So the lemma to prove/disprove:
  apex_in_bridge: The universal apex of X is in B whenever B is an X-adjacent bridge.
-/

import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators Classical
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t X ∧
  ∀ Y ∈ M, Y ≠ X → ¬sharesEdgeWith t Y

def isBridgeOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (X Y B : Finset V) : Prop :=
  B ∈ G.cliqueFinset 3 ∧ B ∉ M ∧ X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧
  sharesEdgeWith B X ∧ sharesEdgeWith B Y

-- ═══════════════════ PROVEN SCAFFOLDING ═══════════════════

lemma sharesEdgeWith_iff_card_inter_ge_two (t S : Finset V) :
    sharesEdgeWith t S ↔ 2 ≤ (t ∩ S).card := by
  constructor <;> intro h
  · obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := h
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩,
                                   v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    exact ⟨u, v, huv, Finset.mem_of_mem_inter_left hu, Finset.mem_of_mem_inter_left hv,
           Finset.mem_of_mem_inter_right hu, Finset.mem_of_mem_inter_right hv⟩

lemma triangle_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) : T.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp hT).2

lemma bridge_inter_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (B X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (hBX : sharesEdgeWith B X) (hBY : sharesEdgeWith B Y)
    (hB_card : B.card = 3) :
    (B ∩ X ∩ Y).Nonempty := by
  by_contra h_empty
  rw [Finset.not_nonempty_iff_eq_empty] at h_empty
  have hBX_ge : (B ∩ X).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two B X |>.mp hBX
  have hBY_ge : (B ∩ Y).card ≥ 2 := sharesEdgeWith_iff_card_inter_ge_two B Y |>.mp hBY
  have h_disj : Disjoint (B ∩ X) (B ∩ Y) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    convert h_empty using 1; ext v; simp [Finset.mem_inter]
  have h_union_card : ((B ∩ X) ∪ (B ∩ Y)).card ≥ 4 := by
    rw [Finset.card_union_of_disjoint h_disj]; omega
  have h_sub : (B ∩ X) ∪ (B ∩ Y) ⊆ B := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv' | hv'
    · exact Finset.mem_of_mem_inter_left hv'
    · exact Finset.mem_of_mem_inter_left hv'
  have := Finset.card_le_card h_sub
  omega

-- ═══════════════════ TARGET LEMMA ═══════════════════

/-
PROOF SKETCH:
1. Let apex be the universal apex for X-externals (exists by universal_apex_exists)
2. apex ∈ X (by definition - it's a vertex that all externals share with X)
3. B ∩ X = {v, x} for some v ∈ X ∩ Y and x ∈ X (by bridge_inter_nonempty + shares edge)
4. X = {v, x, apex} (X has 3 vertices, contains v, x, and apex)

CASE A: apex ∈ {v, x}
- Then apex ∈ B (since {v,x} ⊆ B)
- Edges incident to apex from X hit B

CASE B: apex = z where z ∉ {v, x}
- X = {v, x, z}
- Any X-external T shares apex z with X
- But B is NOT an external (it's a bridge sharing with Y too)
- So we only need externals to share apex, not bridges!

WAIT: This means the lemma might be FALSE!
The apex is defined for EXTERNALS, not for bridges.
Bridges are different triangles that share with 2+ M-elements.

Let's test: Can apex = z ∉ B?
If so, the naive apex-based selection DOES miss bridges!

ALTERNATIVE APPROACH:
Instead of proving apex ∈ B, prove:
For any bridge B adjacent to X, one of X's 3 edges hits B.

B ∩ X = {v, x}, B = {v, x, y}
X = {v, x, z}
B.sym2 = {s(v,x), s(v,y), s(x,y)}
X edges incident to X: s(v,x), s(v,z), s(x,z)

s(v,x) is in BOTH B.sym2 and X's edges!

So ANY X-edge selection that includes s(v,x) covers B.
The issue is: apex-based selection chooses 2 edges incident to apex.
If apex = z, edges are s(z,v), s(z,x), which DON'T include s(v,x).

SOLUTION:
Not all 2-edge selections work. But we can CHOOSE to include s(v,x).
The question is: can we cover X + externals + bridges with 2 edges?

NEW LEMMA: For X with bridge B where B ∩ X = {v, x}:
The edge s(v, x) covers B.
We need 1 more edge to cover X + externals.
If externals share apex z, edge s(z, v) or s(z, x) covers X and some externals.

Hmm, 2 edges might not be enough if there are many externals with different apexes.
But universal_apex_exists says all externals share ONE apex!

So:
- Edge 1: s(v, x) - covers B and X (hits edge of X)
- Edge 2: s(apex, v) or s(apex, x) - covers all externals (they all contain apex)

Wait, does edge 2 cover ALL externals? An external T contains apex and shares edge with X.
If T shares edge {apex, w} with X, then s(apex, w) ∈ T.
We need s(apex, v) or s(apex, x) to be in T.

If apex = v, then s(v, x) is edge 1, and edge 2 could be s(v, z).
All externals contain v = apex. Each external shares edge with X = {v, x, z}.
An external T contains v plus one of {x, z}.
So T's edge with X is either {v, x} or {v, z}.
Edge s(v, x) or s(v, z) hits T. We have both!

If apex = z (not in B), then:
- Edge 1: s(v, x) - covers B
- Edge 2: s(z, ?) - should cover externals

Each external contains z and shares edge {z, v} or {z, x} with X.
So edge 2 = s(z, v) or s(z, x).
But we need ONE edge to cover ALL externals.
If some externals share {z, v} and others share {z, x}, we need both!

So 2 edges might NOT suffice if apex ∉ {v, x}!

UNLESS: All externals share the SAME edge with X.
That is, all X-externals share edge {z, v} (or all share {z, x}).

Hmm, let me re-examine universal_apex_exists.
-/

-- Test lemma: Does shared edge between X and bridge determine apex location?
-- This might be FALSE - submit to Aristotle for counterexample search on Fin 6.

lemma apex_in_bridge_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X Y B : Finset V) (hBridge : isBridgeOf G M X Y B)
    -- Universal apex for X-externals
    (apex : V) (hApex : apex ∈ X)
    (hApex_universal : ∀ T, isExternalOf G M X T → apex ∈ T) :
    -- Apex is in the shared edge with B
    apex ∈ B ∩ X := by
  sorry

-- If above is FALSE, this alternative might work:
-- The shared edge {v, x} of B and X plus one apex edge covers X + externals + B

lemma two_edges_cover_X_externals_and_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (X Y B : Finset V) (hBridge : isBridgeOf G M X Y B)
    (hX_card : X.card = 3) :
    ∃ e1 e2 : Sym2 V, e1 ∈ G.edgeFinset ∧ e2 ∈ G.edgeFinset ∧
    -- e1 or e2 hits X
    (∃ u ∈ X, ∃ v ∈ X, u ≠ v ∧ (e1 = s(u,v) ∨ e2 = s(u,v))) ∧
    -- e1 or e2 hits all X-externals
    (∀ T, isExternalOf G M X T → e1 ∈ T.sym2 ∨ e2 ∈ T.sym2) ∧
    -- e1 or e2 hits B
    (e1 ∈ B.sym2 ∨ e2 ∈ B.sym2) := by
  sorry

end
