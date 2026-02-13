/-
  slot528_6packing_argument.lean

  FOCUSED: Just the 6-packing argument (not_all_three_types)

  KEY INSIGHT: If M.card = 4 and all 3 edge-types have externals,
  we can construct a 6-packing, contradicting ν = 4.

  TIER: 2-3 (construction + pigeonhole)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS on Fin 12
-- ══════════════════════════════════════════════════════════════════════════════

abbrev V12 := Fin 12

def isTrianglePacking12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V12)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def S_e12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12) : Finset (Finset V12) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧ ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

/-- Externals using specific edges of e -/
def S_e_type12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12) (x y z : V12) : Finset (Finset V12) :=
  (S_e12 G M e).filter (fun T => x ∈ T ∧ y ∈ T ∧ z ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Triangle card = 3 from packing membership
-- ══════════════════════════════════════════════════════════════════════════════

lemma packing_elem_card3 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (e : Finset V12) (he : e ∈ M) : e.card = 3 := by
  have he_clq := hM.1 he
  rw [SimpleGraph.mem_cliqueFinset_iff] at he_clq
  exact he_clq.1.card_eq

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Externals share only vertex, not edge, with each other
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
If T_ab ∈ S_e_type for edge {a,b} and T_bc ∈ S_e_type for edge {b,c}:
- T_ab contains a, b but not c
- T_bc contains b, c but not a
- T_ab ∩ T_bc contains b (shared)
- If T_ab ∩ T_bc contains another vertex x:
  - x ∈ T_ab means x ∈ {a, b, third} where third ∉ e
  - x ∈ T_bc means x ∈ {b, c, third'} where third' ∉ e
  - x ≠ a (since a ∉ T_bc)
  - x ≠ c (since c ∉ T_ab)
  - x = b or x is the third vertex of both
- Therefore |T_ab ∩ T_bc| ≤ 1 (they share at most vertex b)
-/

lemma externals_share_at_most_one (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (e : Finset V12)
    (a b c : V12) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (T1 T2 : Finset V12)
    (hT1 : T1 ∈ S_e_type12 G M e a b c)  -- T1 uses edge {a,b}
    (hT2 : T2 ∈ S_e_type12 G M e b c a)  -- T2 uses edge {b,c}
    (hT12 : T1 ≠ T2) :
    (T1 ∩ T2).card ≤ 1 := by
  simp only [S_e_type12, S_e12, mem_filter] at hT1 hT2
  -- T1 contains a, b, not c
  -- T2 contains b, c, not a
  have ha1 : a ∈ T1 := hT1.2.1
  have hb1 : b ∈ T1 := hT1.2.2.1
  have hc1 : c ∉ T1 := hT1.2.2.2
  have hb2 : b ∈ T2 := hT2.2.1
  have hc2 : c ∈ T2 := hT2.2.2.1
  have ha2 : a ∉ T2 := hT2.2.2.2
  -- T1 ∩ T2 ⊆ {b} (a ∉ T2, c ∉ T1, and any other vertex is in at most one)
  have hsub : T1 ∩ T2 ⊆ {b} := by
    intro x hx
    simp only [mem_inter] at hx
    simp only [mem_singleton]
    -- x ∈ T1 and x ∈ T2
    -- x ≠ a (since a ∉ T2)
    -- x ≠ c (since c ∉ T1)
    by_contra hxb
    -- x is the third vertex of both T1 and T2
    -- T1 = {a, b, x} and T2 = {b, c, x}
    -- Both are triangles (card 3)
    have hT1_3 : T1.card = 3 := by
      rw [SimpleGraph.mem_cliqueFinset_iff] at hT1
      exact hT1.1.1.1.card_eq
    have hT2_3 : T2.card = 3 := by
      rw [SimpleGraph.mem_cliqueFinset_iff] at hT2
      exact hT2.1.1.1.card_eq
    -- If x ≠ a, x ≠ b, x ≠ c, then T1 = {a, b, x} and T2 = {b, c, x}
    -- are distinct triangles sharing edge {b, x}
    -- But they're both in S_e, which requires exclusivity to e...
    -- Actually, this doesn't immediately give a contradiction
    -- The key is that if x ∈ T1 ∩ T2 and x ≠ b, then x is the third vertex
    -- But T1 and T2 are exclusive to e, so they don't share edges with
    -- any other M-element. Since T1 ≠ T2, they could share vertex x.
    -- Wait, we need a different argument.
    -- Let me just prove by exhaustion that T1 ∩ T2 ⊆ {b}
    -- x ∈ T1, x ∈ T2, x ≠ b
    -- x ∈ T1 means x = a or x = b or x is the third vertex of T1
    -- x ≠ a (since a ∉ T2)
    -- x ≠ b (assumption)
    -- So x is the third vertex of T1
    -- Similarly, x is the third vertex of T2
    -- So T1 and T2 share their third vertices
    -- T1 = {a, b, x}, T2 = {b, c, x}
    -- Then T1 ∩ T2 = {b, x}, so |T1 ∩ T2| = 2, not ≤ 1
    -- So we need to show this can't happen...
    -- Actually, it CAN happen! Two externals can share their third vertex.
    -- So this lemma as stated is FALSE.
    sorry
  calc (T1 ∩ T2).card ≤ ({b} : Finset V12).card := card_le_card hsub
       _ = 1 := card_singleton b

-- Actually, the above lemma is FALSE. Two externals CAN share their third vertex.
-- Example: e = {0,1,2}, T_ab = {0,1,3}, T_bc = {1,2,3}
-- Both are valid externals, and T_ab ∩ T_bc = {1,3} has card 2.

-- The 6-packing argument needs a different approach:
-- We use the fact that M itself has 4 elements, and externals
-- are exclusive to e (don't share edges with other M-elements).

-- ══════════════════════════════════════════════════════════════════════════════
-- CORRECT APPROACH: Build 6-packing from externals + other M-elements
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH (corrected):
Given M = {e, f, g, h} with M.card = 4, if e has externals T_ab, T_bc, T_ac:
1. T_ab, T_bc, T_ac are each exclusive to e (share edge with e, ≤1 vertex with f,g,h)
2. Consider the 6 triangles: {T_ab, T_bc, T_ac, f, g, h}
3. We need to show they form a valid packing:
   - f, g, h are pairwise edge-disjoint (from M being a packing)
   - T_ab, T_bc, T_ac each share ≤1 vertex with f, g, h (exclusivity)
   - T_ab, T_bc, T_ac: could share edges with each other!

The issue is that T_ab and T_bc could share edge {b, x} where x is
their common third vertex. So we can't directly claim 6-packing.

ALTERNATIVE: Use that T_ab, T_bc, T_ac are triangles in G.cliqueFinset,
and their union with {f, g, h} gives a superpacking only if they're
pairwise edge-disjoint.

KEY INSIGHT: T_ab, T_bc, T_ac cannot ALL have the same third vertex x.
If they did:
- T_ab = {a, b, x}
- T_bc = {b, c, x}
- T_ac = {a, c, x}
Then {a, b, c, x} forms a K4 subgraph.
In K4, the triangle {a,b,c} = e has ν = 1 (can't add more edge-disjoint triangles).
But M.card = 4, so there must be other triangles f, g, h edge-disjoint from e.
These f, g, h cannot use only vertices from {a,b,c,x}, since all edges
involving those 4 vertices are already used by e and the 3 externals.
So f, g, h must involve vertices outside {a,b,c,x}, call them V'.
But then the externals T_ab, T_bc, T_ac together with e use all edges
of {a,b,c,x}, while f, g, h use only edges involving V'.
This means {e, T_ab, T_bc, T_ac, f, g, h} minus e gives a 6-packing.
Contradiction since ν = 4.
-/

-- Let's state the 6-packing lemma more carefully
lemma six_packing_contradiction (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (hM4 : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (T_ab T_bc T_ac : Finset V12)
    (hTab : T_ab ∈ S_e_type12 G M e a b c)
    (hTbc : T_bc ∈ S_e_type12 G M e b c a)
    (hTac : T_ac ∈ S_e_type12 G M e a c b) :
    False := by
  -- The 3 externals plus the other 3 elements of M form a 6-packing
  -- This contradicts ν = 4
  -- Get the other 3 elements of M
  have hMne : e ∈ M := he
  have hM_other : (M.erase e).card = 3 := by
    rw [card_erase_of_mem he, hM4]
    norm_num
  -- The 6-packing is {T_ab, T_bc, T_ac} ∪ (M.erase e)
  -- We need to verify it's a valid packing
  sorry

-- Main theorem: at most 2 edge-types have externals
theorem not_all_three_types12 (G : SimpleGraph V12) [DecidableRel G.Adj]
    (M : Finset (Finset V12)) (hM : isTrianglePacking12 G M)
    (hM4 : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking12 G S → S.card ≤ 4)
    (e : Finset V12) (he : e ∈ M)
    (a b c : V12) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬((S_e_type12 G M e a b c).Nonempty ∧
      (S_e_type12 G M e b c a).Nonempty ∧
      (S_e_type12 G M e a c b).Nonempty) := by
  intro ⟨⟨T_ab, hTab⟩, ⟨T_bc, hTbc⟩, ⟨T_ac, hTac⟩⟩
  exact six_packing_contradiction G M hM hM4 hNu4 e he a b c ha hb hc hab hbc hac T_ab T_bc T_ac hTab hTbc hTac
