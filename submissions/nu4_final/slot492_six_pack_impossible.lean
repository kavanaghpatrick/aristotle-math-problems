/-
  slot492_six_pack_impossible.lean

  FOCUSED: Prove no 6-packing exists on Fin 9 via native_decide.

  This is the KEY axiom needed for the τ ≤ 8 proof.
  If we can verify no 6 edge-disjoint triangles exist on 9 vertices,
  then the "all 3 edges have externals" case is impossible.

  TIER: 1 (pure finite verification)
-/

import Mathlib

set_option maxHeartbeats 2000000

open Finset

abbrev V9 := Fin 9

/-- Ordered edge -/
def mkE (x y : V9) : V9 × V9 := if x ≤ y then (x, y) else (y, x)

/-- Triangle with distinctness proofs -/
structure Tri where
  a : V9
  b : V9
  c : V9
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  deriving DecidableEq

/-- Edges of a triangle -/
def Tri.edges (t : Tri) : Finset (V9 × V9) :=
  {mkE t.a t.b, mkE t.a t.c, mkE t.b t.c}

/-- Two triangles are edge-disjoint -/
def edgeDisj (t1 t2 : Tri) : Prop := Disjoint t1.edges t2.edges

instance (t1 t2 : Tri) : Decidable (edgeDisj t1 t2) :=
  inferInstanceAs (Decidable (Disjoint _ _))

/-- 6 triangles are pairwise edge-disjoint -/
def pack6 (t0 t1 t2 t3 t4 t5 : Tri) : Prop :=
  edgeDisj t0 t1 ∧ edgeDisj t0 t2 ∧ edgeDisj t0 t3 ∧ edgeDisj t0 t4 ∧ edgeDisj t0 t5 ∧
  edgeDisj t1 t2 ∧ edgeDisj t1 t3 ∧ edgeDisj t1 t4 ∧ edgeDisj t1 t5 ∧
  edgeDisj t2 t3 ∧ edgeDisj t2 t4 ∧ edgeDisj t2 t5 ∧
  edgeDisj t3 t4 ∧ edgeDisj t3 t5 ∧
  edgeDisj t4 t5

instance (t0 t1 t2 t3 t4 t5 : Tri) : Decidable (pack6 t0 t1 t2 t3 t4 t5) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

-- ══════════════════════════════════════════════════════════════════════════════
-- EDGE COUNTING ARGUMENT
-- ══════════════════════════════════════════════════════════════════════════════

/--
KEY LEMMA: 6 edge-disjoint triangles use 18 distinct edges.
But Fin 9 has only C(9,2) = 36 edges.
This alone doesn't give a contradiction, but we can verify computationally.
-/

/-- All possible edges on V9 -/
def allEdges : Finset (V9 × V9) :=
  (univ : Finset V9).product (univ : Finset V9) |>.filter (fun (x, y) => x < y)

lemma allEdges_card : allEdges.card = 36 := by native_decide

/-- All edges used by 6 triangles -/
def usedEdges (t0 t1 t2 t3 t4 t5 : Tri) : Finset (V9 × V9) :=
  t0.edges ∪ t1.edges ∪ t2.edges ∪ t3.edges ∪ t4.edges ∪ t5.edges

/--
If 6 triangles are edge-disjoint, they use exactly 18 edges.
-/
lemma pack6_uses_18_edges (t0 t1 t2 t3 t4 t5 : Tri) (h : pack6 t0 t1 t2 t3 t4 t5) :
    (usedEdges t0 t1 t2 t3 t4 t5).card = 18 := by
  unfold pack6 edgeDisj at h
  obtain ⟨h01, h02, h03, h04, h05, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩ := h
  unfold usedEdges
  -- Each triangle has exactly 3 edges
  have ht0 : t0.edges.card = 3 := by
    unfold Tri.edges
    simp only [card_insert_of_not_mem, card_singleton]
    · decide
    · simp [mkE]; intro h; cases h <;> omega
    · simp [mkE]; intro h; cases h <;> omega
  have ht1 : t1.edges.card = 3 := by
    unfold Tri.edges
    simp only [card_insert_of_not_mem, card_singleton]
    · decide
    · simp [mkE]; intro h; cases h <;> omega
    · simp [mkE]; intro h; cases h <;> omega
  -- When disjoint, card of union = sum of cards
  have hc01 : (t0.edges ∪ t1.edges).card = t0.edges.card + t1.edges.card :=
    card_union_of_disjoint h01
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN: No 6-packing on Fin 9
-- ══════════════════════════════════════════════════════════════════════════════

/--
MAIN THEOREM: No 6-packing exists on Fin 9.

Proof idea: Verify by exhaustive search that no valid 6-packing exists.
This is computationally intensive but decidable.
-/
theorem no_six_pack_fin9 : ∀ t0 t1 t2 t3 t4 t5 : Tri, ¬pack6 t0 t1 t2 t3 t4 t5 := by
  intro t0 t1 t2 t3 t4 t5 h
  -- Edge counting: 6 disjoint triangles need 18 edges
  -- Fin 9 has 36 edges, so this is not obviously impossible
  -- However, vertex constraints make it impossible
  -- Each triangle uses 3 vertices
  -- 6 disjoint triangles could use up to 18 vertices
  -- But we only have 9 vertices
  -- By pigeonhole, vertices must be shared
  -- But edge-disjointness constrains how vertices can be shared
  sorry

end
