/-
  slot185_universal_apex.lean

  ATTACK: Prove all external fan apexes coincide in cycle_4

  STRATEGY: If x_A ≠ x_B for adjacent M-elements, construct 5-packing contradiction

  KEY INSIGHT:
  - External T_A of A at shared vertex v contains apex x_A
  - External T_B of B at shared vertex v contains apex x_B
  - If x_A ≠ x_B, then T_A and T_B are edge-disjoint
  - Combined with opposite M-elements, get 5-packing → contradiction
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TuzaNu4

/-- A triangle is a 3-element set forming a clique -/
def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t.card = 3 ∧ G.IsClique t

/-- Two triangles share an edge -/
def sharesEdge (t₁ t₂ : Finset V) : Prop :=
  ∃ u v : V, u ≠ v ∧ u ∈ t₁ ∧ v ∈ t₁ ∧ u ∈ t₂ ∧ v ∈ t₂

/-- A packing is edge-disjoint -/
def isPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  (∀ t ∈ M, isTriangle G t) ∧
  (∀ t₁ ∈ M, ∀ t₂ ∈ M, t₁ ≠ t₂ → ¬sharesEdge t₁ t₂)

/-- External triangle: shares edge with exactly one M-element -/
def isExternal (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T : Finset V) (A : Finset V) : Prop :=
  isTriangle G T ∧
  T ∉ M ∧
  A ∈ M ∧
  sharesEdge T A ∧
  (∀ B ∈ M, B ≠ A → ¬sharesEdge T B)

/-- The fan apex: vertex shared by all externals of A -/
def fanApex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (x : V) : Prop :=
  x ∉ A ∧ (∀ T : Finset V, isExternal G M T A → x ∈ T)

/-- Cycle_4 structure: 4 M-elements sharing vertices in cycle pattern -/
def isCycle4 (M : Finset (Finset V)) (vAB vBC vCD vDA a b c d : V) : Prop :=
  let A := ({vDA, vAB, a} : Finset V)
  let B := ({vAB, vBC, b} : Finset V)
  let C := ({vBC, vCD, c} : Finset V)
  let D := ({vCD, vDA, d} : Finset V)
  M = {A, B, C, D} ∧
  -- All 8 vertices are distinct
  [vAB, vBC, vCD, vDA, a, b, c, d].Nodup ∧
  -- No shared edges between M-elements (they share vertices, not edges)
  ¬sharesEdge A B ∧ ¬sharesEdge B C ∧ ¬sharesEdge C D ∧ ¬sharesEdge D A ∧
  ¬sharesEdge A C ∧ ¬sharesEdge B D

/-- KEY THEOREM: If fan apexes differ, we can construct a 5-packing -/
theorem different_apexes_give_five_packing
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM : isPacking G M) (hM4 : M.card = 4)
    (vAB vBC vCD vDA a b c d : V)
    (hCycle : isCycle4 M vAB vBC vCD vDA a b c d)
    (T_A T_B : Finset V)
    (x_A x_B : V)
    -- T_A is external of A with apex x_A
    (hTA : isExternal G M T_A ({vDA, vAB, a} : Finset V))
    (hxA : x_A ∈ T_A ∧ x_A ∉ ({vDA, vAB, a} : Finset V))
    -- T_B is external of B with apex x_B
    (hTB : isExternal G M T_B ({vAB, vBC, b} : Finset V))
    (hxB : x_B ∈ T_B ∧ x_B ∉ ({vAB, vBC, b} : Finset V))
    -- Apexes are different
    (h_diff : x_A ≠ x_B)
    -- Additional constraint: apexes not in opposite M-elements
    (hxA_not_C : x_A ∉ ({vBC, vCD, c} : Finset V))
    (hxA_not_D : x_A ∉ ({vCD, vDA, d} : Finset V))
    (hxB_not_C : x_B ∉ ({vBC, vCD, c} : Finset V))
    (hxB_not_D : x_B ∉ ({vCD, vDA, d} : Finset V)) :
    -- Then T_A, T_B, C, D form a 4-packing that extends M
    -- This leads to 5-packing if we can add A or B
    ¬sharesEdge T_A T_B := by
  -- If x_A ≠ x_B and both externals contain shared vertex vAB,
  -- the only way they share an edge is if they share {vAB, x_A} or {vAB, x_B}
  -- But x_A ≠ x_B, so they cannot share such an edge
  intro h_share
  obtain ⟨u, v, huv, hu_TA, hv_TA, hu_TB, hv_TB⟩ := h_share
  -- T_A uses edge from A, so T_A ⊆ A ∪ {x_A} essentially
  -- T_B uses edge from B, so T_B ⊆ B ∪ {x_B} essentially
  -- The shared edge {u,v} must have both vertices in T_A ∩ T_B
  -- Since x_A ≠ x_B, the only shared vertices are from A ∩ B = {vAB}
  -- So T_A ∩ T_B = {vAB} (single vertex, not an edge)
  sorry -- Aristotle: derive contradiction from x_A ≠ x_B

/-- MAIN THEOREM: In cycle_4, all fan apexes coincide -/
theorem universal_apex_in_cycle4
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM : isPacking G M) (hM4 : M.card = 4)
    (hMaximal : ∀ T : Finset V, isTriangle G T → T ∉ M →
                ∃ A ∈ M, sharesEdge T A)
    (vAB vBC vCD vDA a b c d : V)
    (hCycle : isCycle4 M vAB vBC vCD vDA a b c d)
    (x_A x_B : V)
    -- x_A is apex for externals of A
    (hx_A : fanApex G M ({vDA, vAB, a} : Finset V) x_A)
    -- x_B is apex for externals of B
    (hx_B : fanApex G M ({vAB, vBC, b} : Finset V) x_B)
    -- Externals exist
    (T_A : Finset V) (hTA : isExternal G M T_A ({vDA, vAB, a} : Finset V))
    (T_B : Finset V) (hTB : isExternal G M T_B ({vAB, vBC, b} : Finset V)) :
    x_A = x_B := by
  -- By slot182, T_A and T_B might share an edge (if they're externals of same element)
  -- But they're externals of DIFFERENT elements
  -- Key: if x_A ≠ x_B, then {T_A, T_B, C, D} is edge-disjoint
  -- This doesn't immediately give 5-packing, but...
  -- We can show: if x_A ≠ x_B, then we can construct 5 edge-disjoint triangles
  -- by carefully choosing externals and M-elements
  by_contra h_neq
  -- Use different_apexes_give_five_packing to derive contradiction
  sorry -- Aristotle: complete the 5-packing argument

/-- COVERING THEOREM: Universal apex gives τ ≤ 8 -/
theorem tau_le_8_from_universal_apex
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM : isPacking G M) (hM4 : M.card = 4)
    (hMaximal : ∀ T : Finset V, isTriangle G T → T ∉ M →
                ∃ A ∈ M, sharesEdge T A)
    (vAB vBC vCD vDA a b c d : V)
    (hCycle : isCycle4 M vAB vBC vCD vDA a b c d)
    (x : V)
    -- x is universal apex (in all externals)
    (h_universal : ∀ T : Finset V, ∀ A ∈ M, isExternal G M T A → x ∈ T) :
    -- Then 8 edges suffice: 4 M-edges + 4 apex-edges
    ∃ cover : Finset (Sym2 V), cover.card ≤ 8 ∧
      (∀ T : Finset V, isTriangle G T → ∃ e ∈ cover, e ∈ T.sym2) := by
  -- Cover construction:
  -- M-edges: {vDA, a}, {vAB, b}, {vBC, c}, {vCD, d} (one per M-element)
  -- Apex-edges: {vAB, x}, {vBC, x}, {vCD, x}, {vDA, x}
  --
  -- Every M-element is hit by its M-edge
  -- Every external contains x and at least one shared vertex
  -- So every external is hit by some apex-edge
  let A := ({vDA, vAB, a} : Finset V)
  let B := ({vAB, vBC, b} : Finset V)
  let C := ({vBC, vCD, c} : Finset V)
  let D := ({vCD, vDA, d} : Finset V)
  -- Define cover
  let m_edges : Finset (Sym2 V) := {s(vDA, a), s(vAB, b), s(vBC, c), s(vCD, d)}
  let x_edges : Finset (Sym2 V) := {s(vAB, x), s(vBC, x), s(vCD, x), s(vDA, x)}
  use m_edges ∪ x_edges
  constructor
  · -- card ≤ 8
    sorry -- Aristotle: cardinality bound
  · -- covers all triangles
    intro T hT
    by_cases hTM : T ∈ M
    · -- T is an M-element, covered by m_edges
      sorry -- Aristotle: M-element case
    · -- T is not in M, so it's external to some A ∈ M (by maximality)
      obtain ⟨A_elem, hA_elem, h_shares⟩ := hMaximal T hT hTM
      -- T contains x (by universal apex)
      have hx_in_T : x ∈ T := h_universal T A_elem hA_elem ⟨hT, hTM, hA_elem, h_shares, ?_⟩
      · -- T contains x and some shared vertex, so apex-edge covers
        sorry -- Aristotle: external case
      · -- Show T is external of A_elem
        sorry -- Aristotle: external verification

end TuzaNu4
