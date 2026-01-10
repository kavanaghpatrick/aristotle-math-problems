/-
  lemma10_cycle_externals_at_most_one.lean

  LEMMA 10: Each M-element has at most one "cycle external"

  A "cycle external" of A is an external triangle that uses the cycle edge of A
  (the shared-to-shared edge like {vDA, vAB} for A).

  STATEMENT: |{T : T is external of A using edge {vDA, vAB}}| ≤ 1

  DIFFICULTY: 2/5 (edge uniqueness)

  PROOF SKETCH:
  - The cycle edge of A is {vDA, vAB}
  - An external T using this edge has form T = {vDA, vAB, x} for some x ∉ A
  - Since x ∉ A = {vDA, vAB, a}, we have x ≠ vDA, x ≠ vAB, x ≠ a
  - If T₁ = {vDA, vAB, x₁} and T₂ = {vDA, vAB, x₂} are two such externals
  - And T₁ ≠ T₂, then x₁ ≠ x₂
  - But both must contain the fan apex x (by slot182/fan structure)
  - So T₁ = {vDA, vAB, x} and T₂ = {vDA, vAB, x} implies T₁ = T₂
  - Therefore at most one such external exists
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TuzaNu4

/-- A triangle is a 3-element clique -/
def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t.card = 3 ∧ G.IsClique t

/-- Two triangles share an edge -/
def sharesEdge (t₁ t₂ : Finset V) : Prop :=
  ∃ u v : V, u ≠ v ∧ u ∈ t₁ ∧ v ∈ t₁ ∧ u ∈ t₂ ∧ v ∈ t₂

/-- T is external of A in packing M -/
def isExternal (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T A : Finset V) : Prop :=
  isTriangle G T ∧
  T ∉ M ∧
  A ∈ M ∧
  sharesEdge T A ∧
  (∀ B ∈ M, B ≠ A → ¬sharesEdge T B)

/-- T uses a specific edge of A -/
def usesEdge (T : Finset V) (u v : V) : Prop :=
  u ∈ T ∧ v ∈ T

/-- Cycle_4 configuration -/
structure Cycle4Config (V : Type*) where
  vAB vBC vCD vDA : V
  a b c d : V
  all_distinct : [vAB, vBC, vCD, vDA, a, b, c, d].Nodup

def Cycle4Config.A (cfg : Cycle4Config V) : Finset V := {cfg.vDA, cfg.vAB, cfg.a}
def Cycle4Config.B (cfg : Cycle4Config V) : Finset V := {cfg.vAB, cfg.vBC, cfg.b}
def Cycle4Config.C (cfg : Cycle4Config V) : Finset V := {cfg.vBC, cfg.vCD, cfg.c}
def Cycle4Config.D (cfg : Cycle4Config V) : Finset V := {cfg.vCD, cfg.vDA, cfg.d}

/-- The cycle edge of A is {vDA, vAB} -/
def Cycle4Config.cycleEdgeOfA (cfg : Cycle4Config V) : Sym2 V :=
  s(cfg.vDA, cfg.vAB)

/-- Cycle externals of A: externals using the cycle edge {vDA, vAB} -/
def cycleExternalsOfA (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4Config V) : Finset (Finset V) :=
  (Finset.univ.filter (isTriangle G)).filter fun T =>
    isExternal G M T cfg.A ∧ usesEdge T cfg.vDA cfg.vAB

/-- LEMMA 10: At most one cycle external per M-element

The cycle edge of A is {vDA, vAB}. Any external T using this edge has form
T = {vDA, vAB, x} for some x ∉ A. Since the third vertex x is uniquely
determined by T being a triangle containing {vDA, vAB}, there's at most
one such external (the one with x = fan apex). -/
theorem cycle_externals_of_A_at_most_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4Config V)
    (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D}) :
    (cycleExternalsOfA G M cfg).card ≤ 1 := by
  -- Key: any external T using edge {vDA, vAB} has form T = {vDA, vAB, x}
  -- Since T has exactly 3 vertices and contains vDA, vAB, the third is unique.
  -- Two such externals T₁ = {vDA, vAB, x₁}, T₂ = {vDA, vAB, x₂}
  -- If T₁ ≠ T₂ then x₁ ≠ x₂, but both T₁, T₂ contain fan apex x
  -- This forces T₁ = T₂ (contradiction)
  by_cases h_empty : (cycleExternalsOfA G M cfg) = ∅
  · simp [h_empty]
  · -- Non-empty case: show all elements equal (hence card ≤ 1)
    rw [Finset.card_le_one]
    intro T₁ hT₁ T₂ hT₂
    -- Both T₁ and T₂ use edge {vDA, vAB}
    simp only [cycleExternalsOfA, Finset.mem_filter] at hT₁ hT₂
    obtain ⟨⟨hT₁_tri, _⟩, hT₁_ext, hT₁_uses⟩ := hT₁
    obtain ⟨⟨hT₂_tri, _⟩, hT₂_ext, hT₂_uses⟩ := hT₂
    -- T₁ contains vDA, vAB and has card 3, so T₁ = {vDA, vAB, x₁}
    -- T₂ contains vDA, vAB and has card 3, so T₂ = {vDA, vAB, x₂}
    -- Both T₁, T₂ are externals of A, so by fan structure they share apex x
    -- Hence x₁ = x₂ = x, so T₁ = T₂
    sorry -- Aristotle: complete using fan apex uniqueness

end TuzaNu4
