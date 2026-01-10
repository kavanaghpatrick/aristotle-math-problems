/-
  lemma05_fan_apex_not_in_other_M.lean

  LEMMA 5: Fan apex is not in other M-elements

  STATEMENT: If x is the fan apex of A, then x ∉ B, x ∉ C, x ∉ D

  DIFFICULTY: 3/5 (5-packing contradiction)

  PROOF SKETCH:
  - Suppose x ∈ B for some B ≠ A in M
  - Take any external T of A containing x
  - T contains x ∈ B and shares edge with A
  - If T also shares edge with B, T is not external of A (contradiction)
  - So we need T to NOT share edge with B despite containing x ∈ B
  - This constrains T's structure, leading to 5-packing contradiction
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TuzaNu4

def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t.card = 3 ∧ G.IsClique t

def triangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  Finset.univ.filter (isTriangle G)

def sharesEdge (t₁ t₂ : Finset V) : Prop :=
  ∃ u v : V, u ≠ v ∧ u ∈ t₁ ∧ v ∈ t₁ ∧ u ∈ t₂ ∧ v ∈ t₂

def isPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  (∀ t ∈ M, isTriangle G t) ∧
  (∀ t₁ ∈ M, ∀ t₂ ∈ M, t₁ ≠ t₂ → ¬sharesEdge t₁ t₂)

def isExternal (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T A : Finset V) : Prop :=
  isTriangle G T ∧ T ∉ M ∧ A ∈ M ∧ sharesEdge T A ∧
  (∀ B ∈ M, B ≠ A → ¬sharesEdge T B)

def externalsOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (triangles G).filter fun T => isExternal G M T A

def isFanApex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (x : V) : Prop :=
  x ∉ A ∧ ∀ T ∈ externalsOf G M A, x ∈ T

structure Cycle4Config (V : Type*) where
  vAB vBC vCD vDA : V
  a b c d : V
  all_distinct : [vAB, vBC, vCD, vDA, a, b, c, d].Nodup

def Cycle4Config.A (cfg : Cycle4Config V) : Finset V := {cfg.vDA, cfg.vAB, cfg.a}
def Cycle4Config.B (cfg : Cycle4Config V) : Finset V := {cfg.vAB, cfg.vBC, cfg.b}
def Cycle4Config.C (cfg : Cycle4Config V) : Finset V := {cfg.vBC, cfg.vCD, cfg.c}
def Cycle4Config.D (cfg : Cycle4Config V) : Finset V := {cfg.vCD, cfg.vDA, cfg.d}

/-- LEMMA 5: Fan apex x_A is not in B, C, or D -/
theorem fan_apex_not_in_B
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (x : V) (hx_apex : isFanApex G M cfg.A x) :
    x ∉ cfg.B := by
  -- Suppose x ∈ B = {vAB, vBC, b}
  -- x is fan apex of A, so x ∉ A = {vDA, vAB, a}
  -- Thus x ≠ vDA, x ≠ vAB, x ≠ a
  -- If x ∈ B, then x = vAB, vBC, or b
  -- x ≠ vAB (from x ∉ A), so x = vBC or x = b
  --
  -- Case x = vBC:
  -- Any external T of A contains x = vBC
  -- T shares edge with A but not with B
  -- T contains vBC ∈ B, so to not share edge with B,
  -- T must not contain any other vertex of B = {vAB, vBC, b}
  -- So T ∩ B = {vBC}, only 1 vertex, no shared edge ✓
  -- But then T shares edge with A: T ∩ A ≥ 2
  -- T contains vBC ∉ A, so T ∩ A must have 2 vertices from A
  -- If T = {v₁, v₂, vBC} with v₁, v₂ ∈ A and distinct
  -- T is external of A... this could work. Need 5-packing argument.
  --
  -- Key: If x ∈ B and x is apex of A, we can construct 5-packing
  intro hx_in_B
  -- x ∉ A (by fan apex definition)
  have hx_not_A := hx_apex.1
  -- x ∈ B = {vAB, vBC, b}
  simp only [Cycle4Config.B, Finset.mem_insert, Finset.mem_singleton] at hx_in_B
  rcases hx_in_B with rfl | rfl | rfl
  · -- x = vAB: but vAB ∈ A, contradiction with x ∉ A
    have : cfg.vAB ∈ cfg.A := by simp [Cycle4Config.A]
    exact hx_not_A this
  · -- x = vBC: need 5-packing argument
    sorry -- Aristotle: 5-packing contradiction when apex = vBC
  · -- x = b: need 5-packing argument
    sorry -- Aristotle: 5-packing contradiction when apex = b

theorem fan_apex_not_in_C
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (x : V) (hx_apex : isFanApex G M cfg.A x) :
    x ∉ cfg.C := by
  sorry -- Aristotle: similar 5-packing argument

theorem fan_apex_not_in_D
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (x : V) (hx_apex : isFanApex G M cfg.A x) :
    x ∉ cfg.D := by
  sorry -- Aristotle: similar 5-packing argument

/-- Combined: fan apex not in any other M-element -/
theorem fan_apex_not_in_other_M
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (x : V) (hx_apex : isFanApex G M cfg.A x) :
    x ∉ cfg.B ∧ x ∉ cfg.C ∧ x ∉ cfg.D :=
  ⟨fan_apex_not_in_B G M hM hM4 cfg hM_eq x hx_apex,
   fan_apex_not_in_C G M hM hM4 cfg hM_eq x hx_apex,
   fan_apex_not_in_D G M hM hM4 cfg hM_eq x hx_apex⟩

end TuzaNu4
