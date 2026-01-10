/-
  lemma09_private_externals_at_most_two.lean

  LEMMA 9: At most 2 private-type externals per M-element

  STATEMENT: |{T : T is private external of A}| ≤ 2

  DIFFICULTY: 4/5 (5-packing argument)

  PROOF SKETCH:
  - A = {vDA, vAB, a} has 2 private edges: {vDA, a} and {vAB, a}
  - Each private external uses exactly one private edge
  - For each private edge, there's at most 1 external using it
    (because external T = {v, a, x} where x is the fan apex)
  - So at most 2 private externals total
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

def usesEdge (T : Finset V) (u v : V) : Prop := u ∈ T ∧ v ∈ T

def isPrivateExternal (cfg : Cycle4Config V) (T : Finset V) : Prop :=
  (usesEdge T cfg.vDA cfg.a) ∨ (usesEdge T cfg.vAB cfg.a)

def privateExternalsOfA (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4Config V) : Finset (Finset V) :=
  (externalsOf G M cfg.A).filter fun T => isPrivateExternal cfg T

/-- At most one external using edge {vDA, a} -/
theorem at_most_one_external_using_vDA_a
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (x_A : V) (hx_apex : isFanApex G M cfg.A x_A) :
    ((externalsOf G M cfg.A).filter fun T => usesEdge T cfg.vDA cfg.a).card ≤ 1 := by
  -- Any external using {vDA, a} has form T = {vDA, a, x_A}
  -- where x_A is the unique fan apex
  -- So there's at most one such external
  rw [Finset.card_le_one]
  intro T₁ hT₁ T₂ hT₂
  simp only [Finset.mem_filter] at hT₁ hT₂
  obtain ⟨hT₁_ext, hvDA_T₁, ha_T₁⟩ := hT₁
  obtain ⟨hT₂_ext, hvDA_T₂, ha_T₂⟩ := hT₂
  -- Both contain vDA, a, and x_A (fan apex)
  have hx_T₁ : x_A ∈ T₁ := hx_apex.2 T₁ hT₁_ext
  have hx_T₂ : x_A ∈ T₂ := hx_apex.2 T₂ hT₂_ext
  -- T₁ = {vDA, a, x_A} = T₂
  -- Need to show T₁ and T₂ have same 3 vertices
  sorry -- Aristotle: both have form {vDA, a, x_A}

/-- At most one external using edge {vAB, a} -/
theorem at_most_one_external_using_vAB_a
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (x_A : V) (hx_apex : isFanApex G M cfg.A x_A) :
    ((externalsOf G M cfg.A).filter fun T => usesEdge T cfg.vAB cfg.a).card ≤ 1 := by
  sorry -- Aristotle: similar to above

/-- LEMMA 9: At most 2 private externals -/
theorem private_externals_at_most_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (x_A : V) (hx_apex : isFanApex G M cfg.A x_A) :
    (privateExternalsOfA G M cfg).card ≤ 2 := by
  -- Private externals split into those using {vDA, a} and those using {vAB, a}
  -- Each category has at most 1 element
  -- Total ≤ 2
  have h1 := at_most_one_external_using_vDA_a G M hM hM4 cfg hM_eq x_A hx_apex
  have h2 := at_most_one_external_using_vAB_a G M hM hM4 cfg hM_eq x_A hx_apex
  -- The privateExternalsOfA is union of these two sets
  sorry -- Aristotle: union bound gives card ≤ 2

end TuzaNu4
