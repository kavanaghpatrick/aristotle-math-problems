/-
  lemma03_private_external_contains_apex.lean

  LEMMA 3: Private externals contain the fan apex

  STATEMENT: If T is a private-type external of A (uses edge involving
  private vertex a), then T contains the fan apex x_A.

  DIFFICULTY: 3/5 (depends on Lemma 4: fan_apex_exists)

  PROOF SKETCH:
  - By fan_apex_exists, there exists x_A such that all externals of A contain x_A
  - T is an external of A (private type)
  - Therefore T contains x_A
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

def usesEdge (T : Finset V) (u v : V) : Prop := u ∈ T ∧ v ∈ T

def isPrivateExternal (cfg : Cycle4Config V) (T : Finset V) : Prop :=
  (usesEdge T cfg.vDA cfg.a) ∨ (usesEdge T cfg.vAB cfg.a)

/-- Axiom: fan_apex_exists (proven in lemma04) -/
axiom fan_apex_exists
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (h_has_externals : (externalsOf G M A).Nonempty) :
    ∃ x : V, isFanApex G M A x

/-- LEMMA 3: Private externals contain the fan apex -/
theorem private_external_contains_apex
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (T : Finset V)
    (hT_ext : isExternal G M T cfg.A)
    (hT_private : isPrivateExternal cfg T)
    (x : V) (hx_apex : isFanApex G M cfg.A x) :
    x ∈ T := by
  -- T is external of A, and x is the fan apex (in all externals of A)
  -- So x ∈ T by definition of fan apex
  have hT_in_externals : T ∈ externalsOf G M cfg.A := by
    simp only [externalsOf, Finset.mem_filter, triangles, Finset.mem_filter, Finset.mem_univ,
               true_and]
    exact ⟨hT_ext.1, hT_ext⟩
  exact hx_apex.2 T hT_in_externals

end TuzaNu4
