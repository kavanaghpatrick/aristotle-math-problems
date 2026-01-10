/-
  lemma08_apex_private_edge_covers.lean

  LEMMA 8: Apex-private edge covers private externals

  STATEMENT: The edge {a, x_A} covers all private-type externals of A

  DIFFICULTY: 2/5 (fan apex + set membership)

  PROOF SKETCH:
  - Let T be a private external of A using edge {vDA, a} or {vAB, a}
  - T contains a (the private vertex)
  - T contains x_A (by fan apex property - Lemma 3)
  - Therefore {a, x_A} ∈ T.sym2
  - So {a, x_A} covers T
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

def edgeCovers (e : Sym2 V) (T : Finset V) : Prop :=
  ∃ u v : V, u ∈ T ∧ v ∈ T ∧ e = s(u, v)

/-- LEMMA 8: Apex-private edge {a, x_A} covers all private externals of A -/
theorem apex_private_edge_covers_private_external
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (x_A : V) (hx_apex : isFanApex G M cfg.A x_A)
    (T : Finset V)
    (hT_ext : isExternal G M T cfg.A)
    (hT_private : isPrivateExternal cfg T) :
    edgeCovers s(cfg.a, x_A) T := by
  -- T is private external, so T uses edge {vDA, a} or {vAB, a}
  -- Either way, a ∈ T
  have ha_in_T : cfg.a ∈ T := by
    rcases hT_private with ⟨_, ha⟩ | ⟨_, ha⟩ <;> exact ha
  -- T is external of A, and x_A is fan apex, so x_A ∈ T
  have hT_in_externals : T ∈ externalsOf G M cfg.A := by
    simp only [externalsOf, Finset.mem_filter, triangles, Finset.mem_filter,
               Finset.mem_univ, true_and]
    exact ⟨hT_ext.1, hT_ext⟩
  have hx_in_T : x_A ∈ T := hx_apex.2 T hT_in_externals
  -- So edge {a, x_A} is in T
  unfold edgeCovers
  exact ⟨cfg.a, x_A, ha_in_T, hx_in_T, rfl⟩

end TuzaNu4
