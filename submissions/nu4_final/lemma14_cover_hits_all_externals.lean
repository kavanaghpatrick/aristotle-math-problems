/-
  lemma14_cover_hits_all_externals.lean

  LEMMA 14: The 8-edge cover hits all external triangles

  STATEMENT: For every external triangle T, some edge in the cover is in T

  DIFFICULTY: 3/5 (combines lemmas 6-10)

  PROOF SKETCH:
  - T is external of some A ∈ M (by Lemma 11)
  - T is either cycle-type or private-type (by Lemma 1)
  - If cycle-type: covered by cycle edge (Lemma 7 - tautological)
  - If private-type: covered by apex-private edge (Lemma 8)
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

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isPacking G M ∧
  (∀ T : Finset V, isTriangle G T → T ∉ M → ∃ A ∈ M, sharesEdge T A)

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

def isCycleExternal (cfg : Cycle4Config V) (T : Finset V) (A : Finset V) : Prop :=
  (A = cfg.A ∧ usesEdge T cfg.vDA cfg.vAB) ∨
  (A = cfg.B ∧ usesEdge T cfg.vAB cfg.vBC) ∨
  (A = cfg.C ∧ usesEdge T cfg.vBC cfg.vCD) ∨
  (A = cfg.D ∧ usesEdge T cfg.vCD cfg.vDA)

def isPrivateExternal (cfg : Cycle4Config V) (T : Finset V) (A : Finset V) : Prop :=
  (A = cfg.A ∧ ((usesEdge T cfg.vDA cfg.a) ∨ (usesEdge T cfg.vAB cfg.a))) ∨
  (A = cfg.B ∧ ((usesEdge T cfg.vAB cfg.b) ∨ (usesEdge T cfg.vBC cfg.b))) ∨
  (A = cfg.C ∧ ((usesEdge T cfg.vBC cfg.c) ∨ (usesEdge T cfg.vCD cfg.c))) ∨
  (A = cfg.D ∧ ((usesEdge T cfg.vCD cfg.d) ∨ (usesEdge T cfg.vDA cfg.d)))

def Cycle4Config.cycleEdges (cfg : Cycle4Config V) : Finset (Sym2 V) :=
  {s(cfg.vDA, cfg.vAB), s(cfg.vAB, cfg.vBC), s(cfg.vBC, cfg.vCD), s(cfg.vCD, cfg.vDA)}

def edgeCovers (e : Sym2 V) (T : Finset V) : Prop :=
  ∃ u v : V, u ∈ T ∧ v ∈ T ∧ e = s(u, v)

/-- The 8-edge cover set -/
def eightEdgeCover (cfg : Cycle4Config V) (x_A x_B x_C x_D : V) : Finset (Sym2 V) :=
  cfg.cycleEdges ∪ {s(cfg.a, x_A), s(cfg.b, x_B), s(cfg.c, x_C), s(cfg.d, x_D)}

/-- LEMMA 14: 8-edge cover hits all externals -/
theorem cover_hits_all_externals
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (x_A x_B x_C x_D : V)
    (hx_A : isFanApex G M cfg.A x_A)
    (hx_B : isFanApex G M cfg.B x_B)
    (hx_C : isFanApex G M cfg.C x_C)
    (hx_D : isFanApex G M cfg.D x_D)
    (T : Finset V) (A : Finset V) (hA : A ∈ M)
    (hT_ext : isExternal G M T A) :
    ∃ e ∈ eightEdgeCover cfg x_A x_B x_C x_D, edgeCovers e T := by
  -- T is external of A. Determine which M-element A is.
  simp only [hM_eq, Finset.mem_insert, Finset.mem_singleton] at hA
  rcases hA with rfl | rfl | rfl | rfl
  all_goals {
    -- T uses some edge of A (cycle or private)
    -- Case split on which edge type
    -- Cycle edge case: cycle edge covers T
    -- Private edge case: apex-private edge covers T (T contains private vertex and apex)
    sorry -- Aristotle: case analysis on external type
  }

end TuzaNu4
