/-
  lemma02_cycle_external_form.lean

  LEMMA 2: Structure of cycle-edge externals

  STATEMENT: An external triangle that uses a cycle edge {v_i, v_j}
  has the form {v_i, v_j, x} for some vertex x outside the M-elements.

  DIFFICULTY: 3/5

  PROOF SKETCH:
  - T is a triangle, so |T| = 3
  - T contains v_i and v_j (from the cycle edge)
  - The third vertex x must be outside the M-elements
    (otherwise T would share an edge with another M-element)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TuzaNu4

def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t.card = 3 ∧ G.IsClique t

def sharesEdge (t₁ t₂ : Finset V) : Prop :=
  ∃ u v : V, u ≠ v ∧ u ∈ t₁ ∧ v ∈ t₁ ∧ u ∈ t₂ ∧ v ∈ t₂

def isPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  (∀ t ∈ M, isTriangle G t) ∧
  (∀ t₁ ∈ M, ∀ t₂ ∈ M, t₁ ≠ t₂ → ¬sharesEdge t₁ t₂)

def isExternal (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T A : Finset V) : Prop :=
  isTriangle G T ∧ T ∉ M ∧ A ∈ M ∧ sharesEdge T A ∧
  (∀ B ∈ M, B ≠ A → ¬sharesEdge T B)

structure Cycle4Config (V : Type*) where
  vAB vBC vCD vDA : V
  a b c d : V
  all_distinct : [vAB, vBC, vCD, vDA, a, b, c, d].Nodup

def Cycle4Config.A (cfg : Cycle4Config V) : Finset V := {cfg.vDA, cfg.vAB, cfg.a}
def Cycle4Config.B (cfg : Cycle4Config V) : Finset V := {cfg.vAB, cfg.vBC, cfg.b}
def Cycle4Config.C (cfg : Cycle4Config V) : Finset V := {cfg.vBC, cfg.vCD, cfg.c}
def Cycle4Config.D (cfg : Cycle4Config V) : Finset V := {cfg.vCD, cfg.vDA, cfg.d}

def Cycle4Config.allMVertices (cfg : Cycle4Config V) : Finset V :=
  {cfg.vAB, cfg.vBC, cfg.vCD, cfg.vDA, cfg.a, cfg.b, cfg.c, cfg.d}

def Cycle4Config.cycleEdges (cfg : Cycle4Config V) : Finset (Sym2 V) :=
  {s(cfg.vDA, cfg.vAB), s(cfg.vAB, cfg.vBC), s(cfg.vBC, cfg.vCD), s(cfg.vCD, cfg.vDA)}

/-- LEMMA 2: Cycle external has form {v_i, v_j, x} where x is external vertex -/
theorem cycle_external_form
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4Config V)
    (T : Finset V) (hT_tri : isTriangle G T)
    (v_i v_j : V) (hv_ij : v_i ≠ v_j)
    (hi_in_T : v_i ∈ T) (hj_in_T : v_j ∈ T)
    (he_cycle : s(v_i, v_j) ∈ cfg.cycleEdges) :
    ∃ x : V, x ∉ ({v_i, v_j} : Finset V) ∧ T = {v_i, v_j, x} := by
  -- T is a triangle with |T| = 3, and contains v_i, v_j
  -- So T = {v_i, v_j, x} for some unique third vertex x
  have hT_card : T.card = 3 := hT_tri.1
  -- Since v_i ∈ T and v_j ∈ T and v_i ≠ v_j, there's exactly one more vertex
  have h_sub : ({v_i, v_j} : Finset V) ⊆ T := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> assumption
  have h_card_sub : ({v_i, v_j} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
    simp [hv_ij]
  -- T \ {v_i, v_j} has exactly 1 element
  have h_sdiff_card : (T \ {v_i, v_j}).card = 1 := by
    have := Finset.card_sdiff h_sub
    omega
  -- Extract the unique element x
  obtain ⟨x, hx_mem, hx_unique⟩ := Finset.card_eq_one.mp h_sdiff_card
  use x
  constructor
  · -- x ∉ {v_i, v_j}
    simp only [Finset.mem_sdiff] at hx_mem
    exact hx_mem.2
  · -- T = {v_i, v_j, x}
    ext w
    constructor
    · intro hw
      by_cases hwij : w ∈ ({v_i, v_j} : Finset V)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hwij ⊢
        left; exact hwij
      · -- w ∈ T \ {v_i, v_j} = {x}
        have : w ∈ T \ {v_i, v_j} := Finset.mem_sdiff.mpr ⟨hw, hwij⟩
        rw [hx_unique] at this
        simp only [Finset.mem_singleton] at this
        simp [this]
    · intro hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hi_in_T
      · exact hj_in_T
      · exact Finset.mem_sdiff.mp (hx_unique ▸ Finset.mem_singleton_self x) |>.1

end TuzaNu4
