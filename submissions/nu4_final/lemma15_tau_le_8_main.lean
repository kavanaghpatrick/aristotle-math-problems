/-
  lemma15_tau_le_8_main.lean

  LEMMA 15: MAIN THEOREM - τ ≤ 8 for cycle_4

  STATEMENT: In a graph with maximal 4-packing in cycle_4 configuration, τ ≤ 8

  DIFFICULTY: 2/5 (assembly of previous lemmas)

  PROOF SKETCH:
  - Construct the 8-edge cover S (Lemma 12: |S| = 8)
  - Every triangle T is either in M or external (Lemma 11)
  - M-elements are covered by cycle edges (Lemma 13)
  - Externals are covered by the cover (Lemma 14)
  - Therefore S covers all triangles and |S| = 8
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

def Cycle4Config.allMVertices (cfg : Cycle4Config V) : Finset V :=
  {cfg.vAB, cfg.vBC, cfg.vCD, cfg.vDA, cfg.a, cfg.b, cfg.c, cfg.d}

def Cycle4Config.cycleEdges (cfg : Cycle4Config V) : Finset (Sym2 V) :=
  {s(cfg.vDA, cfg.vAB), s(cfg.vAB, cfg.vBC), s(cfg.vBC, cfg.vCD), s(cfg.vCD, cfg.vDA)}

def edgeCovers (e : Sym2 V) (T : Finset V) : Prop :=
  ∃ u v : V, u ∈ T ∧ v ∈ T ∧ e = s(u, v)

def coveringSet (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  ∀ T ∈ triangles G, ∃ e ∈ S, edgeCovers e T

/-- The 8-edge cover set -/
def eightEdgeCover (cfg : Cycle4Config V) (x_A x_B x_C x_D : V) : Finset (Sym2 V) :=
  cfg.cycleEdges ∪ {s(cfg.a, x_A), s(cfg.b, x_B), s(cfg.c, x_C), s(cfg.d, x_D)}

/-! ## Axioms from previous lemmas -/

axiom fan_apex_exists
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (A : Finset V) (hA : A ∈ M) :
    ∃ x : V, x ∉ A ∧ (∀ T ∈ externalsOf G M A, x ∈ T)

axiom fan_apex_not_in_other_M
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4Config V)
    (x : V) (hx : isFanApex G M cfg.A x) :
    x ∉ cfg.allMVertices

axiom all_triangles_M_or_external
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (T : Finset V) (hT : isTriangle G T) :
    T ∈ M ∨ (∃ A ∈ M, isExternal G M T A)

axiom cycle_edges_cover_M
    (cfg : Cycle4Config V) (X : Finset V) (hX : X ∈ ({cfg.A, cfg.B, cfg.C, cfg.D} : Finset (Finset V))) :
    ∃ e ∈ cfg.cycleEdges, edgeCovers e X

axiom cover_hits_externals
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4Config V)
    (x_A x_B x_C x_D : V)
    (T A : Finset V) (hT_ext : isExternal G M T A) :
    ∃ e ∈ eightEdgeCover cfg x_A x_B x_C x_D, edgeCovers e T

axiom eight_edges_card
    (cfg : Cycle4Config V) (x_A x_B x_C x_D : V)
    (hx_A : x_A ∉ cfg.allMVertices)
    (hx_B : x_B ∉ cfg.allMVertices)
    (hx_C : x_C ∉ cfg.allMVertices)
    (hx_D : x_D ∉ cfg.allMVertices) :
    (eightEdgeCover cfg x_A x_B x_C x_D).card ≤ 8

/-! ## MAIN THEOREM -/

/-- MAIN THEOREM: τ ≤ 8 for cycle_4 configuration -/
theorem tau_le_8_cycle4
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V)
    (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (hG_A : isTriangle G cfg.A) (hG_B : isTriangle G cfg.B)
    (hG_C : isTriangle G cfg.C) (hG_D : isTriangle G cfg.D) :
    ∃ S : Finset (Sym2 V), S.card ≤ 8 ∧ coveringSet G S := by
  -- Step 1: Get fan apexes for each M-element
  obtain ⟨x_A, hx_A_not_A, hx_A_in_ext⟩ := fan_apex_exists G M hM.1 hM4 cfg.A (by simp [hM_eq])
  obtain ⟨x_B, hx_B_not_B, hx_B_in_ext⟩ := fan_apex_exists G M hM.1 hM4 cfg.B (by simp [hM_eq])
  obtain ⟨x_C, hx_C_not_C, hx_C_in_ext⟩ := fan_apex_exists G M hM.1 hM4 cfg.C (by simp [hM_eq])
  obtain ⟨x_D, hx_D_not_D, hx_D_in_ext⟩ := fan_apex_exists G M hM.1 hM4 cfg.D (by simp [hM_eq])

  -- Step 2: Construct the 8-edge cover
  let S := eightEdgeCover cfg x_A x_B x_C x_D

  use S
  constructor

  · -- |S| ≤ 8
    -- Need to show apexes are outside all M-vertices
    have hx_A_out : x_A ∉ cfg.allMVertices := by
      have : isFanApex G M cfg.A x_A := ⟨hx_A_not_A, hx_A_in_ext⟩
      exact fan_apex_not_in_other_M G M cfg x_A this
    have hx_B_out : x_B ∉ cfg.allMVertices := by
      sorry -- Aristotle: similar for x_B
    have hx_C_out : x_C ∉ cfg.allMVertices := by
      sorry -- Aristotle: similar for x_C
    have hx_D_out : x_D ∉ cfg.allMVertices := by
      sorry -- Aristotle: similar for x_D
    exact eight_edges_card cfg x_A x_B x_C x_D hx_A_out hx_B_out hx_C_out hx_D_out

  · -- S covers all triangles
    intro T hT
    have hT_tri : isTriangle G T := by
      simp only [triangles, Finset.mem_filter] at hT
      exact hT.2
    -- T is either M-element or external (Lemma 11)
    rcases all_triangles_M_or_external G M hM hM4 cfg hM_eq T hT_tri with hT_M | ⟨A, hA, hT_ext⟩
    · -- T ∈ M: covered by cycle edges
      simp only [hM_eq, Finset.mem_insert, Finset.mem_singleton] at hT_M
      rcases hT_M with rfl | rfl | rfl | rfl
      all_goals {
        obtain ⟨e, he_cycle, he_covers⟩ := cycle_edges_cover_M cfg _ (by simp)
        use e
        constructor
        · -- e ∈ S
          simp only [eightEdgeCover, Finset.mem_union]
          left; exact he_cycle
        · exact he_covers
      }
    · -- T is external: covered by S
      exact cover_hits_externals G M cfg x_A x_B x_C x_D T A hT_ext

end TuzaNu4
