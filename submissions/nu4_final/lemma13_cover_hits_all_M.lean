/-
  lemma13_cover_hits_all_M.lean

  LEMMA 13: The 4 cycle edges cover all 4 M-elements

  STATEMENT: For each M-element X ∈ {A, B, C, D}, there exists a cycle edge
  in the cover that hits X.

  DIFFICULTY: 2/5 (trivial - each M-element contains exactly one cycle edge)

  PROOF SKETCH:
  - The 4 cycle edges are: {vDA,vAB}, {vAB,vBC}, {vBC,vCD}, {vCD,vDA}
  - A = {vDA, vAB, a} contains cycle edge {vDA, vAB}
  - B = {vAB, vBC, b} contains cycle edge {vAB, vBC}
  - C = {vBC, vCD, c} contains cycle edge {vBC, vCD}
  - D = {vCD, vDA, d} contains cycle edge {vCD, vDA}
  - Each M-element is hit by exactly one cycle edge ✓
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Sym.Sym2

variable {V : Type*} [DecidableEq V]

namespace TuzaNu4

/-- Cycle_4 configuration -/
structure Cycle4Config (V : Type*) where
  vAB vBC vCD vDA : V
  a b c d : V
  all_distinct : [vAB, vBC, vCD, vDA, a, b, c, d].Nodup

def Cycle4Config.A (cfg : Cycle4Config V) : Finset V := {cfg.vDA, cfg.vAB, cfg.a}
def Cycle4Config.B (cfg : Cycle4Config V) : Finset V := {cfg.vAB, cfg.vBC, cfg.b}
def Cycle4Config.C (cfg : Cycle4Config V) : Finset V := {cfg.vBC, cfg.vCD, cfg.c}
def Cycle4Config.D (cfg : Cycle4Config V) : Finset V := {cfg.vCD, cfg.vDA, cfg.d}

/-- The 4 cycle edges -/
def Cycle4Config.cycleEdges (cfg : Cycle4Config V) : Finset (Sym2 V) :=
  {s(cfg.vDA, cfg.vAB), s(cfg.vAB, cfg.vBC), s(cfg.vBC, cfg.vCD), s(cfg.vCD, cfg.vDA)}

/-- The M-packing in cycle_4 -/
def Cycle4Config.M (cfg : Cycle4Config V) : Finset (Finset V) :=
  {cfg.A, cfg.B, cfg.C, cfg.D}

/-- An edge e covers triangle t if e is an edge of t -/
def edgeCovers (e : Sym2 V) (t : Finset V) : Prop :=
  ∃ u v : V, u ∈ t ∧ v ∈ t ∧ e = s(u, v)

/-- LEMMA 13: The cycle edges cover all M-elements -/
theorem cycle_edges_cover_all_M (cfg : Cycle4Config V) :
    ∀ X ∈ cfg.M, ∃ e ∈ cfg.cycleEdges, edgeCovers e X := by
  intro X hX
  simp only [Cycle4Config.M, Finset.mem_insert, Finset.mem_singleton] at hX
  rcases hX with rfl | rfl | rfl | rfl
  · -- X = A = {vDA, vAB, a}
    use s(cfg.vDA, cfg.vAB)
    constructor
    · simp only [Cycle4Config.cycleEdges, Finset.mem_insert, true_or]
    · unfold edgeCovers Cycle4Config.A
      exact ⟨cfg.vDA, cfg.vAB, by simp, by simp, rfl⟩
  · -- X = B = {vAB, vBC, b}
    use s(cfg.vAB, cfg.vBC)
    constructor
    · simp only [Cycle4Config.cycleEdges, Finset.mem_insert, Finset.mem_singleton, or_true, true_or]
    · unfold edgeCovers Cycle4Config.B
      exact ⟨cfg.vAB, cfg.vBC, by simp, by simp, rfl⟩
  · -- X = C = {vBC, vCD, c}
    use s(cfg.vBC, cfg.vCD)
    constructor
    · simp only [Cycle4Config.cycleEdges, Finset.mem_insert, Finset.mem_singleton, or_true, true_or]
    · unfold edgeCovers Cycle4Config.C
      exact ⟨cfg.vBC, cfg.vCD, by simp, by simp, rfl⟩
  · -- X = D = {vCD, vDA, d}
    use s(cfg.vCD, cfg.vDA)
    constructor
    · simp only [Cycle4Config.cycleEdges, Finset.mem_insert, Finset.mem_singleton, or_true]
    · unfold edgeCovers Cycle4Config.D
      exact ⟨cfg.vCD, cfg.vDA, by simp, by simp, rfl⟩

/-- Stronger version: exactly which cycle edge covers each M-element -/
theorem cycle_edge_A (cfg : Cycle4Config V) :
    edgeCovers s(cfg.vDA, cfg.vAB) cfg.A := by
  unfold edgeCovers Cycle4Config.A
  sorry -- Aristotle: straightforward membership

theorem cycle_edge_B (cfg : Cycle4Config V) :
    edgeCovers s(cfg.vAB, cfg.vBC) cfg.B := by
  unfold edgeCovers Cycle4Config.B
  sorry -- Aristotle: straightforward membership

theorem cycle_edge_C (cfg : Cycle4Config V) :
    edgeCovers s(cfg.vBC, cfg.vCD) cfg.C := by
  unfold edgeCovers Cycle4Config.C
  sorry -- Aristotle: straightforward membership

theorem cycle_edge_D (cfg : Cycle4Config V) :
    edgeCovers s(cfg.vCD, cfg.vDA) cfg.D := by
  unfold edgeCovers Cycle4Config.D
  sorry -- Aristotle: straightforward membership

end TuzaNu4
