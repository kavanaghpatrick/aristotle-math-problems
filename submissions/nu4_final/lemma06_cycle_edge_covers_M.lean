/-
  lemma06_cycle_edge_covers_M.lean

  LEMMA 6: Each cycle edge covers its corresponding M-element

  STATEMENT: The cycle edge {v_DA, v_AB} is contained in A = {v_DA, v_AB, a}

  DIFFICULTY: 2/5 (trivial set membership)

  PROOF SKETCH:
  - A = {v_DA, v_AB, a} by definition
  - v_DA ∈ A and v_AB ∈ A (both are vertices of A)
  - The edge s(v_DA, v_AB) is in A.sym2 by definition of Finset.sym2
  - Therefore the cycle edge covers A
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Sym.Sym2

variable {V : Type*} [DecidableEq V]

namespace TuzaNu4

/-- Cycle_4 configuration with 8 distinct vertices -/
structure Cycle4Config (V : Type*) where
  vAB vBC vCD vDA : V  -- shared vertices (cycle order)
  a b c d : V          -- private vertices
  all_distinct : [vAB, vBC, vCD, vDA, a, b, c, d].Nodup

/-- M-element A in cycle_4 -/
def Cycle4Config.A (cfg : Cycle4Config V) : Finset V :=
  {cfg.vDA, cfg.vAB, cfg.a}

/-- M-element B in cycle_4 -/
def Cycle4Config.B (cfg : Cycle4Config V) : Finset V :=
  {cfg.vAB, cfg.vBC, cfg.b}

/-- M-element C in cycle_4 -/
def Cycle4Config.C (cfg : Cycle4Config V) : Finset V :=
  {cfg.vBC, cfg.vCD, cfg.c}

/-- M-element D in cycle_4 -/
def Cycle4Config.D (cfg : Cycle4Config V) : Finset V :=
  {cfg.vCD, cfg.vDA, cfg.d}

/-- The 4 cycle edges (shared-to-shared edges) -/
def Cycle4Config.cycleEdges (cfg : Cycle4Config V) : Finset (Sym2 V) :=
  {s(cfg.vDA, cfg.vAB), s(cfg.vAB, cfg.vBC), s(cfg.vBC, cfg.vCD), s(cfg.vCD, cfg.vDA)}

/-- An edge covers a triangle if it's one of the triangle's edges -/
def edgeCoversTriangle (e : Sym2 V) (t : Finset V) : Prop :=
  ∃ u v : V, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ e = s(u, v)

/-- LEMMA 6: Cycle edge {vDA, vAB} covers M-element A -/
theorem cycle_edge_covers_A (cfg : Cycle4Config V) :
    edgeCoversTriangle s(cfg.vDA, cfg.vAB) cfg.A := by
  -- A = {vDA, vAB, a}, so vDA ∈ A and vAB ∈ A
  -- The edge s(vDA, vAB) connects two vertices of A
  unfold edgeCoversTriangle Cycle4Config.A
  -- Need: ∃ u v, u ≠ v ∧ u ∈ {vDA, vAB, a} ∧ v ∈ {vDA, vAB, a} ∧ s(vDA, vAB) = s(u, v)
  refine ⟨cfg.vDA, cfg.vAB, ?_, ?_, ?_, rfl⟩
  · -- vDA ≠ vAB (from all_distinct)
    have h := cfg.all_distinct
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at h
    sorry -- Aristotle: extract vDA ≠ vAB from all_distinct
  · -- vDA ∈ {vDA, vAB, a}
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
  · -- vAB ∈ {vDA, vAB, a}
    simp only [Finset.mem_insert, Finset.mem_singleton, or_true, true_or]

/-- Cycle edge {vAB, vBC} covers M-element B -/
theorem cycle_edge_covers_B (cfg : Cycle4Config V) :
    edgeCoversTriangle s(cfg.vAB, cfg.vBC) cfg.B := by
  unfold edgeCoversTriangle Cycle4Config.B
  refine ⟨cfg.vAB, cfg.vBC, ?_, ?_, ?_, rfl⟩
  · have h := cfg.all_distinct
    sorry -- Aristotle: extract vAB ≠ vBC from all_distinct
  · simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
  · simp only [Finset.mem_insert, Finset.mem_singleton, or_true, true_or]

/-- Cycle edge {vBC, vCD} covers M-element C -/
theorem cycle_edge_covers_C (cfg : Cycle4Config V) :
    edgeCoversTriangle s(cfg.vBC, cfg.vCD) cfg.C := by
  unfold edgeCoversTriangle Cycle4Config.C
  refine ⟨cfg.vBC, cfg.vCD, ?_, ?_, ?_, rfl⟩
  · have h := cfg.all_distinct
    sorry -- Aristotle: extract vBC ≠ vCD from all_distinct
  · simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
  · simp only [Finset.mem_insert, Finset.mem_singleton, or_true, true_or]

/-- Cycle edge {vCD, vDA} covers M-element D -/
theorem cycle_edge_covers_D (cfg : Cycle4Config V) :
    edgeCoversTriangle s(cfg.vCD, cfg.vDA) cfg.D := by
  unfold edgeCoversTriangle Cycle4Config.D
  refine ⟨cfg.vCD, cfg.vDA, ?_, ?_, ?_, rfl⟩
  · have h := cfg.all_distinct
    sorry -- Aristotle: extract vCD ≠ vDA from all_distinct
  · simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
  · simp only [Finset.mem_insert, Finset.mem_singleton, or_true, true_or]

end TuzaNu4
