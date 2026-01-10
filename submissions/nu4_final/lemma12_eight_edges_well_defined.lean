/-
  lemma12_eight_edges_well_defined.lean

  LEMMA 12: The 8-edge cover set is well-defined with |S| = 8

  STATEMENT: The 8 edges are distinct, giving |S| = 8

  DIFFICULTY: 4/5 (requires vertex distinctness)

  PROOF SKETCH:
  - 4 cycle edges: {vDA,vAB}, {vAB,vBC}, {vBC,vCD}, {vCD,vDA}
  - 4 apex-private edges: {a,x_A}, {b,x_B}, {c,x_C}, {d,x_D}
  - Show all 8 are distinct using:
    - The 8 cycle_4 vertices are distinct
    - Fan apexes are outside M-vertices (Lemma 5)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Sym.Sym2

variable {V : Type*} [DecidableEq V]

namespace TuzaNu4

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

/-- The 4 cycle edges are distinct -/
theorem cycle_edges_card (cfg : Cycle4Config V) :
    cfg.cycleEdges.card = 4 := by
  -- The 4 shared vertices are distinct, so the 4 edges are distinct
  simp only [Cycle4Config.cycleEdges]
  rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
      Finset.card_insert_of_not_mem, Finset.card_singleton]
  -- Need to show edges are pairwise distinct
  all_goals {
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
               Prod.swap_prod_mk]
    -- Use distinctness of vertices
    have h := cfg.all_distinct
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at h
    sorry -- Aristotle: vertex distinctness implies edge distinctness
  }

/-- The 4 apex-private edges (given apexes outside M-vertices) -/
def apexPrivateEdges (cfg : Cycle4Config V) (x_A x_B x_C x_D : V) : Finset (Sym2 V) :=
  {s(cfg.a, x_A), s(cfg.b, x_B), s(cfg.c, x_C), s(cfg.d, x_D)}

/-- Apex-private edges are distinct from cycle edges -/
theorem apex_private_disjoint_cycle
    (cfg : Cycle4Config V) (x_A x_B x_C x_D : V)
    (hx_A : x_A ∉ cfg.allMVertices)
    (hx_B : x_B ∉ cfg.allMVertices)
    (hx_C : x_C ∉ cfg.allMVertices)
    (hx_D : x_D ∉ cfg.allMVertices) :
    Disjoint cfg.cycleEdges (apexPrivateEdges cfg x_A x_B x_C x_D) := by
  -- Cycle edges connect shared vertices only
  -- Apex-private edges connect private vertices to external apexes
  -- These sets are disjoint because:
  -- - Cycle edges are between shared vertices (vAB, vBC, vCD, vDA)
  -- - Apex-private edges involve private vertices (a, b, c, d) and external apexes
  rw [Finset.disjoint_iff_ne]
  intro e he_cycle e' he_apex h_eq
  simp only [Cycle4Config.cycleEdges, Finset.mem_insert, Finset.mem_singleton] at he_cycle
  simp only [apexPrivateEdges, Finset.mem_insert, Finset.mem_singleton] at he_apex
  -- Each case: cycle edge vs apex-private edge
  rcases he_cycle with rfl | rfl | rfl | rfl <;>
  rcases he_apex with rfl | rfl | rfl | rfl <;>
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h_eq <;>
  sorry -- Aristotle: vertex distinctness contradiction

/-- LEMMA 12: The 8-edge cover has exactly 8 edges -/
theorem eight_edges_card
    (cfg : Cycle4Config V) (x_A x_B x_C x_D : V)
    (hx_A : x_A ∉ cfg.allMVertices)
    (hx_B : x_B ∉ cfg.allMVertices)
    (hx_C : x_C ∉ cfg.allMVertices)
    (hx_D : x_D ∉ cfg.allMVertices)
    (h_apex_distinct : [x_A, x_B, x_C, x_D].Nodup) :
    (cfg.cycleEdges ∪ apexPrivateEdges cfg x_A x_B x_C x_D).card = 8 := by
  have h_disjoint := apex_private_disjoint_cycle cfg x_A x_B x_C x_D hx_A hx_B hx_C hx_D
  rw [Finset.card_union_of_disjoint h_disjoint]
  have h1 : cfg.cycleEdges.card = 4 := cycle_edges_card cfg
  have h2 : (apexPrivateEdges cfg x_A x_B x_C x_D).card = 4 := by
    -- Private vertices a, b, c, d are distinct
    -- Apexes may or may not be distinct, but edges still distinct
    sorry -- Aristotle: apex-private edges are distinct
  omega

end TuzaNu4
