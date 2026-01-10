/-
  slot187_tau_le_10_fallback.lean

  FALLBACK: Prove τ ≤ 10 for cycle_4 as intermediate result

  STRATEGY: Even if τ ≤ 8 fails, prove τ ≤ 10 via:
  - 4 M-edges (cover M-elements + some externals)
  - At most 6 additional edges for remaining externals

  KEY INSIGHT:
  - τ(Ext(A)) ≤ 2 for each M-element (proven via fan structure)
  - But external covers OVERLAP at shared vertices
  - Each shared vertex v has externals from 2 adjacent M-elements
  - One edge at v can cover externals from BOTH adjacent M-elements
  - This gives: 4 M-edges + 4 shared-vertex edges + ≤2 private edges = 10

  This is a CONSERVATIVE bound that should be provable even if universal
  apex conjecture is false.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TuzaNu4

/-- A triangle is a 3-element set forming a clique -/
def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t.card = 3 ∧ G.IsClique t

/-- The set of all triangles in G -/
def triangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  Finset.univ.filter (isTriangle G)

/-- Two triangles share an edge -/
def sharesEdge (t₁ t₂ : Finset V) : Prop :=
  ∃ u v : V, u ≠ v ∧ u ∈ t₁ ∧ v ∈ t₁ ∧ u ∈ t₂ ∧ v ∈ t₂

/-- An edge covers a triangle -/
def edgeCovers (e : Sym2 V) (t : Finset V) : Prop :=
  e ∈ t.sym2

/-- A set of edges covers all triangles -/
def coveringSet (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  ∀ t ∈ triangles G, ∃ e ∈ S, edgeCovers e t

/-- A packing is edge-disjoint -/
def isPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  (∀ t ∈ M, isTriangle G t) ∧
  (∀ t₁ ∈ M, ∀ t₂ ∈ M, t₁ ≠ t₂ → ¬sharesEdge t₁ t₂)

/-- Maximal packing -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isPacking G M ∧
  (∀ T : Finset V, isTriangle G T → T ∉ M → ∃ A ∈ M, sharesEdge T A)

/-- External of A -/
def externalsOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (triangles G).filter fun T =>
    T ∉ M ∧ sharesEdge T A ∧ (∀ B ∈ M, B ≠ A → ¬sharesEdge T B)

/-- Cycle_4 structure -/
structure Cycle4Config (V : Type*) where
  vAB vBC vCD vDA : V  -- shared vertices
  a b c d : V          -- private vertices
  all_distinct : [vAB, vBC, vCD, vDA, a, b, c, d].Nodup
  A := ({vDA, vAB, a} : Finset V)
  B := ({vAB, vBC, b} : Finset V)
  C := ({vBC, vCD, c} : Finset V)
  D := ({vCD, vDA, d} : Finset V)

/-- Externals at a shared vertex v use edge from that vertex -/
def externalsAtSharedVertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (triangles G).filter fun T =>
    T ∉ M ∧ v ∈ T ∧ (∃ A ∈ M, v ∈ A ∧ sharesEdge T A)

/-- KEY LEMMA: Externals at shared vertex are covered by 2 edges -/
theorem externals_at_shared_vertex_covered_by_2
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V) (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (v : V) (hv : v ∈ ({cfg.vAB, cfg.vBC, cfg.vCD, cfg.vDA} : Finset V)) :
    ∃ S : Finset (Sym2 V), S.card ≤ 2 ∧
      (∀ T ∈ externalsAtSharedVertex G M v, ∃ e ∈ S, edgeCovers e T) := by
  -- At shared vertex v (e.g., vAB):
  -- - Adjacent M-elements are A = {vDA, vAB, a} and B = {vAB, vBC, b}
  -- - External T of A at vAB has form {vAB, a, x_A} or {vAB, vDA, x_A}
  -- - External T of B at vAB has form {vAB, b, x_B} or {vAB, vBC, x_B}
  --
  -- All these externals contain v = vAB.
  -- They also contain their respective fan apex x_A or x_B.
  --
  -- To cover all with 2 edges:
  -- - Option 1: {vAB, x_A} and {vAB, x_B} if x_A ≠ x_B
  -- - Option 2: {vAB, x} if universal apex
  -- - Option 3: Use M-vertex edges {vAB, a}, {vAB, b} etc.
  --
  -- Conservative: 2 edges like {vAB, w₁}, {vAB, w₂} where w₁, w₂
  -- are chosen to hit all externals at vAB
  sorry -- Aristotle: construct 2-edge cover at shared vertex

/-- Externals at private vertex use edge involving that vertex -/
def externalsAtPrivateVertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (p : V) : Finset (Finset V) :=
  (externalsOf G M A).filter fun T => p ∈ T

/-- INTERMEDIATE: τ ≤ 10 construction -/
theorem tau_le_10_cycle4
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V)
    (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (hG_A : isTriangle G cfg.A) (hG_B : isTriangle G cfg.B)
    (hG_C : isTriangle G cfg.C) (hG_D : isTriangle G cfg.D) :
    ∃ S : Finset (Sym2 V), S.card ≤ 10 ∧ coveringSet G S := by
  -- CONSTRUCTION:
  --
  -- Part 1: M-edges (4 edges)
  -- {vDA, a} covers A and externals of A using edge {vDA, a}
  -- {vAB, b} covers B and externals of B using edge {vAB, b}
  -- {vBC, c} covers C and externals of C using edge {vBC, c}
  -- {vCD, d} covers D and externals of D using edge {vCD, d}
  --
  -- Part 2: Shared-vertex edges (4 edges)
  -- At each shared vertex v, pick ONE edge {v, x_v} that covers
  -- all remaining externals at v not already covered by M-edges
  --
  -- Part 3: Private-vertex edges (≤2 edges)
  -- Some externals use private vertices. E.g., external {vDA, vAB, x}
  -- of A uses M-edge {vDA, vAB} but doesn't contain private vertex a.
  -- These need additional coverage.
  --
  -- Analysis:
  -- External types for A = {vDA, vAB, a}:
  -- - {vDA, a, x}: covered by M-edge {vDA, a} ✓
  -- - {vAB, a, x}: covered by M-edge... wait, we chose {vDA, a}
  --   Need {vAB, ?} to cover {vAB, a, x}
  -- - {vDA, vAB, x}: not covered by {vDA, a}
  --   Need edge involving vDA, vAB, or x
  --
  -- Refined Strategy:
  -- M-edge choice affects which externals are auto-covered!
  --
  -- ADAPTIVE M-EDGE SELECTION:
  -- For M-element A = {vDA, vAB, a}:
  -- - If most externals use edge {vDA, a}, pick that
  -- - If most externals use edge {vAB, a}, pick that
  -- - If most externals use edge {vDA, vAB}, pick that
  --
  -- With optimal M-edge selection:
  -- - Each M-edge covers its M-element + some externals
  -- - Remaining externals need additional edges
  --
  -- CLAIM: Remaining externals need ≤6 additional edges
  -- - At most 2 per shared vertex (for externals not covered by M-edges)
  -- - But shared vertices are 4, and overlapping coverage...
  --
  -- Actually simpler: Use M-edges + fan apex edges
  --
  -- M-edges: 4 (one per M-element)
  -- Fan apex edges: τ(Ext(A)) ≤ 2 each, so ≤8 total
  -- But M-edges already cover SOME externals!
  --
  -- Conservative bound:
  -- - 4 M-edges cover M-elements
  -- - Remaining externals: those not hit by M-edges
  -- - Each M-element has ≤2 "uncovered" external directions
  -- - At shared vertices, uncovered externals from both neighbors
  --   can share coverage
  --
  -- Total: 4 + 4 + 2 = 10 (with some slack)

  -- First, establish M-edges cover M-elements
  let m_edges : Finset (Sym2 V) := {s(cfg.vDA, cfg.a), s(cfg.vAB, cfg.b),
                                    s(cfg.vBC, cfg.c), s(cfg.vCD, cfg.d)}

  -- Get shared-vertex covers
  obtain ⟨S_vAB, hS_vAB⟩ := externals_at_shared_vertex_covered_by_2 G M hM.1 hM4 cfg hM_eq
                             cfg.vAB (by simp)
  obtain ⟨S_vBC, hS_vBC⟩ := externals_at_shared_vertex_covered_by_2 G M hM.1 hM4 cfg hM_eq
                             cfg.vBC (by simp)
  obtain ⟨S_vCD, hS_vCD⟩ := externals_at_shared_vertex_covered_by_2 G M hM.1 hM4 cfg hM_eq
                             cfg.vCD (by simp)
  obtain ⟨S_vDA, hS_vDA⟩ := externals_at_shared_vertex_covered_by_2 G M hM.1 hM4 cfg hM_eq
                             cfg.vDA (by simp)

  -- Combine all covers
  let shared_cover := S_vAB ∪ S_vBC ∪ S_vCD ∪ S_vDA
  let full_cover := m_edges ∪ shared_cover

  use full_cover
  constructor
  · -- Card bound: 4 + 4×2 = 12, but with overlap ≤ 10
    -- M-edges are distinct: 4
    -- Shared covers: each has ≤2 edges, total ≤8
    -- But some shared edges may overlap!
    --
    -- E.g., S_vAB might share edge with S_vBC if both use vBC
    -- Actually no, S_vAB uses edges at vAB, S_vBC at vBC
    --
    -- Conservative: 4 + 8 = 12
    -- But we can show overlaps reduce this to 10
    --
    -- Key observation: if we're smart about edge selection,
    -- shared vertex edges can overlap with M-edges!
    -- E.g., M-edge {vAB, b} is already in shared_cover potential
    sorry -- Aristotle: prove |full_cover| ≤ 10

  · -- Coverage
    intro T hT
    by_cases hTM : T ∈ M
    · -- M-element case
      sorry -- Aristotle: covered by m_edges
    · -- External case
      obtain ⟨A_elem, hA_elem, h_shares⟩ := hM.2 T (by
        exact (Finset.mem_filter.mp hT).2) hTM
      -- T is external, contains some vertex v
      -- If v is shared vertex, covered by S_v
      -- If v is only private vertex, use M-edge coverage
      sorry -- Aristotle: external coverage

/-- IMPROVEMENT: τ ≤ 10 with explicit construction -/
theorem tau_le_10_explicit
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V)
    (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D}) :
    ∃ S : Finset (Sym2 V), S.card ≤ 10 ∧ coveringSet G S := by
  -- Explicit 10-edge construction:
  --
  -- Group 1: One edge per M-element (4 edges)
  -- These hit all M-triangles and some externals
  --
  -- Group 2: One edge per "external direction" at shared vertices (4 edges)
  -- At vAB: cover externals of A not hit by Group 1
  -- At vBC: cover externals of B not hit by Group 1
  -- At vCD: cover externals of C not hit by Group 1
  -- At vDA: cover externals of D not hit by Group 1
  --
  -- Group 3: Edges for "private-direction" externals (≤2 edges)
  -- Externals using edges like {vDA, vAB} from A need coverage
  -- These are at shared vertices, may be covered by Group 2
  --
  -- Total: 4 + 4 + 2 = 10
  sorry -- Aristotle: explicit construction

end TuzaNu4
