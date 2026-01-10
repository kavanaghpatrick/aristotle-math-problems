/-
  slot186_direct_8edge_cover.lean

  ATTACK: Direct construction of 8-edge cover for cycle_4

  STRATEGY: Even without universal apex, prove 8 edges suffice via:
  1. τ(Ext(A)) ≤ 2 for each M-element (fan structure)
  2. Overlap between external covers when fan apexes share edges

  KEY INSIGHT:
  If x_A ≠ x_B for adjacent A, B at shared vertex v:
  - T_A = {v, a, x_A} and T_B = {v, b, x_B} don't share edge
  - But BOTH are covered by edge {v, ?} for appropriate ?
  - The shared vertex v is in BOTH external sets!
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

/-- Covering number τ(G) -/
def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.filter (fun S : Finset (Sym2 V) => coveringSet G S) |>.image Finset.card |> Finset.min' sorry

/-- A packing is edge-disjoint -/
def isPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  (∀ t ∈ M, isTriangle G t) ∧
  (∀ t₁ ∈ M, ∀ t₂ ∈ M, t₁ ≠ t₂ → ¬sharesEdge t₁ t₂)

/-- Maximal packing -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isPacking G M ∧
  (∀ T : Finset V, isTriangle G T → T ∉ M → ∃ A ∈ M, sharesEdge T A)

/-- External of A: triangle sharing edge only with A in M -/
def externalsOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) : Finset (Finset V) :=
  (triangles G).filter fun T =>
    T ∉ M ∧ sharesEdge T A ∧ (∀ B ∈ M, B ≠ A → ¬sharesEdge T B)

/-- Fan apex for externals of A -/
def hasFanApex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (x : V) : Prop :=
  x ∉ A ∧ ∀ T ∈ externalsOf G M A, x ∈ T

/-- slot182 result: Two externals of same M-element share an edge -/
axiom two_externals_share_edge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V)
    (hT₁ : T₁ ∈ externalsOf G M A) (hT₂ : T₂ ∈ externalsOf G M A)
    (h_diff : T₁ ≠ T₂) :
    sharesEdge T₁ T₂

/-- Fan apex existence from slot182 -/
theorem fan_apex_exists
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (h_ext : (externalsOf G M A).Nonempty) :
    ∃ x : V, hasFanApex G M A x := by
  -- By slot182, any two externals share an edge
  -- Shared edge implies shared 2 vertices
  -- These shared vertices form the "fan apex" structure
  sorry -- Aristotle: construct fan apex from pairwise edge-sharing

/-- CRITICAL: τ(externals of A) ≤ 2 -/
theorem tau_externals_le_2
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isPacking G M) (hM4 : M.card = 4)
    (A : Finset V) (hA : A ∈ M) :
    ∃ S : Finset (Sym2 V), S.card ≤ 2 ∧
      (∀ T ∈ externalsOf G M A, ∃ e ∈ S, edgeCovers e T) := by
  -- If no externals, empty set works
  by_cases h_empty : (externalsOf G M A).Nonempty
  · -- Externals exist, use fan apex structure
    -- All externals contain common vertex x (fan apex)
    -- Every external T = {u, v, x} where {u,v} is an A-edge
    -- Two edges incident to x suffice to cover all externals:
    -- Pick any two vertices u, v of A. Then {u, x} ∪ {v, x} covers all.
    obtain ⟨x, hx_apex, hx_in_all⟩ := fan_apex_exists G M hM hM4 A hA h_empty
    -- A has 3 vertices, externals use edges of A
    -- Pick 2 edges from x to vertices of A
    sorry -- Aristotle: construct 2-edge cover using fan apex
  · -- No externals, empty set works
    use ∅
    simp [Finset.not_nonempty_iff_eq_empty.mp h_empty]

/-- Cycle_4 structure -/
structure Cycle4Config (V : Type*) where
  vAB vBC vCD vDA : V  -- shared vertices
  a b c d : V          -- private vertices
  all_distinct : [vAB, vBC, vCD, vDA, a, b, c, d].Nodup
  A := ({vDA, vAB, a} : Finset V)
  B := ({vAB, vBC, b} : Finset V)
  C := ({vBC, vCD, c} : Finset V)
  D := ({vCD, vDA, d} : Finset V)

/-- MAIN THEOREM: τ ≤ 8 for cycle_4 via direct construction -/
theorem tau_le_8_cycle4
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V)
    (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (hG_A : isTriangle G cfg.A) (hG_B : isTriangle G cfg.B)
    (hG_C : isTriangle G cfg.C) (hG_D : isTriangle G cfg.D) :
    ∃ S : Finset (Sym2 V), S.card ≤ 8 ∧ coveringSet G S := by
  -- Construction Strategy:
  -- 1. Pick 4 M-edges (one per M-element) - covers all M-triangles
  -- 2. For each M-element A, pick ≤2 edges to cover externals (by tau_externals_le_2)
  -- 3. Key insight: externals can OVERLAP in coverage!
  --
  -- Detailed construction:
  -- M-edges: {vDA, a}, {vAB, b}, {vBC, c}, {vCD, d}
  -- External covers: use fan apex edges, which may overlap
  --
  -- If fan apexes coincide (x_A = x_B = x_C = x_D = x):
  --   Apex edges: {vAB, x}, {vBC, x}, {vCD, x}, {vDA, x}
  --   Total: 4 M-edges + 4 apex edges = 8
  --
  -- If fan apexes differ:
  --   Each M-element needs ≤2 apex edges, but...
  --   Overlap at shared vertices reduces total!
  --   External at vAB uses edge from A or B
  --   Edge {vAB, x} (any x) covers externals at vAB from BOTH A and B

  -- First, get the 4 M-edges
  let m_edges : Finset (Sym2 V) := {s(cfg.vDA, cfg.a), s(cfg.vAB, cfg.b),
                                    s(cfg.vBC, cfg.c), s(cfg.vCD, cfg.d)}

  -- Get external covers for each M-element
  obtain ⟨S_A, hS_A_card, hS_A_covers⟩ := tau_externals_le_2 G M hM.1 hM4 cfg.A (by simp [hM_eq])
  obtain ⟨S_B, hS_B_card, hS_B_covers⟩ := tau_externals_le_2 G M hM.1 hM4 cfg.B (by simp [hM_eq])
  obtain ⟨S_C, hS_C_card, hS_C_covers⟩ := tau_externals_le_2 G M hM.1 hM4 cfg.C (by simp [hM_eq])
  obtain ⟨S_D, hS_D_card, hS_D_covers⟩ := tau_externals_le_2 G M hM.1 hM4 cfg.D (by simp [hM_eq])

  -- Combine all covers
  let external_cover := S_A ∪ S_B ∪ S_C ∪ S_D
  let full_cover := m_edges ∪ external_cover

  use full_cover
  constructor
  · -- Bound the cardinality
    -- m_edges has 4 elements (if distinct)
    -- external_cover has at most 8 elements (4 × 2)
    -- But we claim total ≤ 8 due to overlap!
    --
    -- Key: Many external triangles at shared vertices are covered
    -- by the SAME edges from adjacent fan apexes

    -- Conservative bound first: 4 + 8 = 12
    -- Then show overlap reduces this to 8
    sorry -- Aristotle: prove |full_cover| ≤ 8 via overlap analysis

  · -- Prove coverage
    intro T hT
    by_cases hTM : T ∈ M
    · -- T is an M-element
      rcases hTM with hT_A | hT_B | hT_C | hT_D
      all_goals { use ?_, ?_, ?_; sorry } -- Aristotle: M-element cases
    · -- T is external to some M-element
      obtain ⟨A_elem, hA_elem, h_shares⟩ := hM.2 T (by
        exact (Finset.mem_filter.mp hT).2) hTM
      -- T is external of A_elem
      -- Covered by S_A, S_B, S_C, or S_D depending on A_elem
      sorry -- Aristotle: external coverage

/-- STRONGER CLAIM: τ ≤ 8 via adaptive construction -/
theorem tau_le_8_adaptive
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (cfg : Cycle4Config V)
    (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D}) :
    ∃ S : Finset (Sym2 V), S.card ≤ 8 ∧ coveringSet G S := by
  -- The key insight: at each shared vertex v, there's at most one
  -- "crossing" external type (using edges from both adjacent M-elements)
  --
  -- Externals at vAB:
  -- - Type A: uses edge from A at vAB (covered by edge from A's fan apex)
  -- - Type B: uses edge from B at vAB (covered by edge from B's fan apex)
  -- - Crossing externals use edges from BOTH A and B at vAB
  --   These are impossible! (would share edge with both A and B)
  --
  -- So externals at shared vertex v are partitioned by which M-element
  -- they're external to. No triangle is external to multiple M-elements.
  --
  -- Coverage at vAB: edges to fan apexes suffice
  -- Total apex edges needed: at most 4 (one per shared vertex direction)
  --
  -- Combined with 4 M-edges: total ≤ 8
  sorry -- Aristotle: complete adaptive construction

end TuzaNu4
