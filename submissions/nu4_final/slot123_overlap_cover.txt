/-
Tuza ν=4 Cycle_4: OVERLAP COVER - τ ≤ 8
Slot 123

BREAKTHROUGH CONTEXT:
- τ ≤ 12 is PROVEN (slot113 with 0 sorry)
- But current construction has E_AB ∩ E_CD = ∅ (zero overlap)
- Need to MODIFY construction to achieve |E_AB ∩ E_CD| ≥ 4

KEY INSIGHT (from Grok + Codex analysis):
The "double duty" edges are those connecting ADJACENT shared vertices:
  - s(v_ab, v_bc) ∈ E_AB (spoke at v_ab) AND can cover bridges to C
  - s(v_bc, v_cd) ∈ E_CD (spoke at v_cd) AND can cover bridges from B
  - s(v_cd, v_da) ∈ E_CD (spoke at v_cd) AND can cover bridges to A
  - s(v_da, v_ab) ∈ E_AB (spoke at v_ab) AND can cover bridges from D

These 4 edges form a CYCLE through the shared vertices!

STRATEGY:
1. Define the 4 "cycle edges": s(v_ab,v_bc), s(v_bc,v_cd), s(v_cd,v_da), s(v_da,v_ab)
2. Prove these edges exist in G (from cycle_4 structure)
3. Prove these edges cover ALL bridges
4. Construct modified E_AB and E_CD that both include these 4 edges
5. Show |E_AB ∩ E_CD| ≥ 4, hence |E_AB ∪ E_CD| ≤ 8
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from proven slot113)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ A).card ≥ 2 ∨ (t ∩ B).card ≥ 2)

/-- Bridges: triangles in the overlap of two T_pair sets -/
def bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) : Finset (Finset V) :=
  T_pair G A B ∩ T_pair G C D

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 STRUCTURE (from proven slot113)
-- ══════════════════════════════════════════════════════════════════════════════

structure Cycle4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A

-- ══════════════════════════════════════════════════════════════════════════════
-- THE 4 CYCLE EDGES
-- ══════════════════════════════════════════════════════════════════════════════

/-- The 4 "cycle edges" connecting adjacent shared vertices -/
def cycleEdges (cfg : Cycle4 G M) : Finset (Sym2 V) :=
  {s(cfg.v_ab, cfg.v_bc), s(cfg.v_bc, cfg.v_cd), s(cfg.v_cd, cfg.v_da), s(cfg.v_da, cfg.v_ab)}

/-- These edges exist in G (from the triangle structure) -/
lemma cycleEdges_subset_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    cycleEdges cfg ⊆ G.edgeFinset := by
  -- v_ab and v_bc are both in B (a triangle), so they're adjacent in G
  -- Similarly for the other pairs
  intro e he
  simp only [cycleEdges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · -- s(v_ab, v_bc) ∈ G.edgeFinset because both are in B (a clique)
    have hB_clique : B ∈ G.cliqueFinset 3 := hM.1.1 cfg.hB
    sorry
  · -- s(v_bc, v_cd) from C
    sorry
  · -- s(v_cd, v_da) from D
    sorry
  · -- s(v_da, v_ab) from A
    sorry

/-- The cycle edges have cardinality exactly 4 (assuming distinct shared vertices) -/
lemma cycleEdges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4 G M)
    (h_distinct : cfg.v_ab ≠ cfg.v_bc ∧ cfg.v_bc ≠ cfg.v_cd ∧
                  cfg.v_cd ≠ cfg.v_da ∧ cfg.v_da ≠ cfg.v_ab ∧
                  cfg.v_ab ≠ cfg.v_cd ∧ cfg.v_bc ≠ cfg.v_da) :
    (cycleEdges cfg).card = 4 := by
  simp only [cycleEdges]
  -- The 4 edges are distinct because endpoints are distinct
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE EDGES COVER BRIDGES
-- ══════════════════════════════════════════════════════════════════════════════

/-- Key lemma: Every bridge triangle contains an edge from cycleEdges -/
lemma cycleEdges_cover_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (t : Finset V) (ht : t ∈ bridges G cfg.A cfg.B cfg.C cfg.D) :
    ∃ e ∈ cycleEdges cfg, e ∈ t.sym2 := by
  -- A bridge shares edge with (A or B) AND (C or D)
  -- By the cycle structure, this forces t to contain two adjacent shared vertices
  -- Those two vertices form an edge in cycleEdges
  simp only [bridges, Finset.mem_inter] at ht
  obtain ⟨ht_AB, ht_CD⟩ := ht
  -- t shares edge with A or B
  simp only [T_pair, Finset.mem_filter] at ht_AB ht_CD
  -- Case analysis on which elements t shares edges with
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MODIFIED COVER CONSTRUCTION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Modified E_AB that includes cycle edges at v_ab -/
def E_AB_modified (G : SimpleGraph V) [DecidableRel G.Adj] (cfg : Cycle4 G M) : Finset (Sym2 V) :=
  -- 2 cycle edges at v_ab: s(v_ab, v_bc) and s(v_da, v_ab)
  -- Plus 2 remaining spokes at v_ab (to private vertices)
  -- Plus 2 base edges
  -- But we can REMOVE some if cycle edges cover what bases covered
  sorry -- Construction TBD based on exact overlap analysis

/-- Modified E_CD that includes cycle edges at v_cd -/
def E_CD_modified (G : SimpleGraph V) [DecidableRel G.Adj] (cfg : Cycle4 G M) : Finset (Sym2 V) :=
  sorry -- Construction TBD

/-- The intersection contains at least the 4 cycle edges -/
lemma modified_covers_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    cycleEdges cfg ⊆ E_AB_modified G cfg ∩ E_CD_modified G cfg := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- ALTERNATIVE APPROACH: 2 edges per shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/--
CODEX APPROACH: Instead of 6+6-4, directly prove 2+2+2+2.

Partition ALL triangles by which shared vertex they contain (first match):
- T_ab = triangles containing v_ab
- T_bc = triangles containing v_bc but not v_ab
- T_cd = triangles containing v_cd but not v_ab or v_bc
- T_da = triangles containing v_da but not v_ab, v_bc, or v_cd

By cycle4_all_triangles_contain_shared, this covers ALL triangles.

If each partition needs ≤ 2 edges, total ≤ 8.
-/

def trianglesContainingFirst (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (excluded : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t ∧ ∀ w ∈ excluded, w ∉ t)

/-- Key claim: 2 edges suffice to cover triangles at a shared vertex -/
lemma tau_at_shared_vertex_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (v : V) (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V)) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 2 ∧ E ⊆ G.edgeFinset ∧
      ∀ t ∈ (G.cliqueFinset 3).filter (fun t => v ∈ t), ∃ e ∈ E, e ∈ t.sym2 := by
  -- At shared vertex v, exactly 2 packing elements contain v
  -- Their edges at v form a "star" of 4 edges
  -- Triangles at v must share edge with one of these 2 elements (maximality)
  -- The link graph at v has bounded matching (≤ 1 or ≤ 2)
  -- Therefore vertex cover ≤ 2, giving 2 edges
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (cfg : Cycle4 G M)
    (h_nu_4 : trianglePackingNumber G = 4)
    (h_all_contain : ∀ t ∈ G.cliqueFinset 3,
      cfg.v_ab ∈ t ∨ cfg.v_bc ∈ t ∨ cfg.v_cd ∈ t ∨ cfg.v_da ∈ t) :
    triangleCoveringNumber G ≤ 8 := by
  -- Using the 2+2+2+2 approach:
  -- Partition triangles by first shared vertex
  -- Each partition covered by ≤ 2 edges
  -- Total ≤ 8
  sorry

end
