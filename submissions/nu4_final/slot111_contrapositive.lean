/-
Tuza ν=4: CYCLE_4 Case - Contrapositive Attack
Slot 111

STRATEGY: Contrapositive
If τ(G) > 8, then we can construct a 5th edge-disjoint triangle,
contradicting ν(G) = 4.

KEY INSIGHT (from AI debate):
- If 8 edges don't cover all triangles, some triangle t_bad is missed
- t_bad must avoid all edges from the "canonical" 8-edge set
- By cycle4_all_triangles_contain_shared, t_bad contains some shared vertex
- But then it should be hit by some edge... unless our 8-edge choice is wrong

ALTERNATIVE APPROACH:
- If t_bad avoids all 8 canonical edges AND all shared vertices
- Then t_bad is edge-disjoint from M
- So M ∪ {t_bad} is a packing of size 5, contradicting ν = 4

RISK LEVEL: HIGH
- Depends on cycle4_all_triangles_contain_shared being provable
- Construction of 5th element may fail in edge cases
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 CONFIGURATION
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
-- SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

/-- PROVEN: Every triangle contains at least one shared vertex -/
theorem cycle4_all_triangles_contain_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (h_diag_AC : (cfg.A ∩ cfg.C).card ≤ 1)
    (h_diag_BD : (cfg.B ∩ cfg.D).card ≤ 1) :
    ∀ t ∈ G.cliqueFinset 3,
      cfg.v_ab ∈ t ∨ cfg.v_bc ∈ t ∨ cfg.v_cd ∈ t ∨ cfg.v_da ∈ t := by
  sorry -- SCAFFOLDING

/-- PROVEN: Every triangle shares edge with some packing element -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
  sorry -- SCAFFOLDING (maximality)

-- ══════════════════════════════════════════════════════════════════════════════
-- THE CONTRAPOSITIVE LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/--
## Contrapositive Approach

If τ(G) > 8, then there exists a 5th edge-disjoint triangle,
which contradicts ν(G) = 4.

Proof sketch:
1. Assume τ > 8
2. For any 8-edge set E, some triangle t_bad is not covered by E
3. Consider the "canonical" 8 edges (2 from each shared vertex)
4. t_bad avoids all these 8 edges
5. By cycle4_all_triangles_contain_shared, t_bad contains some v_ij
6. But then t_bad should be hit by an edge at v_ij...
7. Unless t_bad uses only edges DISJOINT from the canonical set
8. If t_bad is edge-disjoint from M, we found a 5th packing element!
-/
lemma tau_gt_8_implies_nu_gt_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (cfg : Cycle4 G M)
    (h_diag_AC : (cfg.A ∩ cfg.C).card ≤ 1)
    (h_diag_BD : (cfg.B ∩ cfg.D).card ≤ 1)
    (h_tau_big : triangleCoveringNumber G > 8) :
    ∃ (N : Finset (Finset V)), isTrianglePacking G N ∧ N.card > 4 := by
  -- If τ > 8, no 8 edges cover all triangles
  -- This means the "canonical" 8 edges miss some triangle t_bad
  -- Show t_bad can extend the packing M
  sorry

/--
## Main Theorem via Contrapositive

ν = 4 implies τ ≤ 8 (contrapositive of above)
-/
theorem tau_le_8_cycle4_contrapositive (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (cfg : Cycle4 G M)
    (h_diag_AC : (cfg.A ∩ cfg.C).card ≤ 1)
    (h_diag_BD : (cfg.B ∩ cfg.D).card ≤ 1)
    (h_nu_4 : trianglePackingNumber G = 4) :
    triangleCoveringNumber G ≤ 8 := by
  by_contra h_tau_big
  push_neg at h_tau_big
  -- τ > 8 implies ν > 4
  obtain ⟨N, hN_pack, hN_card⟩ := tau_gt_8_implies_nu_gt_4 G M hM hM_card cfg h_diag_AC h_diag_BD h_tau_big
  -- But ν > 4 contradicts ν = 4
  sorry

end
