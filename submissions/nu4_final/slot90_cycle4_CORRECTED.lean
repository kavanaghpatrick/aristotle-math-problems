/-
CORRECTED Cycle_4 Proof Strategy - December 26, 2025

CRITICAL FIX: Previous approaches used WRONG partition strategy!

WRONG: Partition by "triangles containing vertex v"
RIGHT: Partition by "triangles sharing M-edge at vertex v"

The difference matters because a triangle t = {v_ab, v_cd, c_ext} can:
- Contain v_ab ✓
- But share M-edge only with C (at v_cd), NOT with A or B (at v_ab)!

So local_cover_le_2 at v_ab CANNOT cover such triangles.

CORRECT PROOF STRUCTURE:
1. Define trianglesSharingMEdgeAt v = {t | ∃ e ∈ M_edges_at v, e ∈ t.sym2}
2. Prove: local_cover_le_2 covers trianglesSharingMEdgeAt v with ≤2 edges
3. Prove: Every triangle is in some trianglesSharingMEdgeAt v for shared v
4. Union bound: τ ≤ 2 + 2 + 2 + 2 = 8
-/

import Mathlib

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Triangle packing definition. -/
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) fun t₁ t₂ => (t₁ ∩ t₂).card ≤ 1

/-- Maximum packing size. -/
noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G)
    |>.image Finset.card |>.max |>.getD 0

/-- Maximum packing. -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

/-- Triangle covering number for a subset of triangles. -/
noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset
    |>.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

/-- Edges from packing elements incident to vertex v. -/
def M_edges_at (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion fun X => X.sym2.filter fun e => v ∈ e

/-- CORRECTED: Triangles that share an M-edge at vertex v.
    This is the RIGHT partition to use, NOT triangles containing v! -/
def trianglesSharingMEdgeAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun t => ∃ e ∈ M_edges_at G M v, e ∈ t.sym2

/-- Cycle-4 configuration with diagonal constraint. -/
def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

/-- LOCAL COVER LEMMA (corrected - no self-loop bug).
    If v is in exactly 2 packing elements A and B, then 2 edges from M_edges_at v
    suffice to cover all triangles in trianglesSharingMEdgeAt v. -/
lemma local_cover_le_2_corrected (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (h_inter : A ∩ B = {v})
    (h_only : ∀ Z ∈ M, v ∈ Z → Z = A ∨ Z = B) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ M_edges_at G M v ∧
    ∀ t ∈ trianglesSharingMEdgeAt G M v, ∃ e ∈ E', e ∈ t.sym2 := by
  -- Key insight: M_edges_at v consists of edges from A and B only (by h_only).
  -- These are: {v, a1}, {v, a2} from A and {v, b1}, {v, b2} from B.
  -- So |M_edges_at v| ≤ 4.
  -- Any triangle sharing an M-edge at v contains v and another vertex from A or B.
  -- By pigeonhole, 2 edges suffice.
  sorry

/-- KEY NEW LEMMA: Every triangle shares an M-edge at SOME shared vertex.
    This is the CORRECTED covering argument. -/
lemma every_triangle_shares_M_edge_at_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab v_bc v_cd v_da : V)
    (hAB : A ∩ B = {v_ab}) (hBC : B ∩ C = {v_bc})
    (hCD : C ∩ D = {v_cd}) (hDA : D ∩ A = {v_da})
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    t ∈ trianglesSharingMEdgeAt G M v_ab ∨
    t ∈ trianglesSharingMEdgeAt G M v_bc ∨
    t ∈ trianglesSharingMEdgeAt G M v_cd ∨
    t ∈ trianglesSharingMEdgeAt G M v_da := by
  -- Proof sketch:
  -- 1. By maximality, t shares edge e with some X ∈ M (otherwise could extend packing)
  -- 2. X ∈ {A, B, C, D} is a triangle in the cycle
  -- 3. Every edge of X contains at least one of the two shared vertices of X
  --    (e.g., edges of A are {v_ab, v_da, a3}, and every edge contains v_ab or v_da)
  -- 4. So e contains some shared vertex v_ij
  -- 5. Therefore e ∈ M_edges_at v_ij and e ∈ t.sym2
  -- 6. So t ∈ trianglesSharingMEdgeAt v_ij
  sorry

/-- H_only condition holds from diagonal constraint. -/
lemma h_only_from_diagonal (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab : V) (hAB : A ∩ B = {v_ab}) :
    ∀ Z ∈ M, v_ab ∈ Z → Z = A ∨ Z = B := by
  -- v_ab ∉ C because (A ∩ C).card = 0 and v_ab ∈ A
  -- v_ab ∉ D because (B ∩ D).card = 0 and v_ab ∈ B
  sorry

/-- MAIN THEOREM with CORRECTED strategy. -/
theorem tau_le_8_cycle4_corrected (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab v_bc v_cd v_da : V)
    (hAB : A ∩ B = {v_ab}) (hBC : B ∩ C = {v_bc})
    (hCD : C ∩ D = {v_cd}) (hDA : D ∩ A = {v_da}) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- CORRECTED PROOF:
  -- Step 1: Get h_only for each shared vertex (from diagonal constraint)
  have h_only_ab := h_only_from_diagonal G M A B C D hcycle v_ab hAB
  -- (similarly for v_bc, v_cd, v_da)

  -- Step 2: Apply local_cover_le_2_corrected at each shared vertex
  -- Get E_ab, E_bc, E_cd, E_da each with ≤2 edges

  -- Step 3: By every_triangle_shares_M_edge_at_shared, every triangle is covered
  -- by one of the E_v sets

  -- Step 4: Union bound
  -- |E_ab ∪ E_bc ∪ E_cd ∪ E_da| ≤ 2 + 2 + 2 + 2 = 8
  sorry
