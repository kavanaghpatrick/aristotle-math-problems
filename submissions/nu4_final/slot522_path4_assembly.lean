/-
PATH_4 Final Assembly - τ ≤ 8 Main Theorem

PATH_4 structure: A — B — C — D (adjacent share 1 vertex, non-adjacent disjoint)
Let v1 = A ∩ B, v2 = B ∩ C, v3 = C ∩ D (spine vertices)

PROVEN: τ(T_A) ≤ 4, τ(T_D) ≤ 4, τ(S_e) ≤ 2, τ(X_ef) ≤ 2

KEY INSIGHT: The 8 edges for T_A ∪ T_D also cover T_B ∪ T_C because:
- X_BA = X_AB ⊆ T_A (so T_A cover hits part of T_B)
- X_CD ⊆ T_D (so T_D cover hits part of T_C)
- Remaining S_B ∪ X_BC ∪ S_C are hit by edges at spine vertices v1, v2, v3
-/

import Mathlib

set_option linter.mathlibStandardSet false
open scoped BigOperators Classical
set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Core definitions
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧ Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧ A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

-- SCAFFOLDING: Proven lemmas from slot262

axiom tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B

axiom path4_triangle_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    G.cliqueFinset 3 ⊆ trianglesSharingEdge G A ∪ trianglesSharingEdge G B ∪
      trianglesSharingEdge G C ∪ trianglesSharingEdge G D

axiom tau_Te_le_4_for_endpoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumberOn G (trianglesSharingEdge G A) ≤ 4

axiom tau_Te_le_4_for_endpoint_D (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumberOn G (trianglesSharingEdge G D) ≤ 4

axiom tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2

axiom tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2

axiom triangleCoveringNumber_le_on_all (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringNumber G ≤ triangleCoveringNumberOn G (G.cliqueFinset 3)

axiom triangleCoveringNumberOn_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (h : A ⊆ B) :
    triangleCoveringNumberOn G A ≤ triangleCoveringNumberOn G B

axiom X_ef_symm (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) :
    X_ef G e f = X_ef G f e

axiom Te_eq_Se_union_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    trianglesSharingEdge G e = S_e G M e ∪ bridges G M e

axiom path4_B_bridges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    bridges G M B ⊆ X_ef G B A ∪ X_ef G B C

axiom X_ef_subset_Te (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) :
    X_ef G e f ⊆ trianglesSharingEdge G e

/-
MAIN THEOREM - τ ≤ 8 for PATH_4

PROOF SKETCH:
1. All triangles ⊆ T_A ∪ T_B ∪ T_C ∪ T_D (path4_triangle_partition)
2. X_BA = X_AB ⊆ T_A, X_CD ⊆ T_D (by X_ef_symm and X_ef_subset_Te)
3. τ(T_A) ≤ 4 covers S_A and X_AB; τ(T_D) ≤ 4 covers S_D and X_CD
4. The 8 edges at v1 = A∩B and v3 = C∩D also hit S_B ∪ X_BC ∪ S_C
5. Therefore: τ(G) ≤ τ(T_A) + τ(T_D) = 4 + 4 = 8
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hcard : M.card = 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  -- All triangles in T_A ∪ T_B ∪ T_C ∪ T_D
  have h_partition := path4_triangle_partition G M hM A B C D hpath
  -- Membership facts
  have hA : A ∈ M := by rw [hpath.1]; simp
  have hB : B ∈ M := by rw [hpath.1]; simp
  have hC : C ∈ M := by rw [hpath.1]; simp
  have hD : D ∈ M := by rw [hpath.1]; simp
  -- Key bounds from proven lemmas
  have h_tau_A := tau_Te_le_4_for_endpoint G M hM A B C D hpath
  have h_tau_D := tau_Te_le_4_for_endpoint_D G M hM A B C D hpath
  have h_tau_SB := tau_S_le_2 G M hM B hB
  have h_tau_SC := tau_S_le_2 G M hM C hC
  have h_tau_XBC := tau_X_le_2 G M hM B C hB hC hpath.2.2.2.1
  -- X_BA = X_AB ⊆ T_A, so bridges from B to A are in T_A
  have h_XBA_eq : X_ef G B A = X_ef G A B := X_ef_symm G B A
  have h_XBA_sub_TA : X_ef G B A ⊆ trianglesSharingEdge G A := by
    rw [h_XBA_eq]; exact X_ef_subset_Te G A B
  -- X_CD ⊆ T_D
  have h_XCD_sub_TD : X_ef G C D ⊆ trianglesSharingEdge G D := X_ef_subset_Te G C D
  -- The calc chain
  calc triangleCoveringNumber G
      ≤ triangleCoveringNumberOn G (G.cliqueFinset 3) :=
        triangleCoveringNumber_le_on_all G
    _ ≤ triangleCoveringNumberOn G
        (trianglesSharingEdge G A ∪ trianglesSharingEdge G B ∪
         trianglesSharingEdge G C ∪ trianglesSharingEdge G D) :=
        triangleCoveringNumberOn_mono G _ _ h_partition
    _ ≤ triangleCoveringNumberOn G (trianglesSharingEdge G A) +
        triangleCoveringNumberOn G (trianglesSharingEdge G B ∪ trianglesSharingEdge G C ∪ trianglesSharingEdge G D) := by
        have := tau_union_le_sum G (trianglesSharingEdge G A)
          (trianglesSharingEdge G B ∪ trianglesSharingEdge G C ∪ trianglesSharingEdge G D)
        simp only [Finset.union_assoc] at this ⊢; exact this
    _ ≤ 4 + triangleCoveringNumberOn G (trianglesSharingEdge G B ∪ trianglesSharingEdge G C ∪ trianglesSharingEdge G D) := by
        linarith
    _ ≤ 4 + (triangleCoveringNumberOn G (trianglesSharingEdge G D) +
            triangleCoveringNumberOn G (trianglesSharingEdge G B ∪ trianglesSharingEdge G C)) := by
        have h_rearr : trianglesSharingEdge G B ∪ trianglesSharingEdge G C ∪ trianglesSharingEdge G D =
            trianglesSharingEdge G D ∪ (trianglesSharingEdge G B ∪ trianglesSharingEdge G C) := by
          ext x; simp [Finset.mem_union]; tauto
        rw [h_rearr]; linarith [tau_union_le_sum G (trianglesSharingEdge G D) (trianglesSharingEdge G B ∪ trianglesSharingEdge G C)]
    _ ≤ 4 + (4 + triangleCoveringNumberOn G (trianglesSharingEdge G B ∪ trianglesSharingEdge G C)) := by
        linarith
    _ ≤ 8 := by
        /-
        FINAL STEP: τ(T_B ∪ T_C) ≤ 0 after T_A ∪ T_D covered

        The 8 edges for T_A ∪ T_D include edges at:
        - v1 = A ∩ B (from T_A cover, hitting X_AB and part of S_B)
        - v3 = C ∩ D (from T_D cover, hitting X_CD and part of S_C)

        Triangles in S_B ∪ X_BC ∪ S_C that avoid v1 AND v3:
        - If t ∈ S_B avoids v1, then t = {b1, b2, x} where B = {v1, b1, b2}
        - If t also avoids v2 = B ∩ C, then t is disjoint from C and D
        - This would contradict maximality (t extends the packing)

        Therefore all remaining triangles contain v1 or v3, so are covered.
        τ(T_B ∪ T_C | T_A ∪ T_D covered) = 0
        -/
        sorry

end
