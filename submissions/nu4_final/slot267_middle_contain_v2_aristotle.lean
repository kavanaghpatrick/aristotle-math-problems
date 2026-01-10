/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b32e014d-3184-4499-870e-6e27c8e264fd
-/

/-
slot267: middle_triangles_contain_v2 - FALSIFICATION TEST

HYPOTHESIS: All triangles in the "middle" (S_B ∪ X_BC ∪ S_C) contain vertex v2.
If TRUE: 2 edges incident to v2 cover the middle, giving τ ≤ 4 + 4 + 0 = 8
If FALSE: Aristotle finds counterexample, and we know this approach is blocked.

This is a quick test before committing to the full dynamic pairwise approach.
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot262)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

structure Path4Config (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  hM_card : M.card = 4
  v1 : V
  v2 : V
  v3 : V
  hAB : A ∩ B = {v1}
  hBC : B ∩ C = {v2}
  hCD : C ∩ D = {v3}
  hAC : A ∩ C = ∅
  hAD : A ∩ D = ∅
  hBD : B ∩ D = ∅
  h_v1_ne_v2 : v1 ≠ v2
  h_v2_ne_v3 : v2 ≠ v3
  h_v1_ne_v3 : v1 ≠ v3

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN HELPERS
-- ══════════════════════════════════════════════════════════════════════════════

lemma v1_in_A (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v1 ∈ cfg.A := by
  have h := cfg.hAB
  simp only [Finset.ext_iff, Finset.mem_inter, Finset.mem_singleton] at h
  exact (h cfg.v1).mpr rfl |>.1

lemma v1_in_B (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v1 ∈ cfg.B := by
  have h := cfg.hAB
  simp only [Finset.ext_iff, Finset.mem_inter, Finset.mem_singleton] at h
  exact (h cfg.v1).mpr rfl |>.2

lemma v2_in_B (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v2 ∈ cfg.B := by
  have h := cfg.hBC
  simp only [Finset.ext_iff, Finset.mem_inter, Finset.mem_singleton] at h
  exact (h cfg.v2).mpr rfl |>.1

lemma v2_in_C (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v2 ∈ cfg.C := by
  have h := cfg.hBC
  simp only [Finset.ext_iff, Finset.mem_inter, Finset.mem_singleton] at h
  exact (h cfg.v2).mpr rfl |>.2

lemma v3_in_C (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v3 ∈ cfg.C := by
  have h := cfg.hCD
  simp only [Finset.ext_iff, Finset.mem_inter, Finset.mem_singleton] at h
  exact (h cfg.v3).mpr rfl |>.1

lemma v3_in_D (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v3 ∈ cfg.D := by
  have h := cfg.hCD
  simp only [Finset.ext_iff, Finset.mem_inter, Finset.mem_singleton] at h
  exact (h cfg.v3).mpr rfl |>.2

lemma v2_not_in_A (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v2 ∉ cfg.A := by
  intro h
  have hAC := cfg.hAC
  have hv2C := v2_in_C G M cfg
  have : cfg.v2 ∈ cfg.A ∩ cfg.C := Finset.mem_inter.mpr ⟨h, hv2C⟩
  rw [hAC] at this
  exact Finset.not_mem_empty _ this

lemma v2_not_in_D (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4Config G M) : cfg.v2 ∉ cfg.D := by
  intro h
  have hBD := cfg.hBD
  have hv2B := v2_in_B G M cfg
  have : cfg.v2 ∈ cfg.B ∩ cfg.D := Finset.mem_inter.mpr ⟨hv2B, h⟩
  rw [hBD] at this
  exact Finset.not_mem_empty _ this

-- ══════════════════════════════════════════════════════════════════════════════
-- THE MIDDLE SET
-- ══════════════════════════════════════════════════════════════════════════════

/-- The "middle" triangles: those in S_B, X_BC, or S_C -/
def middleTriangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4Config G M) : Finset (Finset V) :=
  S_e G M cfg.B ∪ X_ef G cfg.B cfg.C ∪ S_e G M cfg.C

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET LEMMA: FALSIFICATION TEST
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH (if true):
1. If t ∈ S_B: t shares edge with B = {v1, v2, b}
   - If t shares {v1, v2}: v2 ∈ t ✓
   - If t shares {v1, b}: t = {v1, b, x} for some x
     - t ∉ S_B unless x avoids A,C,D... but does x = v2 forced?
   - If t shares {v2, b}: v2 ∈ t ✓

2. If t ∈ X_BC: t shares edge with both B and C
   - B ∩ C = {v2}, so t must contain v2 to share edges with both ✓

3. If t ∈ S_C: t shares edge with C = {v2, v3, c}
   - Similar analysis to S_B

KEY INSIGHT: The problematic case is t ∈ S_B with t = {v1, b, x} where x ≠ v2.
Such a triangle avoids v2. If x = v3, this is the "gap" triangle {v1, b, v3}.
This would be a COUNTEREXAMPLE to the lemma.

EXPECTED RESULT: FALSE - Aristotle should find {v1, b, v3} as counterexample.
-/
theorem middle_triangles_contain_v2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4Config G M)
    (t : Finset V) (ht : t ∈ middleTriangles G M cfg) :
    cfg.v2 ∈ t := by
  sorry

end