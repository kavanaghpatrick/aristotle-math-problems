/-
slot265: cover_hits_sharing_C - ISOLATED 1-SORRY SUBMISSION

This lemma is INDEPENDENT - can be proven without the other sorries.
Goal: Prove triangles sharing ≥2 vertices with C (but ≤1 with D) are covered.
Symmetric to cover_hits_sharing_B.
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

structure Path4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
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
  h_v1_A : v1 ∈ A
  h_v1_B : v1 ∈ B
  h_v2_B : v2 ∈ B
  h_v2_C : v2 ∈ C
  h_v3_C : v3 ∈ C
  h_v3_D : v3 ∈ D

/-- The explicit 8-edge cover for PATH_4 -/
def path4_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4 G M) : Finset (Sym2 V) :=
  cfg.A.sym2.filter (fun e => e ∈ G.edgeFinset) ∪
  ({s(cfg.v1, cfg.v2)} : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeFinset) ∪
  ({s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeFinset) ∪
  cfg.D.sym2.filter (fun e => e ∈ G.edgeFinset)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN HELPERS (from Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

lemma M_element_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (X : Finset V) (hX : X ∈ M) : X.card = 3 := by
  have := hM.1 hX
  exact SimpleGraph.mem_cliqueFinset_iff.mp this |>.2

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET LEMMA (1 SORRY)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Any triangle sharing an edge with C (but not D) is covered via spine edge {v2, v3} -/
lemma cover_hits_sharing_C (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (ht_shares_C : (t ∩ cfg.C).card ≥ 2) (ht_not_D : (t ∩ cfg.D).card ≤ 1) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  /-
  Symmetric to cover_hits_sharing_B.

  Key insight: C = {v2, v3, c} for some third vertex c.
  t shares ≥2 vertices with C, so t contains two of {v2, v3, c}.
  t shares ≤1 vertex with D, and C ∩ D = {v3}.

  Case analysis on which two vertices of C are in t:
  - {v2, v3} ⊆ t: Then s(v2, v3) ∈ t.sym2 and s(v2, v3) is in path4_cover ✓
  - {v3, c} ⊆ t: Since t shares ≤1 with D and v3 ∈ D, we have c ∉ D.
  - {v2, c} ⊆ t: Need to check if v1 ∈ t (would give spine edge {v1, v2})

  The cover includes: edges(A), {v1,v2}, {v2,v3}, edges(D).

  For {v2, v3} ⊆ t: spine edge {v2, v3} covers t. ✓

  If t = C, then v2, v3 ∈ t, so s(v2, v3) covers it ✓
  -/
  sorry

end
