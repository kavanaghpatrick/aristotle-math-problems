/-
slot269: PATH_4 τ ≤ 8 via Structural Decomposition

KEY INSIGHT (from AI consultation):
Every triangle in PATH_4 either:
1. Contains a spine vertex (v1, v2, or v3), OR
2. Is "endpoint-private" (shares edge with A avoiding v1, or D avoiding v3)

8-EDGE COVER:
- edges(A) = 3 edges (covers A, endpoint-private A, triangles with v1)
- {v1,v2}, {v2,v3} = 2 edges (covers triangles with v2)
- edges(D) = 3 edges (covers D, endpoint-private D, triangles with v3)
Total: 8 edges
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

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
  v1 : V
  v2 : V
  v3 : V
  hAB : A ∩ B = {v1}
  hBC : B ∩ C = {v2}
  hCD : C ∩ D = {v3}
  hAC : A ∩ C = ∅
  hAD : A ∩ D = ∅
  hBD : B ∩ D = ∅

-- Basic membership lemmas
lemma v1_in_A (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v1 ∈ cfg.A := by
  have h := cfg.hAB
  rw [Finset.ext_iff] at h
  have := (h cfg.v1).mpr (by simp)
  exact Finset.mem_inter.mp this |>.1

lemma v1_in_B (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v1 ∈ cfg.B := by
  have h := cfg.hAB
  rw [Finset.ext_iff] at h
  have := (h cfg.v1).mpr (by simp)
  exact Finset.mem_inter.mp this |>.2

lemma v2_in_B (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v2 ∈ cfg.B := by
  have h := cfg.hBC
  rw [Finset.ext_iff] at h
  have := (h cfg.v2).mpr (by simp)
  exact Finset.mem_inter.mp this |>.1

lemma v2_in_C (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v2 ∈ cfg.C := by
  have h := cfg.hBC
  rw [Finset.ext_iff] at h
  have := (h cfg.v2).mpr (by simp)
  exact Finset.mem_inter.mp this |>.2

lemma v3_in_C (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v3 ∈ cfg.C := by
  have h := cfg.hCD
  rw [Finset.ext_iff] at h
  have := (h cfg.v3).mpr (by simp)
  exact Finset.mem_inter.mp this |>.1

lemma v3_in_D (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v3 ∈ cfg.D := by
  have h := cfg.hCD
  rw [Finset.ext_iff] at h
  have := (h cfg.v3).mpr (by simp)
  exact Finset.mem_inter.mp this |>.2

-- Key structural lemma
/-
PROOF SKETCH:
For any triangle t, by maximality of M, t shares edge with some m ∈ {A,B,C,D}.
- If m = A and v1 ∉ t: then t ∩ A has ≥2 elements from A\{v1}, endpoint-private
- If m = B and v1 ∉ t and v2 ∉ t: t ∩ B ⊆ {b}, so |t ∩ B| ≤ 1, contradiction
- If m = C and v2 ∉ t and v3 ∉ t: t ∩ C ⊆ {c}, so |t ∩ C| ≤ 1, contradiction
- If m = D and v3 ∉ t: then t ∩ D has ≥2 elements from D\{v3}, endpoint-private
-/
theorem triangle_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    cfg.v1 ∈ t ∨ cfg.v2 ∈ t ∨ cfg.v3 ∈ t ∨
    ((t ∩ cfg.A).card ≥ 2 ∧ cfg.v1 ∉ t) ∨
    ((t ∩ cfg.D).card ≥ 2 ∧ cfg.v3 ∉ t) := by
  sorry

-- 8-edge cover
def path4_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4 G M) : Finset (Sym2 V) :=
  cfg.A.sym2.filter (· ∈ G.edgeFinset) ∪
  ({s(cfg.v1, cfg.v2), s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset) ∪
  cfg.D.sym2.filter (· ∈ G.edgeFinset)

lemma path4_cover_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M) :
    path4_cover G cfg ⊆ G.edgeFinset := by
  -- Each component is filtered to G.edgeFinset, so union is subset
  unfold path4_cover
  intro e he
  simp only [Finset.mem_union, Finset.mem_filter] at he
  aesop

/-
PROOF SKETCH:
A.sym2 has ≤ 3 edges (A is a 3-clique)
Spine set has ≤ 2 edges
D.sym2 has ≤ 3 edges
Total ≤ 8
-/
lemma path4_cover_card_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (cfg : Path4 G M) :
    (path4_cover G cfg).card ≤ 8 := by
  sorry

/-
PROOF SKETCH (coverage):
By triangle_structure, every triangle t either:
1. Contains v1: t has edge in A.sym2 (since v1 ∈ A and t is a clique)
2. Contains v2 (not v1): t has edge {v1,v2} or {v2,v3}
3. Contains v3 (not v1,v2): t has edge in D.sym2 or {v2,v3}
4. Endpoint-private A: t shares {a,a'} with A, edge in A.sym2
5. Endpoint-private D: t shares edge with D, in D.sym2
-/
lemma path4_cover_covers (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  sorry

-- Main theorem
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  use path4_cover G cfg
  refine ⟨path4_cover_card_le_8 G M hM.1 cfg, path4_cover_subset G M cfg, ?_⟩
  intro t ht
  exact path4_cover_covers G M hM cfg t ht

end
