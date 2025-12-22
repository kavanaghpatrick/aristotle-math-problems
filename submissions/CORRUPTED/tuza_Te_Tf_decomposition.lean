/-
Tuza T_e ∪ T_f Decomposition Completeness

This proves that the set of triangles sharing edges with e or f decomposes cleanly into:
- S_e: triangles sharing edges only with e (not with any other packing element)
- S_f: triangles sharing edges only with f (not with any other packing element)
- X(e,f): triangles sharing edges with both e and f

Key property: These sets partition T_e ∪ T_f (with possible overlaps handled).

Submission: 2025-12-21
Pattern: Boris Minimal (let Aristotle explore decomposition structure)
Target: Decomposition completeness for Tuza ν=4 proof
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def SharesEdge (t₁ t₂ : Finset V) : Prop :=
  (t₁ ∩ t₂).card ≥ 2

def EdgeDisjoint (t₁ t₂ : Finset V) : Prop :=
  (t₁ ∩ t₂).card ≤ 1

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => SharesEdge t e)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ m ∈ M, m ≠ e → EdgeDisjoint t m)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => SharesEdge t e ∧ SharesEdge t f)

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

/-
LEMMA: T_e is the set of triangles sharing an edge with e.
-/
lemma T_e_def' (G : SimpleGraph V) [DecidableRel G.Adj] (e t : Finset V) :
    t ∈ T_e G e ↔ t ∈ G.cliqueFinset 3 ∧ SharesEdge t e := by
  simp [T_e, SharesEdge]

/-
LEMMA: X_ef consists of triangles that share edges with BOTH e and f.
-/
lemma X_ef_subset_Te_inter_Tf (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) :
    X_ef G e f ⊆ T_e G e ∩ T_e G f := by
  intro t ht
  simp only [X_ef, Finset.mem_filter] at ht
  simp only [T_e, Finset.mem_inter, Finset.mem_filter]
  exact ⟨⟨ht.1, ht.2.1⟩, ⟨ht.1, ht.2.2⟩⟩

/-
LEMMA: S_e ⊆ T_e (by definition)
-/
lemma S_e_subset_T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) (M : Finset (Finset V)) :
    S_e G e M ⊆ T_e G e := by
  intro t ht
  simp only [S_e, Finset.mem_filter] at ht
  exact ht.1

/-
THEOREM: Decomposition of T_e ∪ T_f

For any two triangles e, f in a max packing M, every triangle in T_e ∪ T_f falls into
at least one of: S_e, S_f, or X_ef.

More precisely:
- If t shares edge with e only (among M), t ∈ S_e
- If t shares edge with f only (among M), t ∈ S_f
- If t shares edge with both e and f, t ∈ X_ef

Note: A triangle in X_ef might ALSO be in S_e or S_f if it's edge-disjoint from all other packing elements.
-/
theorem Te_Tf_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    T_e G e ∪ T_e G f ⊆ S_e G e M ∪ S_e G f M ∪ X_ef G e f := by
  intro t ht
  simp only [Finset.mem_union] at ht ⊢
  simp only [T_e, S_e, X_ef, Finset.mem_filter] at ht ⊢
  rcases ht with ⟨ht_clique, ht_e⟩ | ⟨ht_clique, ht_f⟩
  · by_cases h_share_f : SharesEdge t f
    · right; exact ⟨ht_clique, ht_e, h_share_f⟩
    · left; left
      refine ⟨⟨ht_clique, ht_e⟩, ?_⟩
      intro m hm hne
      by_cases hmf : m = f
      · rw [hmf]; exact Nat.not_lt.mp (by unfold SharesEdge at h_share_f; omega)
      · exact hM.1.2 he hm (fun h => hne h.symm)
  · by_cases h_share_e : SharesEdge t e
    · right; exact ⟨ht_clique, h_share_e, ht_f⟩
    · left; right
      refine ⟨⟨ht_clique, ht_f⟩, ?_⟩
      intro m hm hne
      by_cases hme : m = e
      · rw [hme]; exact Nat.not_lt.mp (by unfold SharesEdge at h_share_e; omega)
      · exact hM.1.2 hf hm (fun h => hne h.symm)

/-
THEOREM: The decomposition handles overlaps correctly.

If t ∈ X_ef, it may or may not be in S_e or S_f depending on whether it's edge-disjoint
from other packing elements.
-/
theorem X_ef_overlap (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f t : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (ht : t ∈ X_ef G e f) :
    (t ∈ S_e G e M ↔ ∀ m ∈ M, m ≠ e → EdgeDisjoint t m) ∧
    (t ∈ S_e G f M ↔ ∀ m ∈ M, m ≠ f → EdgeDisjoint t m) := by
  simp only [X_ef, Finset.mem_filter] at ht
  constructor
  · constructor
    · intro hs m hm hne
      simp only [S_e, T_e, Finset.mem_filter] at hs
      exact hs.2 m hm hne
    · intro hall
      simp only [S_e, T_e, Finset.mem_filter]
      exact ⟨⟨ht.1, ht.2.1⟩, hall⟩
  · constructor
    · intro hs m hm hne
      simp only [S_e, T_e, Finset.mem_filter] at hs
      exact hs.2 m hm hne
    · intro hall
      simp only [S_e, T_e, Finset.mem_filter]
      exact ⟨⟨ht.1, ht.2.2⟩, hall⟩

/-
THEOREM: Covering number bound via decomposition.

If τ(S_e) ≤ 2, τ(S_f) ≤ 2, and τ(X_ef) ≤ 2 (with shared edges at v), then τ(T_e ∪ T_f) ≤ 4.

The key insight is that edges covering X_ef can be reused: if all triangles in X_ef
contain v (by bridge lemma), then the 2 edges at v used for X_ef might also cover
some triangles in S_e ∩ X_ef or S_f ∩ X_ef.
-/
theorem tau_union_from_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_tau_Se : triangleCoveringNumberOn G (S_e G e M) ≤ 2)
    (h_tau_Sf : triangleCoveringNumberOn G (S_e G f M) ≤ 2)
    (h_tau_X : triangleCoveringNumberOn G (X_ef G e f) ≤ 2) :
    triangleCoveringNumberOn G (T_e G e ∪ T_e G f) ≤ 6 := by
  sorry

/-
THEOREM: Improved bound when X_ef triangles share a common vertex.

If all triangles in X_ef contain a common vertex v (guaranteed by bridge_lemma when
e and f are edge-disjoint), then covering X_ef reuses edges from S_e and S_f.
-/
theorem tau_union_with_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (v : V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_edge_disjoint : EdgeDisjoint e f)
    (h_bridge : ∀ t ∈ X_ef G e f, v ∈ t)
    (h_v_in_e : v ∈ e) (h_v_in_f : v ∈ f)
    (h_tau_Se : triangleCoveringNumberOn G (S_e G e M) ≤ 2)
    (h_tau_Sf : triangleCoveringNumberOn G (S_e G f M) ≤ 2) :
    triangleCoveringNumberOn G (T_e G e ∪ T_e G f) ≤ 4 := by
  sorry

end
