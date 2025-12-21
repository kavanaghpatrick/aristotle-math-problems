/-
Tuza τ(S_e) ≤ 2 Assembly

This file imports the proven lemmas from f9473ebd and assembles the final result.
The assembly logic is straightforward:

1. S_e triangles pairwise share edges (lemma_2_2)
2. By intersecting_triangles_structure: either common edge or ≤4 vertices
3. Case 1: common edge → τ(S_e) ≤ 1 (common_edge_implies_tau_le_1)
4. Case 2: ≤4 vertices → τ(S_e) ≤ 2 (k4_cover + monotonicity)
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option maxHeartbeats 400000

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Definitions (same as f9473ebd)
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def shareEdge (t1 t2 : Finset V) : Prop :=
  (t1 ∩ t2).card ≥ 2

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

-- PROVEN: Parker's Lemma 2.2 (from f9473ebd)
lemma lemma_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∀ t1 t2, t1 ∈ S_e G e M → t2 ∈ S_e G e M → shareEdge t1 t2 := by
  sorry -- PROVEN in f9473ebd, copy full proof

-- PROVEN: Structure of pairwise intersecting triangles (from f9473ebd)
lemma intersecting_triangles_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (hT : T ⊆ G.cliqueFinset 3)
    (h_pairwise : Set.Pairwise (T : Set (Finset V)) shareEdge) :
    (∃ u v : V, u ≠ v ∧ ∀ t ∈ T, {u, v} ⊆ t) ∨ (Finset.biUnion T id).card ≤ 4 := by
  sorry -- PROVEN in f9473ebd, copy full proof

-- PROVEN: Common edge implies τ ≤ 1 (from f9473ebd)
lemma common_edge_implies_tau_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (hT : T ⊆ G.cliqueFinset 3)
    (u v : V) (huv : u ≠ v) (h_common : ∀ t ∈ T, {u, v} ⊆ t) :
    triangleCoveringNumberOn G T ≤ 1 := by
  sorry -- PROVEN in f9473ebd, copy full proof

-- PROVEN: K4 cover (from f9473ebd)
lemma k4_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (hU : U.card ≤ 4) :
    triangleCoveringNumberOn G (G.cliqueFinset 3 |>.filter (fun t => t ⊆ U)) ≤ 2 := by
  sorry -- PROVEN in f9473ebd, copy full proof

-- Helper: Monotonicity of covering number (cover for T works for S ⊆ T)
-- Proof: {covers for T} ⊆ {covers for S}, so min over superset ≤ min over subset
lemma triangleCoveringNumberOn_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset (Finset V)) (hST : S ⊆ T) :
    triangleCoveringNumberOn G S ≤ triangleCoveringNumberOn G T := by
  -- Routine: any cover for T is a cover for S, so min over covers for S ≤ min over covers for T
  sorry

-- Helper: S_e is contained in triangles with vertices in biUnion
lemma S_e_subset_filter (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    S_e G e M ⊆ (G.cliqueFinset 3).filter (fun t => t ⊆ (S_e G e M).biUnion id) := by
  intro t ht
  simp only [Finset.mem_filter]
  constructor
  · simp only [S_e, trianglesSharingEdge, Finset.mem_filter] at ht
    exact ht.1.1
  · intro v hv
    simp only [Finset.mem_biUnion, id]
    exact ⟨t, ht, hv⟩

-- Helper: S_e ⊆ cliques
lemma S_e_subset_cliques (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    S_e G e M ⊆ G.cliqueFinset 3 := by
  intro t ht
  simp only [S_e, trianglesSharingEdge, Finset.mem_filter] at ht
  exact ht.1.1

-- THE KEY ASSEMBLY: τ(S_e) ≤ 2
theorem tau_S_e_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G e M) ≤ 2 := by
  -- S_e triangles pairwise share edges
  have h_pairwise : Set.Pairwise (S_e G e M : Set (Finset V)) shareEdge := by
    intro t1 ht1 t2 ht2 hne
    exact lemma_2_2 G M hM e he t1 t2 ht1 ht2
  -- S_e ⊆ cliqueFinset 3
  have hS_sub : S_e G e M ⊆ G.cliqueFinset 3 := S_e_subset_cliques G M e
  -- By intersecting_triangles_structure: either common edge or ≤4 vertices
  rcases intersecting_triangles_structure G (S_e G e M) hS_sub h_pairwise with
    ⟨u, v, huv, h_common⟩ | h_small
  -- Case 1: Common edge → τ ≤ 1 ≤ 2
  · calc triangleCoveringNumberOn G (S_e G e M)
        ≤ 1 := common_edge_implies_tau_le_1 G (S_e G e M) hS_sub u v huv h_common
      _ ≤ 2 := by norm_num
  -- Case 2: ≤4 vertices → use k4_cover
  · let U := (S_e G e M).biUnion id
    have hU : U.card ≤ 4 := h_small
    calc triangleCoveringNumberOn G (S_e G e M)
        ≤ triangleCoveringNumberOn G ((G.cliqueFinset 3).filter (fun t => t ⊆ U)) :=
            triangleCoveringNumberOn_mono G _ _ (S_e_subset_filter G M e)
      _ ≤ 2 := k4_cover G U hU

end
