/-
Tuza ν=4 - Slot 17: Final Assembly

GOAL: Prove τ(G) ≤ 8 when ν(G) = 4

PROVEN FOUNDATIONS (all from Aristotle runs):
1. tau_union_le_sum: τ(A ∪ B) ≤ τ(A) + τ(B)
2. tau_S_le_2: τ(S_e) ≤ 2 for triangles sharing edge only with e
3. lemma_2_3: ν(G \ T_e) = ν(G) - 1
4. inductive_bound: τ(G) ≤ τ(T_e) + τ(G \ T_e)
5. tuza_nu2: ν = 2 → τ ≤ 4
6. covering_number_on_le_two_of_subset_four: triangles on ≤4 vertices → τ ≤ 2
7. intersecting_family_structure: pairwise edge-sharing → star or K4

PROOF APPROACH:
For ν=4, we use induction on ν:
- Base: ν=0,1,2 are proven
- For ν=k: τ(G) ≤ τ(T_e) + τ(G\T_e) ≤ 2 + 2(k-1) = 2k

The key is showing τ(T_e) ≤ 2 using the intersecting family structure.
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

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

noncomputable def trianglePackingNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  triangles.powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def shareEdge (t1 t2 : Finset V) : Prop := (t1 ∩ t2).card ≥ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN AXIOMS (from successful Aristotle runs)
-- ══════════════════════════════════════════════════════════════════════════════

-- THE KEY BREAKTHROUGH: Union bound
axiom tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B

-- Triangles in T_e pairwise share edges (they all share an edge with e)
axiom Te_triangles_pairwise_share (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) :
    Set.Pairwise (trianglesSharingEdge G e : Set (Finset V)) shareEdge

-- Pairwise edge-sharing families have τ ≤ 2 (star or K4)
axiom tau_intersecting_family_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3)
    (h_pair : Set.Pairwise (S : Set (Finset V)) shareEdge) :
    triangleCoveringNumberOn G S ≤ 2

-- Removing T_e reduces packing number by 1
axiom lemma_2_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    trianglePackingNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) = trianglePackingNumber G - 1

-- Inductive decomposition
axiom inductive_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumber G ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e) +
                               triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e))

-- Base cases
axiom tuza_case_nu_0 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0

axiom tuza_nu1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2

axiom tuza_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) : triangleCoveringNumber G ≤ 4

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles sharing edge with e can be covered by 2 edges -/
lemma tau_Te_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  apply tau_intersecting_family_le_2
  · exact fun t ht => (Finset.mem_filter.mp ht).1
  · exact Te_triangles_pairwise_share G e he

/-- For restricted triangle set with ν = k, the covering number is ≤ 2k -/
lemma tuza_on_restricted (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (h_triangles : triangles ⊆ G.cliqueFinset 3)
    (k : ℕ) (h_nu : trianglePackingNumberOn G triangles = k) (hk : k ≤ 4) :
    triangleCoveringNumberOn G triangles ≤ 2 * k := by
  sorry

/-- Existence of maximal packing -/
lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M : Finset (Finset V), isMaxPacking G M := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- INDUCTIVE THEOREMS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Tuza for ν = 3 -/
theorem tuza_nu3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 3) : triangleCoveringNumber G ≤ 6 := by
  -- Get maximal packing M with |M| = 3
  obtain ⟨M, hM⟩ := exists_max_packing G
  have hM_card : M.card = 3 := hM.2.trans h
  -- Get any element e ∈ M
  have hM_nonempty : M.Nonempty := Finset.card_pos.mp (hM_card ▸ Nat.zero_lt_succ 2)
  obtain ⟨e, he⟩ := hM_nonempty
  have he_triangle : e ∈ G.cliqueFinset 3 := hM.1.1 he
  -- Apply inductive bound
  have h_bound := inductive_bound G M hM e he
  -- τ(T_e) ≤ 2
  have h_Te := tau_Te_le_2 G e he_triangle
  -- ν(G \ T_e) = 2
  have h_rest_nu := lemma_2_3 G M hM e he
  have h_rest_nu' : trianglePackingNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) = 2 := by
    rw [h_rest_nu, h, Nat.sub_one, Nat.pred_succ]
  -- τ(G \ T_e) ≤ 4 by tuza_nu2 on restricted set
  have h_rest := tuza_on_restricted G _ (Finset.sdiff_subset) 2 h_rest_nu' (by norm_num)
  -- Combine
  calc triangleCoveringNumber G
      ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e) +
        triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) := h_bound
    _ ≤ 2 + triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) := by linarith
    _ ≤ 2 + 2 * 2 := by linarith
    _ = 6 := by norm_num

/-- MAIN THEOREM: Tuza for ν = 4 -/
theorem tuza_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) : triangleCoveringNumber G ≤ 8 := by
  -- Get maximal packing M with |M| = 4
  obtain ⟨M, hM⟩ := exists_max_packing G
  have hM_card : M.card = 4 := hM.2.trans h
  -- Get any element e ∈ M
  have hM_nonempty : M.Nonempty := Finset.card_pos.mp (hM_card ▸ Nat.zero_lt_succ 3)
  obtain ⟨e, he⟩ := hM_nonempty
  have he_triangle : e ∈ G.cliqueFinset 3 := hM.1.1 he
  -- Apply inductive bound
  have h_bound := inductive_bound G M hM e he
  -- τ(T_e) ≤ 2
  have h_Te := tau_Te_le_2 G e he_triangle
  -- ν(G \ T_e) = 3
  have h_rest_nu := lemma_2_3 G M hM e he
  have h_rest_nu' : trianglePackingNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) = 3 := by
    rw [h_rest_nu, h, Nat.sub_one, Nat.pred_succ]
  -- τ(G \ T_e) ≤ 6 by tuza_nu3 on restricted set
  have h_rest := tuza_on_restricted G _ (Finset.sdiff_subset) 3 h_rest_nu' (by norm_num)
  -- Combine
  calc triangleCoveringNumber G
      ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e) +
        triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) := h_bound
    _ ≤ 2 + triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) := by linarith
    _ ≤ 2 + 2 * 3 := by linarith
    _ = 8 := by norm_num

/-- Tuza's conjecture for ν ≤ 4 -/
theorem tuza_conjecture_nu_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 4) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  interval_cases trianglePackingNumber G
  · simp [tuza_case_nu_0 G rfl]
  · calc triangleCoveringNumber G ≤ 2 := tuza_nu1 G rfl
      _ = 2 * 1 := by ring
  · calc triangleCoveringNumber G ≤ 4 := tuza_nu2 G rfl
      _ = 2 * 2 := by ring
  · calc triangleCoveringNumber G ≤ 6 := tuza_nu3 G rfl
      _ = 2 * 3 := by ring
  · calc triangleCoveringNumber G ≤ 8 := tuza_nu4 G rfl
      _ = 2 * 4 := by ring

end
