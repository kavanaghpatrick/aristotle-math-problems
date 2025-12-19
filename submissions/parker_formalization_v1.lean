/-
Parker's Proof Formalization (arXiv:2406.06501)
"New bounds on a generalization of Tuza's conjecture"

FORMALIZATION NOTES (from Grok analysis):

Key insight: Parker uses (k-1)-matchings in k-uniform hypergraphs.
For k=3 (triangles), a 2-matching is a set of triangles where every pair
shares < 2 vertices (i.e., at most 1 vertex, so NO shared edge).
This is exactly edge-disjoint triangle packing!

Definition 2.1:
- T_e = {h ∈ H : |h ∩ e| ≥ k-1} = triangles sharing an edge with e
- S_e = {h ∈ T_e : |h ∩ f| < k-1 for all f ∈ M \ {e}}
      = triangles sharing an edge with e but NOT with any other matching triangle

Lemma 2.2: ν_{k-1}(S_e) = 1
  Meaning: Every pair of triangles in S_e shares an edge.
  Proof: By contradiction. If h₁, h₂ ∈ S_e don't share an edge, then
         (M \ {e}) ∪ {h₁, h₂} is a larger matching, contradicting maximality.

Lemma 2.3: Inductive covering
  If τ_{k-1}(T_e) ≤ ⌈(k+1)/2⌉ for some e ∈ M, then we can reduce matching size.
  After removing T_e, the remaining hypergraph H' has ν_{k-1}(H') = ν - 1.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Basic triangle infrastructure (same as our ν=2 work)
def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges S).cliqueFinset 3 = ∅

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

-- Two triangles share an edge iff their edge sets intersect
def sharesEdge (t1 t2 : Finset V) : Prop :=
  ¬ Disjoint (triangleEdges t1) (triangleEdges t2)

-- Parker's Definition 2.1: T_e
-- T_e = triangles that share an edge with e
def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun h => sharesEdge h e)

-- Parker's Definition 2.1: S_e
-- S_e = triangles that share an edge with e but NOT with any other triangle in M
def S_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun h =>
    sharesEdge h e ∧ ∀ f ∈ M, f ≠ e → ¬ sharesEdge h f)

-- Key property: S_e ⊆ T_e
lemma S_e_subset_T_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) : S_e G M e ⊆ T_e G e := by
  intro h hh
  simp only [S_e, T_e, Finset.mem_filter] at *
  exact ⟨hh.1, hh.2.1⟩

-- Parker's Lemma 2.2 (Formalization)
-- Every pair of triangles in S_e shares an edge.
-- Equivalently: the packing number of S_e is 1.
-- Proof: By contradiction using replacement argument.
lemma parker_lemma_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM_sub : M ⊆ G.cliqueFinset 3)
    (hM_disj : IsEdgeDisjoint M)
    (hM_max : M.card = trianglePackingNumber G)
    (e : Finset V) (he : e ∈ M) :
    ∀ h1 h2 : Finset V, h1 ∈ S_e G M e → h2 ∈ S_e G M e → h1 ≠ h2 → sharesEdge h1 h2 := by
  intro h1 h2 hh1 hh2 hne
  -- Proof by contradiction: assume h1 and h2 don't share an edge
  by_contra h_no_share
  -- Then (M \ {e}) ∪ {h1, h2} would be a larger edge-disjoint packing
  -- Since h1, h2 ∈ S_e, they don't share edges with any f ∈ M \ {e}
  -- And by assumption, h1 and h2 don't share an edge with each other
  -- So this new set is edge-disjoint with size |M| - 1 + 2 = |M| + 1
  -- Contradicting maximality of M

  -- Extract properties from S_e membership
  simp only [S_e, Finset.mem_filter] at hh1 hh2
  have h1_in_G : h1 ∈ G.cliqueFinset 3 := hh1.1
  have h2_in_G : h2 ∈ G.cliqueFinset 3 := hh2.1
  have h1_not_share_other : ∀ f ∈ M, f ≠ e → ¬ sharesEdge h1 f := hh1.2.2
  have h2_not_share_other : ∀ f ∈ M, f ≠ e → ¬ sharesEdge h2 f := hh2.2.2

  -- Build the new matching M' = (M \ {e}) ∪ {h1, h2}
  let M' := (M.erase e).insert h1 |>.insert h2

  -- Show M' is edge-disjoint
  have hM'_disj : IsEdgeDisjoint M' := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_erase] at hx hy
    rcases hx with rfl | rfl | ⟨hx_ne, hx_in⟩ <;>
    rcases hy with rfl | rfl | ⟨hy_ne, hy_in⟩
    · exact (hxy rfl).elim
    · exact (hne rfl).elim
    · -- h2 vs f ∈ M \ {e}
      have := h2_not_share_other y hy_in hy_ne
      simp only [sharesEdge] at this
      push_neg at this
      exact this.symm
    · exact (hne rfl).elim
    · exact (hxy rfl).elim
    · -- h1 vs f ∈ M \ {e}
      have := h1_not_share_other y hy_in hy_ne
      simp only [sharesEdge] at this
      push_neg at this
      exact this.symm
    · -- f ∈ M \ {e} vs h2
      have := h2_not_share_other x hx_in hx_ne
      simp only [sharesEdge] at this
      push_neg at this
      exact this
    · -- f ∈ M \ {e} vs h1
      have := h1_not_share_other x hx_in hx_ne
      simp only [sharesEdge] at this
      push_neg at this
      exact this
    · -- f, f' ∈ M \ {e}
      exact hM_disj hx_in hy_in hxy

  -- Show M' ⊆ G.cliqueFinset 3
  have hM'_sub : M' ⊆ G.cliqueFinset 3 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx
    rcases hx with rfl | rfl | ⟨_, hx_in⟩
    · exact h2_in_G
    · exact h1_in_G
    · exact hM_sub hx_in

  -- Show |M'| ≥ |M| + 1
  have h_h1_notin_erase : h1 ∉ M.erase e := by
    intro hh1_in
    simp only [Finset.mem_erase] at hh1_in
    have := h1_not_share_other h1 hh1_in.2 hh1_in.1
    simp only [sharesEdge, Finset.disjoint_self_iff_empty] at this
    have h1_card := h1_in_G.card_eq
    simp only [triangleEdges] at this
    sorry -- h1 is a triangle, so triangleEdges h1 ≠ ∅

  have h_h2_notin : h2 ∉ (M.erase e).insert h1 := by
    simp only [Finset.mem_insert, Finset.mem_erase]
    push_neg
    constructor
    · exact hne.symm
    · intro hy_ne hy_in
      have := h2_not_share_other h2 hy_in hy_ne
      simp only [sharesEdge, Finset.disjoint_self_iff_empty] at this
      sorry -- same as above

  have hM'_card : M'.card ≥ M.card + 1 := by
    simp only [M']
    rw [Finset.card_insert_of_not_mem h_h2_notin]
    rw [Finset.card_insert_of_not_mem h_h1_notin_erase]
    rw [Finset.card_erase_of_mem he]
    omega

  -- This contradicts maximality of M
  have hM'_in_filter : M' ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hM'_sub, hM'_disj⟩

  have h_contra : trianglePackingNumber G ≥ M'.card :=
    Finset.le_sup (f := Finset.card) hM'_in_filter

  omega

-- Consequence of Lemma 2.2: packing number of S_e is at most 1
lemma S_e_packing_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM_sub : M ⊆ G.cliqueFinset 3)
    (hM_disj : IsEdgeDisjoint M)
    (hM_max : M.card = trianglePackingNumber G)
    (e : Finset V) (he : e ∈ M) :
    ∀ P ⊆ S_e G M e, IsEdgeDisjoint P → P.card ≤ 1 := by
  intro P hP_sub hP_disj
  by_contra h_gt_1
  push_neg at h_gt_1
  -- If |P| ≥ 2, there exist h1 ≠ h2 in P
  have ⟨h1, hh1, h2, hh2, hne⟩ := Finset.one_lt_card.mp h_gt_1
  -- By Lemma 2.2, h1 and h2 share an edge
  have h_share := parker_lemma_2_2 G M hM_sub hM_disj hM_max e he h1 h2 (hP_sub hh1) (hP_sub hh2) hne
  -- But P is edge-disjoint, contradiction
  have h_disj := hP_disj hh1 hh2 hne
  simp only [sharesEdge] at h_share
  exact h_share h_disj

-- Parker's Lemma 2.3: Inductive reduction
-- After removing T_e, the remaining graph has packing number ν - 1
lemma parker_lemma_2_3_matching_reduction (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM_sub : M ⊆ G.cliqueFinset 3)
    (hM_disj : IsEdgeDisjoint M)
    (hM_max : M.card = trianglePackingNumber G)
    (e : Finset V) (he : e ∈ M)
    (H' : Finset (Finset V)) (hH' : H' = G.cliqueFinset 3 \ T_e G e) :
    ∀ N ⊆ H', IsEdgeDisjoint N → N.card ≤ M.card - 1 := by
  intro N hN_sub hN_disj
  -- Proof: If |N| ≥ |M|, then N ∪ {e} would be a larger matching in G
  by_contra h_ge
  push_neg at h_ge
  -- Every h ∈ N doesn't share an edge with e (since N ⊆ H' = cliques \ T_e)
  have h_N_not_share_e : ∀ h ∈ N, ¬ sharesEdge h e := by
    intro h hh
    have := hN_sub hh
    rw [hH'] at this
    simp only [Finset.mem_sdiff, T_e, Finset.mem_filter] at this
    exact this.2

  -- So N ∪ {e} is edge-disjoint
  let N' := N.insert e
  have hN'_disj : IsEdgeDisjoint N' := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · have := h_N_not_share_e y hy
      simp only [sharesEdge] at this
      push_neg at this
      exact this.symm
    · have := h_N_not_share_e x hx
      simp only [sharesEdge] at this
      push_neg at this
      exact this
    · exact hN_disj hx hy hxy

  -- N' ⊆ G.cliqueFinset 3
  have hN'_sub : N' ⊆ G.cliqueFinset 3 := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hM_sub he
    · have := hN_sub hx
      rw [hH'] at this
      exact (Finset.mem_sdiff.mp this).1

  -- |N'| = |N| + 1 ≥ |M| + 1
  have he_notin_N : e ∉ N := by
    intro he_in
    have := h_N_not_share_e e he_in
    simp only [sharesEdge, Finset.disjoint_self_iff_empty] at this
    have e_card := (hM_sub he).card_eq
    simp only [triangleEdges] at this
    sorry -- e is a triangle, so triangleEdges e ≠ ∅

  have hN'_card : N'.card ≥ M.card + 1 := by
    simp only [N']
    rw [Finset.card_insert_of_not_mem he_notin_N]
    omega

  -- Contradiction with maximality
  have hN'_in_filter : N' ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hN'_sub, hN'_disj⟩

  have h_contra : trianglePackingNumber G ≥ N'.card :=
    Finset.le_sup (f := Finset.card) hN'_in_filter

  omega

-- Helper: M \ {e} is a maximum packing in H' = G.cliqueFinset 3 \ T_e G e
lemma M_minus_e_max_in_complement (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM_sub : M ⊆ G.cliqueFinset 3)
    (hM_disj : IsEdgeDisjoint M)
    (hM_max : M.card = trianglePackingNumber G)
    (e : Finset V) (he : e ∈ M) :
    (M.erase e) ⊆ G.cliqueFinset 3 \ T_e G e := by
  intro f hf
  simp only [Finset.mem_erase] at hf
  simp only [Finset.mem_sdiff, T_e, Finset.mem_filter]
  constructor
  · exact hM_sub hf.2
  · push_neg
    intro hf_in
    -- f shares an edge with e, but M is edge-disjoint
    have h_disj := hM_disj hf.2 he hf.1
    simp only [sharesEdge] at hf_in
    exact hf_in h_disj

-- Main covering strategy from Parker
-- If we can cover T_e with few edges, we can reduce and apply induction
theorem parker_covering_strategy (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM_sub : M ⊆ G.cliqueFinset 3)
    (hM_disj : IsEdgeDisjoint M)
    (hM_max : M.card = trianglePackingNumber G)
    (e : Finset V) (he : e ∈ M)
    (C_e : Finset (Sym2 V)) (hC_e_covers : ∀ t ∈ T_e G e, ¬ Disjoint (triangleEdges t) C_e)
    (C_rest : Finset (Sym2 V))
    (hC_rest_covers : ∀ t ∈ G.cliqueFinset 3 \ T_e G e, ¬ Disjoint (triangleEdges t) C_rest) :
    IsTriangleCovering G (C_e ∪ C_rest) := by
  simp only [IsTriangleCovering]
  ext t
  simp only [Finset.not_mem_empty, iff_false]
  intro ht
  -- t is in the deleted graph, so (triangleEdges t) ∩ (C_e ∪ C_rest) = ∅
  simp only [SimpleGraph.deleteEdges, SimpleGraph.cliqueFinset, SimpleGraph.mem_cliqueFinset_iff] at ht
  -- But t is a triangle in original G
  have t_in_G : t ∈ G.cliqueFinset 3 := by
    sorry -- Need to show t was in original G
  -- Either t ∈ T_e or t ∈ G.cliqueFinset 3 \ T_e
  by_cases ht_in_Te : t ∈ T_e G e
  · have := hC_e_covers t ht_in_Te
    -- But t's edges should be disjoint from C_e ∪ C_rest in deleted graph
    sorry
  · have : t ∈ G.cliqueFinset 3 \ T_e G e := Finset.mem_sdiff.mpr ⟨t_in_G, ht_in_Te⟩
    have := hC_rest_covers t this
    sorry

-- Tuza bound using Parker's method
-- For ν = n, we have τ ≤ 2n (by induction)
theorem tuza_by_parker_induction (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : trianglePackingNumber G = n) : triangleCoveringNumber G ≤ 2 * n := by
  induction n with
  | zero =>
    -- Base case: ν = 0 means no triangles
    simp only [Nat.zero_eq, mul_zero, Nat.le_zero]
    unfold triangleCoveringNumber
    sorry -- Need: if no triangles, covering number is 0
  | succ m ih =>
    -- Inductive case: ν = m + 1
    -- Find maximum matching M with |M| = m + 1
    -- Pick e ∈ M, cover T_e with ≤ 2 edges
    -- Apply induction to H' = G \ T_e which has ν ≤ m
    sorry

end
