/-
TUZA'S CONJECTURE - FULL PROOF ATTEMPT v3
τ(G) ≤ 2ν(G) for ALL graphs G

STRATEGY: Strong induction on ν using the "2-Edge Reduction Lemma"

KEY INSIGHT FROM ARISTOTLE'S ν=2 WORK:
- Proved `triangle_shares_edge_with_packing` for ν=2
- This GENERALIZES: every triangle shares edge with SOME packing triangle
- This follows from MAXIMALITY of packing (trivial proof)
- This enables the reduction lemma

PROVEN BUILDING BLOCKS (from tuza_SUCCESS_nu1_case.lean):
- tuza_base_case: ν=0 → τ=0
- tuza_case_nu_1: ν=1 → τ≤2
- triangleCoveringNumber_le_card_add_deleteEdges: τ(G) ≤ |S| + τ(G\S)
- packing_mono_deleteEdges: ν(G\S) ≤ ν(G)
- exists_max_packing: extracts maximum packing
- packing_one_implies_intersect: foundation for ν=1

NEW LEMMAS NEEDED:
- triangle_shares_edge_with_max_packing: GENERAL version (from maximality)
- exists_two_edge_reduction: THE key lemma
-/

import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Core Definitions -/

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

/-! ## Proven Foundational Lemmas -/

lemma tuza_base_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  have h_no_triangles : (G.cliqueFinset 3).card = 0 := by
    contrapose! h
    refine' ne_of_gt (lt_of_lt_of_le _ (Finset.le_sup (f := Finset.card)
      (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr
        (Classical.choose_spec (Finset.card_pos.mp (Nat.pos_of_ne_zero h)))), _⟩))) <;> norm_num
    intro x hx y hy; aesop
  unfold triangleCoveringNumber IsTriangleCovering; aesop
  rw [show (Finset.image Finset.card (Finset.filter (fun S => (G.deleteEdges S).CliqueFree 3)
    G.edgeFinset.powerset)).min = some 0 from ?_]
  · rfl
  · refine' le_antisymm _ _
    · refine' Finset.min_le _; aesop
    · simp +decide [Finset.min]
      exact fun _ _ _ => WithTop.coe_le_coe.mpr (Nat.zero_le _)

lemma triangleCoveringNumber_le_card_add_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) :
    triangleCoveringNumber G ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (Sym2 V), T ⊆ (G.deleteEdges S).edgeFinset ∧
    IsTriangleCovering (G.deleteEdges S) T ∧ T.card = triangleCoveringNumber (G.deleteEdges S) := by
    unfold triangleCoveringNumber; aesop
    have := Finset.min_of_nonempty (show Finset.Nonempty (Finset.image Finset.card
      (Finset.filter (IsTriangleCovering (G.deleteEdges S))
        (G.deleteEdges S).edgeFinset.powerset)) from ?_); aesop
    · have := Finset.mem_of_min h; aesop
    · simp +zetaDelta at *; use (G.deleteEdges S).edgeFinset; simp [IsTriangleCovering]
  have h_union : IsTriangleCovering G (S ∪ T) := by unfold IsTriangleCovering at *; aesop
  have h_union_card : triangleCoveringNumber G ≤ (S ∪ T).card := by
    unfold triangleCoveringNumber
    have h_card : (S ∪ T).card ∈ Finset.image Finset.card
      (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
      simp_all +decide [Finset.subset_iff, SimpleGraph.deleteEdges]
      exact ⟨S ∪ T, ⟨fun x hx => by aesop, h_union⟩, rfl⟩
    have := Finset.min_le h_card; aesop
    cases h : Finset.min (Finset.image Finset.card
      (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)) <;> aesop
  exact h_union_card.trans (Finset.card_union_le _ _) |> le_trans <| by rw [hT.2.2]

lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
  have h_finite : (G.cliqueFinset 3).powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr <| Finset.empty_subset _⟩
  have h_exists : ∃ P : Finset (Finset V), P ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint ∧
      ∀ Q ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint, P.card ≥ Q.card :=
    Finset.exists_max_image _ _ ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),
      by simp +decide [IsEdgeDisjoint]⟩⟩
  obtain ⟨P, hP₁, hP₂⟩ := h_exists; use P; aesop
  exact le_antisymm (Finset.le_sup (f := Finset.card) (by aesop)) (Finset.sup_le fun Q hQ => by aesop)

lemma packing_mono_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) :
    trianglePackingNumber (G.deleteEdges S) ≤ trianglePackingNumber G := by
  unfold trianglePackingNumber
  apply Finset.sup_mono
  intro P hP
  simp only [Finset.mem_filter, Finset.mem_powerset] at hP ⊢
  constructor
  · intro t ht
    have := hP.1 ht
    simp only [SimpleGraph.mem_cliqueFinset_iff] at this ⊢
    exact ⟨this.1.mono (SimpleGraph.deleteEdges_le _ _), this.2⟩
  · exact hP.2

-- Proven in tuza_SUCCESS_nu1_case.lean (400+ lines using K₄ structure)
lemma tuza_case_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  sorry

/-! ## The Key Generalization: Every Triangle Shares Edge with Some Packing Triangle -/

/--
GENERAL VERSION of triangle_shares_edge_with_packing (proven for ν=2 in v6)

This follows DIRECTLY from maximality of the packing:
If triangle t were edge-disjoint from ALL triangles in max packing P,
then P ∪ {t} would be a larger edge-disjoint set, contradicting maximality.
-/
lemma triangle_shares_edge_with_max_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) (hP_card : P.card = trianglePackingNumber G)
    (hP_sub : P ⊆ G.cliqueFinset 3) (hP_disj : IsEdgeDisjoint P)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ p ∈ P, ¬ Disjoint (triangleEdges t) (triangleEdges p) := by
  by_contra h_all_disj
  push_neg at h_all_disj
  -- h_all_disj : ∀ p ∈ P, Disjoint (triangleEdges t) (triangleEdges p)
  -- Then P ∪ {t} is edge-disjoint, contradicting maximality
  have h_disj' : IsEdgeDisjoint (insert t P) := by
    unfold IsEdgeDisjoint Set.PairwiseDisjoint
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · exact h_all_disj y hy
    · exact (h_all_disj x hx).symm
    · exact hP_disj hx hy hxy
  have h_sub' : insert t P ⊆ G.cliqueFinset 3 := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact ht
    · exact hP_sub hx
  -- Now (insert t P) is a valid packing larger than P
  have ht_notin : t ∉ P := by
    intro ht_in
    have := h_all_disj t ht_in
    simp only [Finset.disjoint_self_iff_empty] at this
    unfold triangleEdges at this
    have ht_card : t.card = 3 := ht.2
    have : t.offDiag.Nonempty := by
      rw [Finset.offDiag_nonempty]
      exact Finset.one_lt_card.mpr ⟨_, _, (Finset.card_eq_three.mp ht_card).choose_spec.choose_spec.1,
        (Finset.card_eq_three.mp ht_card).choose_spec.choose_spec.2.1,
        (Finset.card_eq_three.mp ht_card).choose_spec.choose_spec.2.2.2.1⟩
    simp only [Finset.image_eq_empty, Finset.not_nonempty_iff_eq_empty] at this
    exact this.symm ▸ Finset.not_nonempty_empty this
  have h_card_bigger : (insert t P).card > trianglePackingNumber G := by
    rw [Finset.card_insert_of_not_mem ht_notin, ← hP_card]
    omega
  have h_card_le : (insert t P).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    apply Finset.le_sup
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h_sub', h_disj'⟩
  omega

/-! ## The 2-Edge Reduction Lemma -/

/--
Helper: A triangle has 3 edges, any 2 of which determine the triangle.
Removing 2 edges destroys the triangle.
-/
lemma triangle_has_three_edges (t : Finset V) (ht : t.card = 3) :
    (triangleEdges t).card = 3 := by
  unfold triangleEdges
  obtain ⟨a, b, c, hab, hbc, hac, ht_eq⟩ := Finset.card_eq_three.mp ht
  simp only [ht_eq, Finset.offDiag_insert, Finset.offDiag_singleton]
  -- The edges are {a,b}, {a,c}, {b,c}, {b,a}, {c,a}, {c,b}
  -- After Sym2, these become 3 distinct edges
  sorry

/--
Helper: Edge-disjoint triangles in the packing don't share any edges.
So removing edges from one packing triangle doesn't affect others.
-/
lemma packing_triangle_edges_disjoint (P : Finset (Finset V)) (hP_disj : IsEdgeDisjoint P)
    (p q : Finset V) (hp : p ∈ P) (hq : q ∈ P) (hne : p ≠ q) :
    Disjoint (triangleEdges p) (triangleEdges q) :=
  hP_disj hp hq hne

/--
THE KEY LEMMA: For any G with ν(G) > 0, there exist ≤2 edges whose removal
strictly decreases the packing number.

PROOF SKETCH:
1. Get max packing P, pick any p ∈ P
2. Let S = any 2 edges of p
3. In G\S, triangle p is destroyed
4. Claim: ν(G\S) ≤ ν(G) - 1

Why: Any max packing Q in G\S:
- Is also a packing in G
- By triangle_shares_edge_with_max_packing, each triangle in Q shares edge with some P-triangle
- p is destroyed in G\S, so Q can't contain p
- The remaining P\{p} has size ν-1
- Q can't be larger than ν because it's a packing in G
- But Q can't match P's triangles one-to-one (p is gone)
- So |Q| ≤ ν - 1
-/
lemma exists_two_edge_reduction (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G > 0) :
    ∃ (S : Finset (Sym2 V)), S.card ≤ 2 ∧ S ⊆ G.edgeFinset ∧
      trianglePackingNumber (G.deleteEdges S) < trianglePackingNumber G := by
  -- Step 1: Get maximum packing P
  obtain ⟨P, hP_sub, hP_disj, hP_card⟩ := exists_max_packing G
  -- Step 2: P is nonempty since ν > 0
  have hP_nonempty : P.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hP_empty
    simp only [hP_empty, Finset.card_empty] at hP_card
    omega
  -- Step 3: Pick any triangle p from the packing
  obtain ⟨p, hp_mem⟩ := hP_nonempty
  have hp_tri : p ∈ G.cliqueFinset 3 := hP_sub hp_mem
  have hp_clique : G.IsClique p := hp_tri.1
  have hp_card : p.card = 3 := hp_tri.2
  -- Step 4: Extract vertices of p
  obtain ⟨a, b, c, hab, hbc, hac, hp_eq⟩ := Finset.card_eq_three.mp hp_card
  -- Step 5: S = two edges of p (say {a,b} and {a,c})
  have hab' : G.Adj a b := by
    have : G.IsClique p := hp_clique
    rw [hp_eq] at this
    exact this (Finset.mem_insert_self a _)
      (Finset.mem_insert_of_mem (Finset.mem_insert_self b _)) hab
  have hac' : G.Adj a c := by
    have : G.IsClique p := hp_clique
    rw [hp_eq] at this
    exact this (Finset.mem_insert_self a _)
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self c))) hac
  let e1 : Sym2 V := s(a, b)
  let e2 : Sym2 V := s(a, c)
  use {e1, e2}
  constructor
  -- |S| ≤ 2
  · by_cases h_eq : e1 = e2
    · simp [h_eq]
    · rw [Finset.card_pair h_eq]
  constructor
  -- S ⊆ G.edgeFinset
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact G.mem_edgeFinset.mpr hab'
    · exact G.mem_edgeFinset.mpr hac'
  -- ν(G\S) < ν(G)
  · -- The key argument: p is destroyed, and the general lemma constrains other triangles
    sorry

/-! ## Full Tuza's Conjecture via Strong Induction -/

/--
TUZA'S CONJECTURE: τ(G) ≤ 2ν(G) for all graphs G

Proof by strong induction on ν:
- Base: ν = 0 → τ = 0 (tuza_base_case)
- Step: For ν = k > 0:
  - Get S with |S| ≤ 2 and ν(G\S) < k (exists_two_edge_reduction)
  - By IH: τ(G\S) ≤ 2·ν(G\S) ≤ 2·(k-1)
  - By deletion: τ(G) ≤ |S| + τ(G\S) ≤ 2 + 2·(k-1) = 2k
-/
theorem tuza_conjecture (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  induction h : trianglePackingNumber G using Nat.strong_induction_on generalizing G with
  | _ k ih =>
    by_cases hk : k = 0
    · -- Base case: ν = 0
      subst hk
      have := tuza_base_case G h
      simp [this]
    · -- Inductive case: ν > 0
      have hpos : trianglePackingNumber G > 0 := by omega
      -- Apply the 2-edge reduction lemma
      obtain ⟨S, hS_card, hS_sub, hS_reduce⟩ := exists_two_edge_reduction G hpos
      -- Apply deletion lemma
      have h_del := triangleCoveringNumber_le_card_add_deleteEdges G S hS_sub
      -- Apply induction hypothesis to G\S
      have h_smaller : trianglePackingNumber (G.deleteEdges S) < k := by
        rw [← h]; exact hS_reduce
      have h_ih := ih (trianglePackingNumber (G.deleteEdges S)) h_smaller (G.deleteEdges S) rfl
      -- Combine bounds
      calc triangleCoveringNumber G
          ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := h_del
        _ ≤ 2 + 2 * trianglePackingNumber (G.deleteEdges S) := by
            have : S.card ≤ 2 := hS_card
            omega
        _ ≤ 2 + 2 * (k - 1) := by
            have : trianglePackingNumber (G.deleteEdges S) ≤ k - 1 := by omega
            omega
        _ = 2 * k := by omega

end
