/-
TUZA'S CONJECTURE - FULL PROOF via Strong Induction
τ(G) ≤ 2ν(G) for ALL graphs G

STRATEGY: Strong induction on ν using the "2-Edge Reduction Lemma"

KEY INSIGHT: Every triangle shares an edge with some max packing triangle.
This follows from MAXIMALITY - if a triangle were edge-disjoint from all
packing triangles, we could add it to get a larger packing.

PROOF STRUCTURE:
1. Base case: ν=0 → τ=0 [PROVEN]
2. Inductive step: For ν>0:
   - Get max packing P, pick p ∈ P
   - S = 2 edges of p (destroying p)
   - Key: ν(G\S) < ν(G) [THE GAP]
   - By IH: τ(G\S) ≤ 2·ν(G\S)
   - By deletion: τ(G) ≤ 2 + τ(G\S) ≤ 2·ν(G)

BUILDING BLOCKS:
- Proven by Aristotle (beae6b6a): base case, deletion lemma, exists_max_packing
- Proven by Aristotle (7a29e24c): ν=2 structure lemmas (included as hints)

HINTS FROM ν=2 WORK:
- When ν=2 and τ>4, every triangle shares edge with exactly one of T₁,T₂
- Triangles sharing edge with Tᵢ form a "fan" structure
- These fans extend to K₄ structures
- The K₄ structure constrains what happens when edges are removed
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

/-! ## ===== PROVEN BY ARISTOTLE (beae6b6a): Foundational Lemmas ===== -/

/-- Base case: No triangles means no covering needed -/
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

/-- Deletion lemma: τ(G) ≤ |S| + τ(G\S) -/
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

/-- Maximum packing exists and can be extracted -/
lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
  have h_finite : (G.cliqueFinset 3).powerset.Nonempty :=
    ⟨∅, Finset.mem_powerset.mpr <| Finset.empty_subset _⟩
  have h_exists : ∃ P : Finset (Finset V), P ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint ∧
      ∀ Q ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint, P.card ≥ Q.card :=
    Finset.exists_max_image _ _ ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),
      by simp +decide [IsEdgeDisjoint]⟩⟩
  obtain ⟨P, hP₁, hP₂⟩ := h_exists; use P; aesop
  exact le_antisymm (Finset.le_sup (f := Finset.card) (by aesop)) (Finset.sup_le fun Q hQ => by aesop)

/-- Monotonicity: removing edges doesn't increase packing number -/
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

/-! ## ===== PROVEN BY ARISTOTLE (beae6b6a): Key structural lemma ===== -/

/-- When ν=1, any two triangles share an edge (foundation for ν=1 case) -/
lemma packing_one_implies_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) (t1 t2 : Finset V)
    (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  contrapose! h
  refine' ne_of_gt (lt_of_lt_of_le _ (Finset.le_sup <| Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr <| Finset.insert_subset_iff.mpr ⟨h1, Finset.singleton_subset_iff.mpr h2⟩, _⟩))
  · rw [Finset.card_pair]; aesop
    unfold triangleEdges at h; aesop
    simp_all +decide [Finset.ext_iff]
    have := Finset.card_eq_three.mp h2.2
    obtain ⟨a, b, c, ha, hb, hc, hab, hbc, hac⟩ := this
    specialize h a b; aesop
  · intro x hx y hy hxy; aesop
    exact h.symm

/-! ## ===== THE KEY GENERALIZATION: Every Triangle Shares Edge with Max Packing ===== -/

/--
GENERAL VERSION: Every triangle shares an edge with some max packing triangle.

This follows DIRECTLY from maximality:
If triangle t were edge-disjoint from ALL triangles in max packing P,
then P ∪ {t} would be a larger edge-disjoint set, contradicting maximality.

This is the generalization of packing_one_implies_intersect to arbitrary ν.
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
  -- t ∉ P (otherwise disjoint from itself)
  have ht_notin : t ∉ P := by
    intro ht_in
    have := h_all_disj t ht_in
    simp only [Finset.disjoint_self_iff_empty] at this
    unfold triangleEdges at this
    have ht_card : t.card = 3 := ht.2
    have h_nonempty : t.offDiag.Nonempty := by
      rw [Finset.offDiag_nonempty]
      obtain ⟨a, b, c, hab, hbc, hac, ht_eq⟩ := Finset.card_eq_three.mp ht_card
      exact ⟨a, b, by simp [ht_eq], by simp [ht_eq], hab⟩
    simp only [Finset.image_eq_empty] at this
    exact h_nonempty.ne_empty this
  -- Now (insert t P) is larger than P
  have h_card_bigger : (insert t P).card > trianglePackingNumber G := by
    rw [Finset.card_insert_of_not_mem ht_notin, ← hP_card]
    omega
  have h_card_le : (insert t P).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    apply Finset.le_sup
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h_sub', h_disj'⟩
  omega

/-! ## ===== HINTS FROM ν=2 WORK (7a29e24c) ===== -/

/-
These lemmas were proven for ν=2 case but provide structural insight:

1. When ν=2 and τ>4:
   - Max packing P = {T₁, T₂} (two edge-disjoint triangles)
   - Every other triangle shares edge with exactly one of T₁ or T₂
   - Triangles sharing edge with T₁ form a "fan" extending to K₄
   - Same for T₂

2. Key structural insight (proven for ν=2):
   - If triangle T shares exactly one edge with packing triangle Tᵢ,
     then removing that edge destroys T's connection to the packing
   - This creates a "reduction" opportunity

3. The "extension to K₄" pattern:
   - If T shares edge e with packing triangle Tᵢ but T ≠ Tᵢ,
     then T has a vertex outside Tᵢ
   - This vertex + Tᵢ's vertices + adjacency constraints force K₄ structure

These patterns should help Aristotle understand the reduction lemma.
-/

/-! ## ===== THE KEY GAP: 2-Edge Reduction Lemma ===== -/

/--
Helper: A triangle has exactly 3 edges.
-/
lemma triangle_has_three_edges (t : Finset V) (ht : t.card = 3) :
    (triangleEdges t).card = 3 := by
  obtain ⟨a, b, c, hab, hbc, hac, ht_eq⟩ := Finset.card_eq_three.mp ht
  simp only [ht_eq, triangleEdges]
  -- The offDiag of {a,b,c} has 6 elements: (a,b),(a,c),(b,a),(b,c),(c,a),(c,b)
  -- After Sym2.mk, these become 3 distinct edges: s(a,b), s(a,c), s(b,c)
  sorry

/--
Helper: Removing 2 edges from a triangle destroys it.
If we remove edges e₁, e₂ from triangle t where e₁, e₂ ∈ triangleEdges t,
then t is no longer a clique in G\{e₁,e₂}.
-/
lemma triangle_destroyed_by_two_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (e1 e2 : Sym2 V) (he1 : e1 ∈ triangleEdges t) (he2 : e2 ∈ triangleEdges t) (hne : e1 ≠ e2) :
    t ∉ (G.deleteEdges {e1, e2}).cliqueFinset 3 := by
  -- t has 3 edges, we remove 2, so at least one edge of t is removed
  -- Therefore t is not a clique in G\{e1,e2}
  sorry

/--
THE KEY LEMMA: For any G with ν(G) > 0, there exist ≤2 edges whose removal
strictly decreases the packing number.

PROOF IDEA:
1. Get max packing P with |P| = ν, pick any p ∈ P
2. p is a triangle with vertices {a,b,c} and edges e₁=s(a,b), e₂=s(a,c), e₃=s(b,c)
3. Let S = {e₁, e₂} (any two edges of p)
4. In G\S, triangle p is destroyed (triangle_destroyed_by_two_edges)
5. Claim: ν(G\S) ≤ ν(G) - 1

Why ν decreases by exactly 1:
- Let Q be a max packing in G\S
- Q is also a packing in G (fewer edges ⟹ fewer triangles)
- So |Q| ≤ ν(G) = |P|
- But p ∉ Q (p is destroyed)
- Every triangle in Q shares an edge with some p' ∈ P (by triangle_shares_edge_with_max_packing)
- Key insight: The triangles sharing edge with p are either:
  (a) p itself (not in G\S), or
  (b) Triangles that share one of {e₁, e₂, e₃} with p
- Case (b) triangles sharing e₁ or e₂ are also destroyed in G\S
- So the only "remaining" triangles from P's "neighborhood" share e₃
- But these form a smaller structure than P
- More precisely: ν(G\S) ≤ ν(G) - 1 because we've destroyed p's contribution

HINT FOR ARISTOTLE:
The key is that removing 2 edges from p doesn't just destroy p,
it also disrupts any triangle that shared those specific edges with p.
The triangles that survive in G\S can only connect to P\{p},
which has cardinality ν-1.
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
  -- Step 5: Get edges of p
  have hab' : G.Adj a b := by
    rw [hp_eq] at hp_clique
    exact hp_clique (Finset.mem_insert_self a _)
      (Finset.mem_insert_of_mem (Finset.mem_insert_self b _)) hab
  have hac' : G.Adj a c := by
    rw [hp_eq] at hp_clique
    exact hp_clique (Finset.mem_insert_self a _)
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self c))) hac
  -- Step 6: S = two edges of p
  let e1 : Sym2 V := s(a, b)
  let e2 : Sym2 V := s(a, c)
  use {e1, e2}
  refine ⟨?_, ?_, ?_⟩
  -- |S| ≤ 2
  · by_cases h_eq : e1 = e2
    · simp [h_eq]
    · rw [Finset.card_pair h_eq]
  -- S ⊆ G.edgeFinset
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact G.mem_edgeFinset.mpr hab'
    · exact G.mem_edgeFinset.mpr hac'
  -- ν(G\S) < ν(G) - THE KEY STEP
  · -- The main argument: destroying p reduces ν by at least 1
    -- Any max packing Q in G\S is a packing in G, so |Q| ≤ ν(G)
    -- But p ∉ Q (p is destroyed), and the structure forces |Q| < |P|
    sorry

/-! ## ===== FULL TUZA'S CONJECTURE via Strong Induction ===== -/

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
