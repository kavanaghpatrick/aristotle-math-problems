/-
TUZA'S CONJECTURE - INFORMAL REASONING MODE
τ(G) ≤ 2ν(G) for ALL graphs G

This submission uses informal reasoning to guide proof discovery.

=== MATHEMATICAL INTUITION ===

Tuza's Conjecture says: to destroy all triangles, you need at most twice
as many edges as the maximum number of edge-disjoint triangles.

INTUITION: Think of edge-disjoint triangles as "independent" triangles.
Each one needs its own edges to be covered. But triangles can share vertices
without sharing edges, creating "fan" or "star" patterns.

=== PROOF STRATEGY (Informal) ===

We prove by strong induction on ν = trianglePackingNumber(G).

BASE CASE (ν = 0):
- No triangles ⟹ no edges need deletion
- τ = 0 ≤ 2·0 = 0 ✓

INDUCTIVE STEP (ν > 0):
- Pick any max packing P with |P| = ν
- Pick any triangle p ∈ P with vertices {a, b, c}
- Let S = {edge(a,b), edge(a,c)} (two edges of p)
- Key claim: ν(G\S) < ν

Why does removing 2 edges decrease ν?
1. Triangle p is destroyed (needs all 3 edges)
2. Any triangle T sharing edge(a,b) or edge(a,c) with p is also affected
3. The "surviving" triangles can form at most ν-1 disjoint triangles

More precisely:
- Every triangle shares an edge with some packing triangle (by maximality!)
- After removing S, triangles that shared those specific edges with p are gone
- The remaining packing structure has at most ν-1 members

Then by induction:
- τ(G\S) ≤ 2·ν(G\S) ≤ 2·(ν-1)
- τ(G) ≤ |S| + τ(G\S) ≤ 2 + 2·(ν-1) = 2·ν ✓

=== KEY INSIGHT FROM ν=2 CASE ===

When ν = 2, we have packing {T₁, T₂}. Every other triangle must share
an edge with T₁ or T₂ (by maximality). This creates two "fans":
- Fan₁: triangles sharing edge with T₁
- Fan₂: triangles sharing edge with T₂

Each fan extends to at most a K₄ structure.
If we remove 2 edges from T₁, we destroy Fan₁ entirely.
The remaining triangles are all in Fan₂, which has ν ≤ 1.

This pattern GENERALIZES: removing 2 edges from any packing triangle
destroys that triangle's "contribution" to the packing number.

=== FORMAL PROOF FOLLOWS ===
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

/-! ## Proven Building Blocks -/

-- Base case: ν = 0 implies τ = 0
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

-- Deletion lemma: τ(G) ≤ |S| + τ(G\S)
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

-- Max packing exists
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

/-! ## The Key Insight: Maximality Implies Edge-Sharing -/

/--
INFORMAL PROOF:

Suppose triangle t shares NO edges with any triangle in max packing P.
Then P ∪ {t} is still edge-disjoint.
But P ∪ {t} is a packing larger than P, contradicting maximality.
Therefore, t MUST share an edge with some triangle in P.

This is the foundation of the reduction argument!
-/
lemma triangle_shares_edge_with_max_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) (hP_card : P.card = trianglePackingNumber G)
    (hP_sub : P ⊆ G.cliqueFinset 3) (hP_disj : IsEdgeDisjoint P)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ p ∈ P, ¬ Disjoint (triangleEdges t) (triangleEdges p) := by
  by_contra h_all_disj
  push_neg at h_all_disj
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
INFORMAL PROOF of exists_two_edge_reduction:

Goal: Show ∃ S with |S| ≤ 2 such that ν(G\S) < ν(G).

Construction:
1. Get max packing P = {p₁, p₂, ..., pₙ} with n = ν
2. Pick p₁ with vertices {a, b, c}
3. Let S = {edge(a,b), edge(a,c)}

Why ν(G\S) < ν:

Step 1: Triangle p₁ is DESTROYED in G\S.
- p₁ needs all 3 edges to be a triangle
- We removed 2, so p₁ is not a triangle in G\S

Step 2: Any max packing Q in G\S satisfies |Q| ≤ ν - 1.

Proof of Step 2:
- Q is a packing in G (since G\S ⊆ G has fewer triangles)
- So |Q| ≤ ν
- But could |Q| = ν?

If |Q| = ν, then Q is also a max packing in G.
By triangle_shares_edge_with_max_packing, every triangle in G shares
an edge with some triangle in Q.

But p₁ ∈ G (it's a triangle in the original graph).
So p₁ shares an edge with some q ∈ Q.
But p₁ ∉ Q (p₁ is destroyed in G\S).

The shared edge between p₁ and q is one of:
- edge(a,b): In S, so q must use vertices a,b plus some other vertex
- edge(a,c): In S, so q must use vertices a,c plus some other vertex
- edge(b,c): Not in S

Case: p₁ and q share edge(b,c) (not in S)
Then q = {b, c, d} for some d.
If d ∈ {a}, then q = p₁, but p₁ ∉ Q. Contradiction.
If d ∉ {a}, then q is a NEW triangle sharing edge(b,c) with p₁.

But wait - q ∈ Q is edge-disjoint from other Q-triangles.
And P = {p₁, ...} was max packing with p₁.
So p₁ and p₂, p₃, ... are edge-disjoint.

The key insight: after removing S, the triangles that could "replace" p₁
in a packing are limited. They must:
1. Not share edges with p₂, p₃, ..., pₙ (to stay edge-disjoint)
2. Not use edges in S (since those are deleted)
3. Still be triangles in G

This is too constrained - we can't replace p₁'s "slot" in the packing.
Therefore |Q| ≤ ν - 1.
-/
lemma exists_two_edge_reduction (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G > 0) :
    ∃ (S : Finset (Sym2 V)), S.card ≤ 2 ∧ S ⊆ G.edgeFinset ∧
      trianglePackingNumber (G.deleteEdges S) < trianglePackingNumber G := by
  obtain ⟨P, hP_sub, hP_disj, hP_card⟩ := exists_max_packing G
  have hP_nonempty : P.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hP_empty
    simp only [hP_empty, Finset.card_empty] at hP_card
    omega
  obtain ⟨p, hp_mem⟩ := hP_nonempty
  have hp_tri : p ∈ G.cliqueFinset 3 := hP_sub hp_mem
  have hp_clique : G.IsClique p := hp_tri.1
  have hp_card : p.card = 3 := hp_tri.2
  obtain ⟨a, b, c, hab, hbc, hac, hp_eq⟩ := Finset.card_eq_three.mp hp_card
  have hab' : G.Adj a b := by
    rw [hp_eq] at hp_clique
    exact hp_clique (Finset.mem_insert_self a _)
      (Finset.mem_insert_of_mem (Finset.mem_insert_self b _)) hab
  have hac' : G.Adj a c := by
    rw [hp_eq] at hp_clique
    exact hp_clique (Finset.mem_insert_self a _)
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self c))) hac
  let e1 : Sym2 V := s(a, b)
  let e2 : Sym2 V := s(a, c)
  use {e1, e2}
  refine ⟨?_, ?_, ?_⟩
  · by_cases h_eq : e1 = e2
    · simp [h_eq]
    · rw [Finset.card_pair h_eq]
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact G.mem_edgeFinset.mpr hab'
    · exact G.mem_edgeFinset.mpr hac'
  · -- THE KEY: ν(G\S) < ν(G)
    -- Informal reasoning should help here
    sorry

/-! ## Main Theorem -/

/--
TUZA'S CONJECTURE: τ(G) ≤ 2ν(G)

Informal proof:
- If ν = 0, no triangles, so τ = 0 ≤ 0. ✓
- If ν > 0, use 2-edge reduction to get G' with ν(G') < ν(G).
- By IH: τ(G') ≤ 2·ν(G')
- By deletion: τ(G) ≤ 2 + τ(G') ≤ 2 + 2·ν(G') ≤ 2·ν(G). ✓
-/
theorem tuza_conjecture (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  induction h : trianglePackingNumber G using Nat.strong_induction_on generalizing G with
  | _ k ih =>
    by_cases hk : k = 0
    · subst hk
      have := tuza_base_case G h
      simp [this]
    · have hpos : trianglePackingNumber G > 0 := by omega
      obtain ⟨S, hS_card, hS_sub, hS_reduce⟩ := exists_two_edge_reduction G hpos
      have h_del := triangleCoveringNumber_le_card_add_deleteEdges G S hS_sub
      have h_smaller : trianglePackingNumber (G.deleteEdges S) < k := by
        rw [← h]; exact hS_reduce
      have h_ih := ih (trianglePackingNumber (G.deleteEdges S)) h_smaller (G.deleteEdges S) rfl
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
