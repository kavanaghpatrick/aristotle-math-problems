/-
TUZA'S CONJECTURE: τ(G) ≤ 2ν(G) - CORRECTED APPROACH (v6)

v5 FLAW (found by Aristotle):
  Removing "any 2 edges from any packing triangle" does NOT always decrease ν.
  Counterexample: Two triangles sharing an edge - removing the non-shared edges
  leaves the other triangle intact, so ν stays the same.

v6 FIX:
  Don't use induction on ν. Instead, DIRECTLY CONSTRUCT the cover:
  1. Get max packing P with |P| = ν
  2. For each p ∈ P, contribute 2 edges that cover all "nearby" triangles
  3. Total edges ≤ 2ν, covers all triangles, so τ ≤ 2ν

KEY LEMMA TO PROVE: `two_edges_cover_nearby`
  For each packing triangle p, we can choose 2 of its edges that hit
  ALL triangles whose only packing connection is through p.
-/

import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Definitions -/

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) S

def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (IsTriangleCovering G)).image Finset.card).min.getD G.edgeFinset.card

/-! ## Proven Lemmas -/

lemma exists_max_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
  have h_exists : ∃ P : Finset (Finset V), P ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint ∧
      ∀ Q ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint, P.card ≥ Q.card :=
    Finset.exists_max_image _ _ ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),
      by simp +decide [IsEdgeDisjoint]⟩⟩
  obtain ⟨P, hP₁, hP₂⟩ := h_exists; use P; aesop
  exact le_antisymm (Finset.le_sup (f := Finset.card) (by aesop)) (Finset.sup_le fun Q hQ => by aesop)

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
    rcases hx with rfl | hx; exact ht; exact hP_sub hx
  have ht_notin : t ∉ P := by
    intro ht_in
    have := h_all_disj t ht_in
    simp only [Finset.disjoint_self_iff_empty] at this
    unfold triangleEdges at this
    have ht_card : t.card = 3 := ht.2
    have h_nonempty : t.offDiag.Nonempty := by
      rw [Finset.offDiag_nonempty]
      obtain ⟨a, b, c, hab, hac, hbc, ht_eq⟩ := Finset.card_eq_three.mp ht_card
      exact ⟨a, b, by simp [ht_eq], by simp [ht_eq], hab⟩
    simp only [Finset.image_eq_empty] at this
    exact h_nonempty.ne_empty this
  have h_card_bigger : (insert t P).card > trianglePackingNumber G := by
    rw [Finset.card_insert_of_not_mem ht_notin, ← hP_card]; omega
  have h_card_le : (insert t P).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    apply Finset.le_sup
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h_sub', h_disj'⟩
  omega

/-! ## Key Definition: Triangles "nearby" a packing triangle -/

/--
A triangle t is "nearby" packing triangle p if:
1. t shares an edge with p
2. t shares NO edges with any OTHER packing triangle
These are the triangles that p is "responsible" for covering.
-/
def NearbyTriangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) (p : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t =>
    ¬Disjoint (triangleEdges t) (triangleEdges p) ∧
    ∀ q ∈ P, q ≠ p → Disjoint (triangleEdges t) (triangleEdges q))

/-! ## THE KEY LEMMA -/

/--
For any packing triangle p, we can find 2 of its edges that cover ALL nearby triangles.

PROOF IDEA:
- Let T1, T2, T3 be triangles sharing edges e1, e2, e3 with p (respectively)
- If one of T1, T2, T3 is empty, we can cover with 2 edges
- If all three are non-empty, pick t1 ∈ T1, t2 ∈ T2, t3 ∈ T3
- Claim: t1, t2, t3 cannot all be pairwise edge-disjoint
- Because otherwise (P \ {p}) ∪ {t1, t2, t3} would be a larger packing (contradiction)
- So at least two of them share an edge
- This constrains the structure enough that 2 edges suffice
-/
lemma two_edges_cover_nearby (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) (hP_sub : P ⊆ G.cliqueFinset 3) (hP_disj : IsEdgeDisjoint P)
    (hP_max : P.card = trianglePackingNumber G)
    (p : Finset V) (hp : p ∈ P) :
    ∃ e1 e2 : Sym2 V, e1 ∈ triangleEdges p ∧ e2 ∈ triangleEdges p ∧
    ∀ t ∈ NearbyTriangles G P p, ¬Disjoint (triangleEdges t) {e1, e2} := by
  sorry

/-! ## Main Theorem -/

/--
TUZA'S CONJECTURE: τ(G) ≤ 2ν(G)

PROOF:
1. Get max packing P with |P| = ν
2. For each p ∈ P, use two_edges_cover_nearby to get 2 edges
3. Collect all these edges into S with |S| ≤ 2|P| = 2ν
4. S covers all triangles:
   - Every triangle t shares edge with some p ∈ P (triangle_shares_edge_with_max_packing)
   - Either t shares edge with multiple p's, or t is "nearby" exactly one p
   - If nearby p, then p's 2 edges cover t
   - If shares with multiple, then one of them covers t
5. So τ ≤ |S| ≤ 2ν
-/
theorem tuza_conjecture (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  -- Get max packing
  obtain ⟨P, hP_sub, hP_disj, hP_card⟩ := exists_max_packing G
  -- For each p ∈ P, get 2 covering edges
  -- Build cover S as union of these edges
  -- Show S covers all triangles
  -- Conclude τ ≤ |S| ≤ 2|P| = 2ν
  sorry

end
