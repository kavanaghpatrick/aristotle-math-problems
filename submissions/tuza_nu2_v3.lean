/-
TUZA ν=2 VERSION 3: With ν=1 Template for Pattern Matching

=== STRATEGY ===
The ν=1 proof uses: "If two triangles are edge-disjoint → ν≥2 → contradiction"
The ν=2 proof needs: "If THREE triangles are pairwise edge-disjoint → ν≥3 → contradiction"

We include packing_one_implies_intersect (with FULL proof) as a TEMPLATE.
The AI should recognize the pattern and apply it to the ν=2 case.

=== LEMMA DEPENDENCY ORDER ===
1. packing_one_implies_intersect [TEMPLATE - full proof included]
2. packing_two_implies_third_intersects [KEY INTERMEDIATE - uses same pattern]
3. vertex_disjoint_unique_packing [TARGET - uses #2]
4. All other proven lemmas from v1
5. Final targets

=== YOUR PROVEN WORK (from v1) ===
- packing_two_triangles
- shared_vertices_implies_shared_edge
- vertex_disjoint_blocking
- blocking_implies_nu_decrease (GENERAL tool)
- exists_two_edge_reduction_nu_2
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

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset (Finset V)) : Prop :=
  P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P

def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset (Finset V)) : Prop :=
  IsTrianglePacking G P ∧ P.card = trianglePackingNumber G

def maxPackings (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset (Finset V)) :=
  (G.cliqueFinset 3).powerset.filter (fun P => IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G)

def BlocksAllMaxPackings (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  ∀ P ∈ maxPackings G, ∃ t ∈ P, ¬ Disjoint (triangleEdges t) S

def blockingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.edgeFinset.powerset.filter (BlocksAllMaxPackings G)).image Finset.card
    |>.min.getD G.edgeFinset.card

/-! ## SECTION 1: THE ν=1 TEMPLATE (FULL PROOF INCLUDED)

This lemma shows the KEY PATTERN:
- When ν = k, any (k+1) triangles cannot ALL be pairwise edge-disjoint
- Proof: If they were, we'd have ν ≥ k+1, contradiction

For ν=1: Any TWO triangles must share an edge
For ν=2: Any THREE triangles must have at least one pair sharing an edge
-/

/-- TEMPLATE LEMMA: When ν=1, any two triangles share an edge.

    PROOF PATTERN (use this for ν=2):
    - Assume t1, t2 are edge-disjoint (for contradiction)
    - Then {t1, t2} is an edge-disjoint packing of size 2
    - This means ν ≥ 2
    - Contradiction with ν = 1
-/
lemma packing_one_implies_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) (t1 t2 : Finset V)
    (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  -- This is the FULL proof from the ν=1 case
  contrapose! h
  refine' ne_of_gt (lt_of_lt_of_le _ (Finset.le_sup <| Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr <| Finset.insert_subset_iff.mpr ⟨h1, Finset.singleton_subset_iff.mpr h2⟩, _⟩))
  · rw [Finset.card_pair]; aesop
    unfold triangleEdges at h; aesop
    simp_all +decide [Finset.ext_iff]
    have := Finset.card_eq_three.mp h2.2; obtain ⟨a, b, c, ha, hb, hc, hab, hbc, hac⟩ := this; specialize h a b; aesop
  · intro x hx y hy hxy; aesop
    exact h.symm

/-! ## SECTION 2: KEY INTERMEDIATE LEMMA (NEW TARGET)

Apply the SAME pattern as packing_one_implies_intersect, but for ν=2:
- When ν=2, any THREE triangles cannot ALL be pairwise edge-disjoint
-/

/-- KEY INTERMEDIATE: When ν=2, given three triangles, at least two share an edge.

    PROOF STRATEGY (same as ν=1 template):
    - Assume t1, t2, t3 are pairwise edge-disjoint (for contradiction)
    - Then {t1, t2, t3} is an edge-disjoint packing of size 3
    - This means ν ≥ 3
    - Contradiction with ν = 2

    This is the DIRECT GENERALIZATION of packing_one_implies_intersect.
-/
lemma packing_two_implies_third_intersects (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (t1 t2 t3 : Finset V)
    (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) (h3 : t3 ∈ G.cliqueFinset 3)
    (h12 : Disjoint (triangleEdges t1) (triangleEdges t2)) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t3) ∨
    ¬ Disjoint (triangleEdges t2) (triangleEdges t3) := by
  -- Same pattern as packing_one_implies_intersect:
  -- If both were disjoint, {t1,t2,t3} would give ν≥3
  sorry

/-- Alternative formulation: If t3 is edge-disjoint from BOTH t1 and t2, then ν≥3 -/
lemma third_disjoint_implies_nu_ge_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (t1 t2 t3 : Finset V)
    (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) (h3 : t3 ∈ G.cliqueFinset 3)
    (h12 : Disjoint (triangleEdges t1) (triangleEdges t2))
    (h13 : Disjoint (triangleEdges t1) (triangleEdges t3))
    (h23 : Disjoint (triangleEdges t2) (triangleEdges t3)) :
    trianglePackingNumber G ≥ 3 := by
  -- {t1, t2, t3} is an edge-disjoint packing of size 3
  sorry

/-! ## SECTION 3: YOUR PROVEN LEMMAS (from v1) -/

/-- When ν=2, extract the two triangles [PROVEN] -/
lemma packing_two_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ (t1 t2 : Finset V), t1 ∈ G.cliqueFinset 3 ∧ t2 ∈ G.cliqueFinset 3 ∧
      t1 ≠ t2 ∧ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  aesop
  obtain ⟨P, hP⟩ : ∃ P : Finset (Finset V), P ∈ Finset.powerset (G.cliqueFinset 3) ∧ IsEdgeDisjoint P ∧ P.card = 2 := by
    by_contra h_contra
    have h_contra : ∀ P ∈ Finset.powerset (G.cliqueFinset 3), IsEdgeDisjoint P → P.card ≤ 1 := by
      intro P hP hP'; exact Nat.le_of_not_lt fun hP'' => h_contra ⟨P, hP, hP', by linarith [show P.card ≤ 2 from h ▸ Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨hP, hP'⟩)]⟩
    exact absurd h (ne_of_lt (lt_of_le_of_lt (Finset.sup_le fun P hP => h_contra P (Finset.mem_filter.mp hP |>.1) (Finset.mem_filter.mp hP |>.2)) (by decide)))
  rcases Finset.card_eq_two.mp hP.2.2 with ⟨t1, t2, ht1, ht2, h⟩; use t1, ?_, t2, ?_, ?_, ?_ <;> aesop
  · exact Finset.mem_filter.mp (left (Finset.mem_insert_self _ _)) |>.2
  · simp_all +decide [Finset.insert_subset_iff]

/-- Two triangles sharing ≥2 vertices share an edge [PROVEN] -/
lemma shared_vertices_implies_shared_edge (t1 t2 : Finset V)
    (h1 : t1.card = 3) (h2 : t2.card = 3) (h_inter : 2 ≤ (t1 ∩ t2).card) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  bound
  obtain ⟨v1, v2, hv1, hv2⟩ : ∃ v1 v2 : V, v1 ∈ t1 ∧ v2 ∈ t1 ∧ v1 ≠ v2 ∧ v1 ∈ t2 ∧ v2 ∈ t2 := by
    have := Finset.one_lt_card.1 (lt_of_lt_of_le (by decide) h_inter); aesop
  exact Finset.disjoint_left.mp a (Finset.mem_image.mpr ⟨(v1, v2), by aesop⟩) (Finset.mem_image.mpr ⟨(v1, v2), by aesop⟩)

/-- Blocking all max packings → ν decreases [PROVEN - GENERAL TOOL] -/
lemma blocking_implies_nu_decrease (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset)
    (h_blocks : BlocksAllMaxPackings G S) :
    trianglePackingNumber (G.deleteEdges S) < trianglePackingNumber G := by
  refine' Nat.lt_of_le_of_lt (Finset.sup_le _) _
  exact trianglePackingNumber G - 1
  · intro b hb
    have h_b_max_packing : b.card ≤ trianglePackingNumber G := by
      refine' Finset.le_sup (f := Finset.card) _
      aesop
      intro t ht; specialize left ht; aesop
      rw [SimpleGraph.isNClique_iff] at *; aesop
      intro x hx y hy hxy; specialize left hx hy hxy; aesop
    cases lt_or_eq_of_le h_b_max_packing <;> aesop
    · exact Nat.le_sub_one_of_lt h
    · have := h_blocks b ?_ <;> simp_all +decide [Finset.subset_iff]
      · obtain ⟨t, ht₁, ht₂⟩ := this; specialize left ht₁; simp_all +decide [SimpleGraph.isNClique_iff]
        rw [Finset.disjoint_left] at ht₂; aesop
        unfold triangleEdges at left_1; aesop
        have := left left_1 left_2; simp_all +decide [SimpleGraph.deleteEdges]
      · unfold maxPackings; aesop
        intro x hx; specialize left hx; rw [SimpleGraph.isNClique_iff] at left; aesop
        rw [SimpleGraph.isNClique_iff]; aesop
        intro u hu v hv huv; specialize left hu hv; aesop
  · contrapose! h_blocks
    rcases n : trianglePackingNumber G with (_ | _ | n) <;> simp_all +decide
    unfold BlocksAllMaxPackings
    unfold maxPackings
    simp +decide [n, IsEdgeDisjoint]

/-! ## SECTION 4: TARGET LEMMAS -/

/-- THE CRITICAL LEMMA: Vertex-disjoint triangles form UNIQUE max packing.

    PROOF using packing_two_implies_third_intersects:
    - Let P be any max packing with |P| = 2, containing s1, s2
    - If s1 ∉ {t1, t2}, then s1 is a third triangle
    - Since t1, t2 are vertex-disjoint (hence edge-disjoint),
      by packing_two_implies_third_intersects, s1 shares edge with t1 or t2
    - But s1 is in a max packing with s2, so edge-disjoint from s2
    - If s1 shares edge with t1, and s2 is edge-disjoint from s1...
    - Case analysis shows P must be {t1, t2}
-/
lemma vertex_disjoint_unique_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (hne : t1 ≠ t2) (h_edge_disj : Disjoint (triangleEdges t1) (triangleEdges t2))
    (h_vertex_disj : Disjoint t1 t2) :
    maxPackings G = {{t1, t2}} := by
  -- Use packing_two_implies_third_intersects to show any other triangle
  -- must share an edge with t1 or t2, hence can't form a different max packing
  sorry

/-- For vertex-disjoint case: edges block all max packings [PROVEN - uses unique_packing] -/
lemma vertex_disjoint_blocking (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2)
    (t1 t2 : Finset V) (ht1 : t1 ∈ G.cliqueFinset 3) (ht2 : t2 ∈ G.cliqueFinset 3)
    (h_vertex_disj : Disjoint t1 t2)
    (e1 e2 : Sym2 V) (he1 : e1 ∈ triangleEdges t1) (he2 : e2 ∈ triangleEdges t2) :
    BlocksAllMaxPackings G {e1, e2} := by
  have h_unique : maxPackings G = {{t1, t2}} := by
    apply vertex_disjoint_unique_packing G h t1 t2 ht1 ht2
    · aesop
    · unfold triangleEdges; aesop
      simp_all +decide [Finset.disjoint_left, Sym2.forall]
      grind
    · assumption
  unfold BlocksAllMaxPackings; aesop

/-! ## SECTION 5: BOWTIE CASE AND FINAL THEOREM -/

/-- When ν(G) = 2, blocking number ≤ 2 -/
theorem blocking_number_le_2_when_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    blockingNumber G ≤ 2 := by
  obtain ⟨t1, t2, ht1, ht2, hne, h_edge_disj⟩ := packing_two_triangles G h
  by_cases h_vertex_disj : Disjoint t1 t2
  · -- Case 1: Vertex-disjoint → use vertex_disjoint_blocking
    sorry
  · -- Case 2: Share vertex(es) → bowtie structure
    -- By shared_vertices_implies_shared_edge, if share ≥2 vertices, share edge
    -- So they share exactly 1 vertex (bowtie)
    sorry

/-- THE REDUCTION LEMMA FOR ν=2 [builds on blocking_number_le_2] -/
theorem exists_two_edge_reduction_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 2) :
    ∃ (S : Finset (Sym2 V)), S.card ≤ 2 ∧ S ⊆ G.edgeFinset ∧
      trianglePackingNumber (G.deleteEdges S) < 2 := by
  have h_block := blocking_number_le_2_when_nu_2 G h
  obtain ⟨S, hS⟩ : ∃ S : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ BlocksAllMaxPackings G S ∧ S.card = blockingNumber G := by
    unfold blockingNumber
    have h_exists_S : Finset.Nonempty (Finset.filter (BlocksAllMaxPackings G) G.edgeFinset.powerset) := by
      refine' ⟨G.edgeFinset, _⟩; simp +decide [BlocksAllMaxPackings]
      intro P hP
      obtain ⟨t, ht⟩ : ∃ t ∈ P, t ∈ G.cliqueFinset 3 := by
        unfold maxPackings at hP; aesop
        exact Exists.elim (Finset.card_pos.mp (by linarith)) fun t ht => ⟨t, ht, by simpa using left ht⟩
      simp_all +decide [Finset.disjoint_left, SimpleGraph.cliqueFinset]
      rcases ht.2 with ⟨ht₁, ht₂⟩
      rcases Finset.card_eq_three.mp ht₂ with ⟨x, y, z, hx, hy, hz, hxyz⟩; use t, ht.1; use s(x, y); simp_all +decide [SimpleGraph.isNClique_iff]
      exact Finset.mem_image.mpr ⟨(x, y), by aesop⟩
    have := Finset.min_of_mem (Finset.mem_image_of_mem Finset.card h_exists_S.choose_spec)
    cases' this with b hb; have := Finset.mem_of_min hb; aesop
  exact ⟨S, hS.2.2.symm ▸ h_block, hS.1, by linarith [blocking_implies_nu_decrease G S hS.1 hS.2.1]⟩

end
