/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bb81e3dc-f448-4d09-8403-56cf1adca6b7

The following was proved by Aristotle:

- theorem tuza_conjecture_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G
-/

/-
Tuza's Conjecture: τ(T_e) ≤ 2 for PACKING elements

CRITICAL CORRECTION: Previous submission asked about arbitrary triangles.
The flowerGraph counterexample showed τ(T_e) = 3 for the central triangle,
but that triangle is NOT in the maximum packing!

For actual packing elements in flowerGraph:
- M = {{0,1,3}, {1,2,4}, {0,2,5}} with ν = 3
- τ(T_{0,1,3}) = 1 (shares edge {0,1} with {0,1,2})
- τ(T_{1,2,4}) = 1 (shares edge {1,2} with {0,1,2})
- τ(T_{0,2,5}) = 1 (shares edge {0,2} with {0,1,2})

This is what Parker (arXiv:2406.06501) actually proves for ν ≤ 3.
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Edge set of a triangle
def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun p => Sym2.mk p)

-- Two triangles share an edge
def sharesEdge (t1 t2 : Finset V) : Prop :=
  ¬Disjoint (triangleEdges t1) (triangleEdges t2)

-- Edge-disjoint family
def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

-- Triangle packing number
noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter IsEdgeDisjoint).sup Finset.card

-- Maximum packing predicate
def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M ∧ M.card = trianglePackingNumber G

-- T_e: triangles sharing an edge with e
def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => sharesEdge t e)

-- S_e: triangles sharing edge ONLY with e (not other packing elements)
def S_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ f ∈ M, f ≠ e → ¬sharesEdge t f)

-- Triangle covering predicate
def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset (Sym2 V)) : Prop :=
  C ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) C

-- Covering number for a subset of triangles
noncomputable def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : ℕ :=
  (G.edgeFinset.powerset.filter (fun C =>
    ∀ t ∈ S, ¬Disjoint (triangleEdges t) C)).image Finset.card |>.min |>.getD 0

-- Global covering number
noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  coveringNumberOn G (G.cliqueFinset 3)

/- Aristotle failed to find a proof. -/
/-
MAIN LEMMA: For e in a maximum packing M with |M| ≤ 3, τ(T_e) ≤ 2

This is the CORRECTED version that applies to packing elements only.
-/
lemma tau_Te_le_2_for_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

/-
Corollary: Tuza's conjecture for ν ≤ 3
Using induction: τ(G) ≤ τ(T_e) + τ(G \ T_e) ≤ 2 + 2(ν-1) = 2ν
-/
theorem tuza_conjecture_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G ≤ 3) :
    triangleCoveringNumber G ≤ 2 * trianglePackingNumber G := by
  -- By definition of trianglePackingNumber, there exists a maximum packing M with |M| = trianglePackingNumber G.
  obtain ⟨M, hM_max, hM_card⟩ : ∃ M : Finset (Finset V), IsMaxPacking G M ∧ M.card = trianglePackingNumber G := by
    -- By definition of supremum, there exists a subset $M$ of the cliqueFinset 3 such that $M$ is edge-disjoint and has cardinality equal to the trianglePackingNumber G.
    obtain ⟨M, hM⟩ : ∃ M : Finset (Finset V), M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M ∧ M.card = trianglePackingNumber G := by
      have h_max_packing : ∃ M ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint, ∀ N ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint, M.card ≥ N.card := by
        exact Finset.exists_max_image _ _ ⟨ ∅, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.empty_subset _ ), by simp +decide [ IsEdgeDisjoint ] ⟩ ⟩;
      obtain ⟨ M, hM₁, hM₂ ⟩ := h_max_packing;
      refine' ⟨ M, Finset.mem_powerset.mp ( Finset.mem_filter.mp hM₁ |>.1 ), Finset.mem_filter.mp hM₁ |>.2, le_antisymm _ _ ⟩;
      · exact Finset.le_sup ( f := Finset.card ) hM₁;
      · exact Finset.sup_le fun N hN => hM₂ N hN;
    unfold IsMaxPacking; aesop;
  have h_tau_Te : ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
    exact fun e he => tau_Te_le_2_for_packing G M hM_max ( by linarith ) e he;
  -- By definition of $T_e$, we know that every triangle in $G$ is either in $T_e$ for some $e \in M$ or in $G \setminus T_e$.
  have h_union : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ M, t ∈ T_e G e := by
    intro t ht
    by_contra h_contra;
    -- If $t$ is not in any $T_e$ for $e \in M$, then $M \cup \{t\}$ is also a packing, contradicting the maximality of $M$.
    have h_union_packing : IsEdgeDisjoint (M ∪ {t}) := by
      intro e he f hf hne;
      cases' Finset.mem_union.mp he with he he <;> cases' Finset.mem_union.mp hf with hf hf <;> simp_all +decide [ Finset.disjoint_left ];
      · have := hM_max.2.1 he hf hne; simp_all +decide [ Finset.disjoint_left, IsEdgeDisjoint ] ;
      · intro a ha hb; specialize h_contra e he; unfold T_e at h_contra; simp_all +decide [ Finset.disjoint_left ] ;
        exact h_contra ( by rw [ sharesEdge ] ; exact Finset.not_disjoint_iff.mpr ⟨ a, hb, ha ⟩ );
      · intro a ha hb; specialize h_contra f hf; unfold T_e at h_contra; simp_all +decide [ Finset.disjoint_left ] ;
        exact h_contra ( Finset.not_disjoint_iff.mpr ⟨ a, ha, hb ⟩ );
    have h_union_packing_card : (M ∪ {t}).card > M.card := by
      simp +zetaDelta at *;
      rw [ Finset.card_insert_of_notMem ] ; aesop;
      intro h; specialize h_contra t h; simp_all +decide [ T_e ] ;
      unfold sharesEdge at h_contra; simp_all +decide [ Finset.disjoint_left ] ;
      unfold triangleEdges at h_contra; simp_all +decide [ Finset.ext_iff ] ;
      rcases Finset.card_eq_three.mp ht.2 with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; specialize h_contra ( Sym2.mk ( x, y ) ) x y ; aesop;
    have h_union_packing_card : (M ∪ {t}).card ≤ trianglePackingNumber G := by
      refine' Finset.le_sup ( f := Finset.card ) _;
      simp_all +decide [ Finset.subset_iff ];
      exact fun x hx => by have := hM_max.1 hx; aesop;
    linarith;
  have h_covering_union : ∀ S : Finset (Finset V), (∀ t ∈ S, ∃ e ∈ M, t ∈ T_e G e) → coveringNumberOn G S ≤ ∑ e ∈ M, coveringNumberOn G (T_e G e) := by
    intros S hS_union
    have h_covering_union : ∀ e ∈ M, ∃ C_e : Finset (Sym2 V), C_e ⊆ G.edgeFinset ∧ (∀ t ∈ T_e G e, ¬Disjoint (triangleEdges t) C_e) ∧ C_e.card ≤ coveringNumberOn G (T_e G e) := by
      intro e he;
      have h_covering_Te : ∃ C_e ∈ Finset.powerset (G.edgeFinset), (∀ t ∈ T_e G e, ¬Disjoint (triangleEdges t) C_e) ∧ C_e.card = coveringNumberOn G (T_e G e) := by
        have h_covering_Te : ∃ C_e ∈ Finset.powerset (G.edgeFinset), (∀ t ∈ T_e G e, ¬Disjoint (triangleEdges t) C_e) ∧ C_e.card = (Finset.image Finset.card (Finset.filter (fun C => ∀ t ∈ T_e G e, ¬Disjoint (triangleEdges t) C) (G.edgeFinset.powerset))).min := by
          have h_covering_Te : ∃ C_e ∈ Finset.filter (fun C => ∀ t ∈ T_e G e, ¬Disjoint (triangleEdges t) C) (G.edgeFinset.powerset), ∀ C ∈ Finset.filter (fun C => ∀ t ∈ T_e G e, ¬Disjoint (triangleEdges t) C) (G.edgeFinset.powerset), C_e.card ≤ C.card := by
            apply_rules [ Finset.exists_min_image ];
            refine' ⟨ G.edgeFinset, _ ⟩ ; simp +decide [ Finset.disjoint_left ];
            simp +decide [ T_e, triangleEdges ];
            intro t ht hte
            obtain ⟨a, b, hab⟩ : ∃ a b : V, a ∈ t ∧ b ∈ t ∧ a ≠ b ∧ G.Adj a b := by
              have := Finset.card_eq_three.mp ht.2;
              rcases this with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            exact ⟨ Sym2.mk ( a, b ), ⟨ a, b, ⟨ hab.1, hab.2.1, hab.2.2.1 ⟩, rfl ⟩, by simpa [ Sym2.eq_swap ] using hab.2.2.2 ⟩;
          obtain ⟨ C_e, hC_e₁, hC_e₂ ⟩ := h_covering_Te;
          refine' ⟨ C_e, _, _, _ ⟩ <;> simp_all +decide [ Finset.min ];
          refine' le_antisymm _ _;
          · exact Finset.le_inf fun C hC => Nat.cast_le.mpr ( hC_e₂ C ( by simpa using Finset.mem_powerset.mp ( Finset.mem_filter.mp hC |>.1 ) ) ( Finset.mem_filter.mp hC |>.2 ) );
          · exact Finset.inf_le ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( fun x hx => by simpa using hC_e₁.1 hx ), hC_e₁.2 ⟩ );
        convert h_covering_Te using 1;
        simp +decide [ coveringNumberOn ];
        cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun C => ∀ t ∈ T_e G e, ¬Disjoint ( triangleEdges t ) C ) ( G.edgeFinset.powerset ) ) ) <;> aesop;
      exact ⟨ h_covering_Te.choose, Finset.mem_powerset.mp h_covering_Te.choose_spec.1, h_covering_Te.choose_spec.2.1, h_covering_Te.choose_spec.2.2.le ⟩;
    choose! C hC₁ hC₂ hC₃ using h_covering_union;
    have h_covering_union : ∀ t ∈ S, ¬Disjoint (triangleEdges t) (Finset.biUnion M C) := by
      intro t ht; obtain ⟨ e, he₁, he₂ ⟩ := hS_union t ht; specialize hC₂ e he₁ t he₂; simp_all +decide [ Finset.disjoint_left ] ;
      exact ⟨ hC₂.choose, hC₂.choose_spec.1, e, he₁, hC₂.choose_spec.2 ⟩;
    have h_covering_union : coveringNumberOn G S ≤ (Finset.biUnion M C).card := by
      unfold coveringNumberOn;
      have h_covering_union : (Finset.image Finset.card ({C ∈ G.edgeFinset.powerset | ∀ t ∈ S, ¬Disjoint (triangleEdges t) C})).min ≤ (Finset.biUnion M C).card := by
        exact Finset.min_le ( Finset.mem_image.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.biUnion_subset.mpr fun e he => hC₁ e he ), h_covering_union ⟩, rfl ⟩ );
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun C => ∀ t ∈ S, ¬Disjoint ( triangleEdges t ) C ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop;
    exact h_covering_union.trans ( Finset.card_biUnion_le.trans ( Finset.sum_le_sum hC₃ ) );
  exact le_trans ( h_covering_union _ h_union ) ( le_trans ( Finset.sum_le_sum h_tau_Te ) ( by simp +decide [ mul_comm, hM_card ] ) )

end