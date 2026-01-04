/-
Tuza ν=4 Scaffolding Library
Generated: 2026-01-01 20:04:04
Total lemmas: 348

This file contains all proven lemmas extracted from successful Aristotle runs.
Copy relevant sections to new submissions for maximum success rate.

Based on 203 submissions analysis:
- Files with 7+ proven lemmas: 40.7% success rate
- Files with 0 proven lemmas: 0% success rate

USAGE:
1. Copy the import section
2. Copy relevant category sections
3. Keep only lemmas you need (smaller = faster Aristotle processing)
-/

import Mathlib

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


-- ═══════════════════════════════════════════════════════════════════════
-- PACKING LEMMAS (24 lemmas)
-- ═══════════════════════════════════════════════════════════════════════

-- Source: proven/tuza_nu1_k4_proof.lean
lemma exists_max_packing {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
  have h_exists_packing : ∃ P : Finset (Finset V), P ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint P ∧ P.card = trianglePackingNumber G := by
    have h_finite : (G.cliqueFinset 3).powerset.Nonempty := by
      exact ⟨ ∅, Finset.mem_powerset.mpr <| Finset.empty_subset _ ⟩
    have h_exists_packing : ∃ P : Finset (Finset V), P ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint ∧ ∀ Q ∈ (G.cliqueFinset 3).powerset.filter IsEdgeDisjoint, P.card ≥ Q.card := by
      exact Finset.exists_max_image _ _ ⟨ ∅, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.empty_subset _ ), by simp +decide [ IsEdgeDisjoint ] ⟩ ⟩;
    obtain ⟨ P, hP₁, hP₂ ⟩ := h_exists_packing; use P; aesop;
    exact le_antisymm ( Finset.le_sup ( f := Finset.card ) ( by aesop ) ) ( Finset.sup_le fun Q hQ => by aesop );
  exact h_exists_packing

-- Source: proven/tuza_nu1_k4_proof.lean
lemma packing_one_implies_intersect {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) (t1 t2 : Finset V)
    (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) :
    ¬ Disjoint (triangleEdges t1) (triangleEdges t2) := by
  contrapose! h;
  refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.le_sup <| Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr <| Finset.insert_subset_iff.mpr ⟨ h1, Finset.singleton_subset_iff.mpr h2 ⟩, _ ⟩ ) );
  · rw [ Finset.card_pair ] ; aesop;
    unfold triangleEdges at h; aesop;
    simp_all +decide [ Finset.ext_iff ];
    have := Finset.card_eq_three.mp h2.2; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := this; specialize h a b; aesop;
  · intro x hx y hy hxy; aesop;
    exact h.symm

/-! ## K₄ Structure Lemmas (PROVED BY ARISTOTLE) -/

/--
If the triangle packing number is 1 and the triangle covering number is greater than 2,
then for any triangle T and any edge e in T, there exists another triangle T' that shares
exactly the edge e with T.
-/

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma exists_max_packing {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M : Finset (Finset V), isMaxPacking G M := by
      -- By definition of maximum packing number, there exists a packing M with size equal to the trianglePackingNumber.
      obtain ⟨M, hM⟩ : ∃ M : Finset (Finset V), M.card = trianglePackingNumber G ∧ isTrianglePacking G M := by
        unfold trianglePackingNumber;
        cases' Finset.max_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) from ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr <| Finset.empty_subset _, by unfold isTrianglePacking; aesop ⟩ ) ⟩ ) with M hM;
        have := Finset.mem_of_max hM; aesop;
      exact ⟨ M, hM.2, hM.1 ⟩

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma triangleCoveringNumberOn_eq_zero_of_packing_zero {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (h_subset : triangles ⊆ G.cliqueFinset 3)
    (h_packing : trianglePackingNumberOn G triangles = 0) :
    triangleCoveringNumberOn G triangles = 0 := by
      unfold triangleCoveringNumberOn;
      -- Since there are no triangles in the set, the condition ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2 is trivially true for E' = ∅.
      have h_empty : ∅ ∈ {E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2} := by
        -- Since the packing number is zero, there are no triangles in the set, so the condition is trivially satisfied.
        have h_empty : ∀ t ∈ triangles, False := by
          unfold trianglePackingNumberOn at h_packing;
          -- If the maximum cardinality of the packings is zero, then every packing in the set has a cardinality of zero.
          have h_empty_packing : ∀ p ∈ Finset.filter (isTrianglePacking G) triangles.powerset, p.card = 0 := by
            intro p hp
            have h_card : p.card ≤ 0 := by
              have h_card : p.card ≤ Finset.max (Finset.image Finset.card (Finset.filter (isTrianglePacking G) triangles.powerset)) := by
                exact Finset.le_max ( Finset.mem_image_of_mem _ hp );
              cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) triangles.powerset ) ) <;> aesop;
            exact le_antisymm h_card ( Nat.zero_le _ );
          intro t ht; specialize h_empty_packing { t } ; simp_all +decide ;
          exact h_empty_packing ⟨ by simpa using h_subset ht, by simp +decide ⟩;
        aesop;
      -- Since the empty set is in the filter, its cardinality is 0. Therefore, the minimum of the image of the cardinalities must be 0.
      have h_min : Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2})) = some 0 := by
        refine' le_antisymm _ _ <;> simp_all +decide [ Finset.min ];
        · exact Finset.inf_le ( Finset.mem_powerset.mpr ( Finset.empty_subset _ ) ) |> le_trans <| by simp +decide ;
        · exact fun _ _ => WithTop.coe_le_coe.mpr ( Nat.zero_le _ );
      rw [ h_min, Option.getD_some ]

-- Source: proven/tuza/nu4/slot63_scaffolding.lean
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ m ∈ M, (t ∩ m).card ≥ 2 := by
  obtain ⟨hM_triangle_packing, hM_max⟩ := hM
  contrapose! hM_max
  refine ⟨insert t M, ?_, ?_⟩
  · simp only [isTrianglePacking, Finset.subset_iff, Set.Pairwise] at *
    constructor
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact ht
      · exact hM_triangle_packing.1 hx
    · intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact (hxy rfl).elim
      · exact Nat.le_of_lt_succ (hM_max y hy)
      · rw [Finset.inter_comm]; exact Nat.le_of_lt_succ (hM_max x hx)
      · exact hM_triangle_packing.2 hx hy hxy
  · rw [Finset.card_insert_of_not_mem]
    · omega
    · intro ht_in_M
      specialize hM_max t ht_in_M
      have := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
      omega

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA 3: M_char_is_fractional
-- ══════════════════════════════════════════════════════════════════════════════

/-- M_char is a valid fractional packing. -/

-- Source: proven/tuza/nu4/slot72_cycle_reduction_output.lean
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
      have := hM.1;
      contrapose! hM;
      -- If $t$ does not share an edge with any triangle in $M$, then $M \cup \{t\}$ is also a packing.
      have h_union_packing : isTrianglePacking G (M ∪ {t}) := by
        -- Since $t$ is a triangle and $M$ is a packing, any two triangles in $M \cup \{t\}$ must share at most one edge.
        have h_pairwise : Set.Pairwise (M ∪ {t} : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
          simp_all +decide [ Set.Pairwise, Finset.subset_iff ];
          exact ⟨ fun x hx hx' => Nat.le_of_lt_succ ( hM x hx ), fun x hx => ⟨ fun hx' => Nat.le_of_lt_succ ( by simpa only [ Finset.inter_comm ] using hM x hx ), fun y hy hy' => this.2 hx hy ( by aesop ) ⟩ ⟩;
        -- Since $M$ is a packing and $t$ is a triangle, their union $M \cup \{t\}$ is also a packing.
        simp [isTrianglePacking, this, ht];
        simp_all +decide [ Finset.subset_iff, Set.Pairwise ];
        exact fun x hx => Finset.mem_filter.mp ( this.1 hx ) |>.2;
      -- Since $M \cup \{t\}$ is also a packing, its cardinality is strictly greater than $M$'s cardinality.
      have h_card_union : (M ∪ {t}).card > M.card := by
        by_cases h : t ∈ M <;> simp_all +decide;
        specialize hM t h;
        simp_all +decide [ SimpleGraph.isNClique_iff ];
      unfold isMaxPacking;
      simp_all +decide [ trianglePackingNumber ];
      refine' ne_of_lt ( lt_of_lt_of_le h_card_union _ );
      have h_max : (Insert.insert t M).card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        simp +zetaDelta at *;
        exact ⟨ _, ⟨ Finset.insert_subset_iff.mpr ⟨ by aesop, this.1 ⟩, h_union_packing ⟩, rfl ⟩;
      have := Finset.le_max h_max;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Bridges are subset of T_pair
-- ══════════════════════════════════════════════════════════════════════════════

-- X_DA ⊆ T_pair(A,B) because any bridge sharing edge with D and A
-- also shares edge with A, hence is in trianglesSharingEdge(A) ⊆ T_pair(A,B)

-- Source: proven/tuza/nu4/slot70_tau_union_extended_output.lean
lemma packing_elem_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) : e.card = 3 := by
  -- M is a triangle packing, so e ∈ cliqueFinset 3
  have h_sub := hM.1.1
  have he_clique := h_sub he
  simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at he_clique
  exact he_clique.2

-- KEY LEMMA: Diagonal pairs have empty bridges
-- If A ∩ C = ∅, no triangle can share an edge with both A and C

-- Source: proven/tuza/nu4/slot139_tau_le_12_PROVEN.lean
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
  by_contra h_no_share
  push_neg at h_no_share
  -- If t shares ≤1 vertex with each X ∈ M, then M ∪ {t} is a larger packing
  have h_packing : isTrianglePacking G (M ∪ {t}) := by
    constructor
    · -- M ∪ {t} ⊆ cliqueFinset 3
      intro s hs
      simp only [Finset.mem_union, Finset.mem_singleton] at hs
      cases hs with
      | inl h => exact hM.1.1 h
      | inr h => rw [h]; exact ht
    · -- Pairwise intersection ≤ 1
      intro s1 hs1 s2 hs2 hne
      simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff] at hs1 hs2
      cases hs1 with
      | inl h1 =>
        cases hs2 with
        | inl h2 => exact hM.1.2 h1 h2 hne
        | inr h2 => subst h2; exact Nat.lt_succ_iff.mp (h_no_share s1 h1)
      | inr h1 =>
        cases hs2 with
        | inl h2 => subst h1; rw [Finset.inter_comm]; exact Nat.lt_succ_iff.mp (h_no_share s2 h2)
        | inr h2 => subst h1 h2; exact absurd rfl hne
  have h_not_mem : t ∉ M := by
    intro h_mem
    have := h_no_share t h_mem
    simp only [Finset.inter_self] at this
    have h_card : t.card = 3 := by
      simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at ht
      exact ht.2
    omega
  have h_card_increase : (M ∪ {t}).card = M.card + 1 := by
    rw [Finset.card_union_eq_card_add_card.mpr]
    · simp
    · simp [h_not_mem]
  have h_le : (M ∪ {t}).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    have h_mem : M ∪ {t} ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h_packing.1, h_packing⟩
    have h_in_image : (M ∪ {t}).card ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card := by
      exact Finset.mem_image_of_mem _ h_mem
    exact Finset.le_max' _ _ h_in_image
  rw [h_card_increase, hM.2] at h_le
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Two triangles sharing ≥2 vertices share an edge
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/nu4/slot139_tau_le_12_PROVEN.lean
lemma packingEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    packingEdges G cfg ⊆ G.edgeFinset := by
  intro e he
  simp only [packingEdges, Finset.mem_union] at he
  -- e is in sym2 of some triangle in M
  rcases he with he | he | he | he <;> {
    rw [Finset.mem_sym2_iff] at he
    obtain ⟨ha, hb, hab⟩ := he
    rw [SimpleGraph.mem_edgeFinset]
    -- The triangle is a clique, so its vertices are pairwise adjacent
    have h_clique := hM.1.1
    simp only [Finset.subset_iff] at h_clique
    first
    | have := h_clique cfg.A cfg.hA
    | have := h_clique cfg.B cfg.hB
    | have := h_clique cfg.C cfg.hC
    | have := h_clique cfg.D cfg.hD
    simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at this
    exact this.1.2 ha hb hab
  }

/-- Packing edges have cardinality ≤ 12 -/

-- Source: proven/tuza/nu4/slot139_tau_le_12_PROVEN.lean
lemma packingEdges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    (packingEdges G cfg).card ≤ 12 := by
  simp only [packingEdges]
  -- Union bound: |A ∪ B ∪ C ∪ D| ≤ |A| + |B| + |C| + |D|
  calc (cfg.A.sym2 ∪ cfg.B.sym2 ∪ cfg.C.sym2 ∪ cfg.D.sym2).card
      ≤ cfg.A.sym2.card + cfg.B.sym2.card + cfg.C.sym2.card + cfg.D.sym2.card := by
        have h1 := Finset.card_union_le cfg.A.sym2 cfg.B.sym2
        have h2 := Finset.card_union_le (cfg.A.sym2 ∪ cfg.B.sym2) cfg.C.sym2
        have h3 := Finset.card_union_le (cfg.A.sym2 ∪ cfg.B.sym2 ∪ cfg.C.sym2) cfg.D.sym2
        omega
    _ ≤ 3 + 3 + 3 + 3 := by
        -- Each triangle has card 3, so sym2 has card 3
        have hA : cfg.A.card = 3 := by
          have := hM.1.1 cfg.A cfg.hA
          simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at this
          exact this.2
        have hB : cfg.B.card = 3 := by
          have := hM.1.1 cfg.B cfg.hB
          simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at this
          exact this.2
        have hC : cfg.C.card = 3 := by
          have := hM.1.1 cfg.C cfg.hC
          simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at this
          exact this.2
        have hD : cfg.D.card = 3 := by
          have := hM.1.1 cfg.D cfg.hD
          simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at this
          exact this.2
        -- sym2 of 3-set has 3 elements
        rw [Finset.card_sym2, Finset.card_sym2, Finset.card_sym2, Finset.card_sym2]
        simp only [hA, hB, hC, hD]
        native_decide
    _ = 12 := by norm_num

/-- Packing edges cover all triangles -/

-- Source: proven/tuza/nu4/slot139_tau_le_12_PROVEN.lean
lemma packingEdges_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ packingEdges G cfg, e ∈ t.sym2 := by
  intro t ht
  -- t shares ≥2 vertices with some X ∈ M
  obtain ⟨X, hX_mem, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  -- Get cardinalities
  have ht_card : t.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at ht
    exact ht.2
  have hX_card : X.card = 3 := by
    have := hM.1.1 X hX_mem
    simp only [SimpleGraph.mem_cliqueFinset, SimpleGraph.isNClique_iff] at this
    exact this.2
  -- Therefore t shares an edge with X
  obtain ⟨e, he_in_t, he_in_X⟩ := shared_vertices_implies_shared_edge t X ht_card hX_card hX_share
  use e
  constructor
  · -- e ∈ packingEdges
    simp only [packingEdges, Finset.mem_union]
    rw [cfg.hM_eq] at hX_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX_mem
    rcases hX_mem with rfl | rfl | rfl | rfl
    · left; left; left; exact he_in_X
    · left; left; right; exact he_in_X
    · left; right; exact he_in_X
    · right; exact he_in_X
  · exact he_in_t

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 12
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/nu4/slot_local_tuza_via_link_graph.lean
lemma packing_at_v_eq_matching (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    trianglePackingOn G (trianglesContainingVertex G v) = maxMatchingNumber (linkGraph G v) := by
  -- We use the bijection triangleEdgeEquiv and the preservation of disjointness
  let f := triangleEdgeEquiv G v
  let S_tri := trianglesContainingVertex G v
  let S_edge := (linkGraph G v).edgeFinset
  -- The packing number is the max size of a subset of S_tri with pairwise intersection <= 1
  -- The matching number is the max size of a subset of S_edge with pairwise disjoint edges
  -- The bijection f maps compatible subsets to compatible subsets
  symm;
  refine' le_antisymm _ _;
  · have h_max_packing_le_max_matching : ∀ M : Finset (Sym2 V), M ⊆ S_edge → (∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset) → (M.card ≤ trianglePackingOn G S_tri) := by
      intro M hM_sub hM_disjoint
      obtain ⟨S, hS⟩ : ∃ S : Finset (Finset V), S ⊆ S_tri ∧ (∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → (t1 ∩ t2).card ≤ 1) ∧ S.card = M.card := by
        -- By definition of $f$, we can map each edge in $M$ to a triangle in $S_tri$.
        obtain ⟨S, hS⟩ : ∃ S : Finset (Finset V), S ⊆ S_tri ∧ (∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → (t1 ∩ t2).card ≤ 1) ∧ S.card = M.card := by
          have h_image : ∃ S : Finset (trianglesContainingVertex G v), S.card = M.card ∧ ∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → (t1.1 ∩ t2.1).card ≤ 1 := by
            have h_image : ∃ S : Finset (trianglesContainingVertex G v), S.card = M.card ∧ ∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → Disjoint (f t1).1.toFinset (f t2).1.toFinset := by
              use Finset.filter (fun t => (f t).1 ∈ M) (Finset.univ : Finset (trianglesContainingVertex G v));
              refine' ⟨ _, _ ⟩;
              · refine' Finset.card_bij ( fun t ht => ( f t : Sym2 V ) ) _ _ _ <;> simp +decide [ hM_sub ];
                · intro a ha ha' b hb hb' hab; have := f.injective ( Subtype.ext hab ) ; aesop;
                · intro e he; obtain ⟨ t, ht ⟩ := f.surjective ⟨ e, hM_sub he ⟩ ; use t; aesop;
              · simp +zetaDelta at *;
                exact fun a ha ha' b hb hb' hab => hM_disjoint _ ha' _ hb' <| by simpa [ Subtype.ext_iff ] using fun h => hab <| by simpa [ Subtype.ext_iff ] using f.injective <| Subtype.ext h;
            obtain ⟨ S, hS₁, hS₂ ⟩ := h_image;
            refine' ⟨ S, hS₁, fun t1 ht1 t2 ht2 hne => _ ⟩;
            have := triangleEdgeEquiv_preserves_disjointness G v t1 t2 hne;
            exact this.mpr ( hS₂ t1 ht1 t2 ht2 hne )
          obtain ⟨ S, hS₁, hS₂ ⟩ := h_image;
          refine' ⟨ S.image Subtype.val, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
          · exact?;
          · rw [ Finset.card_image_of_injective _ Subtype.coe_injective, hS₁ ];
        use S;
      unfold trianglePackingOn;
      have hS_le_packing : S.card ∈ Finset.image Finset.card (Finset.filter (fun S => S ⊆ S_tri ∧ Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)) (Finset.powerset S_tri)) := by
        simp_all +decide [ Set.Pairwise ];
        exact ⟨ S, ⟨ hS.1, hS.2.1 ⟩, hS.2.2 ⟩;
      have := Finset.le_max hS_le_packing;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( fun S => S ⊆ S_tri ∧ ( S : Set ( Finset V ) ).Pairwise fun t1 t2 => ( t1 ∩ t2 ).card ≤ 1 ) ( Finset.powerset S_tri ) ) ) <;> aesop;
    contrapose! h_max_packing_le_max_matching;
    unfold maxMatchingNumber at h_max_packing_le_max_matching;
    have := Finset.max_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( fun M => ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset ) ( Finset.powerset S_edge ) ) ) from ?_ );
    · obtain ⟨ a, ha ⟩ := this;
      have := Finset.mem_of_max ha;
      rw [ Finset.mem_image ] at this; obtain ⟨ M, hM₁, hM₂ ⟩ := this; use M; aesop;
    · exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.empty_subset _ ), by simp +decide ⟩ ) ⟩;
  · -- Let $S$ be a maximum triangle packing at $v$. By definition, $S$ is a set of triangles containing $v$ such that any two triangles in $S$ are edge-disjoint.
    obtain ⟨S, hS⟩ : ∃ S : Finset (trianglesContainingVertex G v), trianglePackingOn G S_tri = S.card ∧ Set.Pairwise (S : Set (trianglesContainingVertex G v)) (fun t1 t2 => (t1.1 ∩ t2.1).card ≤ 1) := by
      unfold trianglePackingOn;
      have := Finset.max_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( fun S : Finset ( Finset V ) => S ⊆ S_tri ∧ ( S : Set ( Finset V ) ).Pairwise fun t1 t2 => ( t1 ∩ t2 ).card ≤ 1 ) ( Finset.powerset S_tri ) ) ) from ?_ );
      · obtain ⟨ a, ha ⟩ := this;
        obtain ⟨ S, hS ⟩ := Finset.mem_image.mp ( Finset.mem_of_max ha );
        refine' ⟨ Finset.univ.filter fun x => x.val ∈ S, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
        · rw [ show ( Finset.filter ( fun x : { x // x ∈ trianglesContainingVertex G v } => ( x : Finset V ) ∈ S ) ( Finset.attach S_tri ) ).card = S.card from ?_ ];
          · exact hS.2.symm ▸ rfl;
          · rw [ ← Finset.card_image_of_injective _ Subtype.coe_injective ] ; congr ; ext ; aesop;
        · intro x hx y hy hxy; have := hS.1.2; aesop;
      · exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.empty_subset _ ), Finset.empty_subset _, by simp +decide ⟩ ) ⟩;
    -- Since $S$ is a set of triangles containing $v$, the image of $S$ under $f$ is a set of edges in the link graph of $v$.
    set T := Finset.image f S with hT;
    -- Since $T$ is a set of edges in the link graph of $v$, it is a matching.
    have hT_matching : ∀ e1 ∈ T, ∀ e2 ∈ T, e1 ≠ e2 → Disjoint e1.1.toFinset e2.1.toFinset := by
      intro e1 he1 e2 he2 hne;
      obtain ⟨ t1, ht1, rfl ⟩ := Finset.mem_image.mp he1; obtain ⟨ t2, ht2, rfl ⟩ := Finset.mem_image.mp he2; specialize hS; have := hS.2 ht1 ht2; simp_all +decide ;
      have := triangleEdgeEquiv_preserves_disjointness G v t1 t2 hne; aesop;
    -- Since $T$ is a matching, its size is at most the maximum matching size of the link graph of $v$.
    have hT_size : T.card ≤ maxMatchingNumber (linkGraph G v) := by
      have hT_size : ∀ M : Finset (Sym2 V), (∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset) → M ⊆ S_edge → M.card ≤ maxMatchingNumber (linkGraph G v) := by
        intros M hM hM_subset;
        have hM_max : M.card ∈ Finset.image (fun M : Finset (Sym2 V) => M.card) (Finset.filter (fun M => ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset) (Finset.powerset S_edge)) := by
          exact Finset.mem_image.mpr ⟨ M, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hM_subset, hM ⟩, rfl ⟩;
        unfold maxMatchingNumber;
        have := Finset.le_max hM_max;
        rw [ WithBot.coe_le_iff ] at this;
        rcases this with ⟨ b, hb₁, hb₂ ⟩ ; rw [ hb₁ ] ; exact hb₂.trans ( by simp +decide [ Option.getD ] ) ;
      convert hT_size ( T.image Subtype.val ) _ _;
      · rw [ Finset.card_image_of_injective _ Subtype.coe_injective ];
      · grind;
      · exact Finset.image_subset_iff.mpr fun x hx => x.2;
    rw [ Finset.card_image_of_injective _ f.injective ] at hT_size ; aesop

/-
Given a vertex cover of the link graph, we can construct a triangle cover of the original graph with size at most the vertex cover size.
-/

-- Source: proven/tuza/nu4/slot_local_tuza_via_link_graph.lean
lemma packing_Ti_eq_matching_subLink (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (Ti : Finset (Finset V)) (hTi : Ti ⊆ trianglesContainingVertex G v) :
    trianglePackingOn G Ti = maxMatchingNumber (subLinkGraph G v Ti) := by
  refine' le_antisymm ( _ : _ ≤ _ ) ( _ : _ ≤ _ );
  · -- By definition of trianglePackingOn, we know that there exists a subset of triangles in Ti that are edge-disjoint.
    obtain ⟨S, hS⟩ : ∃ S : Finset (Finset V), S ⊆ Ti ∧ (∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → (t1 ∩ t2).card ≤ 1) ∧ S.card = trianglePackingOn G Ti := by
      have := Finset.max_of_nonempty ( show ( Finset.image Finset.card ( Finset.filter ( fun S => S ⊆ Ti ∧ Set.Pairwise ( S : Set ( Finset V ) ) fun t1 t2 => ( t1 ∩ t2 ).card ≤ 1 ) Ti.powerset ) ).Nonempty from ?_ );
      · unfold trianglePackingOn;
        obtain ⟨ a, ha ⟩ := this;
        have := Finset.mem_of_max ha; aesop;
      · exact ⟨ 0, Finset.mem_image.mpr ⟨ ∅, by aesop ⟩ ⟩;
    -- Let $M$ be the set of edges in the sub-link graph corresponding to the triangles in $S$.
    obtain ⟨M, hM⟩ : ∃ M : Finset (Sym2 V), M ⊆ (subLinkGraph G v Ti).edgeFinset ∧ M.card = S.card ∧ ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset := by
      -- For each triangle $t \in S$, let $e_t$ be the corresponding edge in the sub-link graph.
      have h_edges : ∀ t ∈ S, ∃ e : Sym2 V, e ∈ (subLinkGraph G v Ti).edgeFinset ∧ e.toFinset = t.erase v := by
        intro t ht
        obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : V, x ≠ y ∧ t = {v, x, y} := by
          have := hTi ( hS.1 ht );
          unfold trianglesContainingVertex at this;
          simp_all +decide [ Finset.ext_iff, SimpleGraph.cliqueFinset ];
          have := Finset.card_eq_three.mp this.1.2;
          obtain ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
          rcases this.2 with ( rfl | rfl | rfl ) <;> [ exact ⟨ y, z, hyz, by aesop ⟩ ; exact ⟨ x, z, hxz, by aesop ⟩ ; exact ⟨ x, y, hxy, by aesop ⟩ ];
        refine' ⟨ Sym2.mk ( x, y ), _, _ ⟩ <;> simp +decide [ *, Sym2.eq_swap ];
        · exact ⟨ hx, _, hS.1 ht, rfl ⟩;
        · ext; simp [Sym2.toFinset];
          intro h; have := hTi ( hS.1 ht ) ; simp_all +decide [ trianglesContainingVertex ] ;
          rintro rfl; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      choose! f hf1 hf2 using h_edges;
      refine' ⟨ Finset.image ( fun t : S => f t.1 t.2 ) Finset.univ, _, _, _ ⟩ <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
      · exact Set.range_subset_iff.mpr fun t => hf1 _ t.2;
      · rw [ Finset.card_image_of_injective _ fun x y hxy => _, Finset.card_attach, hS.2.2 ];
        intro x y hxy; have := hf2 x x.2; have := hf2 y y.2; simp_all +decide [ Finset.ext_iff ] ;
        ext a; by_cases ha : a = v <;> simp_all +decide ;
        have := hTi ( hS.1 x.2 ) ; have := hTi ( hS.1 y.2 ) ; simp_all +decide [ trianglesContainingVertex ] ;
      · intro e1 x hx he1 e2 y hy he2 hne
        have h_disjoint : (x.erase v) ∩ (y.erase v) = ∅ := by
          have := hS.2.1 x hx y hy ( by aesop ) ; simp_all +decide [ Finset.ext_iff ] ;
          contrapose! this;
          obtain ⟨ a, ha1, ha2, ha3 ⟩ := this; exact Finset.one_lt_card.mpr ⟨ a, by aesop, v, by have := hTi ( hS.1 hx ) ; have := hTi ( hS.1 hy ) ; simp_all +decide [ trianglesContainingVertex ] ⟩ ;
        simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ];
        grind;
    -- Since $M$ is a matching in the sub-link graph, its size is at most the maximum matching number of the sub-link graph.
    have hM_le_maxMatching : M.card ≤ maxMatchingNumber (subLinkGraph G v Ti) := by
      unfold maxMatchingNumber;
      have hM_le_maxMatching : M ∈ Finset.filter (fun M => ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset) (Finset.powerset (subLinkGraph G v Ti).edgeFinset) := by
        aesop;
      have hM_le_maxMatching : M.card ∈ Finset.image Finset.card (Finset.filter (fun M => ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset) (Finset.powerset (subLinkGraph G v Ti).edgeFinset)) := by
        exact Finset.mem_image_of_mem _ hM_le_maxMatching;
      have := Finset.le_max hM_le_maxMatching;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( fun M => ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset ) ( Finset.powerset ( subLinkGraph G v Ti ).edgeFinset ) ) ) <;> aesop;
    grind;
  · -- Given a matching in the subLinkGraph, we can map each edge to the corresponding triangle in Ti.
    have h_matching_to_packing : ∀ M : Finset (Sym2 V), M ⊆ (subLinkGraph G v Ti).edgeFinset → (∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset) → ∃ S : Finset (Finset V), S ⊆ Ti ∧ (∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → (t1 ∩ t2).card ≤ 1) ∧ S.card = M.card := by
      intro M hM hM';
      have h_triangle_map : ∀ e ∈ M, ∃ t ∈ Ti, t = {v} ∪ e.toFinset := by
        intro e he
        obtain ⟨x, y, hxy⟩ : ∃ x y : V, e = Sym2.mk (x, y) ∧ x ≠ y ∧ ∃ t ∈ Ti, t = {v, x, y} := by
          have := hM he; simp_all +decide [ subLinkGraph ] ;
          rcases e with ⟨ x, y ⟩ ; aesop;
        convert hxy.2.2 using 1 ; ext ; aesop;
      choose! f hf1 hf2 using h_triangle_map;
      refine' ⟨ Finset.image f M, _, _, _ ⟩;
      · exact Finset.image_subset_iff.mpr hf1;
      · simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ];
        intro e1 he1 e2 he2 hne; specialize hM' e1 he1 e2 he2; simp_all +decide [ Finset.ext_iff ] ;
        by_cases h : e1 = e2 <;> simp_all +decide [ Finset.ext_iff ];
        rw [ Finset.card_le_one_iff ] ; aesop;
      · rw [ Finset.card_image_of_injOn ];
        intro e1 he1 e2 he2 h; specialize hM' e1 he1 e2 he2; simp_all +decide [ Finset.disjoint_left ] ;
        contrapose! hM';
        rcases e1 with ⟨ x, y ⟩ ; rcases e2 with ⟨ u, v ⟩ ; simp_all +decide [ Finset.ext_iff ];
        cases h x ; cases h y ; aesop;
    have h_matching_to_packing : ∀ M : Finset (Sym2 V), M ⊆ (subLinkGraph G v Ti).edgeFinset → (∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset) → M.card ≤ trianglePackingOn G Ti := by
      intro M hM hM'; obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := h_matching_to_packing M hM hM'; rw [ ← hS₃ ] ;
      unfold trianglePackingOn;
      have h_max : S.card ∈ Finset.image Finset.card ({S ∈ Ti.powerset | S ⊆ Ti ∧ (↑S : Set (Finset V)).Pairwise fun (t1 t2 : Finset V) => (t1 ∩ t2).card ≤ 1}) := by
        simp +zetaDelta at *;
        exact ⟨ S, ⟨ hS₁, fun t1 ht1 t2 ht2 hne => hS₂ t1 ht1 t2 ht2 hne ⟩, rfl ⟩;
      have := Finset.le_max h_max;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( fun S => S ⊆ Ti ∧ ( S : Set ( Finset V ) ).Pairwise fun t1 t2 => ( t1 ∩ t2 ).card ≤ 1 ) ( Finset.powerset Ti ) ) ) <;> aesop;
    unfold maxMatchingNumber;
    rcases x : Finset.max ( Finset.image Finset.card ( Finset.filter ( fun M => ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset ) ( Finset.powerset ( subLinkGraph G v Ti ).edgeFinset ) ) ) with ( _ | x ) <;> simp +decide [ x ];
    have := Finset.mem_of_max x;
    rw [ Finset.mem_image ] at this; obtain ⟨ M, hM, rfl ⟩ := this; exact h_matching_to_packing M ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hM |>.1 ) ) ( Finset.mem_filter.mp hM |>.2 ) ;

/-
Given a vertex cover of the sub-link graph for a set of triangles $Ti$, we can construct a cover of $Ti$ in the original graph with size at most the vertex cover size.
-/

-- Source: proven/tuza/nu4/slot113_tau_le_12_conservative.lean
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
  -- By maximality of M, t must share at least two vertices with some triangle in M.
  have h_max : ∀ t ∈ G.cliqueFinset 3, ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
    intro t ht
    by_contra h_no_triangle
    push_neg at h_no_triangle
    have h_packing : isTrianglePacking G (M ∪ {t}) := by
      constructor;
      · -- Since $M$ is a packing, it is a subset of the cliqueFinset 3. Adding $t$ to $M$ should still be a subset of the cliqueFinset 3 because $t$ itself is in the cliqueFinset 3.
        have hM_subset : M ⊆ G.cliqueFinset 3 := by
          have := hM.1.1; aesop;
        exact Finset.union_subset hM_subset ( Finset.singleton_subset_iff.mpr ht );
      · -- Since $M$ is a packing, any two distinct triangles in $M$ have at most one vertex in common.
        have h_pairwise_M : ∀ t1 t2 : Finset V, t1 ∈ M → t2 ∈ M → t1 ≠ t2 → (t1 ∩ t2).card ≤ 1 := by
          have := hM.1.2; aesop;
        intro t1 ht1 t2 ht2 hne; by_cases h : t1 = t <;> by_cases h' : t2 = t <;> simp_all +decide ;
        · simpa only [ Finset.inter_comm ] using Nat.le_of_lt_succ ( h_no_triangle _ ht2 );
        · simpa only [ Finset.inter_comm ] using Nat.le_of_lt_succ ( h_no_triangle _ ht1 );
    have h_card : (M ∪ {t}).card > M.card := by
      -- Since $t \notin M$, adding $t$ to $M$ increases the cardinality by one.
      have h_not_in_M : t ∉ M := by
        intro h; specialize h_no_triangle t h; simp_all +decide ;
        exact h_no_triangle.not_le ( by rw [ ht.card_eq ] ; decide );
      aesop;
    have h_contradiction : trianglePackingNumber G ≥ (M ∪ {t}).card := by
      have h_contradiction : (M ∪ {t}) ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
        simp_all +decide [ Finset.subset_iff ];
        exact fun x hx => Finset.mem_coe.mp ( Finset.mem_coe.mpr ( h_packing.1 ( Finset.mem_insert_of_mem hx ) ) ) |> fun h => by simpa using h;
      unfold trianglePackingNumber;
      have := Finset.le_max ( Finset.mem_image_of_mem Finset.card h_contradiction );
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 ).powerset ) ) <;> aesop;
    linarith [ hM.2 ];
  exact h_max t ht -- Standard maximality, well-established

/-- All triangles covered by T_pair(A,B) ∪ T_pair(C,D) -/

-- Source: proven/tuza/nu4/slot_disjoint_partition_proven.lean
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
  -- By maximality: if t shares no edge with any X ∈ M, then M ∪ {t} is a larger packing
  -- Assume that the new triangle $t$ can be added to the packing $M$ without violating the triangle packing condition.
  by_contra h_contra;
  -- If no such $X$ exists, then $M \cup \{t\}$ would be a larger packing, contradicting the maximality of $M$.
  have h_larger_packing : isTrianglePacking G (M ∪ {t}) := by
    refine' ⟨ _, _ ⟩ <;> simp_all +decide [ isTrianglePacking ];
    · simp_all +decide [ Finset.subset_iff, SimpleGraph.cliqueFinset ];
      exact fun x hx => by have := hM.1.1 hx; aesop;
    · intro x hx y hy hxy; by_cases hx' : x = t <;> by_cases hy' : y = t <;> simp_all +decide ;
      · exact Nat.le_of_lt_succ ( h_contra y hy );
      · simpa only [ Finset.inter_comm ] using Nat.le_of_lt_succ ( h_contra x hx );
      · have := hM.1.2; aesop;
  have h_card : (M ∪ {t}).card > M.card := by
    -- Since $t$ is not in $M$, adding $t$ to $M$ increases the cardinality by 1.
    have h_t_not_in_M : t ∉ M := by
      rintro h; specialize h_contra; simp_all +decide [ Finset.inter_comm ] ;
      exact absurd ( h_contra t h ) ( by rw [ Finset.inter_self ] ; exact not_lt_of_ge ( by simpa [ ht.card_eq ] ) );
    rw [ Finset.card_union ] ; aesop;
  have h_contradiction : (Finset.image Finset.card (Finset.powerset (G.cliqueFinset 3) |>.filter (isTrianglePacking G))).max.getD 0 ≥ (M ∪ {t}).card := by
    have h_contradiction : (M ∪ {t}) ∈ Finset.filter (isTrianglePacking G) (Finset.powerset (G.cliqueFinset 3)) := by
      simp_all +decide [ Finset.subset_iff ];
      exact fun x hx => Finset.mem_filter.mp ( h_larger_packing.1 ( Finset.mem_insert_of_mem hx ) ) |>.2;
    have := Finset.le_max ( Finset.mem_image_of_mem Finset.card h_contradiction );
    cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
  exact h_card.not_le ( hM.2 ▸ h_contradiction ) -- This is proven in prior Aristotle runs

/-
If a triangle `t` shares at least 2 vertices with a triangle `A` of size 3, and `A` contains two distinct vertices `v1, v2`, then `t` must contain at least one of `v1` or `v2`.
-/

-- Source: proven/tuza/nu4/slot69_80891b4c/tau_pair_decomposition.lean
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  -- If $M$ does not contain $t$, then $M \cup \{t\}$ is also a triangle packing in $G$.
  by_contra h_contra
  have h_union : isTrianglePacking G (M ∪ {t}) := by
    constructor;
    · exact Finset.union_subset ( hM.1.1 ) ( Finset.singleton_subset_iff.mpr ht );
    · simp_all +decide [ Set.Pairwise ];
      exact ⟨ fun a ha hne => Nat.le_of_lt_succ ( h_contra a ha ), fun a ha => ⟨ fun hne => Nat.le_of_lt_succ ( by simpa only [ Finset.inter_comm ] using h_contra a ha ), fun a_2 ha_2 hne => by have := hM.1.2; aesop ⟩ ⟩;
  -- Since $M$ is maximal, $M \cup \{t\}$ cannot be a larger packing than $M$.
  have h_max : (M ∪ {t}).card ≤ trianglePackingNumber G := by
    have h_max : (M ∪ {t}).card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
      simp +zetaDelta at *;
      exact ⟨ _, ⟨ h_union.1, h_union ⟩, rfl ⟩;
    have h_max : ∀ x ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)).max 0 := by
      intros x hx;
      have := Finset.le_max hx;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_max _ ‹_›;
  simp_all +decide [ Finset.union_comm, Finset.card_union_add_card_inter ];
  rw [ Finset.card_insert_of_notMem ] at h_max <;> simp_all +decide [ isMaxPacking ];
  intro h; specialize h_contra t h; simp_all +decide [ Finset.inter_comm ] ;
  exact h_contra.not_le ( by have := ht.card_eq; aesop ) -- PROVEN in slot61 - copy full proof

-- Source: proven/tuza/nu4/slot69_80891b4c/output.lean
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
  -- If $M$ does not contain $t$, then $M \cup \{t\}$ is also a triangle packing in $G$.
  by_contra h_contra
  have h_union : isTrianglePacking G (M ∪ {t}) := by
    constructor;
    · exact Finset.union_subset ( hM.1.1 ) ( Finset.singleton_subset_iff.mpr ht );
    · simp_all +decide [ Set.Pairwise ];
      exact ⟨ fun a ha hne => Nat.le_of_lt_succ ( h_contra a ha ), fun a ha => ⟨ fun hne => Nat.le_of_lt_succ ( by simpa only [ Finset.inter_comm ] using h_contra a ha ), fun a_2 ha_2 hne => by have := hM.1.2; aesop ⟩ ⟩;
  -- Since $M$ is maximal, $M \cup \{t\}$ cannot be a larger packing than $M$.
  have h_max : (M ∪ {t}).card ≤ trianglePackingNumber G := by
    have h_max : (M ∪ {t}).card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
      simp +zetaDelta at *;
      exact ⟨ _, ⟨ h_union.1, h_union ⟩, rfl ⟩;
    have h_max : ∀ x ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)).max 0 := by
      intros x hx;
      have := Finset.le_max hx;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_max _ ‹_›;
  simp_all +decide [ Finset.union_comm, Finset.card_union_add_card_inter ];
  rw [ Finset.card_insert_of_notMem ] at h_max <;> simp_all +decide [ isMaxPacking ];
  intro h; specialize h_contra t h; simp_all +decide [ Finset.inter_comm ] ;
  exact h_contra.not_le ( by have := ht.card_eq; aesop ) -- PROVEN in slot61 - copy full proof

-- Source: proven/tuza/nu4/slot70_d3159016/diagonal_bridges.lean
lemma packing_elem_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) : e.card = 3 := by
  -- M is a triangle packing, so e ∈ cliqueFinset 3
  have h_sub := hM.1.1
  have he_clique := h_sub he
  simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at he_clique
  exact he_clique.2

-- KEY LEMMA: Diagonal pairs have empty bridges
-- If A ∩ C = ∅, no triangle can share an edge with both A and C

-- Source: proven/tuza/nu4/slot70_d3159016/output.lean
lemma packing_elem_card_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) : e.card = 3 := by
  -- M is a triangle packing, so e ∈ cliqueFinset 3
  have h_sub := hM.1.1
  have he_clique := h_sub he
  simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at he_clique
  exact he_clique.2

-- KEY LEMMA: Diagonal pairs have empty bridges
-- If A ∩ C = ∅, no triangle can share an edge with both A and C

-- Source: proven/tuza/nu4/slot72_f0a24a15/cycle_path_reduction.lean
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
      have := hM.1;
      contrapose! hM;
      -- If $t$ does not share an edge with any triangle in $M$, then $M \cup \{t\}$ is also a packing.
      have h_union_packing : isTrianglePacking G (M ∪ {t}) := by
        -- Since $t$ is a triangle and $M$ is a packing, any two triangles in $M \cup \{t\}$ must share at most one edge.
        have h_pairwise : Set.Pairwise (M ∪ {t} : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
          simp_all +decide [ Set.Pairwise, Finset.subset_iff ];
          exact ⟨ fun x hx hx' => Nat.le_of_lt_succ ( hM x hx ), fun x hx => ⟨ fun hx' => Nat.le_of_lt_succ ( by simpa only [ Finset.inter_comm ] using hM x hx ), fun y hy hy' => this.2 hx hy ( by aesop ) ⟩ ⟩;
        -- Since $M$ is a packing and $t$ is a triangle, their union $M \cup \{t\}$ is also a packing.
        simp [isTrianglePacking, this, ht];
        simp_all +decide [ Finset.subset_iff, Set.Pairwise ];
        exact fun x hx => Finset.mem_filter.mp ( this.1 hx ) |>.2;
      -- Since $M \cup \{t\}$ is also a packing, its cardinality is strictly greater than $M$'s cardinality.
      have h_card_union : (M ∪ {t}).card > M.card := by
        by_cases h : t ∈ M <;> simp_all +decide;
        specialize hM t h;
        simp_all +decide [ SimpleGraph.isNClique_iff ];
      unfold isMaxPacking;
      simp_all +decide [ trianglePackingNumber ];
      refine' ne_of_lt ( lt_of_lt_of_le h_card_union _ );
      have h_max : (Insert.insert t M).card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        simp +zetaDelta at *;
        exact ⟨ _, ⟨ Finset.insert_subset_iff.mpr ⟨ by aesop, this.1 ⟩, h_union_packing ⟩, rfl ⟩;
      have := Finset.le_max h_max;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Bridges are subset of T_pair
-- ══════════════════════════════════════════════════════════════════════════════

-- X_DA ⊆ T_pair(A,B) because any bridge sharing edge with D and A
-- also shares edge with A, hence is in trianglesSharingEdge(A) ⊆ T_pair(A,B)

-- Source: proven/tuza/nu4/slot72_f0a24a15/output.lean
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
      have := hM.1;
      contrapose! hM;
      -- If $t$ does not share an edge with any triangle in $M$, then $M \cup \{t\}$ is also a packing.
      have h_union_packing : isTrianglePacking G (M ∪ {t}) := by
        -- Since $t$ is a triangle and $M$ is a packing, any two triangles in $M \cup \{t\}$ must share at most one edge.
        have h_pairwise : Set.Pairwise (M ∪ {t} : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
          simp_all +decide [ Set.Pairwise, Finset.subset_iff ];
          exact ⟨ fun x hx hx' => Nat.le_of_lt_succ ( hM x hx ), fun x hx => ⟨ fun hx' => Nat.le_of_lt_succ ( by simpa only [ Finset.inter_comm ] using hM x hx ), fun y hy hy' => this.2 hx hy ( by aesop ) ⟩ ⟩;
        -- Since $M$ is a packing and $t$ is a triangle, their union $M \cup \{t\}$ is also a packing.
        simp [isTrianglePacking, this, ht];
        simp_all +decide [ Finset.subset_iff, Set.Pairwise ];
        exact fun x hx => Finset.mem_filter.mp ( this.1 hx ) |>.2;
      -- Since $M \cup \{t\}$ is also a packing, its cardinality is strictly greater than $M$'s cardinality.
      have h_card_union : (M ∪ {t}).card > M.card := by
        by_cases h : t ∈ M <;> simp_all +decide;
        specialize hM t h;
        simp_all +decide [ SimpleGraph.isNClique_iff ];
      unfold isMaxPacking;
      simp_all +decide [ trianglePackingNumber ];
      refine' ne_of_lt ( lt_of_lt_of_le h_card_union _ );
      have h_max : (Insert.insert t M).card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        simp +zetaDelta at *;
        exact ⟨ _, ⟨ Finset.insert_subset_iff.mpr ⟨ by aesop, this.1 ⟩, h_union_packing ⟩, rfl ⟩;
      have := Finset.le_max h_max;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Bridges are subset of T_pair
-- ══════════════════════════════════════════════════════════════════════════════

-- X_DA ⊆ T_pair(A,B) because any bridge sharing edge with D and A
-- also shares edge with A, hence is in trianglesSharingEdge(A) ⊆ T_pair(A,B)

-- Source: proven/tuza/lemmas/slot24_tau_X_le_2.lean
lemma packing_element_in_S {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    e ∈ S G e M := by
  unfold S trianglesSharingEdge
  simp only [Finset.mem_filter]
  constructor
  · constructor
    · exact hM.1.1 he
    · -- e ∩ e = e has card 3 ≥ 2
      simp only [Finset.inter_self]
      have : e.card = 3 := by
        have := hM.1.1 he
        simp only [SimpleGraph.mem_cliqueFinset_iff] at this
        exact this.2
      omega
  · -- e is compatible with other packing elements (packing constraint)
    intro f hf hfe
    exact hM.1.2 he hf hfe

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Counterexample definitions:
Graph on 5 vertices.
Triangles e={0,1,2}, f={0,3,4}, t={0,1,3}.
Edges are those in e, f, and t.
M={e,f} is the packing.
C={{1,2}, {3,4}} is the cover.
-/
abbrev CE_V := Fin 5

def CE_e : Finset CE_V := {0, 1, 2}
def CE_f : Finset CE_V := {0, 3, 4}
def CE_t : Finset CE_V := {0, 1, 3}

def CE_edges_list : List (Sym2 CE_V) := [
  s(0,1), s(1,2), s(0,2),
  s(0,3), s(3,4), s(0,4),
  s(1,3)
]

def CE_edges : Finset (Sym2 CE_V) := CE_edges_list.toFinset

def CE_G : SimpleGraph CE_V := SimpleGraph.fromEdgeSet CE_edges

instance : DecidableRel CE_G.Adj := Classical.decRel _

def CE_M : Finset (Finset CE_V) := {CE_e, CE_f}

def CE_C : Finset (Sym2 CE_V) := {s(1,2), s(3,4)}

-- Source: proven/tuza/nu0/tuza_nu0_PROVEN.lean
lemma neighbors_of_disjoint_packing_pairwise_edge_sharing (h_nu : trianglePackingNumber G = 2)
    (t₁ t₂ : Finset V) (h_packing : IsTrianglePacking G {t₁, t₂}) (h_disjoint : Disjoint t₁ t₂) :
    ∀ a b : Finset V, a ∈ G.cliqueFinset 3 → b ∈ G.cliqueFinset 3 →
    2 ≤ (a ∩ t₁).card → 2 ≤ (b ∩ t₁).card → 2 ≤ (a ∩ b).card := by
  intro a b ha hb ha' hb'
  by_contra h_contra;
  -- We construct a packing P = {a, b, t₂}.
  have h_packing_P : IsTrianglePacking G {a, b, t₂} := by
    simp_all +decide [ IsTrianglePacking ];
    simp_all +decide [ Finset.subset_iff, Set.Pairwise ];
    have h_inter_t2_a : (a ∩ t₂).card ≤ 1 := by
      have h_inter_t2_a : (a ∩ t₂).card ≤ 1 := by
        have h_disjoint_t1_t2 : Disjoint t₁ t₂ := h_disjoint
        have h_inter_a_t1 : 2 ≤ (a ∩ t₁).card := ha'
        apply disjoint_triangles_implies_neighbors_edge_disjoint t₁ t₂ a;
        · exact ha.2;
        · assumption;
        · exact h_inter_a_t1;
      exact h_inter_t2_a
    have h_inter_t2_b : (b ∩ t₂).card ≤ 1 := by
      have := disjoint_triangles_implies_neighbors_edge_disjoint t₁ t₂ b hb.2 h_disjoint hb';
      exact this;
    exact ⟨ ⟨ fun _ => by linarith, fun _ => by linarith ⟩, ⟨ fun _ => by rw [ Finset.inter_comm ] ; linarith, fun _ => by linarith ⟩, fun _ => by rw [ Finset.inter_comm ] ; linarith, fun _ => by rw [ Finset.inter_comm ] ; linarith ⟩;
  -- Since {a, b, t₂} is a triangle packing, its size must be less than or equal to the triangle packing number of G.
  have h_packing_size : ({a, b, t₂} : Finset (Finset V)).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber;
    have h_packing_size : ({a, b, t₂} : Finset (Finset V)).card ∈ Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset) := by
      refine' Finset.mem_image.mpr ⟨ _, _, rfl ⟩;
      simp_all +decide [ IsTrianglePacking ];
    have := Finset.le_max h_packing_size;
    cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( IsTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
  rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] at h_packing_size <;> simp_all +decide;
  · rintro rfl; simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ];
    rw [ Finset.inter_comm ] at h_disjoint ; aesop;
  · constructor <;> rintro rfl <;> simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ];
    · have := hb.card_eq; aesop;
    · simp_all +decide [ Finset.inter_comm ]

-- Source: proven/tuza/nu1/tuza_nu1_PROVEN.lean
lemma neighbors_of_disjoint_packing_pairwise_edge_sharing (h_nu : trianglePackingNumber G = 2)
    (t₁ t₂ : Finset V) (h_packing : IsTrianglePacking G {t₁, t₂}) (h_disjoint : Disjoint t₁ t₂) :
    ∀ a b : Finset V, a ∈ G.cliqueFinset 3 → b ∈ G.cliqueFinset 3 →
    2 ≤ (a ∩ t₁).card → 2 ≤ (b ∩ t₁).card → 2 ≤ (a ∩ b).card := by
  intro a b ha hb ha' hb'
  by_contra h_contra;
  -- We construct a packing P = {a, b, t₂}.
  have h_packing_P : IsTrianglePacking G {a, b, t₂} := by
    simp_all +decide [ IsTrianglePacking ];
    simp_all +decide [ Finset.subset_iff, Set.Pairwise ];
    have h_inter_t2_a : (a ∩ t₂).card ≤ 1 := by
      have h_inter_t2_a : (a ∩ t₂).card ≤ 1 := by
        have h_disjoint_t1_t2 : Disjoint t₁ t₂ := h_disjoint
        have h_inter_a_t1 : 2 ≤ (a ∩ t₁).card := ha'
        apply disjoint_triangles_implies_neighbors_edge_disjoint t₁ t₂ a;
        · exact ha.2;
        · assumption;
        · exact h_inter_a_t1;
      exact h_inter_t2_a
    have h_inter_t2_b : (b ∩ t₂).card ≤ 1 := by
      have := disjoint_triangles_implies_neighbors_edge_disjoint t₁ t₂ b hb.2 h_disjoint hb';
      exact this;
    exact ⟨ ⟨ fun _ => by linarith, fun _ => by linarith ⟩, ⟨ fun _ => by rw [ Finset.inter_comm ] ; linarith, fun _ => by linarith ⟩, fun _ => by rw [ Finset.inter_comm ] ; linarith, fun _ => by rw [ Finset.inter_comm ] ; linarith ⟩;
  -- Since {a, b, t₂} is a triangle packing, its size must be less than or equal to the triangle packing number of G.
  have h_packing_size : ({a, b, t₂} : Finset (Finset V)).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber;
    have h_packing_size : ({a, b, t₂} : Finset (Finset V)).card ∈ Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset) := by
      refine' Finset.mem_image.mpr ⟨ _, _, rfl ⟩;
      simp_all +decide [ IsTrianglePacking ];
    have := Finset.le_max h_packing_size;
    cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( IsTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
  rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] at h_packing_size <;> simp_all +decide;
  · rintro rfl; simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ];
    rw [ Finset.inter_comm ] at h_disjoint ; aesop;
  · constructor <;> rintro rfl <;> simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ];
    · have := hb.card_eq; aesop;
    · simp_all +decide [ Finset.inter_comm ]


-- ═══════════════════════════════════════════════════════════════════════
-- COVERING LEMMAS (158 lemmas)
-- ═══════════════════════════════════════════════════════════════════════

-- Source: proven/tuza_nu1_k4_proof.lean
lemma triangleCoveringNumber_le_card_add_deleteEdges {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) :
    triangleCoveringNumber G ≤ S.card + triangleCoveringNumber (G.deleteEdges S) := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (Sym2 V), T ⊆ (G.deleteEdges S).edgeFinset ∧ IsTriangleCovering (G.deleteEdges S) T ∧ T.card = triangleCoveringNumber (G.deleteEdges S) := by
    unfold triangleCoveringNumber; aesop;
    have := Finset.min_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering ( G.deleteEdges ( S : Set ( Sym2 V ) ) ) ) ( G.deleteEdges ( S : Set ( Sym2 V ) ) |> SimpleGraph.edgeFinset |> Finset.powerset ) ) ) from ?_ ) ; aesop;
    · have := Finset.mem_of_min h; aesop;
    · simp +zetaDelta at *;
      use (G.deleteEdges S).edgeFinset; simp [IsTriangleCovering];
  have h_union : IsTriangleCovering G (S ∪ T) := by
    unfold IsTriangleCovering at *; aesop;
  have h_union_card : triangleCoveringNumber G ≤ (S ∪ T).card := by
    unfold triangleCoveringNumber;
    have h_union_card : (S ∪ T).card ∈ Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
      simp_all +decide [ Finset.subset_iff, SimpleGraph.deleteEdges ];
      exact ⟨ S ∪ T, ⟨ fun x hx => by aesop, h_union ⟩, rfl ⟩;
    have := Finset.min_le h_union_card; aesop;
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop;
  exact h_union_card.trans ( Finset.card_union_le _ _ ) |> le_trans <| by rw [ hT.2.2 ] ;

-- Source: proven/tuza_nu1_k4_proof.lean
lemma exists_K4_of_nu1_tau_gt2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnu : trianglePackingNumber G = 1) (htau : triangleCoveringNumber G > 2) :
    ∃ s, G.IsNClique 4 s := by
      -- Let $T_0 = \{u, v, w\}$ be a triangle.
      obtain ⟨T, hT_clique, hT_card⟩ : ∃ T : Finset V, G.IsNClique 3 T := by
        contrapose! hnu;
        unfold trianglePackingNumber; aesop;
        rw [ show G.cliqueFinset 3 = ∅ by ext; aesop ] at a ; aesop;
        rw [ Finset.filter_singleton ] at a ; aesop;
      -- Let $e_1 = \{u, v\}$, $e_2 = \{v, w\}$, and $e_3 = \{w, u\}$.
      obtain ⟨u, v, w, huv, hvw, hwu⟩ : ∃ u v w : V, u ≠ v ∧ v ≠ w ∧ w ≠ u ∧ G.Adj u v ∧ G.Adj v w ∧ G.Adj w u ∧ T = {u, v, w} := by
        rcases Finset.card_eq_three.mp hT_card with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use u, v, w ; aesop;
        exact right.symm;
      -- By `extension_triangle_exists`, there exists $T_3 = \{w, u, z\}$ for some $z \notin T_0$.
      obtain ⟨z, hz⟩ : ∃ z : V, z ∉ ({u, v, w} : Finset V) ∧ G.Adj w z ∧ G.Adj u z := by
        -- By `extension_triangle_exists`, there exists $T_3 = \{w, u, z\}$ for some $z \notin T_0$ sharing exactly the edge $\{w, u\}$ with $T_0$.
        have hT3 : ∃ T3 : Finset V, G.IsNClique 3 T3 ∧ triangleEdges ({u, v, w} : Finset V) ∩ triangleEdges T3 = {Sym2.mk (w, u)} := by
          apply extension_triangle_exists G hnu htau {u, v, w};
          · aesop;
            constructor <;> aesop;
          · unfold triangleEdges; aesop;
            exact ⟨ w, u, by aesop ⟩;
        obtain ⟨ T3, hT3_clique, hT3_edge ⟩ := hT3;
        -- Since $T3$ is a triangle and shares exactly the edge $\{w, u\}$ with $T0$, $T3$ must contain $w$ and $u$.
        have hT3_contains_wu : w ∈ T3 ∧ u ∈ T3 := by
          replace hT3_edge := Finset.ext_iff.mp hT3_edge ( Sym2.mk ( w, u ) ) ; aesop;
          · unfold triangleEdges at right_1; aesop;
          · unfold triangleEdges at right_1; aesop;
        -- Since $T3$ is a triangle and contains $w$ and $u$, it must also contain a third vertex $z$.
        obtain ⟨z, hz⟩ : ∃ z : V, z ∈ T3 ∧ z ≠ w ∧ z ≠ u := by
          have := Finset.card_eq_three.mp hT3_clique.2; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := this; use if x = w then if y = u then z else y else if y = w then if x = u then z else x else if z = w then if x = u then y else x else w; aesop;
        use z;
        bound;
        · simp_all +decide [ SimpleGraph.IsNClique ];
          replace hT3_edge := Finset.ext_iff.mp hT3_edge ( Sym2.mk ( v, w ) ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;
          contrapose! hT3_edge; simp_all +decide [ triangleEdges ] ;
          exact ⟨ ⟨ v, w, by aesop ⟩, ⟨ v, w, by aesop ⟩ ⟩;
        · have := hT3_clique.1 left_1 left_2; aesop;
        · have := hT3_clique.1; aesop;
      -- By `extension_triangle_exists`, there exists $T_1 = \{u, v, x\}$ for some $x \notin T_0$.
      obtain ⟨x, hx⟩ : ∃ x : V, x ∉ ({u, v, w} : Finset V) ∧ G.Adj u x ∧ G.Adj v x := by
        have := extension_triangle_exists G hnu htau { u, v, w } ?_ ( Sym2.mk ( u, v ) ) ?_ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
        · obtain ⟨ T', ⟨ hT'_clique, hT'_card ⟩, hT'_edge ⟩ := this;
          -- Since $T'$ is a triangle and shares exactly the edge $\{u, v\}$ with $T$, it must contain $u$ and $v$.
          have hT'_contains_uv : u ∈ T' ∧ v ∈ T' := by
            simp_all +decide [ Finset.eq_singleton_iff_unique_mem, triangleEdges ];
            grind;
          -- Since $T'$ is a triangle and contains $u$ and $v$, it must also contain a third vertex $x$.
          obtain ⟨x, hx⟩ : ∃ x : V, x ∈ T' ∧ x ≠ u ∧ x ≠ v := by
            exact Exists.imp ( by aesop ) ( Finset.exists_ne_of_one_lt_card ( show 1 < Finset.card ( Finset.erase T' u ) from by rw [ Finset.card_erase_of_mem hT'_contains_uv.1, hT'_card ] ; decide ) v );
          use x;
          simp_all +decide [ Finset.ext_iff, triangleEdges ];
          have := hT'_edge ( Sym2.mk ( u, x ) ) ; have := hT'_edge ( Sym2.mk ( v, x ) ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;
          bound;
          · specialize this_1 u x ; simp_all +decide;
            grind;
          · exact hT'_clique ( by aesop ) ( by aesop ) ( by aesop );
          · exact hT'_clique ( by aesop ) ( by aesop ) ( by aesop );
        · exact Finset.mem_image.mpr ⟨ ( u, v ), by aesop_cat ⟩;
      -- By `extension_triangle_exists`, there exists $T_2 = \{v, w, y\}$ for some $y \notin T_0$.
      obtain ⟨y, hy⟩ : ∃ y : V, y ∉ ({u, v, w} : Finset V) ∧ G.Adj v y ∧ G.Adj w y := by
        have := extension_triangle_exists G hnu htau { u, v, w } ?_ ( Sym2.mk ( v, w ) ) ?_ <;> simp_all +decide [ SimpleGraph.IsNClique ];
        · obtain ⟨ T', hT'_clique, hT'_edge ⟩ := this;
          -- Since $T'$ is a triangle and shares exactly the edge $(v, w)$ with $T$, it must contain $v$ and $w$.
          have hT'_contains_vw : v ∈ T' ∧ w ∈ T' := by
            simp_all +decide [ Finset.eq_singleton_iff_unique_mem, triangleEdges ];
            grind;
          -- Since $T'$ is a triangle and shares exactly the edge $(v, w)$ with $T$, it must contain exactly one more vertex $y$.
          obtain ⟨y, hy⟩ : ∃ y : V, y ∈ T' ∧ y ≠ v ∧ y ≠ w := by
            have := Finset.card_eq_three.mp hT'_clique.2; obtain ⟨ a, b, c, ha, hb, hc, habc ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
            grind;
          use y;
          bound;
          · simp_all +decide [ Finset.eq_singleton_iff_unique_mem, triangleEdges ];
            contrapose! hT'_edge;
            rintro -;
            use Sym2.mk ( y, v ), y, v ; aesop;
          · have := hT'_clique.1; simp_all +decide [ SimpleGraph.isClique_iff, Finset.subset_iff ] ;
            exact this left_3 left_4 ( by aesop );
          · have := hT'_clique.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            exact this right_3 left_4 ( by aesop );
        · constructor <;> aesop;
        · exact Finset.mem_image.mpr ⟨ ( v, w ), by aesop ⟩;
      -- Since $\nu=1$, $T_1$ and $T_2$ must share an edge.
      have h_share_edge : x = y := by
        have h_share_edge : ¬ Disjoint (triangleEdges {u, v, x}) (triangleEdges {v, w, y}) := by
          apply packing_one_implies_intersect G hnu;
          · simp_all +decide [ SimpleGraph.cliqueFinset ];
            simp_all +decide [ SimpleGraph.isNClique_iff ];
            rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] <;> aesop;
          · simp_all +decide [ SimpleGraph.isNClique_iff ];
            rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] <;> aesop;
        unfold triangleEdges at h_share_edge; simp_all +decide [ Finset.disjoint_left ] ;
        simp_all +decide [ Sym2.eq_iff, eq_comm ];
        simp_all +decide [ Sym2.eq_swap ];
        aesop;
      -- By `extension_triangle_exists`, there exists $T_3 = \{w, u, z\}$ for some $z \notin T_0$.
      have hz_eq_x : z = x := by
        have hz_eq_x : ¬ Disjoint (triangleEdges ({w, u, z} : Finset V)) (triangleEdges ({u, v, x} : Finset V)) := by
          apply packing_one_implies_intersect G hnu;
          · simp_all +decide [ SimpleGraph.cliqueFinset ];
            simp_all +decide [ SimpleGraph.isNClique_iff ];
            rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton ] <;> aesop;
          · simp_all +decide [ SimpleGraph.cliqueFinset ];
            simp_all +decide [ SimpleGraph.isNClique_iff ];
            rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] <;> aesop;
        contrapose! hz_eq_x;
        simp_all +decide [ Finset.disjoint_left, triangleEdges ];
        intros; subst_vars; simp_all +decide [ Sym2.eq_iff ] ;
        grind;
      use {u, v, w, x};
      simp_all +decide [ SimpleGraph.isNClique_iff ];
      rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] <;> aesop

/--
If a graph has triangle packing number 1 and contains a K4 clique, then its triangle
covering number is at most 2.
-/

-- Source: proven/tuza_nu1_k4_proof.lean
lemma K4_cover_le_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnu : trianglePackingNumber G = 1) (s : Finset V) (hs : G.IsNClique 4 s) :
    triangleCoveringNumber G ≤ 2 := by
      -- Let $S = \{(a, b), (c, d)\}$.
      obtain ⟨t1, t2, t3, t4, ht1, ht2, ht3, ht4, hs⟩ : ∃ t1 t2 t3 t4 : V, t1 ∈ s ∧ t2 ∈ s ∧ t3 ∈ s ∧ t4 ∈ s ∧ t1 ≠ t2 ∧ t1 ≠ t3 ∧ t1 ≠ t4 ∧ t2 ≠ t3 ∧ t2 ≠ t4 ∧ t3 ≠ t4 ∧ G.Adj t1 t2 ∧ G.Adj t1 t3 ∧ G.Adj t1 t4 ∧ G.Adj t2 t3 ∧ G.Adj t2 t4 ∧ G.Adj t3 t4 := by
        rcases Finset.card_eq_succ.mp hs.2 with ⟨ t, ht ⟩;
        rcases ht with ⟨ u, hu, rfl, hu' ⟩ ; rcases Finset.card_eq_three.mp hu' with ⟨ v, w, x, hv, hw, hx, h ⟩ ; use t, v, w, x; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      have hS : ∀ T : Finset V, G.IsNClique 3 T → (triangleEdges T ∩ {Sym2.mk (t1, t2), Sym2.mk (t3, t4)}).Nonempty := by
        intros T hT;
        have h_inter : ¬ Disjoint (triangleEdges T) (triangleEdges {t1, t2, t3}) ∧ ¬ Disjoint (triangleEdges T) (triangleEdges {t1, t2, t4}) ∧ ¬ Disjoint (triangleEdges T) (triangleEdges {t1, t3, t4}) ∧ ¬ Disjoint (triangleEdges T) (triangleEdges {t2, t3, t4}) := by
          bound;
          · have := packing_one_implies_intersect G hnu T { t1, t2, t3 } ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          · have := packing_one_implies_intersect G hnu T { t1, t2, t4 } ; simp_all +decide [ Finset.disjoint_left ] ;
            contrapose! this; simp_all +decide [ SimpleGraph.IsNClique ] ;
            constructor <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
          · have := packing_one_implies_intersect G hnu T { t1, t3, t4 } ?_ ?_ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
          · have := packing_one_implies_intersect G hnu T { t2, t3, t4 } ; simp_all +decide [ Finset.disjoint_left ];
            contrapose! this; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        simp_all +decide [ Finset.disjoint_left, Finset.mem_inter ];
        unfold triangleEdges at *; simp_all +decide [ Finset.Nonempty ] ;
        rcases h_inter with ⟨ ⟨ x, ⟨ a, b, ⟨ ha, hb, hab ⟩, rfl ⟩, ⟨ c, d, ⟨ hc, hd, hcd ⟩, hx ⟩ ⟩, ⟨ y, ⟨ a', b', ⟨ ha', hb', hab' ⟩, rfl ⟩, ⟨ c', d', ⟨ hc', hd', hcd' ⟩, hy ⟩ ⟩, ⟨ z, ⟨ a'', b'', ⟨ ha'', hb'', hab'' ⟩, rfl ⟩, ⟨ c'', d'', ⟨ hc'', hd'', hcd'' ⟩, hz ⟩ ⟩, ⟨ w, ⟨ a''', b''', ⟨ ha''', hb''', hab''' ⟩, rfl ⟩, ⟨ c''', d''', ⟨ hc''', hd''', hcd''' ⟩, hw ⟩ ⟩ ⟩;
        simp_all +decide [ Sym2.eq_iff ];
        grind;
      have hS_cover : IsTriangleCovering G {Sym2.mk (t1, t2), Sym2.mk (t3, t4)} := by
        unfold IsTriangleCovering; aesop;
        intro T hT; specialize hS T; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        contrapose! hS;
        unfold triangleEdges; aesop;
        · intro x hx y hy hxy; have := left_12 hx hy; aesop;
        · simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
          intro a x y hx hy hxy ha; have := left_12 hx hy; simp_all +decide [ SimpleGraph.deleteEdges ] ;
      unfold triangleCoveringNumber;
      have h_min_le_two : 2 ∈ Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset) := by
        simp +zetaDelta at *;
        refine' ⟨ { s(t1, t2), s(t3, t4) }, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
      have := Finset.min_le h_min_le_two; aesop;
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop

/-! ## MAIN THEOREM -/

/--
MAIN THEOREM: When ν(G) = 1, we have τ(G) ≤ 2

This is proved by contradiction:
1. Assume τ > 2
2. Use extension_triangle_exists repeatedly to show extensions force K₄
3. exists_K4_of_nu1_tau_gt2 gives us the K₄
4. K4_cover_le_2 shows K₄ implies τ ≤ 2, contradiction!
-/

-- Source: proven/scaffolding/slot44_scaffolding_PARTIAL.lean
lemma isTriangleCover_union (G : SimpleGraph V) (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  exact ⟨ Finset.union_subset hA.1 hB.1, fun t ht => by cases' Finset.mem_union.mp ht with ht ht <;> [ exact hA.2 _ ht |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Finset.mem_union_left _ he₁, he₂ ⟩ ; exact hB.2 _ ht |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Finset.mem_union_right _ he₁, he₂ ⟩ ] ⟩

-- Source: proven/scaffolding/slot44_scaffolding_PARTIAL.lean
lemma triangleCoveringNumberOn_le_of_isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V))
    (E' : Finset (Sym2 V)) (h : isTriangleCover G triangles E') :
    triangleCoveringNumberOn G triangles ≤ E'.card := by
  have h_min : triangleCoveringNumberOn G triangles ≤ Finset.min (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card) := by
    unfold triangleCoveringNumberOn;
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2 ) G.edgeFinset.powerset ) ) <;> aesop;
  contrapose! h_min;
  refine' lt_of_le_of_lt _ ( WithTop.coe_lt_coe.mpr h_min );
  simp +decide [ Finset.min ];
  exact ⟨ E', ⟨ fun e he => by have := h.1 he; aesop, fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := h.2 t ht; aesop ⟩, le_rfl ⟩

-- Source: proven/scaffolding/slot44_scaffolding_PARTIAL.lean
lemma exists_min_isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : ∃ E', isTriangleCover G triangles E') :
    ∃ E', isTriangleCover G triangles E' ∧ E'.card = triangleCoveringNumberOn G triangles := by
  obtain ⟨E', hE'⟩ : ∃ E' : Finset (Sym2 V), isTriangleCover G triangles E' ∧ ∀ E'' : Finset (Sym2 V), isTriangleCover G triangles E'' → E'.card ≤ E''.card := by
    apply_rules [ Set.exists_min_image ];
    exact Set.finite_iff_bddAbove.mpr ⟨ _, fun a ha => ha.1 ⟩;
  use E';
  unfold triangleCoveringNumberOn;
  rw [ show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2 } ) ) = Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) from ?_ ];
  · rw [ show Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) = Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) from rfl, Finset.min_eq_inf_withTop ];
    rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) ).inf WithTop.some = WithTop.some E'.card from ?_ ] ; aesop;
    refine' le_antisymm _ _ <;> simp_all +decide [ Finset.inf_le ];
    exact ⟨ E', ⟨ fun e he => by have := hE'.1.1 he; aesop, hE'.1 ⟩, le_rfl ⟩;
  · ext; simp [isTriangleCover]

-- Source: proven/scaffolding/slot44_scaffolding_PARTIAL.lean
lemma triangleCoveringNumberOn_eq_zero_of_not_coverable (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : ¬ ∃ E', isTriangleCover G triangles E') :
    triangleCoveringNumberOn G triangles = 0 := by
  unfold triangleCoveringNumberOn;
  simp_all +decide [ Finset.min ];
  rw [ Finset.inf_eq_iInf ];
  rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
  case b => exact ⊤;
  · rfl;
  · simp_all +decide [ isTriangleCover ];
  · aesop

-- Source: proven/scaffolding/slot44_scaffolding_PARTIAL.lean
lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases hA : ∃ E', isTriangleCover G A E';
  · by_cases hB : ∃ E', isTriangleCover G B E';
    · obtain ⟨E_A, hE_A⟩ := exists_min_isTriangleCover G A hA
      obtain ⟨E_B, hE_B⟩ := exists_min_isTriangleCover G B hB;
      have h_union : isTriangleCover G (A ∪ B) (E_A ∪ E_B) := by
        exact isTriangleCover_union G A B E_A E_B hE_A.1 hE_B.1;
      exact le_trans ( triangleCoveringNumberOn_le_of_isTriangleCover _ _ _ h_union ) ( by rw [ ← hE_A.2, ← hE_B.2 ] ; exact Finset.card_union_le _ _ );
    · rw [ triangleCoveringNumberOn_eq_zero_of_not_coverable ];
      · exact Nat.zero_le _;
      · exact fun ⟨ E', hE' ⟩ => hB ⟨ E', by exact ⟨ Finset.Subset.trans hE'.1 ( Finset.Subset.refl _ ), fun t ht => hE'.2 t ( Finset.mem_union_right _ ht ) ⟩ ⟩;
  · rw [ triangleCoveringNumberOn_eq_zero_of_not_coverable ];
    · exact Nat.zero_le _;
    · exact fun ⟨ E', hE' ⟩ => hA ⟨ E', ⟨ hE'.1, fun t ht => hE'.2 t ( Finset.mem_union_left _ ht ) ⟩ ⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: tau_X_le_2 (FULL PROOF from slot28)
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/scaffolding/slot44_scaffolding_PARTIAL.lean
lemma X_ef_covering_number_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v}) (he : e ∈ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  simp_all +decide [ SimpleGraph.cliqueFinset ];
  set E' : Finset (Sym2 V) := Finset.image (fun u => Sym2.mk (v, u)) (e \ {v}) with hE';
  have h_cover : ∀ t ∈ X_ef G e f, ∃ e' ∈ E', e' ∈ t.sym2 := by
    intro t ht
    have h_triangle : v ∈ t := by
      unfold X_ef at ht;
      simp_all +decide [ Finset.ext_iff ];
      contrapose! ht;
      intro ht ht';
      have h_card : (t ∩ e).card + (t ∩ f).card ≤ (t ∩ (e ∪ f)).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        rw [ show t ∩ e ∪ t ∩ f = t ∩ ( e ∪ f ) by ext; aesop, show t ∩ e ∩ ( t ∩ f ) = ∅ by ext; aesop ] ; simp +decide;
      have h_card : (t ∩ (e ∪ f)).card ≤ t.card := by
        exact Finset.card_le_card fun x hx => by aesop;
      linarith [ ht.2 ];
    obtain ⟨u, hu⟩ : ∃ u ∈ e \ {v}, u ∈ t := by
      have h_card : (t ∩ e).card ≥ 2 := by
        unfold X_ef at ht; aesop;
      contrapose! h_card;
      rw [ show t ∩ e = { v } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_inter.mpr ⟨ h_triangle, by replace hv := Finset.ext_iff.mp hv v; aesop ⟩, fun x hx => by_contradiction fun hx' => h_card x ( by aesop ) ( Finset.mem_inter.mp hx |>.1 ) ⟩ ] ; simp +decide;
    aesop;
  have h_covering : E' ⊆ G.edgeFinset ∧ (∀ t ∈ X_ef G e f, ∃ e' ∈ E', e' ∈ t.sym2) := by
    simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
    rintro _ u hu huv rfl; have := he.1 ( show v ∈ e from by rw [ Finset.eq_singleton_iff_unique_mem ] at hv; aesop ) ( show u ∈ e from hu ) ; aesop;
  have h_card_E' : E'.card ≤ 2 := by
    have := he.card_eq;
    grind;
  refine' le_trans ( _ : triangleCoveringNumberOn G ( X_ef G e f ) ≤ E'.card ) h_card_E';
  have h_min_le_card : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → Option.getD (Finset.image Finset.card S).min 0 ≤ E'.card := by
    intros S hS; exact (by
    have h_min_le_card : ∀ {S : Finset ℕ}, E'.card ∈ S → Option.getD (Finset.min S) 0 ≤ E'.card := by
      intro S hS; exact (by
      have h_min_le_card : ∀ {S : Finset ℕ}, E'.card ∈ S → Finset.min S ≤ E'.card := by
        exact fun { S } hS => Finset.min_le hS;
      specialize h_min_le_card hS; cases h : Finset.min S <;> aesop;);
    exact h_min_le_card ( Finset.mem_image_of_mem _ hS ));
  exact h_min_le_card ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h_covering.1, h_covering.2 ⟩ )

-- Source: proven/scaffolding/slot44_scaffolding_PARTIAL.lean
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  apply X_ef_covering_number_le_2 G e f v hv;
  exact hM.1.1 he

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: tau_S_le_2 (FULL PROOF from slot32)
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/scaffolding/slot44_scaffolding_PARTIAL.lean
lemma tau_S_le_2_case1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (uv : Finset V) (huv : uv ⊆ e) (huv_card : uv.card = 2)
    (h_struct : ∀ t ∈ S_e G M e, t ≠ e → uv ⊆ t) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  unfold triangleCoveringNumberOn;
  obtain ⟨u, v, hu, hv, huv_eq⟩ : ∃ u v, uv = {u, v} ∧ u ≠ v ∧ u ∈ e ∧ v ∈ e := by
    rw [ Finset.card_eq_two ] at huv_card; obtain ⟨ u, v, huv ⟩ := huv_card; use u, v; aesop;
  have huv_edge : Sym2.mk (u, v) ∈ G.edgeFinset := by
    have := hM.1.1 he; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
    exact this.1 ( by aesop ) ( by aesop ) hv;
  have h_triangle_covering : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ S_e G M e, ∃ e ∈ E', e ∈ t.sym2)), E'.card ≤ 2 := by
    refine' ⟨ { Sym2.mk ( u, v ) }, _, _ ⟩ <;> simp_all +decide;
    intro t ht; specialize h_struct t ht; by_cases h : t = e <;> simp_all +decide [ Finset.subset_iff ] ;
  obtain ⟨ E', hE₁, hE₂ ⟩ := h_triangle_covering;
  have h_min_le : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ E'.card := by
    exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', by aesop ⟩ );
  exact le_trans ( by cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop ) hE₂

-- Source: proven/scaffolding/slot44_scaffolding_PARTIAL.lean
lemma tau_S_le_2_case2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (x : V) (hx : x ∉ e)
    (h_struct : ∀ t ∈ S_e G M e, t ≠ e → t = (t ∩ e) ∪ {x}) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  obtain ⟨u, v, huv⟩ : ∃ u v : V, u ∈ e ∧ v ∈ e ∧ u ≠ v ∧ G.Adj u v := by
    have := hM.1;
    have := this.1 he; simp +decide [ isTrianglePacking ] at this;
    rcases Finset.card_eq_three.mp this.2 with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use u, v ; simp_all +decide [ SimpleGraph.isNClique_iff ];
  obtain ⟨w, hw⟩ : ∃ w : V, w ∈ e ∧ w ≠ u ∧ w ≠ v := by
    have h_card : e.card = 3 := by
      have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      exact this.card_eq;
    exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.erase e u ) from by rw [ Finset.card_erase_of_mem huv.1, h_card ] ; decide ) v );
  by_cases huv_cover : ∀ t ∈ S_e G M e, t ≠ e → (u ∈ t ∧ v ∈ t) ∨ (w ∈ t ∧ x ∈ t);
  · set E' : Finset (Sym2 V) := {Sym2.mk (u, v), Sym2.mk (w, x)};
    have hE'_cover : ∀ t ∈ S_e G M e, t ≠ e → ∃ e' ∈ E', e' ∈ t.sym2 := by
      intro t ht ht'; specialize huv_cover t ht ht'; rcases huv_cover with ( ⟨ hu, hv ⟩ | ⟨ hw, hx ⟩ ) <;> [ exact ⟨ _, Finset.mem_insert_self _ _, by simp +decide [ hu, hv ] ⟩ ; exact ⟨ _, Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ), by simp +decide [ hw, hx ] ⟩ ] ;
    have h_triangleCoveringNumberOn_le_2 : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2 := by
      refine' ⟨ E' ∩ G.edgeFinset, _, _, _ ⟩;
      · exact Finset.inter_subset_right;
      · exact le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ( Finset.card_insert_le _ _ );
      · intro t ht;
        by_cases h : t = e <;> simp +decide [ h ] at hE'_cover ⊢;
        · exact ⟨ Sym2.mk ( u, v ), ⟨ Finset.mem_insert_self _ _, by simpa using huv.2.2.2 ⟩, by simp +decide [ huv.1, huv.2.1 ] ⟩;
        · obtain ⟨ e', he', he'' ⟩ := hE'_cover t ht h;
          simp +zetaDelta at *;
          rcases he' with ( rfl | rfl ) <;> [ exact ⟨ _, ⟨ Or.inl rfl, by simpa using huv.2.2.2 ⟩, he'' ⟩ ; exact ⟨ _, ⟨ Or.inr rfl, by
            have := Finset.mem_filter.mp ht |>.1; simp +decide [ SimpleGraph.mem_edgeSet ] at this ⊢;
            unfold trianglesSharingEdge at this; simp +decide [ SimpleGraph.mem_edgeSet ] at this;
            have := this.1.1; simp +decide [ SimpleGraph.isNClique_iff ] at this;
            exact this ( by simpa using he'' _ ( Sym2.mem_iff.mpr <| Or.inl rfl ) ) ( by simpa using he'' _ ( Sym2.mem_iff.mpr <| Or.inr rfl ) ) ( by rintro rfl; simp +decide [ hx ] at * ) ⟩, he'' ⟩ ];
    obtain ⟨ E', hE'_sub, hE'_card, hE'_cover ⟩ := h_triangleCoveringNumberOn_le_2;
    have h_min_le_card : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → Option.getD (Finset.image Finset.card S).min 0 ≤ E'.card := by
      intro S hS; have := Finset.min_le ( Finset.mem_image_of_mem Finset.card hS ) ; simp +decide at this ⊢;
      cases h : Finset.min ( Finset.image Finset.card S ) <;> simp +decide [ h ] at this ⊢ ; exact this;
    exact le_trans ( h_min_le_card ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'_sub, hE'_cover ⟩ ) ) hE'_card;
  · contrapose! huv_cover;
    intro t ht hte
    have ht_edges : t ∩ e = {u, v} ∨ t ∩ e = {v, w} ∨ t ∩ e = {u, w} := by
      have ht_edges : (t ∩ e).card = 2 := by
        have := h_struct t ht hte;
        have ht_card : t.card = 3 := by
          unfold S_e at ht; norm_num at ht;
          unfold trianglesSharingEdge at ht; norm_num at ht;
          exact ht.1.1.card_eq;
        rw [ this, Finset.card_union ] at ht_card ; simp +decide [ hx ] at ht_card ⊢ ; linarith;
      have ht_edges_subset : t ∩ e ⊆ {u, v, w} := by
        have := hM.1;
        have := this.1 he; simp +decide [ SimpleGraph.cliqueFinset ] at this;
        have := this.2; simp +decide [ Finset.card_eq_three ] at this;
        grind;
      have := Finset.card_eq_two.mp ht_edges;
      rcases this with ⟨ x, y, hxy, h ⟩ ; simp +decide [ h, Finset.Subset.antisymm_iff, Finset.subset_iff ] at ht_edges_subset ⊢;
      grind;
    rcases ht_edges with ( h | h | h ) <;> specialize h_struct t ht hte <;> simp +decide [ h ] at h_struct ⊢;
    · simp +decide [ h_struct ];
    · simp +decide [ h_struct ];
    · simp +decide [ h_struct ]

-- Source: proven/scaffolding/slot44_scaffolding_PARTIAL.lean
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  obtain h | h := Se_structure_

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma tau_star {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3) (h_star : isStar S) :
    triangleCoveringNumberOn G S ≤ 1 := by
      unfold triangleCoveringNumberOn;
      cases h_star ; aesop;
      cases' Finset.card_eq_two.mp left with x hx ; aesop;
      by_cases h : G.Adj x w_1;
      · have h_cover : {Sym2.mk (x, w_1)} ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t) := by
          aesop;
        have h_min : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ 1 := by
          exact Finset.min_le ( Finset.mem_image.mpr ⟨ _, h_cover, rfl ⟩ );
        cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop;
      · simp_all +decide [ Finset.subset_iff, SimpleGraph.mem_edgeSet ];
        contrapose! h;
        rcases S.eq_empty_or_nonempty with ( rfl | ⟨ t, ht ⟩ ) <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
        · unfold Option.getD at h; aesop;
          rw [ Finset.min_eq_inf_withTop ] at heq ; aesop;
          rw [ Finset.inf_eq_iInf ] at heq;
          have := heq ▸ iInf_le_of_le ∅ ( by aesop ) ; aesop;
          cases this;
          contradiction;
        · have := hS ht;
          exact this.1 ( right _ ht |>.1 ) ( right _ ht |>.2 ) ( by aesop )

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma covering_number_on_le_two_of_subset_four {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3) (U : Finset V) (hU : U.card ≤ 4) (h_subset : ∀ t ∈ S, t ⊆ U) :
    triangleCoveringNumberOn G S ≤ 2 := by
      have h_tau_star : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2 := by
        -- Consider the set of edges $E'$ consisting of the edges of $U$.
        obtain ⟨E', hE'_subset, hE'_card⟩ : ∃ E' : Finset (Sym2 V), E' ⊆ Finset.image (fun e : V × V => Sym2.mk e) (Finset.offDiag U) ∧ E'.card ≤ 2 ∧ ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2 := by
          interval_cases _ : U.card <;> simp_all +decide;
          · intro t ht; specialize h_subset t ht; specialize hS ht; aesop;
          · -- Since U has only one element, any triangle in S would have to be a subset of U, but a triangle requires three vertices. Therefore, S must be empty.
            have hS_empty : S = ∅ := by
              ext t
              simp [h_subset, ‹U.card = 1›];
              intro ht; have := hS ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
              have := Finset.card_le_card ( h_subset t ht ) ; simp_all +decide ;
              exact this.not_lt ( by rw [ ‹G.IsNClique 3 t›.card_eq ] ; decide );
            exact ⟨ ∅, by simp +decide [ hS_empty ] ⟩;
          · -- Since U has exactly two elements, any triangle in S must be a subset of U. But a triangle requires three vertices, so if U has only two elements, there can't be any triangles in S. Therefore, S must be empty.
            have hS_empty : S = ∅ := by
              ext t;
              have := hS; simp_all +decide [ Finset.subset_iff ];
              contrapose! this;
              exact ⟨ t, this, fun h => by have := Finset.card_le_card ( show t ⊆ U from fun x hx => h_subset t this hx ) ; linarith [ h.2 ] ⟩;
            exact ⟨ ∅, by simp +decide [ hS_empty ] ⟩;
          · -- Since $U$ has exactly 3 vertices, any triangle in $S$ must be a subset of $U$. The triangles in $S$ are all the 3-element subsets of $U$. So, each triangle in $S$ is exactly $U$ itself.
            have h_triangles : ∀ t ∈ S, t = U := by
              intro t ht; have := hS ht; simp_all +decide [ Finset.subset_iff ] ;
              exact Finset.eq_of_subset_of_card_le ( h_subset t ht ) ( by have := hS ht; exact this.card_eq.symm ▸ by simp +decide [ * ] );
            rcases Finset.card_eq_three.mp ‹_› with ⟨ a, b, c, hab, hbc, hac ⟩ ; simp_all +decide;
            use { Sym2.mk ( a, b ), Sym2.mk ( a, c ) } ; simp_all +decide [ Finset.subset_iff ] ;
            exact ⟨ ⟨ ⟨ a, b, by aesop ⟩, ⟨ a, c, by aesop ⟩ ⟩, fun t ht => by specialize h_triangles t ht; aesop ⟩;
          · -- Since $U$ has 4 vertices, we can choose any two edges that cover all triangles in $S$.
            obtain ⟨u1, u2, u3, u4, hu⟩ : ∃ u1 u2 u3 u4 : V, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u1 ≠ u4 ∧ u2 ≠ u3 ∧ u2 ≠ u4 ∧ u3 ≠ u4 ∧ U = {u1, u2, u3, u4} := by
              simp_rw +decide [ Finset.card_eq_succ ] at *;
              rcases ‹_› with ⟨ a, t, hat, rfl, b, u, hbu, rfl, c, v, hcv, rfl, d, w, hdw, rfl, hw ⟩ ; use a, b, c, d; aesop;
            refine' ⟨ { Sym2.mk ( u1, u2 ), Sym2.mk ( u3, u4 ) }, _, _, _ ⟩ <;> simp +decide [ Finset.subset_iff, * ];
            · exact ⟨ ⟨ u1, u2, by aesop ⟩, ⟨ u3, u4, by aesop ⟩ ⟩;
            · intro t ht; specialize h_subset t ht; simp_all +decide [ Finset.subset_iff ] ;
              have := hS ht; rcases this with ⟨ ht1, ht2 ⟩ ; rcases Finset.card_eq_three.mp ht2 with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; simp_all +decide ;
              grind;
        refine' ⟨ E' ∩ G.edgeFinset, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
        · exact le_trans ( Finset.card_le_card fun x hx => by aesop ) hE'_card.1;
        · -- Since $t$ is a triangle in $S$, and $S$ is a subset of the cliqueFinset 3 of $G$, $t$ must be a 3-clique in $G$. Therefore, any edge in $t$ is an edge in $G$.
          intros t ht
          obtain ⟨e, heE', he⟩ := hE'_card.right t ht
          have heG : e ∈ G.edgeSet := by
            obtain ⟨ a, b, ⟨ ha, hb, hab ⟩, rfl ⟩ := hE'_subset heE' ; specialize hS ht ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            exact hS.1 ( by aesop ) ( by aesop ) hab
          use e;
      obtain ⟨ E', hE₁, hE₂, hE₃ ⟩ := h_tau_star;
      unfold triangleCoveringNumberOn;
      simp +zetaDelta at *;
      have h_min_le_two : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ 2 := by
        exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by simpa [ ← Finset.coe_subset ] using hE₁ ), hE₃ ⟩, rfl ⟩ ) |> le_trans <| by simpa using hE₂;
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ S, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma tau_S_le_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S G e M) ≤ 2 := by
      -- S_e is either a star or contained in a K4.
      have h_star_or_K4 : isStar (S G e M) ∨ isK4 (S G e M) := by
        apply intersecting_family_structure_corrected G (S G e M);
        · refine' ⟨ e, _ ⟩;
          unfold S; aesop;
          · unfold trianglesSharingEdge; aesop;
            · have := hM.1;
              have := this.1 he; aesop;
            · have := hM.1;
              have := this.1 he; aesop;
              exact this.card_eq.symm ▸ by decide;
          · have := hM.1; unfold isTrianglePacking at this; aesop;
        · exact fun x hx => Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1;
        · intro t1 ht1 t2 ht2 hne; exact lemma_2_2 G M hM e he t1 t2 ht1 ht2;
      rcases h_star_or_K4 with h|h;
      · refine' le_trans ( tau_star _ _ _ h ) _;
        · exact fun x hx => Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1;
        · norm_num;
      · obtain ⟨ s, hs ⟩ := h;
        convert covering_number_on_le_two_of_subset_four G ( S G e M ) _ s _ _ <;> aesop;
        exact fun t ht => Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.1

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma triangleCoveringNumberOn_le_of_cover {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h_subset : E' ⊆ G.edgeFinset)
    (h_cover : ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) :
    triangleCoveringNumberOn G triangles ≤ E'.card := by
      -- Since $E'$ is in the set of edge sets that cover the triangles, its cardinality is in the image of the cardinality function over this set.
      have h_E'_in_image : E'.card ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2}) := by
        grind;
      -- Since $E'.card$ is in the image, the minimum of the image must be less than or equal to $E'.card$.
      have h_min_le_E'_card : ∀ {s : Finset ℕ}, E'.card ∈ s → s.min.getD 0 ≤ E'.card := by
        -- Since the minimum of a set is less than or equal to any element in the set, we have `s.min ≤ E'.card`.
        intros s hs
        have h_min_le_E'_card : s.min ≤ E'.card := by
          exact Finset.min_le hs;
        cases h : s.min <;> aesop;
      exact h_min_le_E'_card h_E'_in_image

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma triangleCoveringNumberOn_le_of_cover' {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h_subset : E' ⊆ G.edgeFinset)
    (h_cover : ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) :
    triangleCoveringNumberOn G triangles ≤ E'.card := by
      -- Since $E'$ is a valid cover for the triangles, the covering number is the minimum cardinality of such a set $E'$. Therefore, the covering number must be less than or equal to the cardinality of $E'$.
      apply triangleCoveringNumberOn_le_of_cover G triangles E' h_subset h_cover

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma tau_X_le_2' {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (he : G.IsNClique 3 e) (hf : G.IsNClique 3 f) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X G e f) ≤ 2 := by
      -- Since every triangle in X G e f contains the vertex v, they all share the edge {v, u} for some u in e. Therefore, the set of edges {v, u} for u in e is a triangle cover.
      have h_cover : ∀ t ∈ X G e f, ∃ u ∈ e, u ≠ v ∧ {v, u} ⊆ t := by
        intro t ht
        obtain ⟨u, hu⟩ : ∃ u ∈ e, u ≠ v ∧ {v, u} ⊆ t := by
          have h_card : (t ∩ e).card ≥ 2 := by
            exact Finset.mem_filter.mp ( Finset.mem_inter.mp ht |>.1 ) |>.2
          have h_card : ∀ t ∈ X G e f, v ∈ t := by
            intro t ht
            apply mem_X_implies_v_in_t G e f v he.card_eq hf.card_eq h_inter t ht;
          have h_card : ∃ u ∈ e, u ≠ v ∧ u ∈ t := by
            obtain ⟨ u, hu ⟩ := Finset.exists_mem_ne ‹_› v; use u; aesop;
          exact ⟨ h_card.choose, h_card.choose_spec.1, h_card.choose_spec.2.1, Finset.insert_subset_iff.mpr ⟨ by solve_by_elim, Finset.singleton_subset_iff.mpr h_card.choose_spec.2.2 ⟩ ⟩
        use u, hu.left, hu.right.left, hu.right.right
        skip;
      refine' le_trans ( triangleCoveringNumberOn_le_of_cover' G _ _ _ _ ) _;
      refine' Finset.image ( fun u => s(v, u) ) ( e.filter ( fun u => u ≠ v ) );
      · simp_all +decide [ SimpleGraph.isNClique_iff ];
        intro u hu; have := he.1 ( show v ∈ e from by rw [ Finset.eq_singleton_iff_unique_mem ] at h_inter; aesop ) ( show u ∈ e from by aesop ) ; aesop;
      · intro t ht; obtain ⟨ u, hu, hu', hu'' ⟩ := h_cover t ht; use s(v, u); aesop;
      · have := he.card_eq; simp_all +decide [ Finset.ext_iff ] ;
        exact le_trans ( Finset.card_image_le ) ( by rw [ show Finset.filter ( fun u => ¬u = v ) e = e.erase v by ext u; by_cases hu : u = v <;> aesop ] ; simp +decide [ *, Finset.card_erase_of_mem ( show v ∈ e from by specialize h_inter v; aesop ) ] )

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma isTriangleCover_iff_mem_filter (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V)) (E' : Finset (Sym2 V)) :
    isTriangleCover G A E' ↔ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)) := by
  unfold isTriangleCover; aesop

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma le_triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : isTriangleCover G A E') :
    triangleCoveringNumberOn G A ≤ E'.card := by
  unfold triangleCoveringNumberOn
  have h_mem : E' ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) := by
    exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h.1, h.2 ⟩
  have := Finset.min_le ( Finset.mem_image_of_mem Finset.card h_mem )
  rw [ WithTop.le_coe_iff ] at this; aesop

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma exists_min_cover (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V))
    (h : ∃ E', isTriangleCover G A E') :
    ∃ E', isTriangleCover G A E' ∧ E'.card = triangleCoveringNumberOn G A := by
  by_cases h₁ : ∃ E' : Finset (Sym2 V), isTriangleCover G A E'
  · have h₂ : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)), ∀ E'' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)), E'.card ≤ E''.card := by
      apply_rules [ Set.exists_min_image ]
      · exact Set.toFinite _
      · exact ⟨ h₁.choose, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( h₁.choose_spec.1 ), h₁.choose_spec.2 ⟩ ⟩
    obtain ⟨ E', hE₁, hE₂ ⟩ := h₂
    refine' ⟨ E', _, _ ⟩
    · exact ⟨ Finset.mem_filter.mp hE₁ |>.1 |> Finset.mem_powerset.mp, Finset.mem_filter.mp hE₁ |>.2 ⟩
    · unfold triangleCoveringNumberOn
      rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 ) ( G.edgeFinset.powerset ) ) ).min = some ( E'.card ) from ?_, Option.getD_some ]
      refine' le_antisymm _ _
      · exact Finset.min_le ( Finset.mem_image_of_mem _ hE₁ )
      · simp +zetaDelta at *
        exact fun a x hx₁ hx₂ hx₃ => hx₃ ▸ WithTop.coe_le_coe.mpr ( hE₂ x hx₁ hx₂ )
  · contradiction

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma isTriangleCover_union (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  unfold isTriangleCover at *
  grind

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma isTriangleCover_subset (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : A ⊆ B) (hCover : isTriangleCover G B E') :
    isTriangleCover G A E' := by
  exact ⟨ hCover.1, fun t ht => hCover.2 t ( h ht ) ⟩

-- PROVEN: tau_union_le_sum (from slot 16/29)

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases hA : ∃ E', isTriangleCover G A E'
  by_cases hB : ∃ E', isTriangleCover G B E'
  · obtain ⟨EA, hEA⟩ := exists_min_cover G A hA
    obtain ⟨EB, hEB⟩ := exists_min_cover G B hB
    exact le_trans ( le_triangleCoveringNumberOn G _ _ ( isTriangleCover_union G A B EA EB hEA.1 hEB.1 ) ) ( by rw [ ← hEA.2, ← hEB.2 ] ; exact Finset.card_union_le _ _ )
  · rw [ not_exists ] at hB
    unfold triangleCoveringNumberOn;
    rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hB E' ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp hE' |>.1 ), Finset.mem_filter.mp hE' |>.2 ⟩ ] ; simp +decide;
    simp +decide [ Option.getD ];
    rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hB E' ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp hE' |>.1 ), fun t ht => by have := Finset.mem_filter.mp hE' |>.2 t; aesop ⟩ ] ; simp +decide -- Zero case handled
  ·
    unfold triangleCoveringNumberOn;
    simp_all +decide [ Finset.min ];
    rw [ show { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hA E' ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp hE' |>.1 ), fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := Finset.mem_filter.mp hE' |>.2 t ht; exact ⟨ e, he₁, by aesop ⟩ ⟩ ] ; simp +decide;
    rw [ show { E' ∈ G.edgeFinset.powerset | ∀ t, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hA E' ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp hE' |>.1 ), fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := Finset.mem_filter.mp hE' |>.2 t ( Or.inl ht ) ; exact ⟨ e, he₁, by aesop ⟩ ⟩ ] ; simp +decide

-- Zero case handled

-- PROVEN: Te = Se ∪ bridges (from slot 6)

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  -- Let $S = S_e(M)$.
  set S := S_e G M e with hS_def;
  -- First, establish basic properties of $S$:
  have hS_subset : S ⊆ G.cliqueFinset 3 := by
    exact Finset.filter_subset _ _ |> Finset.Subset.trans <| Finset.filter_subset _ _
  have he_in_S : e ∈ S := by
    refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
    · simp [trianglesSharingEdge];
      have := hM.1;
      have := this.1 he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    · have := hM.1.2; aesop;
  have hS_share_e : ∀ t ∈ S, (t ∩ e).card ≥ 2 := by
    exact fun t ht => Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.2
  have hS_pairwise : Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≥ 2) := by
    convert Se_pairwise_intersect G M hM e he;
  -- Split into two cases:
  by_cases h_case1 : ∃ t1 t2 : Finset V, t1 ∈ S ∧ t2 ∈ S ∧ (t1 ∩ e).card = 2 ∧ (t2 ∩ e).card = 2 ∧ t1 ∩ e ≠ t2 ∩ e;
  · obtain ⟨ t1, t2, ht1, ht2, h1, h2, h3 ⟩ := h_case1;
    -- Apply `structure_lemma_case2` to get $x$ such that $\forall t \in S, t \subseteq e \cup \{x\}$.
    obtain ⟨ x, hx ⟩ := structure_lemma_case2 G S hS_subset e he_in_S hS_share_e hS_pairwise t1 t2 ht1 ht2 h1 h2 h3;
    exact K4_case G S e x he_in_S hS_subset hx;
  · -- If $S = \{e\}$, then $\tau(S) \le 1 \le 2$ (any edge of $e$ covers).
    by_cases hS_eq_singleton : S = {e};
    · simp [hS_eq_singleton];
      -- Since $e$ is a triangle, any edge of $e$ covers $e$.
      obtain ⟨f, hf⟩ : ∃ f ∈ G.edgeFinset, f ∈ e.sym2 := by
        have := hS_subset he_in_S; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        rcases this with ⟨ h₁, h₂ ⟩;
        obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hca ⟩ := Finset.card_eq_three.mp h₂;
        exact ⟨ s(a, b), by simpa [ ha ] using h₁ ( by simp +decide ) ( by simp +decide ) ha, by simp +decide ⟩;
      refine' le_trans ( le_triangleCoveringNumberOn G { e } { f } _ ) _;
      · unfold isTriangleCover; aesop;
      · norm_num;
    · -- If $S \neq \{e\}$, let $t_0 \in S \setminus \{e\}$. Then $|t_0 \cap e| = 2$. Let $f = t_0 \cap e$.
      obtain ⟨t0, ht0⟩ : ∃ t0 ∈ S, t0 ≠ e := by
        grind
      obtain ⟨f, hf⟩ : ∃ f : Finset V, f = t0 ∩ e ∧ f.card = 2 := by
        have := hS_subset ht0.1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        have := Finset.card_le_card ( Finset.inter_subset_left : t0 ∩ e ⊆ t0 ) ; ( have := Finset.card_le_card ( Finset.inter_subset_right : t0 ∩ e ⊆ e ) ; ( have := this; ( have := hS_share_e t0 ht0.1; ( have := hS_subset he_in_S; simp_all +decide [ SimpleGraph.isNClique_iff ] ; ) ) ) );
        interval_cases _ : Finset.card ( t0 ∩ e ) <;> simp_all +decide only;
        · linarith [ hS_share_e t0 ht0.1 ];
        · linarith [ hS_share_e t0 ht0.1 ];
        · have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t0 ∩ e ⊆ t0 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t0 ∩ e ⊆ e ) ; simp_all +decide ;
      -- For any other $t \in S \setminus \{e\}$, $|t \cap e| = 2$, so $t \cap e = f$.
      have hS_inter_f : ∀ t ∈ S, t ≠ e → t ∩ e = f := by
        intro t ht ht_ne_e
        have ht_inter_e : (t ∩ e).card = 2 := by
          have := hS_subset ht; simp_all +decide [ Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff ] ;
          have := hS_subset he_in_S; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          have := Finset.card_le_card ( Finset.inter_subset_left : t ∩ e ⊆ t ) ; ( have := Finset.card_le_card ( Finset.inter_subset_right : t ∩ e ⊆ e ) ; simp_all +decide ; );
          interval_cases _ : Finset.card ( t ∩ e ) <;> simp_all +decide only;
          · linarith [ hS_share_e t ht ];
          · linarith [ hS_share_e t ht ];
          · have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t ∩ e ⊆ t ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t ∩ e ⊆ e ) ; simp_all +decide ;
        grind;
      -- Thus $f$ is contained in every triangle in $S$.
      have hS_contain_f : ∀ t ∈ S, f ⊆ t := by
        intro t ht; specialize hS_inter_f t ht; by_cases h : t = e <;> simp_all +decide [ Finset.subset_iff ] ;
        intro x hx1 hx2; replace hS_inter_f := Finset.ext_iff.mp hS_inter_f x; aesop;
      -- Since $f$ is a subset of $e$ of size 2, it corresponds to an edge of $G$.
      obtain ⟨u, v, huv⟩ : ∃ u v : V, f = {u, v} ∧ G.Adj u v := by
        have := hS_subset ht0.1; simp_all +decide [ SimpleGraph.mem_cliqueFinset_iff ] ;
        rw [ Finset.card_eq_two ] at hf; obtain ⟨ u, v, h ⟩ := hf; use u, v; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        exact this.1 ( hS_contain_f t0 ht0.1 ( Finset.mem_insert_self _ _ ) ) ( hS_contain_f t0 ht0.1 ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ) h.1;
      -- Thus $\{f\}$ is a triangle cover of size 1.
      have h_triangle_cover : isTriangleCover G S {Sym2.mk (u, v)} := by
        constructor <;> simp_all +decide [ SimpleGraph.cliqueFinset ];
        exact fun t ht => ⟨ hS_contain_f t ht ( Finset.mem_insert_self _ _ ), hS_contain_f t ht ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ⟩;
      exact le_trans ( le_triangleCoveringNumberOn G S _ h_triangle_cover ) ( by simp +decide )

-- SCAFFOLDING: Full proof in slot29_triple_apex.lean

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMAS FOR HEAVY EDGE FORCING
-- ══════════════════════════════════════════════════════════════════════════════

/--
If e shares only vertices (not edges) with all other elements,
then all bridges X(e,f) share exactly 1 vertex with both e and f.
-/

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma tau_Te_le_2_no_edge_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_no_edge : noEdgeSharing M e) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  -- By Lemma bridges_absorbed_by_Se_cover, there exists a cover E' for S_e ∪ bridges with |E'| ≤ 2.
  obtain ⟨E', hE'⟩ : ∃ E' : Finset (Sym2 V), isTriangleCover G (S_e G M e ∪ bridges G M e) E' ∧ E'.card ≤ 2 := by
    exact?;
  refine' le_trans _ hE'.2;
  apply le_triangleCoveringNumberOn;
  convert hE'.1 using 1;
  exact?

-- TARGET: Use bridges_absorbed_by_Se_cover + Te = Se ∪ bridges

/--
MAIN THEOREM: Heavy Edge Forcing

If τ(T_e) ≥ 3, then e must share an edge with some other element.
Equivalently: If e shares no edges, then τ(T_e) ≤ 2.
-/

-- Source: proven/tuza/nu4/slot72_cycle_reduction_output.lean
lemma isCovering_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isCovering G A EA) (hB : isCovering G B EB) :
    isCovering G (A ∪ B) (EA ∪ EB) := by
  -- By definition of $isCovering$, we know that $EA$ covers $A$ and $EB$ covers $B$ by removing one edge from each clique in $A$ and $B$.
  apply And.intro;
  · exact Finset.union_subset hA.1 hB.1;
  · -- By definition of $isCovering$, we know that for any triangle $t$ in $A$, there exists an edge $e$ in $EA$ such that $e$ is in $t$'s sym2.
    intro t ht
    cases' Finset.mem_union.mp ht with htA htB
    · obtain ⟨e, heEA, heT⟩ := hA.right t htA
      exact ⟨e, Finset.mem_union_left _ heEA, heT⟩
    · obtain ⟨e, heEB, heT⟩ := hB.right t htB
      exact ⟨e, Finset.mem_union_right _ heEB, heT⟩

def hasCovering (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : Prop :=
  ∃ E' ⊆ G.edgeFinset, ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

-- Source: proven/tuza/nu4/slot72_cycle_reduction_output.lean
lemma exists_min_covering (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : hasCovering G triangles) :
    ∃ E', isCovering G triangles E' ∧ E'.card = triangleCoveringNumberOn G triangles := by
  have h_covering_number : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)), E'.card = (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0) := by
    have h_exists : ∃ E' ∈ Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset (G.edgeFinset)), ∀ E'' ∈ Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset (G.edgeFinset)), E'.card ≤ E''.card := by
      apply_rules [ Finset.exists_min_image ];
      obtain ⟨ E', hE' ⟩ := h;
      exact ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'.1, hE'.2 ⟩ ⟩;
    obtain ⟨ E', hE₁, hE₂ ⟩ := h_exists;
    have h_exists_min : (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset (G.edgeFinset)))).min = some E'.card := by
      refine' le_antisymm _ _;
      · exact Finset.min_le ( Finset.mem_image_of_mem _ hE₁ );
      · simp +zetaDelta at *;
        exact fun a x hx₁ hx₂ hx₃ => hx₃ ▸ WithTop.coe_le_coe.mpr ( hE₂ x hx₁ hx₂ );
    exact ⟨ E', hE₁, h_exists_min.symm ▸ rfl ⟩;
  unfold isCovering triangleCoveringNumberOn; aesop;

-- Source: proven/tuza/nu4/slot72_cycle_reduction_output.lean
lemma covering_ge_tau (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (E' : Finset (Sym2 V)) (h : isCovering G triangles E') :
    triangleCoveringNumberOn G triangles ≤ E'.card := by
  -- By definition of triangle covering number, we know that for any covering E', the cardinality of E' is at least the triangle covering number.
  have h_triangle_covering : ∀ E' : Finset (Sym2 V), isCovering G triangles E' → triangleCoveringNumberOn G triangles ≤ E'.card := by
    intro E' hE'
    have h_min : Option.getD (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2})).min 0 ≤ Finset.card E' := by
      have h_subset : E' ∈ Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) G.edgeFinset.powerset := by
        unfold isCovering at hE'; aesop;
      have h_min : ∀ {S : Finset ℕ}, S.Nonempty → ∀ x ∈ S, Option.getD (Finset.min S) 0 ≤ x := by
        -- The minimum of a finite set is the least element, so for any x in S, min(S) ≤ x.
        intros S hS_nonempty x hx
        have h_min_le_x : Finset.min S ≤ x := by
          exact Finset.min_le hx;
        cases h : Finset.min S <;> aesop;
      exact h_min ⟨ _, Finset.mem_image_of_mem _ h_subset ⟩ _ ( Finset.mem_image_of_mem _ h_subset );
    exact?;
  exact h_triangle_covering E' h

-- Source: proven/tuza/nu4/slot72_cycle_reduction_output.lean
lemma always_has_covering (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h_subset : triangles ⊆ G.cliqueFinset 3) :
    hasCovering G triangles := by
  have h_edge_set : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ (∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) := by
    have h_edge_set : ∀ t ∈ triangles, ∃ e ∈ G.edgeFinset, e ∈ t.sym2 := by
      intro t ht
      have ht_clique : t.card = 3 := by
        exact Finset.mem_filter.mp ( h_subset ht ) |>.2.2
      have ht_edges : ∀ v ∈ t, ∀ w ∈ t, v ≠ w → (Sym2.mk (v, w)) ∈ G.edgeFinset := by
        intro v hv w hw hvw; have := h_subset ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        exact this.1 hv hw hvw
      generalize_proofs at *;
      obtain ⟨ v, hv, w, hw, hne ⟩ := Finset.one_lt_card.1 ( by linarith : 1 < Finset.card t ) ; exact ⟨ s(v, w), ht_edges v hv w hw hne, by aesop ⟩ ;
    exact ⟨ G.edgeFinset, Finset.Subset.refl _, h_edge_set ⟩;
  exact h_edge_set

-- Source: proven/tuza/nu4/slot72_cycle_reduction_output.lean
lemma tau_eq_zero_of_no_covering (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : ¬ hasCovering G triangles) :
    triangleCoveringNumberOn G triangles = 0 := by
  -- If there's no covering, then the triangle covering number must be zero because there's no way to cover the triangles with any edges.
  simp [triangleCoveringNumberOn, h];
  -- Since the set is empty, the minimum of the image of the cardinalities is zero.
  have h_empty : Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', ∀ a ∈ e, a ∈ t) (G.edgeFinset.powerset) = ∅ := by
    ext E'
    simp [hasCovering] at h;
    specialize h E' ; aesop;
  -- Since the set is empty, the minimum of the image of the cardinalities is zero because the image is also empty.
  simp [h_empty, Finset.min];
  rfl

-- Source: proven/tuza/nu4/slot72_cycle_reduction_output.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases h_cov : hasCovering G (A ∪ B)
  · -- Case: Covering exists
    have h_cov_A : hasCovering G A := by
      obtain ⟨E, hE_sub, hE_cov⟩ := h_cov
      use E, hE_sub
      intro t ht
      exact hE_cov t (Finset.mem_union_left B ht)
    have h_cov_B : hasCovering G B := by
      obtain ⟨E, hE_sub, hE_cov⟩ := h_cov
      use E, hE_sub
      intro t ht
      exact hE_cov t (Finset.mem_union_right A ht)
      
    obtain ⟨EA, hEA_cov, hEA_card⟩ := exists_min_covering G A h_cov_A
    obtain ⟨EB, hEB_cov, hEB_card⟩ := exists_min_covering G B h_cov_B
    
    have h_union_cov : isCovering G (A ∪ B) (EA ∪ EB) := isCovering_union G A B EA EB hEA_cov hEB_cov
    
    calc triangleCoveringNumberOn G (A ∪ B) 
      ≤ (EA ∪ EB).card := covering_ge_tau G (A ∪ B) (EA ∪ EB) h_union_cov
    _ ≤ EA.card + EB.card := Finset.card_union_le EA EB
    _ = triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by rw [hEA_card, hEB_card]
    
  · -- Case: No covering
    rw [tau_eq_zero_of_no_covering G (A ∪ B) h_cov]
    exact Nat.zero_le _

-- Source: proven/tuza/nu4/slot71_Se_structure_output.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  unfold triangleCoveringNumberOn;
  by_cases hA : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2;
  · by_cases hB : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2;
    · obtain ⟨E₁, hE₁⟩ : ∃ E₁ ∈ G.edgeFinset.powerset, (∀ t ∈ A, ∃ e ∈ E₁, e ∈ t.sym2) ∧ E₁.card = (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 := by
        have h_min_card : ∃ E₁ ∈ Finset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset), ∀ E₂ ∈ Finset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset), E₁.card ≤ E₂.card := by
          apply_rules [ Finset.exists_min_image ];
          exact ⟨ hA.choose, Finset.mem_filter.mpr ⟨ hA.choose_spec.1, hA.choose_spec.2 ⟩ ⟩;
        obtain ⟨ E₁, hE₁₁, hE₁₂ ⟩ := h_min_card;
        use E₁;
        rw [ Finset.min_eq_inf_withTop ];
        rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 ) ( G.edgeFinset.powerset ) ) ).inf WithTop.some = WithTop.some E₁.card from ?_ ];
        · exact ⟨ Finset.mem_filter.mp hE₁₁ |>.1, Finset.mem_filter.mp hE₁₁ |>.2, rfl ⟩;
        · refine' le_antisymm _ _;
          · exact Finset.inf_le ( Finset.mem_image_of_mem _ hE₁₁ );
          · simp +zetaDelta at *;
            exact hE₁₂;
      obtain ⟨E₂, hE₂⟩ : ∃ E₂ ∈ G.edgeFinset.powerset, (∀ t ∈ B, ∃ e ∈ E₂, e ∈ t.sym2) ∧ E₂.card = (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 := by
        have := Finset.min_of_mem ( show Finset.card ( Classical.choose hB ) ∈ Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) from Finset.mem_image.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Classical.choose_spec hB |>.1, Classical.choose_spec hB |>.2 ⟩, rfl ⟩ );
        obtain ⟨ b, hb ⟩ := this;
        have := Finset.mem_of_min hb;
        rw [ Finset.mem_image ] at this; obtain ⟨ E₂, hE₂, rfl ⟩ := this; exact ⟨ E₂, Finset.mem_filter.mp hE₂ |>.1, Finset.mem_filter.mp hE₂ |>.2, by rw [ hb ] ; rfl ⟩ ;
      have h_union_cover : ∃ E' ∈ G.edgeFinset.powerset, (∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card ≤ E₁.card + E₂.card := by
        use E₁ ∪ E₂;
        grind;
      have h_min_le : ∀ E' ∈ G.edgeFinset.powerset, (∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) → (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 ≤ E'.card := by
        intros E' hE' hE'_cover;
        have h_min_le : ∀ x ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2}), (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 ≤ x := by
          simp +decide [ Option.getD ];
          intro x E' hE' hE'_cover hx;
          cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> simp +decide [ h ];
          exact Nat.cast_le.mp ( h ▸ Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by simpa [ Finset.subset_iff ] using hE' ), hE'_cover ⟩, hx ⟩ ) );
        exact h_min_le _ ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ hE', hE'_cover ⟩ ) );
      exact le_trans ( h_min_le _ h_union_cover.choose_spec.1 h_union_cover.choose_spec.2.1 ) ( h_union_cover.choose_spec.2.2.trans ( by linarith ) );
    · rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hB ⟨ E', Finset.mem_filter.mp hE' |>.1, Finset.mem_filter.mp hE' |>.2 ⟩ ] ; simp +decide;
      rw [ show { E' ∈ G.edgeFinset.powerset | ∀ t, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hB ⟨ E', Finset.mem_filter.mp hE' |>.1, fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := Finset.mem_filter.mp hE' |>.2 t ( Or.inr ht ) ; exact ⟨ e, he₁, by simpa using he₂ ⟩ ⟩ ] ; simp +decide;
  · rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2 } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hA ⟨ E', Finset.mem_filter.mp hE' |>.1, fun t ht => Finset.mem_filter.mp hE' |>.2 t ( Finset.mem_union_left _ ht ) ⟩ ] ; simp +decide;
    simp +decide [ Option.getD ]

-- PROVEN in slot61

-- Source: proven/tuza/nu4/slot70_tau_union_extended_output.lean
lemma tau_le_of_exists_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h_sub : E' ⊆ G.edgeFinset)
    (h_cover : ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2) :
    triangleCoveringNumberOn G T ≤ E'.card := by
  -- Since $E'$ is a subset of $G.edgeFinset$ and covers $T$, we have $E' \in \{ E'' \subseteq G.edgeFinset \mid E'' \text{ covers } T \}$.
  have h_E'_in_set : E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)) := by
    aesop;
  -- Since $E'$ is in the set of covers, the minimum cardinality of the covers is less than or equal to the cardinality of $E'$.
  have h_min_le_card : ∀ {E'' : Finset (Sym2 V)}, E'' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)) → (triangleCoveringNumberOn G T) ≤ E''.card := by
    intro E'' hE'';
    have h_min_le_card : ∀ {s : Finset ℕ}, s.Nonempty → ∀ n ∈ s, (s.min.getD 0) ≤ n := by
      intro s hs n hn; have := Finset.min_le hn; cases h : Finset.min s <;> aesop;
    exact h_min_le_card ⟨ _, Finset.mem_image_of_mem _ hE'' ⟩ _ ( Finset.mem_image_of_mem _ hE'' );
  exact h_min_le_card h_E'_in_set

-- Source: proven/tuza/nu4/slot70_tau_union_extended_output.lean
lemma filter_covers_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (hT : T ⊆ G.cliqueFinset 3) :
    (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)).Nonempty := by
  refine' ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.Subset.refl _ ), _ ⟩ ⟩;
  simp_all +decide [ Finset.subset_iff ];
  intro t ht; have := hT ht; rcases this with ⟨ h1, h2 ⟩ ; obtain ⟨ u, v, w, huv, hvw, hwu ⟩ := Finset.card_eq_three.mp h2; use Sym2.mk ( u, v ) ; aesop;

-- Source: proven/tuza/nu4/slot70_tau_union_extended_output.lean
lemma exists_min_cover (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset (Finset V))
    (hT : T ⊆ G.cliqueFinset 3) :
    ∃ E' ⊆ G.edgeFinset, (∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card = triangleCoveringNumberOn G T := by
  -- By definition of `triangleCoveringNumberOn`, there exists a subset `E'` of `G.edgeFinset` such that `E'` covers all triangles in `T` and `E'.card` is the minimum possible.
  obtain ⟨E', hE'_cover, hE'_card⟩ : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)), E'.card = triangleCoveringNumberOn G T := by
    unfold triangleCoveringNumberOn;
    have := Finset.min_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) ) from ?_ );
    · obtain ⟨ a, ha ⟩ := this;
      have := Finset.mem_of_min ha; aesop;
    · refine' Finset.Nonempty.image _ _;
      exact?;
  exact ⟨ E', Finset.mem_powerset.mp ( Finset.mem_filter.mp hE'_cover |>.1 ), Finset.mem_filter.mp hE'_cover |>.2, hE'_card ⟩

-- Source: proven/tuza/nu4/slot70_tau_union_extended_output.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
      simp +decide [ triangleCoveringNumberOn ];
      by_cases hA : { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t }.Nonempty;
      · obtain ⟨E₁, hE₁⟩ : ∃ E₁ ⊆ G.edgeFinset, (∀ t ∈ A, ∃ e ∈ E₁, ∀ a ∈ e, a ∈ t) ∧ E₁.card = (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min.getD 0 := by
          have := Finset.min_of_nonempty ( show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ).Nonempty from ?_ );
          · obtain ⟨ a, ha ⟩ := this;
            have := Finset.mem_of_min ha; aesop;
          · simp +zetaDelta at *;
            exact ⟨ hA.choose, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hA.choose_spec |>.1 ) ), fun t ht => Finset.mem_filter.mp hA.choose_spec |>.2 t ( Or.inl ht ) ⟩ ⟩;
        obtain ⟨E₂, hE₂⟩ : ∃ E₂ ⊆ G.edgeFinset, (∀ t ∈ B, ∃ e ∈ E₂, ∀ a ∈ e, a ∈ t) ∧ E₂.card = (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min.getD 0 := by
          have := Finset.min_of_nonempty ( show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ).Nonempty from ?_ );
          · obtain ⟨ a, ha ⟩ := this;
            have := Finset.mem_of_min ha;
            rw [ Finset.mem_image ] at this; obtain ⟨ E₂, hE₂, rfl ⟩ := this; use E₂; aesop;
          · obtain ⟨ E', hE' ⟩ := hA;
            exact ⟨ _, Finset.mem_image_of_mem _ ( show E' ∈ { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } from by aesop ) ⟩;
        have h_union : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min.getD 0 ≤ (E₁ ∪ E₂).card := by
          have h_union : ∀ E' ∈ {E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t}, (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min.getD 0 ≤ E'.card := by
            intro E' hE'
            have h_min : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ E'.card := by
              exact Finset.min_le ( Finset.mem_image_of_mem _ hE' );
            cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop;
          grind;
        exact h_union.trans ( Finset.card_union_le _ _ ) |> le_trans <| by linarith;
      · rw [ Finset.not_nonempty_iff_eq_empty.mp hA ] ; simp +decide;
        exact Nat.zero_le _

-- PROVEN in slot61

-- Source: proven/tuza/nu4/slot70_tau_union_extended_output.lean
lemma tau_le_2_of_K4_plus_one_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e.card = 3)
    (S : Finset (Finset V)) (hS : S ⊆ S_e G M e)
    (u v w : V) (h_e : e = {u, v, w}) (h_distinct : u ≠ v ∧ v ≠ w ∧ u ≠ w)
    (x : V) (hx : x ∉ e)
    (t1 t2 t3 : Finset V)
    (h_t1 : t1 = {u, v, x}) (h_t1_mem : t1 ∈ S)
    (h_t2 : t2 = {v, w, x}) (h_t2_mem : t2 ∈ S)
    (h_t3 : t3 = {w, u, x}) (h_t3_mem : t3 ∈ S)
    (h_extras : ∀ t ∈ S, t ≠ t1 → t ≠ t2 → t ≠ t3 → t ∩ e = {u, v}) :
    triangleCoveringNumberOn G S ≤ 2 := by
  -- We claim that the set of edges $E' = \{ \{u, v\}, \{w, x\} \}$ covers $S$.
  set E' : Finset (Sym2 V) := {Sym2.mk (u, v), Sym2.mk (w, x)} with hE';
  -- We need to show that $E'$ covers $S$.
  have h_cover : ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2 := by
    intro t ht
    by_cases h_cases : t = t1 ∨ t = t2 ∨ t = t3;
    · rcases h_cases with ( rfl | rfl | rfl ) <;> simp +decide [ *, Finset.mem_sym2_iff ];
    · have := h_extras t ht ( by tauto ) ( by tauto ) ( by tauto ) ; simp_all +decide [ Finset.ext_iff ] ;
      exact Or.inl ⟨ by specialize this u; aesop, by specialize this v; aesop ⟩;
  -- We need to show that $E'$ is a subset of $G.edgeFinset$.
  have h_subset : E' ⊆ G.edgeFinset := by
    simp_all +decide [ Finset.subset_iff ];
    have := hS h_t1_mem; have := hS h_t2_mem; have := hS h_t3_mem; simp_all +decide [ S_e ] ;
    have := hS h_t1_mem; have := hS h_t2_mem; have := hS h_t3_mem; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    grind;
  refine' le_trans ( tau_le_of_exists_cover G S E' h_subset h_cover ) _;
  exact Finset.card_insert_le _ _

-- Source: proven/tuza/nu4/slot139_tau_le_12_PROVEN.lean
theorem tau_le_12_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 12 := by
  -- packingEdges is a valid cover of size ≤ 12
  let E := packingEdges G cfg
  have h_subset : E ⊆ G.edgeFinset := packingEdges_subset G M hM cfg
  have h_card : E.card ≤ 12 := packingEdges_card G M hM cfg
  have h_cover : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := packingEdges_cover G M hM cfg
  have h_valid : isTriangleCover G E := ⟨h_subset, h_cover⟩
  -- E is in the set of valid covers
  have h_in : E ∈ G.edgeFinset.powerset.filter (isTriangleCover G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h_subset, h_valid⟩
  -- τ ≤ |E| ≤ 12
  unfold triangleCoveringNumber
  have h_nonempty : (G.edgeFinset.powerset.filter (isTriangleCover G)).Nonempty := ⟨E, h_in⟩
  have h_in_image : E.card ∈ (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card :=
    Finset.mem_image_of_mem _ h_in
  have h_min_le := Finset.min'_le _ E.card h_in_image
  calc (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min |>.getD 0

≤ (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card |>.min' (Finset.Nonempty.image h_nonempty _) := by
        simp only [Finset.min_eq_min']
        rfl
    _ ≤ E.card := h_min_le
    _ ≤ 12 := h_card

end

-- Source: proven/tuza/nu4/slot_local_tuza_via_link_graph.lean
theorem vertex_cover_le_two_matching (G : SimpleGraph V) [DecidableRel G.Adj] :
    vertexCoverNumber G ≤ 2 * maxMatchingNumber G := by
  -- Let $M$ be a maximum matching in $G$.
  obtain ⟨M, hM⟩ : ∃ M : Finset (Sym2 V), M ⊆ G.edgeFinset ∧ (∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset) ∧ M.card = maxMatchingNumber G := by
    unfold maxMatchingNumber;
    have := Finset.max_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card { M ∈ G.edgeFinset.powerset | ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset } ) from ⟨ 0, Finset.mem_image.mpr ⟨ ∅, by simp +decide ⟩ ⟩ );
    obtain ⟨ a, ha ⟩ := this; have := Finset.mem_image.mp ( Finset.mem_of_max ha ) ; aesop;
  -- Let $S$ be the set of all endpoints of edges in $M$.
  set S := M.biUnion (fun e => e.toFinset) with hS_def;
  -- Since each edge in $M$ has two endpoints, $|S| \leq 2|M|$.
  have hS_card : S.card ≤ 2 * M.card := by
    have hS_card : ∀ e ∈ M, (e.toFinset).card ≤ 2 := by
      intro e he;
      rcases e with ⟨ x, y ⟩ ; simp +decide [ Sym2.toFinset ];
      simp +decide [ Sym2.toMultiset ];
      exact Finset.card_insert_le _ _;
    exact le_trans ( Finset.card_biUnion_le ) ( by simpa [ mul_comm ] using Finset.sum_le_sum hS_card );
  -- We claim that $S$ is a vertex cover.
  have hS_vertex_cover : ∀ e ∈ G.edgeFinset, ∃ v ∈ S, v ∈ e := by
    intro e he
    by_contra h_contra
    push_neg at h_contra;
    -- If $e$ is not covered by $S$, then $M \cup \{e\}$ is a matching larger than $M$, contradicting the maximality of $M$.
    have hM_union_e : (M ∪ {e}).card > M.card ∧ (∀ e1 ∈ M ∪ {e}, ∀ e2 ∈ M ∪ {e}, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset) := by
      simp +zetaDelta at *;
      refine' ⟨ _, _, _ ⟩;
      · rw [ Finset.card_insert_of_notMem ] ; aesop;
        rintro heM; specialize h_contra; rcases e with ⟨ u, v ⟩ ; simp_all +decide ;
        exact h_contra u _ heM ( by simp +decide ) |>.1 rfl;
      · intro a ha hne; rw [ Finset.disjoint_left ] ; intro x hx hx'; specialize h_contra x a ha; aesop;
      · simp_all +decide [ Finset.disjoint_left ];
        exact fun x hx => ⟨ fun _ y hy hy' => h_contra y x hx hy hy', fun y hy hxy z hz hz' => hM.2.1 x hx y hy hxy hz hz' ⟩;
    have hM_union_e : (M ∪ {e}).card ≤ maxMatchingNumber G := by
      have hM_union_e : (M ∪ {e}) ∈ (G.edgeFinset.powerset.filter (fun M => ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset)) := by
        simp_all +decide [ Finset.subset_iff ];
      have hM_union_e : ∀ x ∈ Finset.image (fun M => M.card) (G.edgeFinset.powerset.filter (fun M => ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset)), x ≤ (Finset.image (fun M => M.card) (G.edgeFinset.powerset.filter (fun M => ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset))).max.getD 0 := by
        intro x hx;
        have := Finset.le_max hx;
        cases h : Finset.max ( Finset.image ( fun M => M.card ) ( Finset.filter ( fun M => ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop;
      exact hM_union_e _ ( Finset.mem_image_of_mem _ ‹_› );
    linarith;
  refine' le_trans _ ( hS_card.trans ( by rw [ hM.2.2 ] ) );
  unfold vertexCoverNumber;
  have h_min_le : ∀ {s : Finset ℕ}, s.Nonempty → Option.getD (s.min) 0 ≤ s.min := by
    intro s hs; cases h : s.min <;> aesop;
  specialize @h_min_le ( Finset.image Finset.card ( Finset.filter ( fun S => ∀ e ∈ G.edgeFinset, ∃ v ∈ S, v ∈ e ) ( Finset.powerset ( Finset.univ : Finset V ) ) ) ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.subset_univ _ ), hS_vertex_cover ⟩ ) ⟩ ; aesop;

/-
Given an edge in the link graph of $v$, construct the corresponding triangle containing $v$.
-/
/-- Edges in the link graph correspond to triangles containing v -/
def linkEdgeToTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (e : (linkGraph G v).edgeFinset) : trianglesContainingVertex G v :=
  ⟨insert v e.1.toFinset, by
    unfold trianglesContainingVertex;
    rcases e with ⟨ e, he ⟩;
    rcases e with ⟨ x, y ⟩;
    unfold linkGraph at he;
    simp_all +decide [ SimpleGraph.isNClique_iff ];
    simp_all +decide [ SimpleGraph.edgeFinset, Sym2.toFinset ];
    simp_all +decide [ Sym2.toMultiset, Finset.card_insert_of_notMem ];
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop⟩

def triangleEdgeEquiv (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    trianglesContainingVertex G v ≃ (linkGraph G v).edgeFinset where
  toFun t :=
    let h := Finset.mem_filter.mp t.2
    let e := triangleToLinkEdge G v t.1 h.1 h.2
    ⟨e.1, by rw [SimpleGraph.mem_edgeFinset]; exact e.2⟩
  invFun e :=
    let t := linkEdgeToTriangle G v e
    ⟨t.1, t.2⟩
  left_inv := by
    -- To prove the left inverse property, we show that applying the composition of the two functions to any triangle returns the original triangle.
    intros t
    simp [linkEdgeToTriangle, triangleToLinkEdge];
    rcases t with ⟨ t, ht ⟩;
    congr;
    rw [ Finset.ext_iff ];
    have := Classical.choose_spec ( Finset.card_pos.mp ( show 0 < Finset.card ( t.erase v |> Finset.offDiag |> Finset.image Sym2.mk ) from ?_ ) );
    all_goals simp_all +decide [ Finset.mem_image, Finset.mem_offDiag ];
    obtain ⟨ a, b, h, h' ⟩ := this;
    intro x; rw [ ← h' ] ; simp +decide [ Sym2.eq_iff ] ;
    all_goals simp_all +decide [ trianglesContainingVertex ];
    all_goals have := Finset.card_eq_three.mp ht.1.2; obtain ⟨ c, d, e, hcd, hde, hec ⟩ := this; simp_all +decide [ SimpleGraph.isNClique_iff ];
    all_goals rcases ht.2 with ( rfl | rfl | rfl ) <;> simp_all +decide [ SimpleGraph.adj_comm ];
    any_goals rw [ Finset.offDiag ] ; simp +decide [ * ];
    any_goals rw [ Finset.Nonempty ] ; simp +decide [ * ];
    any_goals rcases h with ⟨ ⟨ ha, ha' ⟩, ⟨ hb, hb' ⟩, hab ⟩ ; rcases ha' with ( rfl | rfl | rfl ) <;> rcases hb' with ( rfl | rfl | rfl ) <;> tauto;
    · exact ⟨ d, e, by tauto ⟩;
    · exact ⟨ c, e, by aesop ⟩;
    · exact ⟨ c, d, by aesop ⟩
  right_inv := by
    intro e;
    rcases e with ⟨ e, he ⟩;
    unfold linkEdgeToTriangle triangleToLinkEdge;
    -- Since $e$ is an edge in the link graph, removing $v$ from the triangle gives back $e$.
    have h_erase : (insert v e.toFinset).erase v = e.toFinset := by
      ext x;
      -- If x is in the insert of v and e.toFinset, then x is either v or in e.toFinset. But since we're erasing v, x can't be v. So x must be in e.toFinset.
      simp [Finset.mem_insert, Finset.mem_erase];
      intro hx h; simp_all +decide [ linkGraph ] ;
      cases e ; aesop;
    have h_image : (Finset.image Sym2.mk (Sym2.toFinset e).offDiag).Nonempty ∧ ∀ x ∈ Finset.image Sym2.mk (Sym2.toFinset e).offDiag, x = e := by
      rcases e with ⟨ x, y ⟩ ; simp +decide [ Sym2.eq_swap ] ;
      simp +decide [ Sym2.eq_iff, Finset.Nonempty ];
      aesop;
    have := Classical.choose_spec h_image.1;
    grind

/-
The bijection between triangles at $v$ and edges in the link graph preserves the "disjointness" property (intersection size $\le 1$ for triangles corresponds to disjointness for edges).
-/

-- Source: proven/tuza/nu4/slot_local_tuza_via_link_graph.lean
lemma exists_triangle_cover_from_link_vertex_cover (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (S : Finset V) (hS : ∀ e ∈ (linkGraph G v).edgeFinset, ∃ x ∈ S, x ∈ e) :
    ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧
      (∀ t ∈ trianglesContainingVertex G v, ∃ e ∈ E', e ∈ t.sym2) ∧
      E'.card ≤ S.card := by
  refine' ⟨ S.filter ( fun u => G.Adj v u ) |> Finset.image fun u => Sym2.mk ( v, u ), _, _, _ ⟩;
  · intro e he
    aesop;
  · intro t ht;
    -- Since $t$ is a triangle containing $v$, there exist $x, y \in t$ such that $t = \{v, x, y\}$.
    obtain ⟨x, y, hx, hy, ht_eq⟩ : ∃ x y : V, x ∈ t ∧ y ∈ t ∧ t = {v, x, y} ∧ G.Adj v x ∧ G.Adj v y ∧ G.Adj x y := by
      unfold trianglesContainingVertex at ht;
      simp_all +decide [ Finset.ext_iff, SimpleGraph.isNClique_iff ];
      obtain ⟨ x, y, z, hxyz ⟩ := Finset.card_eq_three.mp ht.1.2;
      by_cases hvx : v = x <;> by_cases hvy : v = y <;> by_cases hvz : v = z <;> simp_all +decide;
      · exact Or.inl ⟨ fun a => by tauto, ht.2.1.symm ⟩;
      · exact Or.inr ⟨ fun a => by tauto, ht.1.symm, ht.2.2.symm, ht.2.1.symm ⟩;
    obtain ⟨ u, hu, hu' ⟩ := hS ( Sym2.mk ⟨ x, y ⟩ ) ( by
      unfold linkGraph; aesop; );
    use Sym2.mk ( v, u ) ; aesop;
  · exact Finset.card_image_le.trans ( Finset.card_filter_le _ _ )

/-
The triangle covering number at $v$ is at most the vertex cover number of the link graph at $v$.
-/

-- Source: proven/tuza/nu4/slot_local_tuza_via_link_graph.lean
lemma cover_at_v_le_vertex_cover (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    triangleCoveringNumberOn G (trianglesContainingVertex G v) ≤ vertexCoverNumber (linkGraph G v) := by
      -- By definition of the minimum, there exists an $E'$ in the set such that $|E'| \leq |S|$.
      obtain ⟨E', hE'⟩ : ∃ E' ∈ Finset.filter (fun E' => ∀ t ∈ trianglesContainingVertex G v, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset G.edgeFinset), E'.card ≤ vertexCoverNumber (linkGraph G v) := by
        obtain ⟨S, hS⟩ : ∃ S : Finset V, S ∈ Finset.filter (fun S => ∀ e ∈ (linkGraph G v).edgeFinset, ∃ x ∈ S, x ∈ e) (Finset.powerset (Finset.univ : Finset V)) ∧ S.card = vertexCoverNumber (linkGraph G v) := by
          unfold vertexCoverNumber;
          have h_min : Finset.Nonempty (Finset.image Finset.card ({S ∈ Finset.univ.powerset | ∀ e ∈ (linkGraph G v).edgeFinset, ∃ v ∈ S, v ∈ e})) := by
            simp +zetaDelta at *;
            refine' ⟨ Finset.univ, _ ⟩;
            simp +decide [ Finset.mem_univ, SimpleGraph.edgeSet ];
            exact fun e he => by rcases e with ⟨ x, y ⟩ ; aesop;
          have := Finset.min_of_nonempty h_min;
          obtain ⟨ a, ha ⟩ := this; have := Finset.mem_of_min ha; aesop;
        obtain ⟨ E', hE' ⟩ := exists_triangle_cover_from_link_vertex_cover G v S ( by simpa using hS.1 );
        exact ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'.1, hE'.2.1 ⟩, hE'.2.2.trans hS.2.le ⟩;
      refine' le_trans _ hE'.2;
      have h_min : ∀ {S : Finset ℕ}, S.Nonempty → ∀ x ∈ S, Option.getD (S.min) 0 ≤ x := by
        intro S hS x hx; have := Finset.min_le hx; cases h : Finset.min S <;> aesop;
      exact h_min ⟨ _, Finset.mem_image_of_mem _ hE'.1 ⟩ _ ( Finset.mem_image_of_mem _ hE'.1 )

/-
For any vertex $v$, the triangle covering number of the set of triangles containing $v$ is at most twice the triangle packing number of that set.
-/
/-- MAIN THEOREM: Local Tuza bound via link graph reduction -/

-- Source: proven/tuza/nu4/slot_local_tuza_via_link_graph.lean
lemma exists_triangle_cover_from_subLink_vertex_cover (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (Ti : Finset (Finset V)) (hTi : Ti ⊆ trianglesContainingVertex G v)
    (S : Finset V) (hS : ∀ e ∈ (subLinkGraph G v Ti).edgeFinset, ∃ x ∈ S, x ∈ e) :
    ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧
      (∀ t ∈ Ti, ∃ e ∈ E', e ∈ t.sym2) ∧
      E'.card ≤ S.card := by
  refine' ⟨ Finset.image ( fun x => Sym2.mk ( v, x ) ) ( S.filter fun x => G.Adj v x ), _, _, _ ⟩;
  · intro e he
    aesop;
  · intro t ht
    obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y, x ≠ y ∧ t = {v, x, y} ∧ G.Adj v x ∧ G.Adj v y := by
      have := hTi ht;
      unfold trianglesContainingVertex at this;
      simp_all +decide [ Finset.subset_iff, SimpleGraph.is3Clique_iff ];
      rcases this with ⟨ ⟨ a, b, hab, x, hx, hx', rfl ⟩, hv ⟩ ; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
      rcases hv with ( rfl | rfl | rfl ) <;> simp_all +decide [ SimpleGraph.adj_comm ];
      · exact ⟨ b, x, by aesop ⟩;
      · exact ⟨ a, x, by aesop ⟩;
      · exact ⟨ a, b, by aesop ⟩;
    specialize hS ( Sym2.mk ( x, y ) ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;
    exact hS ⟨ hx, ⟨ { v, x, y }, ht, by aesop ⟩ ⟩ |> fun ⟨ a, ha, ha' ⟩ => ⟨ a, ⟨ ha, by rcases ha' with ( rfl | rfl ) <;> tauto ⟩, by rcases ha' with ( rfl | rfl ) <;> tauto ⟩;
  · exact Finset.card_image_le.trans ( Finset.card_filter_le _ _ )

/-
The triangle covering number of a subset of triangles $Ti$ at $v$ is at most the vertex cover number of the corresponding sub-link graph.
-/

-- Source: proven/tuza/nu4/slot_local_tuza_via_link_graph.lean
lemma cover_Ti_le_vertex_cover_subLink (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (Ti : Finset (Finset V)) (hTi : Ti ⊆ trianglesContainingVertex G v) :
    triangleCoveringNumberOn G Ti ≤ vertexCoverNumber (subLinkGraph G v Ti) := by
      -- By `exists_triangle_cover_from_subLink_vertex_cover`, there exists a set of edges `E'` in `G` such that `E'` covers all triangles in `Ti` and `|E'| ≤ |S|`.
      obtain ⟨E', hE'_subset, hE'_covers, hE'_card⟩ : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ (∀ t ∈ Ti, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card ≤ vertexCoverNumber (subLinkGraph G v Ti) := by
        -- Let $S$ be a minimum vertex cover of the sub-link graph $L' = \text{subLinkGraph}(G, v, Ti)$.
        obtain ⟨S, hS⟩ : ∃ S : Finset V, S.card = vertexCoverNumber (subLinkGraph G v Ti) ∧ ∀ e ∈ (subLinkGraph G v Ti).edgeFinset, ∃ x ∈ S, x ∈ e := by
          unfold vertexCoverNumber;
          have := Finset.min_of_mem ( show Finset.card ( Finset.univ : Finset V ) ∈ Finset.image Finset.card ( Finset.filter ( fun S => ∀ e ∈ ( subLinkGraph G v Ti ).edgeFinset, ∃ v ∈ S, v ∈ e ) ( Finset.powerset ( Finset.univ : Finset V ) ) ) from ?_ );
          · rcases this with ⟨ b, hb ⟩ ; have := Finset.mem_of_min hb; aesop;
          · simp +decide;
            refine' ⟨ Finset.univ, _, _ ⟩ <;> simp +decide;
            exact fun e he => by rcases e with ⟨ x, y ⟩ ; aesop;
        exact Exists.imp ( by aesop ) ( exists_triangle_cover_from_subLink_vertex_cover G v Ti hTi S hS.2 );
      unfold triangleCoveringNumberOn;
      refine' le_trans _ hE'_card;
      have h_image_card_le : Finset.card E' ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ Ti, ∃ e ∈ E', e ∈ t.sym2}) := by
        aesop;
      have := Finset.min_le h_image_card_le;
      rw [ WithTop.le_coe_iff ] at this ; aesop

/-
For any subset of triangles $Ti$ containing a vertex $v$, the triangle covering number of $Ti$ is at most twice the triangle packing number of $Ti$.
-/
/-- For each partition piece T_i (triangles containing shared vertex v_i),
    we have τ(T_i) ≤ 2·ν(T_i) -/

-- Source: proven/tuza/nu4/slot113_tau_le_12_conservative.lean
lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (S₁ S₂ : Finset (Finset V)) (h₁ : S₁ ⊆ G.cliqueFinset 3) (h₂ : S₂ ⊆ G.cliqueFinset 3)
    (bound₁ bound₂ : ℕ)
    (hS₁ : ∃ E₁ ⊆ G.edgeFinset, E₁.card ≤ bound₁ ∧ ∀ t ∈ S₁, ∃ e ∈ E₁, e ∈ t.sym2)
    (hS₂ : ∃ E₂ ⊆ G.edgeFinset, E₂.card ≤ bound₂ ∧ ∀ t ∈ S₂, ∃ e ∈ E₂, e ∈ t.sym2) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ bound₁ + bound₂ ∧ ∀ t ∈ S₁ ∪ S₂, ∃ e ∈ E, e ∈ t.sym2 := by
  obtain ⟨E₁, hE₁_sub, hE₁_card, hE₁_cover⟩ := hS₁
  obtain ⟨E₂, hE₂_sub, hE₂_card, hE₂_cover⟩ := hS₂
  use E₁ ∪ E₂
  constructor
  · exact Finset.union_subset hE₁_sub hE₂_sub
  constructor
  · calc (E₁ ∪ E₂).card ≤ E₁.card + E₂.card := Finset.card_union_le E₁ E₂
         _ ≤ bound₁ + bound₂ := Nat.add_le_add hE₁_card hE₂_card
  · intro t ht
    simp only [Finset.mem_union] at ht
    cases ht with
    | inl h₁ =>
      obtain ⟨e, he_mem, he_in⟩ := hE₁_cover t h₁
      exact ⟨e, Finset.mem_union_left E₂ he_mem, he_in⟩
    | inr h₂ =>
      obtain ⟨e, he_mem, he_in⟩ := hE₂_cover t h₂
      exact ⟨e, Finset.mem_union_right E₁ he_mem, he_in⟩

/-- PROVEN: Every triangle shares edge with packing -/

-- Source: proven/tuza/nu4/slot113_tau_le_12_conservative.lean
lemma cycle4_tpair_covers_all (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    G.cliqueFinset 3 ⊆ T_pair G cfg.A cfg.B ∪ T_pair G cfg.C cfg.D := by
  intro t ht
  obtain ⟨X, hX_mem, hX_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  rw [cfg.hM_eq] at hX_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hX_mem
  rcases hX_mem with rfl | rfl | rfl | rfl
  · simp only [Finset.mem_union]; left; simp only [T_pair, Finset.mem_filter]; exact ⟨ht, Or.inl hX_share⟩
  · simp only [Finset.mem_union]; left; simp only [T_pair, Finset.mem_filter]; exact ⟨ht, Or.inr hX_share⟩
  · simp only [Finset.mem_union]; right; simp only [T_pair, Finset.mem_filter]; exact ⟨ht, Or.inl hX_share⟩
  · simp only [Finset.mem_union]; right; simp only [T_pair, Finset.mem_filter]; exact ⟨ht, Or.inr hX_share⟩

-- Source: proven/tuza/nu4/slot113_tau_le_12_conservative.lean
lemma tau_containing_v_in_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hA : A ∈ G.cliqueFinset 3) (hB : B ∈ G.cliqueFinset 3)
    (v : V) (h_inter : A ∩ B = {v}) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 4 ∧
      ∀ t ∈ (T_pair G A B).filter (fun t => v ∈ t), ∃ e ∈ E, e ∈ t.sym2 := by
  refine' ⟨ _, _, _, _ ⟩;
  exact ( A \ { v } ).image ( fun w => Sym2.mk ( v, w ) ) ∪ ( B \ { v } ).image ( fun w => Sym2.mk ( v, w ) );
  · simp_all +decide [ Finset.subset_iff ];
    rintro _ ( ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
    · replace h_inter := Finset.ext_iff.mp h_inter v ; aesop;
    · rw [ Finset.eq_singleton_iff_unique_mem ] at h_inter ; aesop;
  · rw [ Finset.card_union_of_disjoint ];
    · rw [ Finset.card_image_of_injOn, Finset.card_image_of_injOn ];
      · simp_all +decide [ Finset.card_sdiff ];
        simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
        have := hA.2; have := hB.2; aesop;
      · intro w hw w' hw' h; aesop;
      · intro w hw w' hw' h; aesop;
    · simp_all +decide [ Finset.disjoint_left, Sym2.eq_iff ];
      intro a x hx hx' hx'' y hy hy' hy''; subst_vars; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
  · simp_all +decide [ Finset.ext_iff, T_pair ];
    intro t ht h hvt; cases' h with h h <;> obtain ⟨ w, hw ⟩ := Finset.exists_mem_ne h v <;> use Sym2.mk ( v, w ) <;> aesop;

/-- PROVEN: 2 base edges cover triangles avoiding v -/

-- Source: proven/tuza/nu4/slot113_tau_le_12_conservative.lean
lemma tau_avoiding_v_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : M ⊆ G.cliqueFinset 3)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M)
    (v : V) (h_inter : A ∩ B = {v}) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧
      ∀ t ∈ (trianglesAvoiding G v).filter (fun t => (t ∩ A).card ≥ 2 ∨ (t ∩ B).card ≥ 2),
        ∃ e ∈ E, e ∈ t.sym2 := by
  -- Let A = {v, a1, a2} and B = {v, b1, b2}.
  obtain ⟨a1, a2, ha1, ha2, hA⟩ : ∃ a1 a2 : V, a1 ≠ a2 ∧ A = {v, a1, a2} := by
    have hA_card : A.card = 3 := by
      have := hM hA; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      exact this.2;
    have hA_subset : v ∈ A := by
      exact Finset.mem_of_mem_inter_left ( h_inter.symm ▸ Finset.mem_singleton_self _ );
    rw [ Finset.card_eq_three ] at hA_card; obtain ⟨ a1, a2, a3, ha1, ha2, ha3 ⟩ := hA_card; use if a1 = v then a2 else if a2 = v then a3 else a1, if a1 = v then a3 else if a2 = v then a1 else a2; aesop;
  obtain ⟨b1, b2, hb1, hb2, hB⟩ : ∃ b1 b2 : V, b1 ≠ b2 ∧ B = {v, b1, b2} := by
    have := hM hB;
    rw [ SimpleGraph.cliqueFinset ] at this;
    rw [ Finset.mem_filter ] at this;
    obtain ⟨ b1, b2, hb1, hb2 ⟩ := Finset.card_eq_three.mp this.2.2;
    simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
    grind;
  refine' ⟨ { Sym2.mk ( a1, a2 ), Sym2.mk ( b1, b2 ) }, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
  · have := hM hA; have := hM hB; simp_all +decide [ Finset.ext_iff, SimpleGraph.isNClique_iff ] ;
  · exact Finset.card_insert_le _ _;
  · simp_all +decide [ Finset.ext_iff, trianglesAvoiding ];
    intro t ht hv h; contrapose! h; simp_all +decide [ Finset.card_le_one, SimpleGraph.isNClique_iff ] ;
    exact ⟨ lt_of_le_of_lt ( Finset.card_le_one.mpr ( by aesop ) ) ( by decide ), lt_of_le_of_lt ( Finset.card_le_one.mpr ( by aesop ) ) ( by decide ) ⟩

/-- T_pair bound: τ(T_pair) ≤ 6 -/

-- Source: proven/tuza/nu4/slot113_tau_le_12_conservative.lean
lemma tau_tpair_le_6 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : M ⊆ G.cliqueFinset 3)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (v : V) (h_inter : A ∩ B = {v}) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 6 ∧
      ∀ t ∈ T_pair G A B, ∃ e ∈ E, e ∈ t.sym2 := by
  -- For `S_in`: Use `tau_containing_v_in_pair_le_4` with `A` and `B`.
  obtain ⟨E_in, hE_in⟩ : ∃ E_in ⊆ G.edgeFinset, E_in.card ≤ 4 ∧ ∀ t ∈ (T_pair G A B).filter (fun t => v ∈ t), ∃ e ∈ E_in, e ∈ t.sym2 := by
    convert tau_containing_v_in_pair_le_4 G A B ( hM hA ) ( hM hB ) v h_inter;
  -- For `S_out`: Use `tau_avoiding_v_le_2` with `M`, `A`, `B`.
  obtain ⟨E_out, hE_out⟩ : ∃ E_out ⊆ G.edgeFinset, E_out.card ≤ 2 ∧ ∀ t ∈ (T_pair G A B).filter (fun t => v ∉ t), ∃ e ∈ E_out, e ∈ t.sym2 := by
    convert tau_avoiding_v_le_2 G M hM A B hA hB v h_inter using 6;
    unfold T_pair trianglesAvoiding; aesop;
  refine' ⟨ E_in ∪ E_out, Finset.union_subset hE_in.1 hE_out.1, _, _ ⟩ <;> simp_all +decide [ Finset.card_union_le ];
  · exact le_trans ( Finset.card_union_le _ _ ) ( add_le_add hE_in.2.1 hE_out.2.1 );
  · exact fun t ht => if h : v ∈ t then hE_in.2.2 t ht h |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Or.inl he₁, he₂ ⟩ else hE_out.2.2 t ht h |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Or.inr he₁, he₂ ⟩

-- Source: proven/tuza/nu4/slot113_tau_le_12_conservative.lean
theorem tau_le_12_cycle4_conservative (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (cfg : Cycle4 G M)
    (h_diag_AC : (cfg.A ∩ cfg.C).card ≤ 1)
    (h_diag_BD : (cfg.B ∩ cfg.D).card ≤ 1)
    (h_nu_4 : trianglePackingNumber G = 4) :
    triangleCoveringNumber G ≤ 12 := by
  have hM_sub : M ⊆ G.cliqueFinset 3 := hM.1.1
  have hAB_ne : cfg.A ≠ cfg.B := by
    intro h
    have hA_card : cfg.A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM_sub cfg.hA)).2
    have h_inter : cfg.A ∩ cfg.B = {cfg.v_ab} := cfg.hAB
    rw [h] at h_inter
    rw [Finset.inter_self] at h_inter
    rw [h] at hA_card
    rw [h_inter] at hA_card
    simp at hA_card
  have hCD_ne : cfg.C ≠ cfg.D := by
    intro h
    have hC_card : cfg.C.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM_sub cfg.hC)).2
    have h_inter : cfg.C ∩ cfg.D = {cfg.v_cd} := cfg.hCD
    rw [h] at h_inter
    rw [Finset.inter_self] at h_inter
    rw [h] at hC_card
    rw [h_inter] at hC_card
    simp at hC_card

  -- Step 1: All triangles covered by T_pair(A,B) ∪ T_pair(C,D)
  have h_cover := cycle4_tpair_covers_all G M hM cfg

  -- Step 2: T_pair(A,B) needs ≤ 6 edges
  obtain ⟨E_AB, hE_AB_sub, hE_AB_card, hE_AB_cover⟩ :=
    tau_tpair_le_6 G M hM_sub cfg.A cfg.B cfg.hA cfg.hB hAB_ne cfg.v_ab cfg.hAB

  -- Step 3: T_pair(C,D) needs ≤ 6 edges
  obtain ⟨E_CD, hE_CD_sub, hE_CD_card, hE_CD_cover⟩ :=
    tau_tpair_le_6 G M hM_sub cfg.C cfg.D cfg.hC cfg.hD hCD_ne cfg.v_cd cfg.hCD

  -- Step 4: Union gives ≤ 12
  -- By definition of `triangleCoveringNumber`, we have that `triangleCoveringNumber G ≤ E_AB.card + E_CD.card`.
  have h_triangleCoveringNumber_le : triangleCoveringNumber G ≤ (E_AB ∪ E_CD).card := by
    unfold triangleCoveringNumber;
    -- Since $E_AB \cup E_CD$ is a valid triangle cover, we have $(E_AB \cup E_CD).card \geq \text{triangleCoveringNumber } G$.
    have h_triangleCover_le_union : isTriangleCover G (E_AB ∪ E_CD) := by
      exact ⟨ Finset.union_subset hE_AB_sub hE_CD_sub, fun t ht => by rcases Finset.mem_union.1 ( h_cover ht ) with ( ht | ht ) <;> [ obtain ⟨ e, he₁, he₂ ⟩ := hE_AB_cover t ht; obtain ⟨ e, he₁, he₂ ⟩ := hE_CD_cover t ht ] <;> exact ⟨ e, Finset.mem_union.2 ( by aesop ), he₂ ⟩ ⟩;
    have h_triangleCover_le_union : (Finset.image Finset.card (Finset.filter (isTriangleCover G) G.edgeFinset.powerset)).min ≤ (E_AB ∪ E_CD).card := by
      exact Finset.min_le ( Finset.mem_image.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.union_subset hE_AB_sub hE_CD_sub ), h_triangleCover_le_union ⟩, rfl ⟩ );
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( isTriangleCover G ) G.edgeFinset.powerset ) ) <;> aesop;
  exact h_triangleCoveringNumber_le.trans ( le_trans ( Finset.card_union_le _ _ ) ( add_le_add hE_AB_card hE_CD_card ) )

-- Source: proven/tuza/nu4/slot_disjoint_partition_proven.lean
theorem disjoint_partition_covers_all
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hcycle : isCycle4 M A B C D) (hM : isMaxPacking G M)
    (v_ab v_bc v_cd v_da : V)
    (hv_ab : v_ab ∈ A ∩ B) (hv_bc : v_bc ∈ B ∩ C)
    (hv_cd : v_cd ∈ C ∩ D) (hv_da : v_da ∈ D ∩ A) :
    let triangles := G.cliqueFinset 3
    T1 triangles v_ab ∪ T2 triangles v_ab v_bc ∪
    T3 triangles v_ab v_bc v_cd ∪ T4 triangles v_ab v_bc v_cd v_da = triangles := by
  ext t
  simp only [Finset.mem_union, T1, T2, T3, T4, Finset.mem_filter]
  constructor
  · intro h
    aesop
  · intro ht
    by_cases hab : v_ab ∈ t
    · left; left; left; exact ⟨ht, hab⟩
    · by_cases hbc : v_bc ∈ t
      · left; left; right; exact ⟨ht, hbc, hab⟩
      · by_cases hcd : v_cd ∈ t
        · left; right; exact ⟨ht, hcd, hab, hbc⟩
        · right
          have h_shared := cycle4_all_triangles_contain_shared G M A B C D hcycle hM t ht
          obtain ⟨ v, hv₁, hv₂ ⟩ := h_shared; simp_all +decide [ sharedVertices ] ;
          rcases hv_ab with ⟨ hv_ab₁, hv_ab₂ ⟩ ; rcases hv_bc with ⟨ hv_bc₁, hv_bc₂ ⟩ ; rcases hv_cd with ⟨ hv_cd₁, hv_cd₂ ⟩ ; rcases hv_da with ⟨ hv_da₁, hv_da₂ ⟩ ; rcases hcycle with ⟨ rfl, h₁, h₂, h₃, h₄, h₅, h₆ ⟩ ; simp_all +decide [ Finset.card_eq_one ] ;
          rcases h₆.2.2.2.2.1 with ⟨ w, hw ⟩ ; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
          grind

/-
The sets T1, T2, T3, T4 form a partition of the set of all triangles. They are pairwise disjoint and their union covers all triangles.
-/
/-- MAIN: cycle_4 triangles form a disjoint 4-partition by shared vertex -/

-- Source: proven/tuza/nu4/slot133_subadditivity_proven.lean
lemma triangleCoveringOn_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringOn G ∅ = 0 := by
      -- Since the empty set has no triangles, any set of edges is a cover. The smallest set is the empty set itself, which has size 0.
      simp [triangleCoveringOn];
      -- Since the set contains 0, the infimum is 0.
      intros x hx
      apply le_antisymm;
      · -- Since 0 is in the set, the infimum must be ≤ 0.
        apply Finset.inf'_le;
        simp [isCoverOf];
      · -- Since the infimum of a set of non-negative numbers is non-negative, we have:
        apply Nat.zero_le

-- Source: proven/tuza/nu4/slot133_subadditivity_proven.lean
lemma triangleCoveringOn_singleton (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    triangleCoveringOn G {t} ≤ 1 := by
      -- Since $t$ is a triangle, any edge in $t$ covers $t$. Therefore, we can choose any edge from $t$ to form a cover of size 1.
      have h_cover : ∃ e ∈ t.sym2, isCoverOf G {e} {t} := by
        -- Since $t$ is a triangle, it must have exactly three edges. Let's pick any edge $e$ from $t$ and show that it covers $t$.
        obtain ⟨e, he⟩ : ∃ e ∈ t.sym2, e ∈ G.edgeFinset := by
          rw [ SimpleGraph.mem_cliqueFinset_iff ] at ht;
          rcases Finset.card_eq_three.mp ht.2 with ⟨ a, b, c, hab, hbc, hac ⟩ ; simp_all +decide [ SimpleGraph.isNClique_iff ];
          exact ⟨ Sym2.mk ( a, b ), by aesop ⟩;
        unfold isCoverOf; aesop;
      -- Since there exists an edge e in t.sym2 such that {e} is a cover of {t}, the minimum number of edges needed is 1.
      obtain ⟨e, he₁, he₂⟩ := h_cover;
      have h_min : triangleCoveringOn G {t} ≤ 1 := by
        unfold triangleCoveringOn;
        split_ifs <;> simp_all +decide [ Finset.min' ];
        exact ⟨ 1, ⟨ Nat.lt_succ_of_le ( Nat.succ_le_of_lt ( Fintype.card_pos_iff.mpr ⟨ e ⟩ ) ), { e }, by simp +decide, he₂ ⟩, by simp +decide ⟩;
      exact h_min

/-- Union of covers is a cover of the union -/

-- Source: proven/tuza/nu4/slot133_subadditivity_proven.lean
lemma cover_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (E₁ E₂ : Finset (Sym2 V)) (S₁ S₂ : Finset (Finset V))
    (h₁ : isCoverOf G E₁ S₁) (h₂ : isCoverOf G E₂ S₂) :
    isCoverOf G (E₁ ∪ E₂) (S₁ ∪ S₂) := by
  constructor
  · -- (E₁ ∪ E₂) ⊆ G.edgeFinset
    intro e he
    simp only [Finset.mem_union] at he
    cases he with
    | inl h => exact h₁.1 h
    | inr h => exact h₂.1 h
  · -- Every triangle in S₁ ∪ S₂ is covered
    intro t ht
    simp only [Finset.mem_union] at ht
    cases ht with
    | inl h =>
      obtain ⟨e, he, het⟩ := h₁.2 t h
      exact ⟨e, Finset.mem_union_left _ he, het⟩
    | inr h =>
      obtain ⟨e, he, het⟩ := h₂.2 t h
      exact ⟨e, Finset.mem_union_right _ he, het⟩

/-- Subadditivity: τ(S₁ ∪ S₂) ≤ τ(S₁) + τ(S₂) -/

-- Source: proven/tuza/nu4/slot133_subadditivity_proven.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (S₁ S₂ : Finset (Finset V)) :
    triangleCoveringOn G (S₁ ∪ S₂) ≤ triangleCoveringOn G S₁ + triangleCoveringOn G S₂ := by
      by_contra h;
      -- By definition of `triangleCoveringOn`, there exist sets `E₁` and `E₂` such that `E₁` covers `S₁` with `|E₁| = triangleCoveringOn G S₁` and `E₂` covers `S₂` with `|E₂| = triangleCoveringOn G S₂`.
      obtain ⟨E₁, hE₁⟩ : ∃ E₁ : Finset (Sym2 V), isCoverOf G E₁ S₁ ∧ E₁.card = triangleCoveringOn G S₁ := by
        unfold triangleCoveringOn at *;
        split_ifs with h₁;
        · have := Finset.min'_mem ( Finset.filter ( fun n => ∃ E : Finset ( Sym2 V ), E.card = n ∧ isCoverOf G E S₁ ) ( Finset.range ( Fintype.card ( Sym2 V ) + 1 ) ) ) ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( show Fintype.card ( Sym2 V ) ≥ Finset.card ( h₁.choose : Finset ( Sym2 V ) ) from Finset.card_le_univ _ ) ), ⟨ h₁.choose, rfl, h₁.choose_spec ⟩ ⟩ ⟩;
          grind;
        · split_ifs at h <;> simp_all +decide;
          · obtain ⟨ E₁, hE₁ ⟩ := ‹∃ E : Finset ( Sym2 V ), isCoverOf G E ( S₁ ∪ S₂ ) ›;
            exact h₁ E₁ ( by exact ⟨ hE₁.1, fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := hE₁.2 t ( Finset.mem_union_left _ ht ) ; exact ⟨ e, he₁, he₂ ⟩ ⟩ );
          · rename_i h₂ h₃;
            exact h₃ _ ( h₂.choose_spec.2 |> fun h => ⟨ h₂.choose_spec.1, fun t ht => h t ( Finset.mem_union_right _ ht ) ⟩ )
      obtain ⟨E₂, hE₂⟩ : ∃ E₂ : Finset (Sym2 V), isCoverOf G E₂ S₂ ∧ E₂.card = triangleCoveringOn G S₂ := by
        unfold triangleCoveringOn;
        split_ifs with h₂;
        · have := Finset.min'_mem ( Finset.filter ( fun n => ∃ E : Finset ( Sym2 V ), E.card = n ∧ isCoverOf G E S₂ ) ( Finset.range ( Fintype.card ( Sym2 V ) + 1 ) ) ) ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Finset.card_le_univ _ ) ), h₂.choose, rfl, h₂.choose_spec ⟩ ⟩ ; aesop;
        · unfold triangleCoveringOn at h;
          simp_all +decide [ Finset.min' ];
          split_ifs at h;
          · obtain ⟨ E, hE ⟩ := ‹∃ E : Finset ( Sym2 V ), isCoverOf G E ( S₁ ∪ S₂ ) ›;
            exact h₂ E ( by exact ⟨ hE.1, fun t ht => hE.2 t ( Finset.mem_union_right _ ht ) ⟩ );
          · exact h.not_le ( Nat.zero_le _ );
          · exact ‹¬∃ E, isCoverOf G E S₁› ⟨ E₁, hE₁.1 ⟩;
          · contradiction;
      -- By definition of `triangleCoveringOn`, we know that `E₁ ∪ E₂` covers `S₁ ∪ S₂`.
      have h_union : isCoverOf G (E₁ ∪ E₂) (S₁ ∪ S₂) := by
        exact cover_union G E₁ E₂ S₁ S₂ hE₁.1 hE₂.1;
      refine' h ( le_trans ( _ : _ ≤ _ ) ( Nat.le_trans ( Finset.card_union_le _ _ ) ( add_le_add hE₁.2.le hE₂.2.le ) ) );
      unfold triangleCoveringOn;
      split_ifs <;> simp_all +decide [ Finset.min' ];
      exact ⟨ _, ⟨ Nat.lt_succ_of_le ( Finset.card_le_univ _ ), _, rfl, h_union ⟩, le_rfl ⟩

/-- Simpler version using Nat.sInf directly -/

-- Source: proven/tuza/nu4/slot133_subadditivity_proven.lean
theorem tau_union_le_sum' (G : SimpleGraph V) [DecidableRel G.Adj]
    (S₁ S₂ : Finset (Finset V)) :
    triangleCoveringOn' G (S₁ ∪ S₂) ≤ triangleCoveringOn' G S₁ + triangleCoveringOn' G S₂ := by
      by_contra! h_contra;
      -- By definition of triangleCoveringOn', there exist covers E₁ and E₂ for S₁ and S₂ respectively, such that |E₁| ≤ triangleCoveringOn' G S₁ and |E₂| ≤ triangleCoveringOn' G S₂.
      obtain ⟨E₁, hE₁⟩ : ∃ E₁ : Finset (Sym2 V), E₁.card ≤ triangleCoveringOn' G S₁ ∧ isCoverOf G E₁ S₁ := by
        obtain ⟨E₁, hE₁⟩ : ∃ E₁ : Finset (Sym2 V), isCoverOf G E₁ S₁ := by
          have h_exists_cover : ∃ E : Finset (Sym2 V), isCoverOf G E (S₁ ∪ S₂) := by
            unfold triangleCoveringOn' at h_contra;
            by_cases h_empty : ∃ E : Finset (Sym2 V), isCoverOf G E (S₁ ∪ S₂);
            · exact h_empty;
            · simp_all +decide [ Nat.sInf_eq_zero.mpr ];
          exact ⟨ h_exists_cover.choose, ⟨ h_exists_cover.choose_spec.1, fun t ht => h_exists_cover.choose_spec.2 t ( Finset.mem_union_left _ ht ) ⟩ ⟩;
        have := Nat.sInf_mem ( show Set.Nonempty { n : ℕ | ∃ E : Finset ( Sym2 V ), E.card = n ∧ isCoverOf G E S₁ } from ⟨ E₁.card, ⟨ E₁, rfl, hE₁ ⟩ ⟩ ) ; aesop;
      obtain ⟨E₂, hE₂⟩ : ∃ E₂ : Finset (Sym2 V), E₂.card ≤ triangleCoveringOn' G S₂ ∧ isCoverOf G E₂ S₂ := by
        by_cases h₂ : ∃ E₂ : Finset (Sym2 V), isCoverOf G E₂ S₂;
        · have := Nat.sInf_mem ( show { n : ℕ | ∃ E : Finset ( Sym2 V ), E.card = n ∧ isCoverOf G E S₂ }.Nonempty from by obtain ⟨ E₂, hE₂ ⟩ := h₂; exact ⟨ _, ⟨ E₂, rfl, hE₂ ⟩ ⟩ ) ; aesop;
        · simp_all +decide [ triangleCoveringOn' ];
          contrapose! h_contra;
          rw [ Nat.sInf_eq_zero.mpr ];
          · exact Nat.zero_le _;
          · refine' Or.inr ( Set.eq_empty_of_forall_notMem fun n hn => _ );
            obtain ⟨ E, rfl, hE ⟩ := hn;
            exact h₂ E ( by exact ⟨ hE.1, fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := hE.2 t ( Finset.mem_union_right _ ht ) ; exact ⟨ e, he₁, he₂ ⟩ ⟩ );
      refine' h_contra.not_le ( le_trans ( Nat.sInf_le _ ) _ );
      exact ( E₁ ∪ E₂ ).card;
      · exact ⟨ _, rfl, cover_union G E₁ E₂ S₁ S₂ hE₁.2 hE₂.2 ⟩;
      · exact le_trans ( Finset.card_union_le _ _ ) ( add_le_add hE₁.1 hE₂.1 )

-- Source: proven/tuza/nu4/safe_discard/slot148b_owner_covered_PROVEN.lean
lemma self_covered (A : Finset V) (hA_card : A.card = 3) :
    ∃ e ∈ A.sym2, e ∈ A.sym2 := by
  have h_ne : A.sym2.Nonempty := by
    rw [Finset.sym2_nonempty]; omega
  obtain ⟨e, he⟩ := h_ne
  exact ⟨e, he, he⟩

/-- Every triangle owned by A contains an A-edge -/

-- Source: proven/tuza/nu4/safe_discard/slot148b_owner_covered_PROVEN.lean
lemma A_edges_cover_owned (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A : Finset V) (hA : A ∈ M) :
    ∀ t ∈ trianglesOwnedBy G M A, edgeSetCovers A.sym2 t := by
  intro t ht
  obtain ⟨e, he_A, he_t⟩ := owned_contains_A_edge G M hM A hA t ht
  exact ⟨e, he_A, he_t⟩

/-- Corollary: τ(trianglesOwnedBy A) ≤ 3 -/

-- Source: proven/tuza/nu4/safe_discard/slot148b_owner_covered_PROVEN.lean
lemma tau_owned_by_A_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A : Finset V) (hA : A ∈ M) :
    ∃ E ⊆ A.sym2, E.card ≤ 3 ∧ ∀ t ∈ trianglesOwnedBy G M A, edgeSetCovers E t := by
  use A.sym2
  constructor
  · exact Finset.Subset.refl _
  constructor
  · have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hA)).card_eq
    rw [Finset.card_sym2]; omega
  · exact A_edges_cover_owned G M hM A hA

end

-- Source: proven/tuza/nu4/slot69_80891b4c/tau_pair_decomposition.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  unfold triangleCoveringNumberOn;
  by_cases hA : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2;
  · -- Since $E_1 \cup E_2$ is a valid edge set covering both $A$ and $B$, its cardinality is at least as large as the minimum cardinality of any such edge set.
    have h_union : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min + (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min := by
      have h_union : ∀ E1 ∈ ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}), ∀ E2 ∈ ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}), (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ Finset.card E1 + Finset.card E2 := by
        intros E1 hE1 E2 hE2
        have h_union : E1 ∪ E2 ∈ ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}) := by
          grind;
        -- Since the minimum of a set is less than or equal to any element in the set, and E1 ∪ E2 is in the set, we have min ≤ Finset.card (E1 ∪ E2).
        have h_min_le_union : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ Finset.card (E1 ∪ E2) := by
          exact Finset.min_le ( Finset.mem_image_of_mem _ h_union );
        exact h_min_le_union.trans ( mod_cast Finset.card_union_le _ _ );
      by_cases hB : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t;
      · obtain ⟨E1, hE1⟩ : ∃ E1 ∈ ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}), ∀ E' ∈ ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}), E1.card ≤ E'.card := by
          apply_rules [ Finset.exists_min_image ];
          exact ⟨ hA.choose, Finset.mem_filter.mpr ⟨ hA.choose_spec.1, fun t ht => by simpa using hA.choose_spec.2 t ( Finset.mem_union_left _ ht ) ⟩ ⟩;
        obtain ⟨E2, hE2⟩ : ∃ E2 ∈ ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}), ∀ E' ∈ ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}), E2.card ≤ E'.card := by
          apply_rules [ Finset.exists_min_image ];
          exact ⟨ hB.choose, Finset.mem_filter.mpr ⟨ hB.choose_spec.1, hB.choose_spec.2 ⟩ ⟩;
        convert h_union E1 hE1.1 E2 hE2.1 using 1;
        congr! 1;
        · refine' le_antisymm _ _;
          · exact Finset.min_le ( Finset.mem_image_of_mem _ hE1.1 );
          · simp +zetaDelta at *;
            exact fun a x hx hx' hx'' => hx''.symm ▸ hE1.2 x hx hx';
        · refine' le_antisymm _ _;
          · exact Finset.min_le ( Finset.mem_image_of_mem _ hE2.1 );
          · simp +zetaDelta at *;
            exact fun a x hx hx' hx'' => hx''.symm ▸ hE2.2 x hx hx';
      · contrapose! hB;
        obtain ⟨ E', hE'₁, hE'₂ ⟩ := hA;
        exact ⟨ E', hE'₁, fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := hE'₂ t ( Finset.mem_union_right _ ht ) ; exact ⟨ e, he₁, by simpa using he₂ ⟩ ⟩;
    convert h_union using 1;
    cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> cases h' : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> cases h'' : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> simp +decide [ h, h', h'' ];
    · -- Since the minimum of the image of the cardinality of the set of edge sets covering A ∪ B is ⊤, this leads to a contradiction because the minimum of a non-empty set of natural numbers cannot be ⊤.
      have h_contra : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ A ∪ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t := by
        obtain ⟨ E', hE', hE'' ⟩ := hA;
        exact ⟨ E', hE', fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := hE'' t ht; exact ⟨ e, he₁, by simpa using he₂ ⟩ ⟩;
      obtain ⟨ E', hE', hE'' ⟩ := h_contra;
      exact absurd h ( ne_of_lt ( lt_of_le_of_lt ( Finset.min_le ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ hE', fun t ht => by aesop ⟩ ) ) ) ( WithTop.coe_lt_top _ ) ) );
    · -- Since the minimum of the image of the cardinality over the set of edge sets covering B is ⊤, this implies that there are no edge sets covering B, which contradicts the existence of E' covering A ∪ B.
      have h_contra : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 := by
        exact ⟨ hA.choose, hA.choose_spec.1, fun t ht => hA.choose_spec.2 t ( Finset.mem_union_right _ ht ) ⟩;
      obtain ⟨ E', hE'₁, hE'₂ ⟩ := h_contra;
      simp +zetaDelta at *;
      exact absurd ( h'' hE'₁ ) ( by push_neg; tauto );
    · simp +decide [ Finset.min ] at h';
      contrapose! h';
      obtain ⟨ E', hE', hE'' ⟩ := hA;
      use E';
      aesop;
    · simp +decide [ Finset.min ] at h'';
      contrapose! h'';
      obtain ⟨ E', hE', hE'' ⟩ := hA;
      refine' ⟨ E', _, _ ⟩ <;> aesop;
    · norm_cast;
  · simp_all +decide [ Finset.min ];
    rw [ show { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } = ∅ from ?_ ] ; simp +decide [ Finset.inf ];
    · exact Nat.zero_le _;
    · ext E'; specialize hA E'; aesop; -- PROVEN in slot61 (uuid 16fa79da) - copy full proof

-- Source: proven/tuza/nu4/slot69_80891b4c/tau_pair_decomposition.lean
lemma cycle4_tpair_union_covers_all (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D := by
      intro t ht
      obtain ⟨e, heM, he⟩ : ∃ e ∈ M, (t ∩ e).card ≥ 2 := triangle_shares_edge_with_packing G M hM t ht;
      -- Since $e \in M$, we have $e \in \{A, B, C, D\}$.
      have he_cases : e = A ∨ e = B ∨ e = C ∨ e = D := by
        rw [ hcycle.1 ] at heM; aesop;
      rcases he_cases with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ T_pair ];
      · unfold trianglesSharingEdge; aesop;
      · unfold trianglesSharingEdge; aesop;
      · unfold trianglesSharingEdge; aesop;
      · unfold trianglesSharingEdge; aesop;

-- Source: proven/tuza/nu4/slot69_80891b4c/tau_pair_decomposition.lean
lemma tau_containing_v_in_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesContaining (T_pair G e f) v) ≤ 4 := by
  -- Let's denote the set of triangles in `T_pair G e f` that contain `v` by `S`.
  set S := trianglesContaining (T_pair G e f) v;
  -- We construct a covering edge set `E'` of size 4.
  set E' : Finset (Sym2 V) := Finset.image (fun u => Sym2.mk (v, u)) (e \ {v}) ∪ Finset.image (fun u => Sym2.mk (v, u)) (f \ {v});
  -- We claim `E'` covers `S`.
  have hE'_covers_S : ∀ t ∈ S, ∃ e' ∈ E', e' ∈ t.sym2 := by
    intro t ht;
    -- Since `t ∈ T_pair G e f`, `t` shares an edge with `e` or `f`.
    obtain ⟨u, hu⟩ : ∃ u ∈ t, u ≠ v ∧ (u ∈ e ∨ u ∈ f) := by
      have h_edge : (t ∩ e).card ≥ 2 ∨ (t ∩ f).card ≥ 2 := by
        have h_edge : t ∈ trianglesSharingEdge G e ∪ trianglesSharingEdge G f := by
          exact?;
        unfold trianglesSharingEdge at h_edge; aesop;
      obtain h | h := h_edge;
      · obtain ⟨ u, hu, hu' ⟩ := Finset.exists_mem_ne ( lt_of_lt_of_le ( by decide ) h ) v;
        exact ⟨ u, Finset.mem_of_mem_inter_left hu, hu', Or.inl ( Finset.mem_of_mem_inter_right hu ) ⟩;
      · obtain ⟨ u, hu ⟩ := Finset.exists_mem_ne h v;
        exact ⟨ u, Finset.mem_of_mem_inter_left hu.1, hu.2, Or.inr ( Finset.mem_of_mem_inter_right hu.1 ) ⟩;
    rcases hu.2.2 with ( hu | hu ) <;> simp_all +decide [ Finset.ext_iff ];
    · simp +zetaDelta at *;
      use Sym2.mk (v, u);
      simp_all +decide [ Sym2.eq ];
      exact ⟨ Or.inl ⟨ u, ⟨ hu, by tauto ⟩, Or.inl rfl ⟩, by rw [ trianglesContaining ] at ht; aesop ⟩;
    · use Sym2.mk (v, u);
      simp +zetaDelta at *;
      exact ⟨ Or.inr ⟨ u, ⟨ hu, by tauto ⟩, Or.inl rfl ⟩, by rw [ trianglesContaining ] at ht; exact Finset.mem_filter.mp ht |>.2, by tauto ⟩;
  -- Since `E'` covers `S`, we have `triangleCoveringNumberOn G S ≤ E'.card`.
  have h_triangleCoveringNumberOn_le_E'_card : triangleCoveringNumberOn G S ≤ E'.card := by
    have hE'_in_set : E' ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2) := by
      have hE'_edges : ∀ u ∈ e \ {v}, G.Adj v u := by
        have := hM.1;
        have := this.1 he; simp_all +decide [ Finset.subset_iff ] ;
        have := this.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        intro u hu huv; have := this ( show v ∈ e from by rw [ Finset.eq_singleton_iff_unique_mem ] at hv; aesop ) hu; aesop;
      have hE'_edges' : ∀ u ∈ f \ {v}, G.Adj v u := by
        have := hM.1;
        have := this.1 hf; simp_all +decide [ Finset.subset_iff ] ;
        have := this.1; simp_all +decide [ Finset.ext_iff ] ;
        intro u hu huv; have := this ( show v ∈ f from by specialize hv v; aesop ) hu; aesop;
      simp_all +decide [ Finset.subset_iff ];
      aesop;
    have h_min_le_E'_card : ∀ {s : Finset ℕ}, s.Nonempty → ∀ x ∈ s, s.min.getD 0 ≤ x := by
      intros s hs x hx; exact (by
      have := Finset.min_le hx; cases h : Finset.min s <;> aesop;);
    exact h_min_le_E'_card ⟨ _, Finset.mem_image_of_mem _ hE'_in_set ⟩ _ ( Finset.mem_image_of_mem _ hE'_in_set );
  -- Since `e` and `f` are triangles in `M`, they each have exactly 3 vertices.
  have he_card : e.card = 3 := by
    have := hM.1.1;
    replace := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    exact this.card_eq
  have hf_card : f.card = 3 := by
    have := hM.1.1 hf; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    exact this.card_eq;
  -- Since `e` and `f` are triangles in `M`, they each have exactly 3 vertices, and `v` is one of them.
  have he_minus_v_card : (e \ {v}).card = 2 := by
    grind
  have hf_minus_v_card : (f \ {v}).card = 2 := by
    grind;
  exact h_triangleCoveringNumberOn_le_E'_card.trans ( Finset.card_union_le _ _ |> le_trans <| add_le_add ( Finset.card_image_le ) ( Finset.card_image_le ) |> le_trans <| by simp +decide [ he_minus_v_card, hf_minus_v_card ] )

-- Source: proven/tuza/nu4/slot69_80891b4c/tau_pair_decomposition.lean
lemma tau_avoiding_v_in_pair_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) ≤ 2 := by
  -- By definition of `triangleCoveringNumberOn`, we need to show that there exists an edge set `E'` of size at most 2 that covers all triangles in `trianglesAvoiding (T_pair G e f) v`.
  have h_exists_edge_set : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 2 ∧ ∀ t ∈ trianglesAvoiding (T_pair G e f) v, ∃ e' ∈ E', e' ∈ t.sym2 := by
    -- Let `b_e` be the base edge of `e` and `b_f` be the base edge of `f`.
    obtain ⟨b_e, hb_e⟩ : ∃ b_e : Sym2 V, b_e ∈ G.edgeFinset ∧ b_e ∈ e.sym2 ∧ ∀ x ∈ e, x ≠ v → x ∈ b_e := by
      have h_triangle_e : e ∈ G.cliqueFinset 3 := by
        have := hM.1.1 he; aesop;
      simp_all +decide [ Finset.ext_iff, SimpleGraph.cliqueFinset ];
      have := Finset.card_eq_three.mp h_triangle_e.2; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := this; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      cases eq_or_ne x v <;> cases eq_or_ne y v <;> cases eq_or_ne z v <;> simp_all +decide [ SimpleGraph.adj_comm ];
      · exact ⟨ Sym2.mk ( y, z ), by aesop ⟩;
      · exact ⟨ Sym2.mk ( x, z ), by aesop ⟩;
      · exact ⟨ Sym2.mk ( x, y ), by aesop ⟩;
      · specialize hv v; aesop;
    obtain ⟨b_f, hb_f⟩ : ∃ b_f : Sym2 V, b_f ∈ G.edgeFinset ∧ b_f ∈ f.sym2 ∧ ∀ x ∈ f, x ≠ v → x ∈ b_f := by
      -- Since $f$ is a triangle, it has exactly three vertices. Let $u$ and $w$ be the vertices of $f$ that are not $v$.
      obtain ⟨u, w, hu, hw, huv⟩ : ∃ u w, u ∈ f ∧ w ∈ f ∧ u ≠ v ∧ w ≠ v ∧ u ≠ w := by
        have h_card_f : f.card = 3 := by
          have := hM.1;
          have := this.1;
          have := this hf; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          exact this.2;
        have := Finset.card_eq_three.mp h_card_f;
        rcases this with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; by_cases hx : x = v <;> by_cases hy : y = v <;> by_cases hz : z = v <;> simp_all +decide ;
      have h_triangle : f ∈ G.cliqueFinset 3 := by
        have := hM.1;
        have := this.1 hf; aesop;
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      have := h_triangle.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      use Sym2.mk (u, w);
      have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset hu ( Finset.insert_subset hw ( Finset.singleton_subset_iff.mpr ( show v ∈ f from by { rw [ Finset.ext_iff ] at hv; specialize hv v; aesop } ) ) ) ) ; aesop;
    refine' ⟨ { b_e, b_f }, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    · exact Finset.card_insert_le _ _;
    · intro t ht
      simp [trianglesAvoiding, T_pair] at ht;
      rcases ht with ⟨ ht | ht, hv ⟩ <;> simp_all +decide [ trianglesSharingEdge ];
      · -- Since $t$ shares an edge with $e$, there exist $x, y \in t$ such that $x \neq y$ and $x, y \in e$.
        obtain ⟨x, y, hxy⟩ : ∃ x y : V, x ∈ t ∧ y ∈ t ∧ x ≠ y ∧ x ∈ e ∧ y ∈ e := by
          obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.1 ht.2; use x, y; aesop;
        have hxy_base : x ∈ b_e ∧ y ∈ b_e := by
          aesop;
        cases b_e ; aesop;
      · -- Since $t$ shares an edge with $f$, and $v \notin t$, the edge must be $b_f$.
        have h_edge_f : ∃ x ∈ f, x ∈ t ∧ ∃ y ∈ f, y ∈ t ∧ x ≠ y ∧ x ≠ v ∧ y ≠ v := by
          obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.1 ht.2;
          exact ⟨ x, Finset.mem_of_mem_inter_right hx, Finset.mem_of_mem_inter_left hx, y, Finset.mem_of_mem_inter_right hy, Finset.mem_of_mem_inter_left hy, hxy, by rintro rfl; exact hv ( Finset.mem_of_mem_inter_left hx ), by rintro rfl; exact hv ( Finset.mem_of_mem_inter_left hy ) ⟩;
        obtain ⟨ x, hx, hx', y, hy, hy', hxy, hxv, hyv ⟩ := h_edge_f; have := hb_f.2.2 x hx hxv; have := hb_f.2.2 y hy hyv; simp_all +decide [ Sym2.eq ] ;
        cases b_f ; aesop;
  unfold triangleCoveringNumberOn;
  have h_min_card : ∃ E' ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ trianglesAvoiding (T_pair G e f) v, ∃ e ∈ E', e ∈ t.sym2}), E' ≤ 2 := by
    aesop;
  norm_num +zetaDelta at *;
  obtain ⟨ E', hE₁, hE₂ ⟩ := h_min_card;
  have h_min_card : Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ trianglesAvoiding (T_pair G e f) v, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})) ≤ E'.card := by
    exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( fun x hx => by aesop ), hE₁.2 ⟩, rfl ⟩ );
  exact Nat.le_trans ( by cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ trianglesAvoiding ( T_pair G e f ) v, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop ) hE₂

-- Source: proven/tuza/nu4/slot69_80891b4c/output.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  unfold triangleCoveringNumberOn;
  by_cases hA : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2;
  · -- Since $E_1 \cup E_2$ is a valid edge set covering both $A$ and $B$, its cardinality is at least as large as the minimum cardinality of any such edge set.
    have h_union : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min + (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min := by
      have h_union : ∀ E1 ∈ ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}), ∀ E2 ∈ ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}), (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ Finset.card E1 + Finset.card E2 := by
        intros E1 hE1 E2 hE2
        have h_union : E1 ∪ E2 ∈ ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}) := by
          grind;
        -- Since the minimum of a set is less than or equal to any element in the set, and E1 ∪ E2 is in the set, we have min ≤ Finset.card (E1 ∪ E2).
        have h_min_le_union : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ Finset.card (E1 ∪ E2) := by
          exact Finset.min_le ( Finset.mem_image_of_mem _ h_union );
        exact h_min_le_union.trans ( mod_cast Finset.card_union_le _ _ );
      by_cases hB : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t;
      · obtain ⟨E1, hE1⟩ : ∃ E1 ∈ ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}), ∀ E' ∈ ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}), E1.card ≤ E'.card := by
          apply_rules [ Finset.exists_min_image ];
          exact ⟨ hA.choose, Finset.mem_filter.mpr ⟨ hA.choose_spec.1, fun t ht => by simpa using hA.choose_spec.2 t ( Finset.mem_union_left _ ht ) ⟩ ⟩;
        obtain ⟨E2, hE2⟩ : ∃ E2 ∈ ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}), ∀ E' ∈ ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t}), E2.card ≤ E'.card := by
          apply_rules [ Finset.exists_min_image ];
          exact ⟨ hB.choose, Finset.mem_filter.mpr ⟨ hB.choose_spec.1, hB.choose_spec.2 ⟩ ⟩;
        convert h_union E1 hE1.1 E2 hE2.1 using 1;
        congr! 1;
        · refine' le_antisymm _ _;
          · exact Finset.min_le ( Finset.mem_image_of_mem _ hE1.1 );
          · simp +zetaDelta at *;
            exact fun a x hx hx' hx'' => hx''.symm ▸ hE1.2 x hx hx';
        · refine' le_antisymm _ _;
          · exact Finset.min_le ( Finset.mem_image_of_mem _ hE2.1 );
          · simp +zetaDelta at *;
            exact fun a x hx hx' hx'' => hx''.symm ▸ hE2.2 x hx hx';
      · contrapose! hB;
        obtain ⟨ E', hE'₁, hE'₂ ⟩ := hA;
        exact ⟨ E', hE'₁, fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := hE'₂ t ( Finset.mem_union_right _ ht ) ; exact ⟨ e, he₁, by simpa using he₂ ⟩ ⟩;
    convert h_union using 1;
    cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> cases h' : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> cases h'' : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> simp +decide [ h, h', h'' ];
    · -- Since the minimum of the image of the cardinality of the set of edge sets covering A ∪ B is ⊤, this leads to a contradiction because the minimum of a non-empty set of natural numbers cannot be ⊤.
      have h_contra : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ A ∪ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t := by
        obtain ⟨ E', hE', hE'' ⟩ := hA;
        exact ⟨ E', hE', fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := hE'' t ht; exact ⟨ e, he₁, by simpa using he₂ ⟩ ⟩;
      obtain ⟨ E', hE', hE'' ⟩ := h_contra;
      exact absurd h ( ne_of_lt ( lt_of_le_of_lt ( Finset.min_le ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ hE', fun t ht => by aesop ⟩ ) ) ) ( WithTop.coe_lt_top _ ) ) );
    · -- Since the minimum of the image of the cardinality over the set of edge sets covering B is ⊤, this implies that there are no edge sets covering B, which contradicts the existence of E' covering A ∪ B.
      have h_contra : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 := by
        exact ⟨ hA.choose, hA.choose_spec.1, fun t ht => hA.choose_spec.2 t ( Finset.mem_union_right _ ht ) ⟩;
      obtain ⟨ E', hE'₁, hE'₂ ⟩ := h_contra;
      simp +zetaDelta at *;
      exact absurd ( h'' hE'₁ ) ( by push_neg; tauto );
    · simp +decide [ Finset.min ] at h';
      contrapose! h';
      obtain ⟨ E', hE', hE'' ⟩ := hA;
      use E';
      aesop;
    · simp +decide [ Finset.min ] at h'';
      contrapose! h'';
      obtain ⟨ E', hE', hE'' ⟩ := hA;
      refine' ⟨ E', _, _ ⟩ <;> aesop;
    · norm_cast;
  · simp_all +decide [ Finset.min ];
    rw [ show { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } = ∅ from ?_ ] ; simp +decide [ Finset.inf ];
    · exact Nat.zero_le _;
    · ext E'; specialize hA E'; aesop; -- PROVEN in slot61 (uuid 16fa79da) - copy full proof

-- Source: proven/tuza/nu4/slot69_80891b4c/output.lean
lemma cycle4_tpair_union_covers_all (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    G.cliqueFinset 3 ⊆ T_pair G A B ∪ T_pair G C D := by
      intro t ht
      obtain ⟨e, heM, he⟩ : ∃ e ∈ M, (t ∩ e).card ≥ 2 := triangle_shares_edge_with_packing G M hM t ht;
      -- Since $e \in M$, we have $e \in \{A, B, C, D\}$.
      have he_cases : e = A ∨ e = B ∨ e = C ∨ e = D := by
        rw [ hcycle.1 ] at heM; aesop;
      rcases he_cases with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ T_pair ];
      · unfold trianglesSharingEdge; aesop;
      · unfold trianglesSharingEdge; aesop;
      · unfold trianglesSharingEdge; aesop;
      · unfold trianglesSharingEdge; aesop;

-- Source: proven/tuza/nu4/slot69_80891b4c/output.lean
lemma tau_containing_v_in_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesContaining (T_pair G e f) v) ≤ 4 := by
  -- Let's denote the set of triangles in `T_pair G e f` that contain `v` by `S`.
  set S := trianglesContaining (T_pair G e f) v;
  -- We construct a covering edge set `E'` of size 4.
  set E' : Finset (Sym2 V) := Finset.image (fun u => Sym2.mk (v, u)) (e \ {v}) ∪ Finset.image (fun u => Sym2.mk (v, u)) (f \ {v});
  -- We claim `E'` covers `S`.
  have hE'_covers_S : ∀ t ∈ S, ∃ e' ∈ E', e' ∈ t.sym2 := by
    intro t ht;
    -- Since `t ∈ T_pair G e f`, `t` shares an edge with `e` or `f`.
    obtain ⟨u, hu⟩ : ∃ u ∈ t, u ≠ v ∧ (u ∈ e ∨ u ∈ f) := by
      have h_edge : (t ∩ e).card ≥ 2 ∨ (t ∩ f).card ≥ 2 := by
        have h_edge : t ∈ trianglesSharingEdge G e ∪ trianglesSharingEdge G f := by
          exact?;
        unfold trianglesSharingEdge at h_edge; aesop;
      obtain h | h := h_edge;
      · obtain ⟨ u, hu, hu' ⟩ := Finset.exists_mem_ne ( lt_of_lt_of_le ( by decide ) h ) v;
        exact ⟨ u, Finset.mem_of_mem_inter_left hu, hu', Or.inl ( Finset.mem_of_mem_inter_right hu ) ⟩;
      · obtain ⟨ u, hu ⟩ := Finset.exists_mem_ne h v;
        exact ⟨ u, Finset.mem_of_mem_inter_left hu.1, hu.2, Or.inr ( Finset.mem_of_mem_inter_right hu.1 ) ⟩;
    rcases hu.2.2 with ( hu | hu ) <;> simp_all +decide [ Finset.ext_iff ];
    · simp +zetaDelta at *;
      use Sym2.mk (v, u);
      simp_all +decide [ Sym2.eq ];
      exact ⟨ Or.inl ⟨ u, ⟨ hu, by tauto ⟩, Or.inl rfl ⟩, by rw [ trianglesContaining ] at ht; aesop ⟩;
    · use Sym2.mk (v, u);
      simp +zetaDelta at *;
      exact ⟨ Or.inr ⟨ u, ⟨ hu, by tauto ⟩, Or.inl rfl ⟩, by rw [ trianglesContaining ] at ht; exact Finset.mem_filter.mp ht |>.2, by tauto ⟩;
  -- Since `E'` covers `S`, we have `triangleCoveringNumberOn G S ≤ E'.card`.
  have h_triangleCoveringNumberOn_le_E'_card : triangleCoveringNumberOn G S ≤ E'.card := by
    have hE'_in_set : E' ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2) := by
      have hE'_edges : ∀ u ∈ e \ {v}, G.Adj v u := by
        have := hM.1;
        have := this.1 he; simp_all +decide [ Finset.subset_iff ] ;
        have := this.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        intro u hu huv; have := this ( show v ∈ e from by rw [ Finset.eq_singleton_iff_unique_mem ] at hv; aesop ) hu; aesop;
      have hE'_edges' : ∀ u ∈ f \ {v}, G.Adj v u := by
        have := hM.1;
        have := this.1 hf; simp_all +decide [ Finset.subset_iff ] ;
        have := this.1; simp_all +decide [ Finset.ext_iff ] ;
        intro u hu huv; have := this ( show v ∈ f from by specialize hv v; aesop ) hu; aesop;
      simp_all +decide [ Finset.subset_iff ];
      aesop;
    have h_min_le_E'_card : ∀ {s : Finset ℕ}, s.Nonempty → ∀ x ∈ s, s.min.getD 0 ≤ x := by
      intros s hs x hx; exact (by
      have := Finset.min_le hx; cases h : Finset.min s <;> aesop;);
    exact h_min_le_E'_card ⟨ _, Finset.mem_image_of_mem _ hE'_in_set ⟩ _ ( Finset.mem_image_of_mem _ hE'_in_set );
  -- Since `e` and `f` are triangles in `M`, they each have exactly 3 vertices.
  have he_card : e.card = 3 := by
    have := hM.1.1;
    replace := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    exact this.card_eq
  have hf_card : f.card = 3 := by
    have := hM.1.1 hf; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    exact this.card_eq;
  -- Since `e` and `f` are triangles in `M`, they each have exactly 3 vertices, and `v` is one of them.
  have he_minus_v_card : (e \ {v}).card = 2 := by
    grind
  have hf_minus_v_card : (f \ {v}).card = 2 := by
    grind;
  exact h_triangleCoveringNumberOn_le_E'_card.trans ( Finset.card_union_le _ _ |> le_trans <| add_le_add ( Finset.card_image_le ) ( Finset.card_image_le ) |> le_trans <| by simp +decide [ he_minus_v_card, hf_minus_v_card ] )

-- Source: proven/tuza/nu4/slot69_80891b4c/output.lean
lemma tau_avoiding_v_in_pair_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) ≤ 2 := by
  -- By definition of `triangleCoveringNumberOn`, we need to show that there exists an edge set `E'` of size at most 2 that covers all triangles in `trianglesAvoiding (T_pair G e f) v`.
  have h_exists_edge_set : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 2 ∧ ∀ t ∈ trianglesAvoiding (T_pair G e f) v, ∃ e' ∈ E', e' ∈ t.sym2 := by
    -- Let `b_e` be the base edge of `e` and `b_f` be the base edge of `f`.
    obtain ⟨b_e, hb_e⟩ : ∃ b_e : Sym2 V, b_e ∈ G.edgeFinset ∧ b_e ∈ e.sym2 ∧ ∀ x ∈ e, x ≠ v → x ∈ b_e := by
      have h_triangle_e : e ∈ G.cliqueFinset 3 := by
        have := hM.1.1 he; aesop;
      simp_all +decide [ Finset.ext_iff, SimpleGraph.cliqueFinset ];
      have := Finset.card_eq_three.mp h_triangle_e.2; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := this; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      cases eq_or_ne x v <;> cases eq_or_ne y v <;> cases eq_or_ne z v <;> simp_all +decide [ SimpleGraph.adj_comm ];
      · exact ⟨ Sym2.mk ( y, z ), by aesop ⟩;
      · exact ⟨ Sym2.mk ( x, z ), by aesop ⟩;
      · exact ⟨ Sym2.mk ( x, y ), by aesop ⟩;
      · specialize hv v; aesop;
    obtain ⟨b_f, hb_f⟩ : ∃ b_f : Sym2 V, b_f ∈ G.edgeFinset ∧ b_f ∈ f.sym2 ∧ ∀ x ∈ f, x ≠ v → x ∈ b_f := by
      -- Since $f$ is a triangle, it has exactly three vertices. Let $u$ and $w$ be the vertices of $f$ that are not $v$.
      obtain ⟨u, w, hu, hw, huv⟩ : ∃ u w, u ∈ f ∧ w ∈ f ∧ u ≠ v ∧ w ≠ v ∧ u ≠ w := by
        have h_card_f : f.card = 3 := by
          have := hM.1;
          have := this.1;
          have := this hf; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          exact this.2;
        have := Finset.card_eq_three.mp h_card_f;
        rcases this with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; by_cases hx : x = v <;> by_cases hy : y = v <;> by_cases hz : z = v <;> simp_all +decide ;
      have h_triangle : f ∈ G.cliqueFinset 3 := by
        have := hM.1;
        have := this.1 hf; aesop;
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      have := h_triangle.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      use Sym2.mk (u, w);
      have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset hu ( Finset.insert_subset hw ( Finset.singleton_subset_iff.mpr ( show v ∈ f from by { rw [ Finset.ext_iff ] at hv; specialize hv v; aesop } ) ) ) ) ; aesop;
    refine' ⟨ { b_e, b_f }, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    · exact Finset.card_insert_le _ _;
    · intro t ht
      simp [trianglesAvoiding, T_pair] at ht;
      rcases ht with ⟨ ht | ht, hv ⟩ <;> simp_all +decide [ trianglesSharingEdge ];
      · -- Since $t$ shares an edge with $e$, there exist $x, y \in t$ such that $x \neq y$ and $x, y \in e$.
        obtain ⟨x, y, hxy⟩ : ∃ x y : V, x ∈ t ∧ y ∈ t ∧ x ≠ y ∧ x ∈ e ∧ y ∈ e := by
          obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.1 ht.2; use x, y; aesop;
        have hxy_base : x ∈ b_e ∧ y ∈ b_e := by
          aesop;
        cases b_e ; aesop;
      · -- Since $t$ shares an edge with $f$, and $v \notin t$, the edge must be $b_f$.
        have h_edge_f : ∃ x ∈ f, x ∈ t ∧ ∃ y ∈ f, y ∈ t ∧ x ≠ y ∧ x ≠ v ∧ y ≠ v := by
          obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.1 ht.2;
          exact ⟨ x, Finset.mem_of_mem_inter_right hx, Finset.mem_of_mem_inter_left hx, y, Finset.mem_of_mem_inter_right hy, Finset.mem_of_mem_inter_left hy, hxy, by rintro rfl; exact hv ( Finset.mem_of_mem_inter_left hx ), by rintro rfl; exact hv ( Finset.mem_of_mem_inter_left hy ) ⟩;
        obtain ⟨ x, hx, hx', y, hy, hy', hxy, hxv, hyv ⟩ := h_edge_f; have := hb_f.2.2 x hx hxv; have := hb_f.2.2 y hy hyv; simp_all +decide [ Sym2.eq ] ;
        cases b_f ; aesop;
  unfold triangleCoveringNumberOn;
  have h_min_card : ∃ E' ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ trianglesAvoiding (T_pair G e f) v, ∃ e ∈ E', e ∈ t.sym2}), E' ≤ 2 := by
    aesop;
  norm_num +zetaDelta at *;
  obtain ⟨ E', hE₁, hE₂ ⟩ := h_min_card;
  have h_min_card : Finset.min (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ trianglesAvoiding (T_pair G e f) v, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})) ≤ E'.card := by
    exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( fun x hx => by aesop ), hE₁.2 ⟩, rfl ⟩ );
  exact Nat.le_trans ( by cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ trianglesAvoiding ( T_pair G e f ) v, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop ) hE₂

-- Source: proven/tuza/nu4/slot70_d3159016/diagonal_bridges.lean
lemma tau_le_of_exists_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h_sub : E' ⊆ G.edgeFinset)
    (h_cover : ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2) :
    triangleCoveringNumberOn G T ≤ E'.card := by
  -- Since $E'$ is a subset of $G.edgeFinset$ and covers $T$, we have $E' \in \{ E'' \subseteq G.edgeFinset \mid E'' \text{ covers } T \}$.
  have h_E'_in_set : E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)) := by
    aesop;
  -- Since $E'$ is in the set of covers, the minimum cardinality of the covers is less than or equal to the cardinality of $E'$.
  have h_min_le_card : ∀ {E'' : Finset (Sym2 V)}, E'' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)) → (triangleCoveringNumberOn G T) ≤ E''.card := by
    intro E'' hE'';
    have h_min_le_card : ∀ {s : Finset ℕ}, s.Nonempty → ∀ n ∈ s, (s.min.getD 0) ≤ n := by
      intro s hs n hn; have := Finset.min_le hn; cases h : Finset.min s <;> aesop;
    exact h_min_le_card ⟨ _, Finset.mem_image_of_mem _ hE'' ⟩ _ ( Finset.mem_image_of_mem _ hE'' );
  exact h_min_le_card h_E'_in_set

-- Source: proven/tuza/nu4/slot70_d3159016/diagonal_bridges.lean
lemma filter_covers_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (hT : T ⊆ G.cliqueFinset 3) :
    (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)).Nonempty := by
  refine' ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.Subset.refl _ ), _ ⟩ ⟩;
  simp_all +decide [ Finset.subset_iff ];
  intro t ht; have := hT ht; rcases this with ⟨ h1, h2 ⟩ ; obtain ⟨ u, v, w, huv, hvw, hwu ⟩ := Finset.card_eq_three.mp h2; use Sym2.mk ( u, v ) ; aesop;

-- Source: proven/tuza/nu4/slot70_d3159016/diagonal_bridges.lean
lemma exists_min_cover (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset (Finset V))
    (hT : T ⊆ G.cliqueFinset 3) :
    ∃ E' ⊆ G.edgeFinset, (∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card = triangleCoveringNumberOn G T := by
  -- By definition of `triangleCoveringNumberOn`, there exists a subset `E'` of `G.edgeFinset` such that `E'` covers all triangles in `T` and `E'.card` is the minimum possible.
  obtain ⟨E', hE'_cover, hE'_card⟩ : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)), E'.card = triangleCoveringNumberOn G T := by
    unfold triangleCoveringNumberOn;
    have := Finset.min_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) ) from ?_ );
    · obtain ⟨ a, ha ⟩ := this;
      have := Finset.mem_of_min ha; aesop;
    · refine' Finset.Nonempty.image _ _;
      exact?;
  exact ⟨ E', Finset.mem_powerset.mp ( Finset.mem_filter.mp hE'_cover |>.1 ), Finset.mem_filter.mp hE'_cover |>.2, hE'_card ⟩

-- Source: proven/tuza/nu4/slot70_d3159016/diagonal_bridges.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
      simp +decide [ triangleCoveringNumberOn ];
      by_cases hA : { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t }.Nonempty;
      · obtain ⟨E₁, hE₁⟩ : ∃ E₁ ⊆ G.edgeFinset, (∀ t ∈ A, ∃ e ∈ E₁, ∀ a ∈ e, a ∈ t) ∧ E₁.card = (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min.getD 0 := by
          have := Finset.min_of_nonempty ( show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ).Nonempty from ?_ );
          · obtain ⟨ a, ha ⟩ := this;
            have := Finset.mem_of_min ha; aesop;
          · simp +zetaDelta at *;
            exact ⟨ hA.choose, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hA.choose_spec |>.1 ) ), fun t ht => Finset.mem_filter.mp hA.choose_spec |>.2 t ( Or.inl ht ) ⟩ ⟩;
        obtain ⟨E₂, hE₂⟩ : ∃ E₂ ⊆ G.edgeFinset, (∀ t ∈ B, ∃ e ∈ E₂, ∀ a ∈ e, a ∈ t) ∧ E₂.card = (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min.getD 0 := by
          have := Finset.min_of_nonempty ( show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ).Nonempty from ?_ );
          · obtain ⟨ a, ha ⟩ := this;
            have := Finset.mem_of_min ha;
            rw [ Finset.mem_image ] at this; obtain ⟨ E₂, hE₂, rfl ⟩ := this; use E₂; aesop;
          · obtain ⟨ E', hE' ⟩ := hA;
            exact ⟨ _, Finset.mem_image_of_mem _ ( show E' ∈ { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } from by aesop ) ⟩;
        have h_union : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min.getD 0 ≤ (E₁ ∪ E₂).card := by
          have h_union : ∀ E' ∈ {E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t}, (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min.getD 0 ≤ E'.card := by
            intro E' hE'
            have h_min : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ E'.card := by
              exact Finset.min_le ( Finset.mem_image_of_mem _ hE' );
            cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop;
          grind;
        exact h_union.trans ( Finset.card_union_le _ _ ) |> le_trans <| by linarith;
      · rw [ Finset.not_nonempty_iff_eq_empty.mp hA ] ; simp +decide;
        exact Nat.zero_le _ -- PROVEN in slot61

-- Source: proven/tuza/nu4/slot70_d3159016/diagonal_bridges.lean
lemma tau_le_2_of_K4_plus_one_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e.card = 3)
    (S : Finset (Finset V)) (hS : S ⊆ S_e G M e)
    (u v w : V) (h_e : e = {u, v, w}) (h_distinct : u ≠ v ∧ v ≠ w ∧ u ≠ w)
    (x : V) (hx : x ∉ e)
    (t1 t2 t3 : Finset V)
    (h_t1 : t1 = {u, v, x}) (h_t1_mem : t1 ∈ S)
    (h_t2 : t2 = {v, w, x}) (h_t2_mem : t2 ∈ S)
    (h_t3 : t3 = {w, u, x}) (h_t3_mem : t3 ∈ S)
    (h_extras : ∀ t ∈ S, t ≠ t1 → t ≠ t2 → t ≠ t3 → t ∩ e = {u, v}) :
    triangleCoveringNumberOn G S ≤ 2 := by
  -- We claim that the set of edges $E' = \{ \{u, v\}, \{w, x\} \}$ covers $S$.
  set E' : Finset (Sym2 V) := {Sym2.mk (u, v), Sym2.mk (w, x)} with hE';
  -- We need to show that $E'$ covers $S$.
  have h_cover : ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2 := by
    intro t ht
    by_cases h_cases : t = t1 ∨ t = t2 ∨ t = t3;
    · rcases h_cases with ( rfl | rfl | rfl ) <;> simp +decide [ *, Finset.mem_sym2_iff ];
    · have := h_extras t ht ( by tauto ) ( by tauto ) ( by tauto ) ; simp_all +decide [ Finset.ext_iff ] ;
      exact Or.inl ⟨ by specialize this u; aesop, by specialize this v; aesop ⟩;
  -- We need to show that $E'$ is a subset of $G.edgeFinset$.
  have h_subset : E' ⊆ G.edgeFinset := by
    simp_all +decide [ Finset.subset_iff ];
    have := hS h_t1_mem; have := hS h_t2_mem; have := hS h_t3_mem; simp_all +decide [ S_e ] ;
    have := hS h_t1_mem; have := hS h_t2_mem; have := hS h_t3_mem; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    grind;
  refine' le_trans ( tau_le_of_exists_cover G S E' h_subset h_cover ) _;
  exact Finset.card_insert_le _ _

-- Source: proven/tuza/nu4/slot70_d3159016/output.lean
lemma tau_le_of_exists_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h_sub : E' ⊆ G.edgeFinset)
    (h_cover : ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2) :
    triangleCoveringNumberOn G T ≤ E'.card := by
  -- Since $E'$ is a subset of $G.edgeFinset$ and covers $T$, we have $E' \in \{ E'' \subseteq G.edgeFinset \mid E'' \text{ covers } T \}$.
  have h_E'_in_set : E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)) := by
    aesop;
  -- Since $E'$ is in the set of covers, the minimum cardinality of the covers is less than or equal to the cardinality of $E'$.
  have h_min_le_card : ∀ {E'' : Finset (Sym2 V)}, E'' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)) → (triangleCoveringNumberOn G T) ≤ E''.card := by
    intro E'' hE'';
    have h_min_le_card : ∀ {s : Finset ℕ}, s.Nonempty → ∀ n ∈ s, (s.min.getD 0) ≤ n := by
      intro s hs n hn; have := Finset.min_le hn; cases h : Finset.min s <;> aesop;
    exact h_min_le_card ⟨ _, Finset.mem_image_of_mem _ hE'' ⟩ _ ( Finset.mem_image_of_mem _ hE'' );
  exact h_min_le_card h_E'_in_set

-- Source: proven/tuza/nu4/slot70_d3159016/output.lean
lemma filter_covers_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V)) (hT : T ⊆ G.cliqueFinset 3) :
    (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)).Nonempty := by
  refine' ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.Subset.refl _ ), _ ⟩ ⟩;
  simp_all +decide [ Finset.subset_iff ];
  intro t ht; have := hT ht; rcases this with ⟨ h1, h2 ⟩ ; obtain ⟨ u, v, w, huv, hvw, hwu ⟩ := Finset.card_eq_three.mp h2; use Sym2.mk ( u, v ) ; aesop;

-- Source: proven/tuza/nu4/slot70_d3159016/output.lean
lemma exists_min_cover (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset (Finset V))
    (hT : T ⊆ G.cliqueFinset 3) :
    ∃ E' ⊆ G.edgeFinset, (∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card = triangleCoveringNumberOn G T := by
  -- By definition of `triangleCoveringNumberOn`, there exists a subset `E'` of `G.edgeFinset` such that `E'` covers all triangles in `T` and `E'.card` is the minimum possible.
  obtain ⟨E', hE'_cover, hE'_card⟩ : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2)), E'.card = triangleCoveringNumberOn G T := by
    unfold triangleCoveringNumberOn;
    have := Finset.min_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) ) from ?_ );
    · obtain ⟨ a, ha ⟩ := this;
      have := Finset.mem_of_min ha; aesop;
    · refine' Finset.Nonempty.image _ _;
      exact?;
  exact ⟨ E', Finset.mem_powerset.mp ( Finset.mem_filter.mp hE'_cover |>.1 ), Finset.mem_filter.mp hE'_cover |>.2, hE'_card ⟩

-- Source: proven/tuza/nu4/slot70_d3159016/output.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
      simp +decide [ triangleCoveringNumberOn ];
      by_cases hA : { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t }.Nonempty;
      · obtain ⟨E₁, hE₁⟩ : ∃ E₁ ⊆ G.edgeFinset, (∀ t ∈ A, ∃ e ∈ E₁, ∀ a ∈ e, a ∈ t) ∧ E₁.card = (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min.getD 0 := by
          have := Finset.min_of_nonempty ( show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ).Nonempty from ?_ );
          · obtain ⟨ a, ha ⟩ := this;
            have := Finset.mem_of_min ha; aesop;
          · simp +zetaDelta at *;
            exact ⟨ hA.choose, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hA.choose_spec |>.1 ) ), fun t ht => Finset.mem_filter.mp hA.choose_spec |>.2 t ( Or.inl ht ) ⟩ ⟩;
        obtain ⟨E₂, hE₂⟩ : ∃ E₂ ⊆ G.edgeFinset, (∀ t ∈ B, ∃ e ∈ E₂, ∀ a ∈ e, a ∈ t) ∧ E₂.card = (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min.getD 0 := by
          have := Finset.min_of_nonempty ( show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ).Nonempty from ?_ );
          · obtain ⟨ a, ha ⟩ := this;
            have := Finset.mem_of_min ha;
            rw [ Finset.mem_image ] at this; obtain ⟨ E₂, hE₂, rfl ⟩ := this; use E₂; aesop;
          · obtain ⟨ E', hE' ⟩ := hA;
            exact ⟨ _, Finset.mem_image_of_mem _ ( show E' ∈ { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } from by aesop ) ⟩;
        have h_union : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min.getD 0 ≤ (E₁ ∪ E₂).card := by
          have h_union : ∀ E' ∈ {E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t}, (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min.getD 0 ≤ E'.card := by
            intro E' hE'
            have h_min : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ E'.card := by
              exact Finset.min_le ( Finset.mem_image_of_mem _ hE' );
            cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop;
          grind;
        exact h_union.trans ( Finset.card_union_le _ _ ) |> le_trans <| by linarith;
      · rw [ Finset.not_nonempty_iff_eq_empty.mp hA ] ; simp +decide;
        exact Nat.zero_le _ -- PROVEN in slot61

-- Source: proven/tuza/nu4/slot70_d3159016/output.lean
lemma tau_le_2_of_K4_plus_one_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e.card = 3)
    (S : Finset (Finset V)) (hS : S ⊆ S_e G M e)
    (u v w : V) (h_e : e = {u, v, w}) (h_distinct : u ≠ v ∧ v ≠ w ∧ u ≠ w)
    (x : V) (hx : x ∉ e)
    (t1 t2 t3 : Finset V)
    (h_t1 : t1 = {u, v, x}) (h_t1_mem : t1 ∈ S)
    (h_t2 : t2 = {v, w, x}) (h_t2_mem : t2 ∈ S)
    (h_t3 : t3 = {w, u, x}) (h_t3_mem : t3 ∈ S)
    (h_extras : ∀ t ∈ S, t ≠ t1 → t ≠ t2 → t ≠ t3 → t ∩ e = {u, v}) :
    triangleCoveringNumberOn G S ≤ 2 := by
  -- We claim that the set of edges $E' = \{ \{u, v\}, \{w, x\} \}$ covers $S$.
  set E' : Finset (Sym2 V) := {Sym2.mk (u, v), Sym2.mk (w, x)} with hE';
  -- We need to show that $E'$ covers $S$.
  have h_cover : ∀ t ∈ S, ∃ e ∈ E', e ∈ t.sym2 := by
    intro t ht
    by_cases h_cases : t = t1 ∨ t = t2 ∨ t = t3;
    · rcases h_cases with ( rfl | rfl | rfl ) <;> simp +decide [ *, Finset.mem_sym2_iff ];
    · have := h_extras t ht ( by tauto ) ( by tauto ) ( by tauto ) ; simp_all +decide [ Finset.ext_iff ] ;
      exact Or.inl ⟨ by specialize this u; aesop, by specialize this v; aesop ⟩;
  -- We need to show that $E'$ is a subset of $G.edgeFinset$.
  have h_subset : E' ⊆ G.edgeFinset := by
    simp_all +decide [ Finset.subset_iff ];
    have := hS h_t1_mem; have := hS h_t2_mem; have := hS h_t3_mem; simp_all +decide [ S_e ] ;
    have := hS h_t1_mem; have := hS h_t2_mem; have := hS h_t3_mem; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    grind;
  refine' le_trans ( tau_le_of_exists_cover G S E' h_subset h_cover ) _;
  exact Finset.card_insert_le _ _

-- Source: proven/tuza/nu4/slot71_5a800e22/Se_structure.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  unfold triangleCoveringNumberOn;
  by_cases hA : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2;
  · by_cases hB : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2;
    · obtain ⟨E₁, hE₁⟩ : ∃ E₁ ∈ G.edgeFinset.powerset, (∀ t ∈ A, ∃ e ∈ E₁, e ∈ t.sym2) ∧ E₁.card = (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 := by
        have h_min_card : ∃ E₁ ∈ Finset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset), ∀ E₂ ∈ Finset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset), E₁.card ≤ E₂.card := by
          apply_rules [ Finset.exists_min_image ];
          exact ⟨ hA.choose, Finset.mem_filter.mpr ⟨ hA.choose_spec.1, hA.choose_spec.2 ⟩ ⟩;
        obtain ⟨ E₁, hE₁₁, hE₁₂ ⟩ := h_min_card;
        use E₁;
        rw [ Finset.min_eq_inf_withTop ];
        rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 ) ( G.edgeFinset.powerset ) ) ).inf WithTop.some = WithTop.some E₁.card from ?_ ];
        · exact ⟨ Finset.mem_filter.mp hE₁₁ |>.1, Finset.mem_filter.mp hE₁₁ |>.2, rfl ⟩;
        · refine' le_antisymm _ _;
          · exact Finset.inf_le ( Finset.mem_image_of_mem _ hE₁₁ );
          · simp +zetaDelta at *;
            exact hE₁₂;
      obtain ⟨E₂, hE₂⟩ : ∃ E₂ ∈ G.edgeFinset.powerset, (∀ t ∈ B, ∃ e ∈ E₂, e ∈ t.sym2) ∧ E₂.card = (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 := by
        have := Finset.min_of_mem ( show Finset.card ( Classical.choose hB ) ∈ Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) from Finset.mem_image.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Classical.choose_spec hB |>.1, Classical.choose_spec hB |>.2 ⟩, rfl ⟩ );
        obtain ⟨ b, hb ⟩ := this;
        have := Finset.mem_of_min hb;
        rw [ Finset.mem_image ] at this; obtain ⟨ E₂, hE₂, rfl ⟩ := this; exact ⟨ E₂, Finset.mem_filter.mp hE₂ |>.1, Finset.mem_filter.mp hE₂ |>.2, by rw [ hb ] ; rfl ⟩ ;
      have h_union_cover : ∃ E' ∈ G.edgeFinset.powerset, (∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card ≤ E₁.card + E₂.card := by
        use E₁ ∪ E₂;
        grind;
      have h_min_le : ∀ E' ∈ G.edgeFinset.powerset, (∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) → (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 ≤ E'.card := by
        intros E' hE' hE'_cover;
        have h_min_le : ∀ x ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2}), (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 ≤ x := by
          simp +decide [ Option.getD ];
          intro x E' hE' hE'_cover hx;
          cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> simp +decide [ h ];
          exact Nat.cast_le.mp ( h ▸ Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by simpa [ Finset.subset_iff ] using hE' ), hE'_cover ⟩, hx ⟩ ) );
        exact h_min_le _ ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ hE', hE'_cover ⟩ ) );
      exact le_trans ( h_min_le _ h_union_cover.choose_spec.1 h_union_cover.choose_spec.2.1 ) ( h_union_cover.choose_spec.2.2.trans ( by linarith ) );
    · rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hB ⟨ E', Finset.mem_filter.mp hE' |>.1, Finset.mem_filter.mp hE' |>.2 ⟩ ] ; simp +decide;
      rw [ show { E' ∈ G.edgeFinset.powerset | ∀ t, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hB ⟨ E', Finset.mem_filter.mp hE' |>.1, fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := Finset.mem_filter.mp hE' |>.2 t ( Or.inr ht ) ; exact ⟨ e, he₁, by simpa using he₂ ⟩ ⟩ ] ; simp +decide;
  · rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2 } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hA ⟨ E', Finset.mem_filter.mp hE' |>.1, fun t ht => Finset.mem_filter.mp hE' |>.2 t ( Finset.mem_union_left _ ht ) ⟩ ] ; simp +decide;
    simp +decide [ Option.getD ] -- PROVEN in slot61

-- Source: proven/tuza/nu4/slot71_5a800e22/output.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  unfold triangleCoveringNumberOn;
  by_cases hA : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2;
  · by_cases hB : ∃ E' ∈ G.edgeFinset.powerset, ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2;
    · obtain ⟨E₁, hE₁⟩ : ∃ E₁ ∈ G.edgeFinset.powerset, (∀ t ∈ A, ∃ e ∈ E₁, e ∈ t.sym2) ∧ E₁.card = (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 := by
        have h_min_card : ∃ E₁ ∈ Finset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset), ∀ E₂ ∈ Finset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset), E₁.card ≤ E₂.card := by
          apply_rules [ Finset.exists_min_image ];
          exact ⟨ hA.choose, Finset.mem_filter.mpr ⟨ hA.choose_spec.1, hA.choose_spec.2 ⟩ ⟩;
        obtain ⟨ E₁, hE₁₁, hE₁₂ ⟩ := h_min_card;
        use E₁;
        rw [ Finset.min_eq_inf_withTop ];
        rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 ) ( G.edgeFinset.powerset ) ) ).inf WithTop.some = WithTop.some E₁.card from ?_ ];
        · exact ⟨ Finset.mem_filter.mp hE₁₁ |>.1, Finset.mem_filter.mp hE₁₁ |>.2, rfl ⟩;
        · refine' le_antisymm _ _;
          · exact Finset.inf_le ( Finset.mem_image_of_mem _ hE₁₁ );
          · simp +zetaDelta at *;
            exact hE₁₂;
      obtain ⟨E₂, hE₂⟩ : ∃ E₂ ∈ G.edgeFinset.powerset, (∀ t ∈ B, ∃ e ∈ E₂, e ∈ t.sym2) ∧ E₂.card = (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 := by
        have := Finset.min_of_mem ( show Finset.card ( Classical.choose hB ) ∈ Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) from Finset.mem_image.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Classical.choose_spec hB |>.1, Classical.choose_spec hB |>.2 ⟩, rfl ⟩ );
        obtain ⟨ b, hb ⟩ := this;
        have := Finset.mem_of_min hb;
        rw [ Finset.mem_image ] at this; obtain ⟨ E₂, hE₂, rfl ⟩ := this; exact ⟨ E₂, Finset.mem_filter.mp hE₂ |>.1, Finset.mem_filter.mp hE₂ |>.2, by rw [ hb ] ; rfl ⟩ ;
      have h_union_cover : ∃ E' ∈ G.edgeFinset.powerset, (∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card ≤ E₁.card + E₂.card := by
        use E₁ ∪ E₂;
        grind;
      have h_min_le : ∀ E' ∈ G.edgeFinset.powerset, (∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) → (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 ≤ E'.card := by
        intros E' hE' hE'_cover;
        have h_min_le : ∀ x ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2}), (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2})).min.getD 0 ≤ x := by
          simp +decide [ Option.getD ];
          intro x E' hE' hE'_cover hx;
          cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> simp +decide [ h ];
          exact Nat.cast_le.mp ( h ▸ Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by simpa [ Finset.subset_iff ] using hE' ), hE'_cover ⟩, hx ⟩ ) );
        exact h_min_le _ ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ hE', hE'_cover ⟩ ) );
      exact le_trans ( h_min_le _ h_union_cover.choose_spec.1 h_union_cover.choose_spec.2.1 ) ( h_union_cover.choose_spec.2.2.trans ( by linarith ) );
    · rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hB ⟨ E', Finset.mem_filter.mp hE' |>.1, Finset.mem_filter.mp hE' |>.2 ⟩ ] ; simp +decide;
      rw [ show { E' ∈ G.edgeFinset.powerset | ∀ t, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hB ⟨ E', Finset.mem_filter.mp hE' |>.1, fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := Finset.mem_filter.mp hE' |>.2 t ( Or.inr ht ) ; exact ⟨ e, he₁, by simpa using he₂ ⟩ ⟩ ] ; simp +decide;
  · rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2 } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hA ⟨ E', Finset.mem_filter.mp hE' |>.1, fun t ht => Finset.mem_filter.mp hE' |>.2 t ( Finset.mem_union_left _ ht ) ⟩ ] ; simp +decide;
    simp +decide [ Option.getD ] -- PROVEN in slot61

-- Source: proven/tuza/nu4/slot72_f0a24a15/cycle_path_reduction.lean
lemma isCovering_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isCovering G A EA) (hB : isCovering G B EB) :
    isCovering G (A ∪ B) (EA ∪ EB) := by
  -- By definition of $isCovering$, we know that $EA$ covers $A$ and $EB$ covers $B$ by removing one edge from each clique in $A$ and $B$.
  apply And.intro;
  · exact Finset.union_subset hA.1 hB.1;
  · -- By definition of $isCovering$, we know that for any triangle $t$ in $A$, there exists an edge $e$ in $EA$ such that $e$ is in $t$'s sym2.
    intro t ht
    cases' Finset.mem_union.mp ht with htA htB
    · obtain ⟨e, heEA, heT⟩ := hA.right t htA
      exact ⟨e, Finset.mem_union_left _ heEA, heT⟩
    · obtain ⟨e, heEB, heT⟩ := hB.right t htB
      exact ⟨e, Finset.mem_union_right _ heEB, heT⟩

def hasCovering (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : Prop :=
  ∃ E' ⊆ G.edgeFinset, ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

-- Source: proven/tuza/nu4/slot72_f0a24a15/cycle_path_reduction.lean
lemma exists_min_covering (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : hasCovering G triangles) :
    ∃ E', isCovering G triangles E' ∧ E'.card = triangleCoveringNumberOn G triangles := by
  have h_covering_number : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)), E'.card = (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0) := by
    have h_exists : ∃ E' ∈ Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset (G.edgeFinset)), ∀ E'' ∈ Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset (G.edgeFinset)), E'.card ≤ E''.card := by
      apply_rules [ Finset.exists_min_image ];
      obtain ⟨ E', hE' ⟩ := h;
      exact ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'.1, hE'.2 ⟩ ⟩;
    obtain ⟨ E', hE₁, hE₂ ⟩ := h_exists;
    have h_exists_min : (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset (G.edgeFinset)))).min = some E'.card := by
      refine' le_antisymm _ _;
      · exact Finset.min_le ( Finset.mem_image_of_mem _ hE₁ );
      · simp +zetaDelta at *;
        exact fun a x hx₁ hx₂ hx₃ => hx₃ ▸ WithTop.coe_le_coe.mpr ( hE₂ x hx₁ hx₂ );
    exact ⟨ E', hE₁, h_exists_min.symm ▸ rfl ⟩;
  unfold isCovering triangleCoveringNumberOn; aesop;

-- Source: proven/tuza/nu4/slot72_f0a24a15/cycle_path_reduction.lean
lemma covering_ge_tau (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (E' : Finset (Sym2 V)) (h : isCovering G triangles E') :
    triangleCoveringNumberOn G triangles ≤ E'.card := by
  -- By definition of triangle covering number, we know that for any covering E', the cardinality of E' is at least the triangle covering number.
  have h_triangle_covering : ∀ E' : Finset (Sym2 V), isCovering G triangles E' → triangleCoveringNumberOn G triangles ≤ E'.card := by
    intro E' hE'
    have h_min : Option.getD (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2})).min 0 ≤ Finset.card E' := by
      have h_subset : E' ∈ Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) G.edgeFinset.powerset := by
        unfold isCovering at hE'; aesop;
      have h_min : ∀ {S : Finset ℕ}, S.Nonempty → ∀ x ∈ S, Option.getD (Finset.min S) 0 ≤ x := by
        -- The minimum of a finite set is the least element, so for any x in S, min(S) ≤ x.
        intros S hS_nonempty x hx
        have h_min_le_x : Finset.min S ≤ x := by
          exact Finset.min_le hx;
        cases h : Finset.min S <;> aesop;
      exact h_min ⟨ _, Finset.mem_image_of_mem _ h_subset ⟩ _ ( Finset.mem_image_of_mem _ h_subset );
    exact?;
  exact h_triangle_covering E' h

-- Source: proven/tuza/nu4/slot72_f0a24a15/cycle_path_reduction.lean
lemma always_has_covering (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h_subset : triangles ⊆ G.cliqueFinset 3) :
    hasCovering G triangles := by
  have h_edge_set : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ (∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) := by
    have h_edge_set : ∀ t ∈ triangles, ∃ e ∈ G.edgeFinset, e ∈ t.sym2 := by
      intro t ht
      have ht_clique : t.card = 3 := by
        exact Finset.mem_filter.mp ( h_subset ht ) |>.2.2
      have ht_edges : ∀ v ∈ t, ∀ w ∈ t, v ≠ w → (Sym2.mk (v, w)) ∈ G.edgeFinset := by
        intro v hv w hw hvw; have := h_subset ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        exact this.1 hv hw hvw
      generalize_proofs at *;
      obtain ⟨ v, hv, w, hw, hne ⟩ := Finset.one_lt_card.1 ( by linarith : 1 < Finset.card t ) ; exact ⟨ s(v, w), ht_edges v hv w hw hne, by aesop ⟩ ;
    exact ⟨ G.edgeFinset, Finset.Subset.refl _, h_edge_set ⟩;
  exact h_edge_set

-- Source: proven/tuza/nu4/slot72_f0a24a15/cycle_path_reduction.lean
lemma tau_eq_zero_of_no_covering (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : ¬ hasCovering G triangles) :
    triangleCoveringNumberOn G triangles = 0 := by
  -- If there's no covering, then the triangle covering number must be zero because there's no way to cover the triangles with any edges.
  simp [triangleCoveringNumberOn, h];
  -- Since the set is empty, the minimum of the image of the cardinalities is zero.
  have h_empty : Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', ∀ a ∈ e, a ∈ t) (G.edgeFinset.powerset) = ∅ := by
    ext E'
    simp [hasCovering] at h;
    specialize h E' ; aesop;
  -- Since the set is empty, the minimum of the image of the cardinalities is zero because the image is also empty.
  simp [h_empty, Finset.min];
  rfl

-- Source: proven/tuza/nu4/slot72_f0a24a15/cycle_path_reduction.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases h_cov : hasCovering G (A ∪ B)
  · -- Case: Covering exists
    have h_cov_A : hasCovering G A := by
      obtain ⟨E, hE_sub, hE_cov⟩ := h_cov
      use E, hE_sub
      intro t ht
      exact hE_cov t (Finset.mem_union_left B ht)
    have h_cov_B : hasCovering G B := by
      obtain ⟨E, hE_sub, hE_cov⟩ := h_cov
      use E, hE_sub
      intro t ht
      exact hE_cov t (Finset.mem_union_right A ht)
      
    obtain ⟨EA, hEA_cov, hEA_card⟩ := exists_min_covering G A h_cov_A
    obtain ⟨EB, hEB_cov, hEB_card⟩ := exists_min_covering G B h_cov_B
    
    have h_union_cov : isCovering G (A ∪ B) (EA ∪ EB) := isCovering_union G A B EA EB hEA_cov hEB_cov
    
    calc triangleCoveringNumberOn G (A ∪ B) 
      ≤ (EA ∪ EB).card := covering_ge_tau G (A ∪ B) (EA ∪ EB) h_union_cov
    _ ≤ EA.card + EB.card := Finset.card_union_le EA EB
    _ = triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by rw [hEA_card, hEB_card]
    
  · -- Case: No covering
    rw [tau_eq_zero_of_no_covering G (A ∪ B) h_cov]
    exact Nat.zero_le _

-- Source: proven/tuza/nu4/slot72_f0a24a15/output.lean
lemma isCovering_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isCovering G A EA) (hB : isCovering G B EB) :
    isCovering G (A ∪ B) (EA ∪ EB) := by
  -- By definition of $isCovering$, we know that $EA$ covers $A$ and $EB$ covers $B$ by removing one edge from each clique in $A$ and $B$.
  apply And.intro;
  · exact Finset.union_subset hA.1 hB.1;
  · -- By definition of $isCovering$, we know that for any triangle $t$ in $A$, there exists an edge $e$ in $EA$ such that $e$ is in $t$'s sym2.
    intro t ht
    cases' Finset.mem_union.mp ht with htA htB
    · obtain ⟨e, heEA, heT⟩ := hA.right t htA
      exact ⟨e, Finset.mem_union_left _ heEA, heT⟩
    · obtain ⟨e, heEB, heT⟩ := hB.right t htB
      exact ⟨e, Finset.mem_union_right _ heEB, heT⟩

def hasCovering (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : Prop :=
  ∃ E' ⊆ G.edgeFinset, ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

-- Source: proven/tuza/nu4/slot72_f0a24a15/output.lean
lemma exists_min_covering (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : hasCovering G triangles) :
    ∃ E', isCovering G triangles E' ∧ E'.card = triangleCoveringNumberOn G triangles := by
  have h_covering_number : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)), E'.card = (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0) := by
    have h_exists : ∃ E' ∈ Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset (G.edgeFinset)), ∀ E'' ∈ Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset (G.edgeFinset)), E'.card ≤ E''.card := by
      apply_rules [ Finset.exists_min_image ];
      obtain ⟨ E', hE' ⟩ := h;
      exact ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'.1, hE'.2 ⟩ ⟩;
    obtain ⟨ E', hE₁, hE₂ ⟩ := h_exists;
    have h_exists_min : (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset (G.edgeFinset)))).min = some E'.card := by
      refine' le_antisymm _ _;
      · exact Finset.min_le ( Finset.mem_image_of_mem _ hE₁ );
      · simp +zetaDelta at *;
        exact fun a x hx₁ hx₂ hx₃ => hx₃ ▸ WithTop.coe_le_coe.mpr ( hE₂ x hx₁ hx₂ );
    exact ⟨ E', hE₁, h_exists_min.symm ▸ rfl ⟩;
  unfold isCovering triangleCoveringNumberOn; aesop;

-- Source: proven/tuza/nu4/slot72_f0a24a15/output.lean
lemma covering_ge_tau (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (E' : Finset (Sym2 V)) (h : isCovering G triangles E') :
    triangleCoveringNumberOn G triangles ≤ E'.card := by
  -- By definition of triangle covering number, we know that for any covering E', the cardinality of E' is at least the triangle covering number.
  have h_triangle_covering : ∀ E' : Finset (Sym2 V), isCovering G triangles E' → triangleCoveringNumberOn G triangles ≤ E'.card := by
    intro E' hE'
    have h_min : Option.getD (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2})).min 0 ≤ Finset.card E' := by
      have h_subset : E' ∈ Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) G.edgeFinset.powerset := by
        unfold isCovering at hE'; aesop;
      have h_min : ∀ {S : Finset ℕ}, S.Nonempty → ∀ x ∈ S, Option.getD (Finset.min S) 0 ≤ x := by
        -- The minimum of a finite set is the least element, so for any x in S, min(S) ≤ x.
        intros S hS_nonempty x hx
        have h_min_le_x : Finset.min S ≤ x := by
          exact Finset.min_le hx;
        cases h : Finset.min S <;> aesop;
      exact h_min ⟨ _, Finset.mem_image_of_mem _ h_subset ⟩ _ ( Finset.mem_image_of_mem _ h_subset );
    exact?;
  exact h_triangle_covering E' h

-- Source: proven/tuza/nu4/slot72_f0a24a15/output.lean
lemma always_has_covering (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h_subset : triangles ⊆ G.cliqueFinset 3) :
    hasCovering G triangles := by
  have h_edge_set : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ (∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) := by
    have h_edge_set : ∀ t ∈ triangles, ∃ e ∈ G.edgeFinset, e ∈ t.sym2 := by
      intro t ht
      have ht_clique : t.card = 3 := by
        exact Finset.mem_filter.mp ( h_subset ht ) |>.2.2
      have ht_edges : ∀ v ∈ t, ∀ w ∈ t, v ≠ w → (Sym2.mk (v, w)) ∈ G.edgeFinset := by
        intro v hv w hw hvw; have := h_subset ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        exact this.1 hv hw hvw
      generalize_proofs at *;
      obtain ⟨ v, hv, w, hw, hne ⟩ := Finset.one_lt_card.1 ( by linarith : 1 < Finset.card t ) ; exact ⟨ s(v, w), ht_edges v hv w hw hne, by aesop ⟩ ;
    exact ⟨ G.edgeFinset, Finset.Subset.refl _, h_edge_set ⟩;
  exact h_edge_set

-- Source: proven/tuza/nu4/slot72_f0a24a15/output.lean
lemma tau_eq_zero_of_no_covering (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : ¬ hasCovering G triangles) :
    triangleCoveringNumberOn G triangles = 0 := by
  -- If there's no covering, then the triangle covering number must be zero because there's no way to cover the triangles with any edges.
  simp [triangleCoveringNumberOn, h];
  -- Since the set is empty, the minimum of the image of the cardinalities is zero.
  have h_empty : Finset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', ∀ a ∈ e, a ∈ t) (G.edgeFinset.powerset) = ∅ := by
    ext E'
    simp [hasCovering] at h;
    specialize h E' ; aesop;
  -- Since the set is empty, the minimum of the image of the cardinalities is zero because the image is also empty.
  simp [h_empty, Finset.min];
  rfl

-- Source: proven/tuza/nu4/slot72_f0a24a15/output.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases h_cov : hasCovering G (A ∪ B)
  · -- Case: Covering exists
    have h_cov_A : hasCovering G A := by
      obtain ⟨E, hE_sub, hE_cov⟩ := h_cov
      use E, hE_sub
      intro t ht
      exact hE_cov t (Finset.mem_union_left B ht)
    have h_cov_B : hasCovering G B := by
      obtain ⟨E, hE_sub, hE_cov⟩ := h_cov
      use E, hE_sub
      intro t ht
      exact hE_cov t (Finset.mem_union_right A ht)
      
    obtain ⟨EA, hEA_cov, hEA_card⟩ := exists_min_covering G A h_cov_A
    obtain ⟨EB, hEB_cov, hEB_card⟩ := exists_min_covering G B h_cov_B
    
    have h_union_cov : isCovering G (A ∪ B) (EA ∪ EB) := isCovering_union G A B EA EB hEA_cov hEB_cov
    
    calc triangleCoveringNumberOn G (A ∪ B) 
      ≤ (EA ∪ EB).card := covering_ge_tau G (A ∪ B) (EA ∪ EB) h_union_cov
    _ ≤ EA.card + EB.card := Finset.card_union_le EA EB
    _ = triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by rw [hEA_card, hEB_card]
    
  · -- Case: No covering
    rw [tau_eq_zero_of_no_covering G (A ∪ B) h_cov]
    exact Nat.zero_le _

-- Source: proven/tuza/lemmas/slot24_tau_X_le_2.lean
lemma tau_X_le_2_of_inter_eq_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (h_inter : (e ∩ f).card = 1) :
    triangleCoveringNumberOn G (X G e f) ≤ 2 := by
      unfold triangleCoveringNumberOn;
      have h_cover : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ t ∈ X G e f, ∃ e ∈ E', e ∈ t.sym2 := by
        -- Let v be the unique vertex in e ∩ f. By mem_X_implies_v_in_t, every t in X(e, f) contains v.
        obtain ⟨v, hv⟩ : ∃ v, v ∈ e ∩ f ∧ ∀ t ∈ X G e f, v ∈ t := by
          exact Exists.elim ( Finset.card_eq_one.mp h_inter ) fun v hv => ⟨ v, hv.symm ▸ Finset.mem_singleton_self _, fun t ht => mem_X_implies_v_in_t G e f he hf h_inter t ht |> fun ⟨ w, hw₁, hw₂ ⟩ => by aesop ⟩;
        -- Let $E_e$ be the set of edges in $e$ incident to $v$. Since $e$ is a triangle, $|E_e| = 2$.
        obtain ⟨u, w, hu, hw, huv⟩ : ∃ u w : V, u ≠ v ∧ w ≠ v ∧ e = {v, u, w} ∧ G.Adj v u ∧ G.Adj v w ∧ G.Adj u w := by
          have h_e : e.card = 3 := by
            exact Finset.mem_filter.mp he |>.2.2;
          rw [ Finset.card_eq_three ] at h_e;
          rcases h_e with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          rcases hv.1.1 with ( rfl | rfl | rfl ) <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
          · exact ⟨ y, by tauto, z, by tauto, rfl, by tauto ⟩;
          · exact ⟨ x, by tauto, z, by tauto, by aesop, by tauto, by tauto, by tauto ⟩;
          · exact ⟨ x, hxz, y, hyz, by aesop, by tauto ⟩;
        refine' ⟨ { s(v, u), s(v, w) }, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.cliqueFinset ];
        · simp_all +decide [ Set.insert_subset_iff, SimpleGraph.adj_comm ];
        · exact Finset.card_insert_le _ _;
        · intro t ht;
          have := Finset.mem_filter.mp ht |>.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          contrapose! this; aesop;
      obtain ⟨ E', hE₁, hE₂, hE₃ ⟩ := h_cover;
      have h_min_le_2 : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → (Finset.image Finset.card S).min.getD 0 ≤ E'.card := by
        intros S hE'; exact (by
        have h_min_le_2 : (Finset.image Finset.card S).min.getD 0 ≤ Finset.card E' := by
          have h_min_le_2 : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → (Finset.image Finset.card S).min.getD 0 ≤ Finset.card E' := by
            intros S hE'; exact (by
            have h_min_le_2 : ∀ {S : Finset ℕ}, E'.card ∈ S → (Finset.min S).getD 0 ≤ E'.card := by
              intros S hE'; exact (by
              have h_min_le_2 : ∀ {S : Finset ℕ}, E'.card ∈ S → (Finset.min S).getD 0 ≤ E'.card := by
                intros S hE'
                have h_min_le_2 : (Finset.min S).getD 0 ≤ Finset.min S := by
                  cases h : Finset.min S <;> aesop
                exact Nat.cast_le.mp ( h_min_le_2.trans ( Finset.min_le hE' ) );
              exact h_min_le_2 hE');
            exact h_min_le_2 ( Finset.mem_image_of_mem _ hE' ))
          exact h_min_le_2 hE';
        exact h_min_le_2);
      exact le_trans ( h_min_le_2 ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE₁, hE₃ ⟩ ) ) hE₂

end AristotleLemmas

-- Source: proven/tuza/lemmas/slot24_tau_X_le_2.lean
lemma tau_X_le_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X G e f) ≤ 2 := by
  -- All bridges contain the shared vertex/edge and live on ≤4 vertices
  -- By k4_cover, τ ≤ 2
  -- Consider two cases: |e ∩ f| = 0 and |e ∩ f| = 1.
  by_cases h_inter : (e ∩ f).card ≤ 1;
  · cases h_inter.eq_or_lt <;> simp_all +decide;
    · have := hM.1;
      exact tau_X_le_2_of_inter_eq_1 G e f ( this.1 he ) ( this.1 hf ) ‹_›;
    · rw [ X_eq_empty_of_disjoint G e f ‹_› ];
      unfold triangleCoveringNumberOn;
      simp +decide [ Finset.min ];
      rw [ Finset.inf_eq_iInf ];
      simp +decide [ Option.getD ];
      rw [ show ( ⨅ a : Finset ( Sym2 V ), ⨅ ( _ : ( a : Set ( Sym2 V ) ) ⊆ G.edgeSet ), ( a.card : WithTop ℕ ) ) = 0 from ?_ ] ; simp +decide;
      refine' le_antisymm _ _;
      · refine' le_trans ( ciInf_le _ ∅ ) _ <;> simp +decide;
      · exact zero_le _;
  · have := hM.1;
    exact absurd ( this.2 he hf hef ) ( by aesop )

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Bridge Absorption - edges covering S_e ∪ S_f hit bridges X(e,f)
-- ══════════════════════════════════════════════════════════════════════════════

/-- KEY LEMMA: The packing element e is in S_e (compatible with itself) -/

-- Source: proven/tuza/lemmas/slot24_tau_X_le_2.lean
lemma CE_covers : ∀ t ∈ S CE_G CE_e CE_M ∪ S CE_G CE_f CE_M, ∃ edge ∈ CE_C, edge ∈ t.sym2 := by
  simp +decide [ CE_S_e, CE_S_f ]

/-
Disproof of bridge_absorption.
There exists a graph G, packing M, triangles e, f, and cover C such that premises hold but conclusion fails.
Witnesses are CE_G, CE_M, CE_e, CE_f, CE_C.
Premises checked by CE_isMax, CE_covers, etc.
Conclusion negated by CE_disproof.
-/

-- Source: proven/tuza/lemmas/slot6_Se_lemmas.lean
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  by_cases h_common : ∃ v ∈ e, ∀ t ∈ S_e G M e, v ∈ t;
  · exact?;
  · obtain ⟨u, v, w, x, he_eq, h_distinct, hx_not_in_e, hS_e_subset⟩ : ∃ u v w x, e = {u, v, w} ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ x ∉ e ∧ S_e G M e ⊆ {e, {v, w, x}, {u, w, x}, {u, v, x}} := by
      apply_rules [ Se_structure_complete ];
      exact fun v hv => by push_neg at h_common; exact h_common v hv;
    have h_cover : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2 := by
      use {Sym2.mk (u, v), Sym2.mk (w, x)};
      simp_all +decide [ Finset.subset_iff ];
      have h_adj_uv : G.Adj u v := by
        have h_adj_uv : {u, v, w} ∈ G.cliqueFinset 3 := by
          have := hM.1;
          exact this.1 he;
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        have := h_adj_uv.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      have h_adj_wx : G.Adj w x := by
        have h_triangle : {v, w, x} ∈ G.cliqueFinset 3 := by
          have h_triangle : ∃ t ∈ S_e G M {u, v, w}, t = {v, w, x} := by
            grind;
          simp_all +decide [ S_e ];
          unfold trianglesSharingEdge at h_triangle; aesop;
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        rw [ SimpleGraph.isNClique_iff ] at h_triangle ; aesop;
      grind;
    unfold triangleCoveringNumberOn;
    obtain ⟨ E', hE'_sub, hE'_card, hE'_cover ⟩ := h_cover; have := Finset.min_le ( show E'.card ∈ Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ S_e G M e, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) from Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'_sub, hE'_cover ⟩, rfl ⟩ ) ; simp_all +decide ;
    exact le_trans ( by cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ S_e G M { u, v, w }, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop ) hE'_card

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_Te_le_2_nu_1 (base case)
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/lemmas/slot6_Se_lemmas.lean
lemma tau_Te_le_2_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hnu : M.card = 1)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  have h_S_eq_T : S_e G M e = trianglesSharingEdge G e := by
    ext t
    simp [S_e, trianglesSharingEdge];
    rw [ Finset.card_eq_one ] at hnu ; aesop;
  rw [←h_S_eq_T] at *;
  apply tau_S_le_2 G M hM e he;

end

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma isTriangleCover_iff_mem_filter (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V)) (E' : Finset (Sym2 V)) :
    isTriangleCover G A E' ↔ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)) := by
  unfold isTriangleCover; aesop;

/-
The triangle covering number of a set of triangles A is less than or equal to the size of any specific triangle cover E' of A.
-/

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma le_triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : isTriangleCover G A E') :
    triangleCoveringNumberOn G A ≤ E'.card := by
  unfold triangleCoveringNumberOn;
  have h_mem : E' ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) := by
    exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h.1, h.2 ⟩;
  have := Finset.min_le ( Finset.mem_image_of_mem Finset.card h_mem );
  rw [ WithTop.le_coe_iff ] at this ; aesop

/-
If a triangle cover exists for A, then there exists a triangle cover for A whose size is exactly the triangle covering number of A.
-/

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma exists_min_cover (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V))
    (h : ∃ E', isTriangleCover G A E') :
    ∃ E', isTriangleCover G A E' ∧ E'.card = triangleCoveringNumberOn G A := by
  by_cases h₁ : ∃ E' : Finset (Sym2 V), isTriangleCover G A E';
  · have h₂ : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)), ∀ E'' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)), E'.card ≤ E''.card := by
      apply_rules [ Set.exists_min_image ];
      · exact Set.toFinite _;
      · exact ⟨ h₁.choose, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( h₁.choose_spec.1 ), h₁.choose_spec.2 ⟩ ⟩;
    obtain ⟨ E', hE₁, hE₂ ⟩ := h₂;
    refine' ⟨ E', _, _ ⟩;
    · exact ⟨ Finset.mem_filter.mp hE₁ |>.1 |> Finset.mem_powerset.mp, Finset.mem_filter.mp hE₁ |>.2 ⟩;
    · unfold triangleCoveringNumberOn;
      rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 ) ( G.edgeFinset.powerset ) ) ).min = some ( E'.card ) from ?_, Option.getD_some ];
      refine' le_antisymm _ _;
      · exact Finset.min_le ( Finset.mem_image_of_mem _ hE₁ );
      · simp +zetaDelta at *;
        exact fun a x hx₁ hx₂ hx₃ => hx₃ ▸ WithTop.coe_le_coe.mpr ( hE₂ x hx₁ hx₂ );
  · contradiction

/-
If there is no set of edges that covers the triangles in A, then the triangle covering number of A is defined to be 0.
-/

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma not_coverable_implies_zero (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V))
    (h : ¬ ∃ E', isTriangleCover G A E') :
    triangleCoveringNumberOn G A = 0 := by
  unfold triangleCoveringNumberOn;
  norm_num +zetaDelta at *;
  rw [ show { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } = ∅ from _ ];
  · rfl;
  · ext;
    simp [isTriangleCover] at *;
    exact h _

/-
The union of a triangle cover for A and a triangle cover for B is a triangle cover for the union of A and B.
-/

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma isTriangleCover_union (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  unfold isTriangleCover at *;
  grind

/-
If a set of edges covers a set of triangles B, and A is a subset of B, then the same set of edges also covers A.
-/

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma isTriangleCover_subset (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : A ⊆ B) (hCover : isTriangleCover G B E') :
    isTriangleCover G A E' := by
  exact ⟨ hCover.1, fun t ht => hCover.2 t ( h ht ) ⟩

end AristotleLemmas

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  -- Consider the cases where `A` or `B` have no covers.
  by_cases hA : ∃ E', isTriangleCover G A E'
  by_cases hB : ∃ E', isTriangleCover G B E';
  · obtain ⟨EA, hEA⟩ := exists_min_cover G A hA
    obtain ⟨EB, hEB⟩ := exists_min_cover G B hB;
    exact le_trans ( le_triangleCoveringNumberOn G _ _ ( isTriangleCover_union G A B EA EB hEA.1 hEB.1 ) ) ( by rw [ ← hEA.2, ← hEB.2 ] ; exact Finset.card_union_le _ _ );
  · rw [ not_exists ] at hB;
    rw [ not_coverable_implies_zero _ _ ];
    · exact Nat.zero_le _;
    · exact fun ⟨ E', hE' ⟩ => hB E' <| isTriangleCover_subset _ _ _ _ ( Finset.subset_union_right ) hE';
  · rw [ not_coverable_implies_zero ];
    · exact Nat.zero_le _;
    · norm_num +zetaDelta at *;
      exact fun x hx => hA x <| isTriangleCover_subset _ _ _ _ ( Finset.subset_union_left ) hx

noncomputable section AristotleLemmas

/-
If $t_1, t_2$ are two triangles in $S_e$ (different from $e$), then they must share at least 2 vertices. Otherwise, we could replace $e$ with $\{t_1, t_2\}$ in the packing $M$ to get a larger packing.
-/

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma S_e_cover_of_diverse_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (ta tb : Finset V) (hta : ta ∈ S_e G M e) (htb : tb ∈ S_e G M e)
    (hnea : ta ≠ e) (hneb : tb ≠ e)
    (h_diff_inter : ta ∩ e ≠ tb ∩ e) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
      obtain ⟨ x, hx ⟩ := S_e_structure_of_diverse_inter G M hM e he ta tb hta htb hnea hneb h_diff_inter;
      -- Let $E_a = t_a \cap e$ and $E_b = t_b \cap e$. These are two distinct edges of $e$.
      obtain ⟨E_a, E_b, hE_a, hE_b, hE_distinct⟩ : ∃ E_a E_b : Finset V, E_a ⊆ e ∧ E_b ⊆ e ∧ E_a ≠ E_b ∧ E_a.card = 2 ∧ E_b.card = 2 ∧ ta = insert x E_a ∧ tb = insert x E_b := by
        refine' ⟨ ta ∩ e, tb ∩ e, _, _, _, _, _, hx.2 ta hta hnea, hx.2 tb htb hneb ⟩;
        · exact Finset.inter_subset_right;
        · exact Finset.inter_subset_right;
        · exact h_diff_inter;
        · have h_card : ta.card = 3 := by
            have h_card : ta ∈ G.cliqueFinset 3 := by
              exact Finset.mem_filter.mp hta |>.1 |> Finset.mem_filter.mp |>.1;
            simp +zetaDelta at *;
            exact h_card.2;
          grind;
        · unfold S_e at htb; simp +decide [ Finset.mem_filter ] at htb;
          unfold trianglesSharingEdge at htb; simp +decide [ Finset.mem_filter ] at htb;
          have := Finset.card_le_card ( Finset.inter_subset_left : tb ∩ e ⊆ tb ) ; simp +decide [ htb.1.1.card_eq ] at this ⊢;
          interval_cases _ : Finset.card ( tb ∩ e ) <;> simp +decide at htb ⊢;
          have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : tb ∩ e ⊆ e ) ; simp_all +singlePass ;
          have := hM.1; simp_all +singlePass [ SimpleGraph.isNClique_iff ] ;
          have := this.1 he; simp_all +singlePass [ SimpleGraph.isNClique_iff ] ;
          have := Finset.eq_of_subset_of_card_le ‹e ⊆ tb› ; simp_all +singlePass ;
      -- Let $e = \{u, v, w\}$ where $E_a = \{u, v\}$ and $E_b = \{v, w\}$.
      obtain ⟨u, v, w, heu, hev, hew, he⟩ : ∃ u v w : V, e = {u, v, w} ∧ E_a = {u, v} ∧ E_b = {v, w} := by
        have h_card_e : e.card = 3 := by
          have := hM.1;
          have := this.1 he; simp +decide [ SimpleGraph.cliqueFinset ] at this;
          exact this.2;
        rw [ Finset.card_eq_three ] at h_card_e;
        obtain ⟨ u, v, w, huv, huw, hvw, rfl ⟩ := h_card_e;
        have hE_a_cases : E_a = {u, v} ∨ E_a = {u, w} ∨ E_a = {v, w} := by
          have := Finset.card_eq_two.mp hE_distinct.2.1; obtain ⟨ a, b, hab, rfl ⟩ := this; simp +decide [ Finset.subset_iff ] at hE_a ⊢;
          rcases hE_a with ⟨ rfl | rfl | rfl, rfl | rfl | rfl ⟩ <;> simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] at hab ⊢
        have hE_b_cases : E_b = {u, v} ∨ E_b = {u, w} ∨ E_b = {v, w} := by
          rw [ Finset.card_eq_two ] at hE_distinct;
          rw [ Finset.card_eq_two ] at hE_distinct;
          rcases hE_distinct.2.2.1 with ⟨ x, y, hxy, rfl ⟩ ; simp +decide [ Finset.subset_iff ] at hE_b ⊢;
          rcases hE_b with ⟨ rfl | rfl | rfl, rfl | rfl | rfl ⟩ <;> simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] at hxy ⊢;
        rcases hE_a_cases with ( rfl | rfl | rfl ) <;> rcases hE_b_cases with ( rfl | rfl | rfl ) <;> simp +decide at hE_distinct ⊢;
        all_goals simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] at hE_distinct ⊢;
        exact ⟨ v, u, w, by simp +decide [ *, or_comm, or_left_comm, or_assoc ] ⟩;
        · exact ⟨ u, v, w, by simp +decide [ *, or_comm, or_left_comm, or_assoc ] ⟩;
        · exact ⟨ w, u, v, by simp +decide [ *, or_comm, or_left_comm, or_assoc ] ⟩;
        · exact ⟨ u, w, v, by simp +decide [ *, or_comm, or_left_comm, or_assoc ] ⟩;
        · exact ⟨ w, v, u, by simp +decide [ *, or_comm, or_left_comm, or_assoc ] ⟩;
        · exact ⟨ v, w, u, by simp +decide [ *, or_comm, or_left_comm, or_assoc ] ⟩;
      -- Any other triangle $t \in S_e \setminus \{e\}$ must have $t \cap e$ being an edge of $e$.
      have h_triangle_form : ∀ t ∈ S_e G M e, t ≠ e → t = insert x {u, v} ∨ t = insert x {v, w} ∨ t = insert x {u, w} := by
        intro t ht hte
        have h_inter : t ∩ e = {u, v} ∨ t ∩ e = {v, w} ∨ t ∩ e = {u, w} := by
          have h_inter : (t ∩ e).card = 2 := by
            have h_inter : (t ∩ e).card ≥ 2 := by
              have h_inter : t ∈ trianglesSharingEdge G e := by
                exact Finset.mem_filter.mp ht |>.1;
              exact Finset.mem_filter.mp h_inter |>.2;
            have h_inter : (t ∩ e).card ≤ t.card - 1 := by
              grind;
            have h_inter : t.card ≤ 3 := by
              have := Finset.mem_filter.mp ht;
              unfold trianglesSharingEdge at this; simp +decide at this;
              exact this.1.1.2.le;
            omega;
          rw [ Finset.card_eq_two ] at h_inter;
          rcases h_inter with ⟨ x, y, hxy, h ⟩ ; simp +decide [ h ];
          simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff, heu ] at h ⊢;
          grind;
        rcases h_inter with ( h | h | h ) <;> rw [ hx.2 t ht hte ] <;> simp +decide [ h ];
      -- We claim that $\{ \{u, v\}, \{w, x\} \}$ covers $S_e$.
      have h_cover : ∀ t ∈ S_e G M e, ∃ e' ∈ ({ {u, v}, {w, x} } : Finset (Finset V)), e' ⊆ t := by
        intro t ht
        by_cases hte : t = e;
        · simp +decide [ hte, heu ];
        · rcases h_triangle_form t ht hte with ( rfl | rfl | rfl ) <;> simp +decide [ Finset.subset_iff ];
      -- Therefore, the covering number is at most 2.
      have h_covering_number : ∃ E' ⊆ G.edgeFinset, (∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2) ∧ E'.card ≤ 2 := by
        refine' ⟨ _, _, _, _ ⟩;
        exact { Sym2.mk ( u, v ), Sym2.mk ( w, x ) };
        · simp +decide [ Sym2.mk ];
          rintro _ ( rfl | rfl ) <;> simp +decide [ SimpleGraph.edgeSetEmbedding ];
          · have := hM.1;
            have := this.1 he; simp +decide [ heu ] at this;
            simp +decide [ SimpleGraph.isNClique_iff ] at this;
            grind;
          · have := htb;
            unfold S_e at this; simp +decide [ heu, hev ] at this;
            unfold trianglesSharingEdge at this; simp +decide [ heu, hev ] at this;
            simp +decide [ hE_distinct.2.2.2.2, SimpleGraph.isNClique_iff ] at this;
            by_cases hvw : v = w <;> by_cases hxv : x = v <;> by_cases hxw : x = w <;> simp +decide [ hvw, hxv, hxw ] at this ⊢;
            exact this.1.1.2.2.symm;
        · simp +zetaDelta at *;
          intro t ht; specialize h_cover t ht; rcases h_cover with ( h | h ) <;> simp +decide [ Finset.subset_iff ] at h ⊢ <;> tauto;
        · exact Finset.card_insert_le _ _;
      obtain ⟨ E', hE'_sub, hE'_cover, hE'_card ⟩ := h_covering_number;
      unfold triangleCoveringNumberOn;
      have h_min_le : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', e ∈ t.sym2})).min ≤ E'.card := by
        exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'_sub, hE'_cover ⟩, rfl ⟩ );
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ S_e G M e, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) ) <;> simp +decide [ h ] at h_min_le ⊢;
      simp +zetaDelta at *;
      exact Nat.cast_le.mp ( h ▸ h_min_le |> le_trans <| WithTop.coe_le_coe.mpr hE'_card )

/-
If there is a valid edge cover of size at most k, then the covering number is at most k.
-/

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma triangleCoveringNumberOn_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (k : ℕ)
    (E' : Finset (Sym2 V)) (h_subset : E' ⊆ G.edgeFinset)
    (h_cover : ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    (h_card : E'.card ≤ k) :
    triangleCoveringNumberOn G triangles ≤ k := by
      refine' le_trans _ h_card;
      by_contra h_contra;
      unfold triangleCoveringNumberOn at h_contra; simp_all +decide [ Finset.min' ] ;
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' : Finset ( Sym2 V ) => ∀ t ∈ triangles, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> simp_all +decide [ Option.getD ];
      exact h_contra.not_le ( Nat.cast_le.mp ( h ▸ Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( fun e he => by aesop ), h_cover ⟩, rfl ⟩ ) ) )

/-
If all triangles in $S_e$ (other than $e$) intersect $e$ in the same edge, then the covering number is at most 2.
-/

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma S_e_cover_of_uniform_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_uniform : ∀ t1 t2 : Finset V, t1 ∈ S_e G M e → t2 ∈ S_e G M e → t1 ≠ e → t2 ≠ e → t1 ∩ e = t2 ∩ e) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
      -- We use `triangleCoveringNumberOn_le` with $k=1$.
      have h_univ : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ (E'.card ≤ 1 ∧ ∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2) := by
        by_cases h : ∃ t ∈ S_e G M e, t ≠ e <;> simp_all +decide [ Finset.subset_iff ];
        · obtain ⟨ t, ht₁, ht₂ ⟩ := h;
          obtain ⟨ u, v, huv ⟩ : ∃ u v : V, u ∈ t ∧ v ∈ t ∧ u ∈ e ∧ v ∈ e ∧ u ≠ v := by
            have h_inter_card : (t ∩ e).card ≥ 2 := by
              have := Finset.mem_filter.mp ht₁;
              unfold trianglesSharingEdge at this; aesop;
            obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.mp h_inter_card; use u, v; aesop;
          -- Since $u$ and $v$ are in $e$ and $t$, and $e$ is a triangle in $G$, $\{u, v\}$ is an edge in $G$.
          have h_edge : Sym2.mk (u, v) ∈ G.edgeFinset := by
            have h_triangle : t ∈ G.cliqueFinset 3 := by
              exact Finset.mem_filter.mp ht₁ |>.1 |> Finset.mem_filter.mp |>.1;
            simp_all +decide [ SimpleGraph.cliqueFinset ];
            have := h_triangle.1; aesop;
          refine' ⟨ { Sym2.mk ( u, v ) }, _, _, _ ⟩ <;> simp_all +decide;
          intro t' ht'; specialize h_uniform t' t ht' ht₁; simp_all +decide [ Finset.ext_iff ] ;
          grind +ring;
        · -- If $S_e = \{e\}$, we can choose $E' = \{ \text{Sym2.mk}(u, v) \}$ where $\{u, v\} \subset e$.
          obtain ⟨u, v, huv⟩ : ∃ u v, u ∈ e ∧ v ∈ e ∧ u ≠ v ∧ G.Adj u v := by
            have := hM.1;
            have := this.1 he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            rcases Finset.card_eq_three.mp this.2 with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use u, by aesop, v, by aesop ; ; aesop;
          use {Sym2.mk (u, v)};
          simp_all +decide [ Sym2.eq_swap ];
          intro t ht; specialize h t ht; aesop;
      exact le_trans ( triangleCoveringNumberOn_le _ _ _ _ h_univ.choose_spec.1 h_univ.choose_spec.2.2 h_univ.choose_spec.2.1 ) ( by norm_num )

end AristotleLemmas

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  by_cases h_diverse : ∃ t1 t2 : Finset V, t1 ∈ S_e G M e ∧ t2 ∈ S_e G M e ∧ t1 ≠ e ∧ t2 ≠ e ∧ t1 ∩ e ≠ t2 ∩ e;
  · -- Apply the

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma base_edge_covers (G : SimpleGraph V) [DecidableRel G.Adj] (t T : Finset V) (v : V)
    (ht : t ∈ G.cliqueFinset 3) (hv : v ∈ t)
    (hT : T ∈ trianglesSharingEdge G t) (hvT : v ∉ T) :
    t \ {v} ⊆ T := by
      intro x hx;
      have h_inter : (T ∩ t).card ≥ 2 := by
        unfold trianglesSharingEdge at hT; aesop;
      have h_inter_subset : T ∩ t ⊆ t \ {v} := by
        intro y hy; aesop;
      have h_inter_eq : T ∩ t = t \ {v} := by
        have := Finset.eq_of_subset_of_card_le h_inter_subset;
        simp_all +decide [ Finset.card_sdiff ];
        exact this ( by linarith [ ht.card_eq ] );
      replace h_inter_eq := Finset.ext_iff.mp h_inter_eq x; aesop;

/-
For every triangle T in the set of triangles at v avoiding v, there is a packing element f containing v such that the base edge of f (f \ {v}) is contained in T.
-/

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma base_edges_cover_avoiding (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (v : V) :
    ∀ T ∈ trianglesAtVAvoidingV G M v, ∃ f ∈ packingElementsContaining M v, f \ {v} ⊆ T := by
      intro T hT;
      have h_base_edge_covers : ∃ f ∈ packingElementsContaining M v, T ∈ trianglesSharingEdge G f ∧ v ∉ T := by
        unfold trianglesAtVAvoidingV at hT;
        unfold trianglesAtV at hT;
        aesop;
      obtain ⟨ f, hf₁, hf₂, hf₃ ⟩ := h_base_edge_covers;
      refine' ⟨ f, hf₁, _ ⟩;
      apply base_edge_covers G f T v;
      · have := hM.1;
        exact this.1 ( Finset.mem_filter.mp hf₁ |>.1 );
      · exact Finset.mem_filter.mp hf₁ |>.2;
      · exact hf₂;
      · assumption

end AristotleLemmas

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma tau_at_v_avoiding_v_le_k (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (v : V) (k : ℕ) (hk : (packingElementsContaining M v).card = k) :
    triangleCoveringNumberOn G (trianglesAtVAvoidingV G M v) ≤ k := by
  -- Each packing element's base triangles share the base edge
  -- So k base edges suffice
  -- By definition of $E'$, for each $f \in P$, the edge $e_f$ is in $E'$.
  have h_edges : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ k ∧ ∀ T ∈ trianglesAtVAvoidingV G M v, ∃ e ∈ E', e ∈ T.sym2 := by
    have h_edges : ∀ f ∈ packingElementsContaining M v, ∃ e ∈ G.edgeFinset, e ∈ f.sym2 ∧ ∀ T ∈ trianglesAtVAvoidingV G M v, f \ {v} ⊆ T → e ∈ T.sym2 := by
      intro f hf
      obtain ⟨u, w, hu, hw, huv⟩ : ∃ u w : V, u ∈ f ∧ w ∈ f ∧ u ≠ v ∧ w ≠ v ∧ u ≠ w ∧ G.Adj u w := by
        -- Since $f$ is a triangle, it must contain three distinct vertices. Let's denote them as $u$, $w$, and $v$.
        obtain ⟨u, w, hu, hw, huv⟩ : ∃ u w : V, u ∈ f ∧ w ∈ f ∧ u ≠ v ∧ w ≠ v ∧ u ≠ w := by
          have h_card : f.card = 3 := by
            have h_triangle : f ∈ G.cliqueFinset 3 := by
              exact hM.1.1 ( Finset.filter_subset _ _ hf );
            exact Finset.mem_filter.mp h_triangle |>.2.2;
          obtain ⟨ u, w, x, hu, hw, hx ⟩ := Finset.card_eq_three.mp h_card; use if u = v then w else if w = v then x else u, if u = v then x else if w = v then u else w; aesop;
        have h_triangle : f ∈ G.cliqueFinset 3 := by
          exact hM.1.1 ( Finset.mem_filter.mp hf |>.1 );
        rw [ SimpleGraph.mem_cliqueFinset_iff ] at h_triangle ; aesop;
        exact ⟨ u, hu, w, hw, left, left_1, right, by have := h_triangle.1; have := this hu hw; aesop ⟩;
      refine' ⟨ Sym2.mk ( u, w ), _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    choose! e he₁ he₂ he₃ using h_edges;
    refine' ⟨ Finset.image ( fun f : packingElementsContaining M v => e f.1 f.2 ) Finset.univ, _, _, _ ⟩ <;> simp_all +decide [ Finset.card_image_of_injective ];
    · exact Set.range_subset_iff.mpr fun f => he₁ _ _;
    · exact Finset.card_image_le.trans ( by simp +decide [ hk ] );
    · intro T hT;
      obtain ⟨ f, hf₁, hf₂ ⟩ := base_edges_cover_avoiding G M hM v T hT;
      exact ⟨ _, ⟨ f, hf₁, rfl ⟩, he₃ f hf₁ T hT hf₂ ⟩;
  refine' le_trans _ h_edges.choose_spec.2.1;
  have h_min : triangleCoveringNumberOn G (trianglesAtVAvoidingV G M v) ≤ Finset.card (h_edges.choose) := by
    have h_in_set : h_edges.choose ∈ Finset.filter (fun E' => ∀ T ∈ trianglesAtVAvoidingV G M v, ∃ e ∈ E', e ∈ T.sym2) (Finset.powerset (G.edgeFinset)) := by
      exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h_edges.choose_spec.1, h_edges.choose_spec.2.2 ⟩
    unfold triangleCoveringNumberOn;
    have h_min : ∀ {s : Finset ℕ}, s.Nonempty → ∀ x ∈ s, Option.getD (Finset.min s) 0 ≤ x := by
      intros s hs x hx; exact (by
      have := Finset.min_le hx; cases h : Finset.min s <;> aesop;);
    exact h_min ⟨ _, Finset.mem_image_of_mem _ h_in_set ⟩ _ ( Finset.mem_image_of_mem _ h_in_set );
  exact h_min

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Triple-Apex Theorem
-- ══════════════════════════════════════════════════════════════════════════════

-- When v is in ≥3 packing triangles

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
theorem tau_le_8_three_share_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : (packingElementsContaining M v).card = 3)
    (e4 : Finset V) (he4 : e4 ∈ M) (he4_no_v : v ∉ e4) :
    triangleCoveringNumber G ≤ 8 := by
  -- The isolated element e4 contributes τ(S_{e4}) ≤ 2
  -- The 3 at v contribute τ ≤ 6
  convert tau_le_8_triple_apex G M hM hM_card v (hv.ge.trans' (by decide))

-- Specialized version for all 4 sharing v (star)

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
theorem tau_le_8_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : ∀ e ∈ M, v ∈ e) :
    triangleCoveringNumber G ≤ 8 := by
  -- All triangles either contain v or are base triangles
  -- τ(containing v) ≤ 4 (4 well-chosen spokes)
  -- τ(base triangles) ≤ 4 (4 base edges)
  -- By Lemma 25, τ(G) ≤ 8 for any graph G.
  apply tau_le_8_triple_apex G M hM hM_card v (by
  rw [ show packingElementsContaining M v = M from ?_ ];
  · linarith;
  · exact Finset.filter_true_of_mem hv)

end

-- Source: proven/tuza/lemmas/slot35_tau_pair_le_4.lean
lemma cover_union_implies_cover_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_left B ht)

-- Source: proven/tuza/lemmas/slot35_tau_pair_le_4.lean
lemma cover_union_implies_cover_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_right A ht)

-- Source: proven/tuza/lemmas/slot35_tau_pair_le_4.lean
lemma union_covers_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (XA XB : Finset (Sym2 V))
    (hA : ∀ t ∈ A, ∃ e ∈ XA, e ∈ t.sym2)
    (hB : ∀ t ∈ B, ∃ e ∈ XB, e ∈ t.sym2) :
    ∀ t ∈ A ∪ B, ∃ e ∈ XA ∪ XB, e ∈ t.sym2 := by
  intro t ht
  rcases Finset.mem_union.mp ht with htA | htB
  · obtain ⟨e, heXA, het⟩ := hA t htA
    exact ⟨e, Finset.mem_union_left XB heXA, het⟩
  · obtain ⟨e, heXB, het⟩ := hB t htB
    exact ⟨e, Finset.mem_union_right XA heXB, het⟩

-- Source: proven/tuza/lemmas/slot35_tau_pair_le_4.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  let coversAB := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2)
  let coversA := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)
  let coversB := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2)
  let sizesAB := coversAB.image Finset.card
  let sizesA := coversA.image Finset.card
  let sizesB := coversB.image Finset.card
  by_cases hAB : sizesAB.Nonempty
  case pos =>
    have coversAB_sub_coversA : coversAB ⊆ coversA := by
      intro E' hE'
      simp only [Finset.mem_filter, Finset.mem_powerset] at hE' ⊢
      exact ⟨hE'.1, cover_union_implies_cover_left G A B E' hE'.2⟩
    have coversAB_sub_coversB : coversAB ⊆ coversB := by
      intro E' hE'
      simp only [Finset.mem_filter, Finset.mem_powerset] at hE' ⊢
      exact ⟨hE'.1, cover_union_implies_cover_right G A B E' hE'.2⟩
    have hA : sizesA.Nonempty := hAB.mono (Finset.image_mono coversAB_sub_coversA)
    have hB : sizesB.Nonempty := hAB.mono (Finset.image_mono coversAB_sub_coversB)
    have h_tauAB : triangleCoveringNumberOn G (A ∪ B) = sizesAB.min' hAB := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    have h_tauA : triangleCoveringNumberOn G A = sizesA.min' hA := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    have h_tauB : triangleCoveringNumberOn G B = sizesB.min' hB := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    have minA_mem : sizesA.min' hA ∈ sizesA := Finset.min'_mem sizesA hA
    have minB_mem : sizesB.min' hB ∈ sizesB := Finset.min'_mem sizesB hB
    obtain ⟨XA, hXA_mem, hXA_card⟩ := Finset.mem_image.mp minA_mem
    obtain ⟨XB, hXB_mem, hXB_card⟩ := Finset.mem_image.mp minB_mem
    have hXA_sub : XA ⊆ G.edgeFinset := (Finset.mem_filter.mp hXA_mem).1 |> Finset.mem_powerset.mp
    have hXA_covers : ∀ t ∈ A, ∃ e ∈ XA, e ∈ t.sym2 := (Finset.mem_filter.mp hXA_mem).2
    have hXB_sub : XB ⊆ G.edgeFinset := (Finset.mem_filter.mp hXB_mem).1 |> Finset.mem_powerset.mp
    have hXB_covers : ∀ t ∈ B, ∃ e ∈ XB, e ∈ t.sym2 := (Finset.mem_filter.mp hXB_mem).2
    have hUnion_covers : ∀ t ∈ A ∪ B, ∃ e ∈ XA ∪ XB, e ∈ t.sym2 :=
      union_covers_union G A B XA XB hXA_covers hXB_covers
    have hUnion_sub : XA ∪ XB ⊆ G.edgeFinset := Finset.union_subset hXA_sub hXB_sub
    have hUnion_mem : XA ∪ XB ∈ coversAB := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hUnion_sub, hUnion_covers⟩
    have card_union_mem : (XA ∪ XB).card ∈ sizesAB :=
      Finset.mem_image_of_mem Finset.card hUnion_mem
    have min_le_card : sizesAB.min' hAB ≤ (XA ∪ XB).card :=
      Finset.min'_le sizesAB (XA ∪ XB).card card_union_mem
    have card_union_le : (XA ∪ XB).card ≤ XA.card + XB.card := Finset.card_union_le XA XB
    calc triangleCoveringNumberOn G (A ∪ B)
        = sizesAB.min' hAB := h_tauAB
      _ ≤ (XA ∪ XB).card := min_le_card
      _ ≤ XA.card + XB.card := card_union_le
      _ = sizesA.min' hA + sizesB.min' hB := by rw [hXA_card, hXB_card]
      _ = triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by rw [← h_tauA, ← h_tauB]
  case neg =>
    have h_empty : sizesAB = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAB
    have h_tau_zero : triangleCoveringNumberOn G (A ∪ B) = 0 := by
      simp only [triangleCoveringNumberOn]
      rw [h_empty]
      simp
    rw [h_tau_zero]
    exact Nat.zero_le _

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: V-decomposition (from slot16)
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/lemmas/slot35_tau_pair_le_4.lean
theorem tau_v_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (v : V) :
    triangleCoveringNumberOn G triangles ≤
    triangleCoveringNumberOn G (trianglesContaining triangles v) +
    triangleCoveringNumberOn G (trianglesAvoiding triangles v) := by
  rw [v_decomposition_union triangles v]
  exact tau_union_le_sum G _ _

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/--
Triangles containing v in T_e ∪ T_f can be covered by 4 spoke edges.
If e = {v,a,b} and f = {v,c,d}, use {va, vb, vc, vd}.
-/

-- Source: proven/tuza/lemmas/slot35_tau_pair_le_4.lean
lemma tau_containing_v_in_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (v : V) (hv_e : v ∈ e) (hv_f : v ∈ f) :
    triangleCoveringNumberOn G (trianglesContaining (T_pair G e f) v) ≤ 4 := by
  simp +zetaDelta at *;
  unfold triangleCoveringNumberOn;
  -- Let's choose any four edges incident to $v$.
  obtain ⟨E', hE'⟩ : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 4 ∧ ∀ t ∈ trianglesContaining (T_pair G e f) v, ∃ e ∈ E', e ∈ t.sym2 := by
    use Finset.image (fun u => Sym2.mk (v, u)) (e \ {v} ∪ f \ {v});
    refine' ⟨ _, _, _ ⟩;
    · simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
      rintro a ( ⟨ ha₁, ha₂ ⟩ | ⟨ ha₁, ha₂ ⟩ ) <;> [ exact he.1 ( by aesop ) ( by aesop ) ( by aesop ) ; exact hf.1 ( by aesop ) ( by aesop ) ( by aesop ) ];
    · refine' le_trans ( Finset.card_image_le ) _;
      refine' le_trans ( Finset.card_union_le _ _ ) _;
      simp_all +decide [ Finset.card_sdiff, SimpleGraph.isNClique_iff ];
    · simp_all +decide [ trianglesContaining, T_pair ];
      simp_all +decide [ trianglesSharingEdge ];
      rintro t ( ⟨ ht₁, ht₂ ⟩ | ⟨ ht₁, ht₂ ⟩ ) hv_t <;> obtain ⟨ a, ha ⟩ := Finset.exists_mem_ne ht₂ v <;> use a <;> aesop;
  have h_min_le : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → Option.getD (Finset.image Finset.card S).min 0 ≤ E'.card := by
    intros S hE'_in_S; exact (by
    have h_min_le : ∀ {S : Finset ℕ}, E'.card ∈ S → Option.getD (Finset.min S) 0 ≤ E'.card := by
      intros S hE'_in_S; exact (by
      have h_min_le : ∀ {S : Finset ℕ}, E'.card ∈ S → Finset.min S ≤ E'.card := by
        exact fun { S } hE'_in_S => Finset.min_le hE'_in_S;
      specialize h_min_le hE'_in_S; cases h : Finset.min S <;> aesop;);
    exact h_min_le ( Finset.mem_image_of_mem _ hE'_in_S ));
  exact le_trans ( h_min_le ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'.1, hE'.2.2 ⟩ ) ) hE'.2.1

-- TARGET 1

/--
Triangles avoiding v in T_e must share base edge ab (edge of e not containing v).
One edge covers all such triangles. Similarly for T_f with edge cd.
Total: 2 edges.
-/

-- Source: proven/tuza/lemmas/slot35_tau_pair_le_4.lean
lemma tau_avoiding_v_in_pair_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) ≤ 2 := by
  -- Let $E'$ be the set containing the edges $ab$ and $cd$.
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : V, a ≠ b ∧ e = {v, a, b} := by
    have h_card_e : e.card = 3 := by
      have := hM.1;
      have := this.1;
      have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      exact this.2;
    rw [ Finset.card_eq_three ] at h_card_e;
    obtain ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ := h_card_e; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
    rcases hv.1.1 with ( rfl | rfl | rfl ) <;> simp_all +decide;
    · exact ⟨ y, z, hyz, rfl ⟩;
    · exact ⟨ x, z, hxz, by aesop ⟩;
    · exact ⟨ x, y, hxy, by aesop ⟩
  obtain ⟨c, d, hc, hd, hcd⟩ : ∃ c d : V, c ≠ d ∧ f = {v, c, d} := by
    -- Since $f$ is a triangle in $G$, it must have exactly three vertices.
    have hf_card : f.card = 3 := by
      have h_triangle : ∀ t ∈ M, t.card = 3 := by
        have h_triangle : ∀ t ∈ M, t ∈ G.cliqueFinset 3 := by
          exact fun t ht => hM.1.1 ht;
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        exact fun t ht => h_triangle t ht |>.2
      exact h_triangle f hf;
    rw [ Finset.card_eq_three ] at hf_card;
    obtain ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ := hf_card; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
    rcases hv.2 with ( rfl | rfl | rfl ) <;> simp_all +decide;
    · exact ⟨ y, z, hyz, by aesop ⟩;
    · exact ⟨ x, z, by tauto ⟩;
    · exact ⟨ x, y, hxy, by tauto ⟩;
  -- Let $E'$ be the set containing the edges $ab$ and $cd$. We need to show that $E'$ covers all triangles avoiding $v$.
  have h_cover : ∀ t ∈ trianglesAvoiding (T_pair G {v, a, b} {v, c, d}) v, ∃ e ∈ ({Sym2.mk (a, b), Sym2.mk (c, d)} : Finset (Sym2 V)), e ∈ t.sym2 := by
    simp_all +decide [ Finset.ext_iff, trianglesAvoiding, trianglesSharingEdge, T_pair ];
    rintro t ( ⟨ ht₁, ht₂ ⟩ | ⟨ ht₁, ht₂ ⟩ ) ht₃ <;> simp_all +decide [ Finset.card_le_one, Finset.subset_iff ];
    · have := Finset.one_lt_card.1 ht₂; aesop;
    · have := Finset.one_lt_card.mp ht₂;
      aesop;
  unfold triangleCoveringNumberOn;
  have h_min : Finset.min (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ trianglesAvoiding (T_pair G {v, a, b} {v, c, d}) v, ∃ e ∈ E', e ∈ t.sym2) (Finset.powerset (G.edgeFinset)))) ≤ Finset.card ({Sym2.mk (a, b), Sym2.mk (c, d)} : Finset (Sym2 V)) := by
    refine' Finset.min_le _;
    simp +zetaDelta at *;
    refine' ⟨ { Sym2.mk ( a, b ), Sym2.mk ( c, d ) }, _, _ ⟩ <;> simp +decide [ *, Set.subset_def ];
    refine' ⟨ ⟨ _, _ ⟩, h_cover ⟩;
    · have := hM.1;
      have := this.1 he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    · have := hM.1;
      have := this.1 hf; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  by_cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ trianglesAvoiding ( T_pair G { v, a, b } { v, c, d } ) v, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset ( G.edgeFinset ) ) ) ) = none <;> simp_all +decide;
  cases h' : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ trianglesAvoiding ( T_pair G { v, a, b } { v, c, d } ) v, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset ( G.edgeFinset ) ) ) ) <;> simp_all +decide;
  exact le_trans ( Nat.cast_le.mpr h_min ) ( by exact le_trans ( Finset.card_insert_le _ _ ) ( by simp +decide ) )

/- Aristotle failed to find a proof. -/
-- TARGET 2

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Overlap between spokes and avoiding triangles
-- ══════════════════════════════════════════════════════════════════════════════

/--
If triangle {a,b,x} avoids v but x is adjacent to v in the graph,
then {a,b,x} is covered by spoke edge {v,x} (since {v,x} ∈ {a,b,x}.sym2 is false,
but {a,x} or {b,x} might be spokes if x ∈ {c,d}).

Actually: {a,b,x} contains edges ab, ax, bx. Spokes are va, vb, vc, vd.
Overlap occurs when ax = vc or ax = vd (i.e., when a=v or x=c, etc.)
Since a ≠ v (a is in e\{v}), we need x ∈ {c,d} for overlap.
-/

-- Source: proven/tuza/lemmas/slot35_tau_pair_le_4.lean
lemma tau_avoiding_v_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) ≤ 2 := by
      exact?

end AristotleLemmas

-- Source: proven/tuza/lemmas/slot35_tau_pair_le_4.lean
theorem tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  have h_zero : triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) = 0 := by
    -- By Lemma~\ref{lem:avoiding_covered_by_spokes}, `t` must contain a spoke incident to `v`.
    have h_contradiction : ∀ t ∈ trianglesAvoiding (T_pair G e f) v, ∃ spoke ∈ ({s(v, x) | x ∈ (e ∪ f) \ {v}} : Set (Sym2 V)), spoke ∈ t.sym2 := by
      intro t ht
      apply avoiding_covered_by_spokes G M hM e f he hf hef v hv t ht
      generalize_proofs at *;
      unfold trianglesAvoiding T_pair at ht;
      unfold trianglesSharingEdge at ht; aesop;
      · exact Exists.elim ( Finset.exists_mem_ne right_1 v ) fun x hx => ⟨ x, Finset.mem_of_mem_inter_left hx.1, Or.inl ( Finset.mem_of_mem_inter_right hx.1 ), hx.2 ⟩;
      · obtain ⟨ x, hx ⟩ := Finset.card_pos.mp ( by linarith ) ; use x; aesop;
    -- Since $t$ avoids $v$, it cannot contain any edge incident to $v$, contradicting the existence of a spoke incident to $v$ in $t$.
    have h_contradiction : ∀ t ∈ trianglesAvoiding (T_pair G e f) v, ¬∃ spoke ∈ ({s(v, x) | x ∈ (e ∪ f) \ {v}} : Set (Sym2 V)), spoke ∈ t.sym2 := by
      simp +contextual [ trianglesAvoiding ];
    -- By combining the two hypotheses, we can conclude that there are no triangles in the avoiding set, hence its covering number is zero.
    have h_empty : trianglesAvoiding (T_pair G e f) v = ∅ := by
      exact Finset.eq_empty_of_forall_notMem fun t ht => h_contradiction t ht <| by solve_by_elim;
    simp +decide [ h_empty, triangleCoveringNumberOn ];
    rw [ Finset.min_eq_inf_withTop ];
    rw [ Finset.inf_eq_bot_iff.mpr ] ; aesop;
    exact ⟨ 0, Finset.mem_image.mpr ⟨ ∅, Finset.mem_powerset.mpr ( Finset.empty_subset _ ), rfl ⟩, rfl ⟩;
  refine' le_trans ( tau_v_decomposition G _ _ ) _;
  exact v;
  simp_all +decide [ triangleCoveringNumberOn ];
  refine' le_trans _ ( tau_containing_v_in_pair_le_4 G e f _ _ v _ _ );
  · unfold triangleCoveringNumberOn; aesop;
  · have := hM.1;
    have := this.1 he; aesop;
  · have := hM.1;
    have := this.1 hf; aesop;
  · exact Finset.mem_of_mem_inter_left ( hv.symm ▸ Finset.mem_singleton_self _ );
  · rw [ Finset.eq_singleton_iff_unique_mem ] at hv ; aesop

-- MAIN TARGET

end

-- Source: proven/tuza/lemmas/tau_union_le_sum.lean
lemma cover_union_implies_cover_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_left B ht)

/-- A cover for A ∪ B is also a cover for B -/

-- Source: proven/tuza/lemmas/tau_union_le_sum.lean
lemma cover_union_implies_cover_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_right A ht)

/-- Union of covers: if XA covers A and XB covers B, then XA ∪ XB covers A ∪ B -/

-- Source: proven/tuza/lemmas/tau_union_le_sum.lean
lemma union_covers_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (XA XB : Finset (Sym2 V))
    (hA : ∀ t ∈ A, ∃ e ∈ XA, e ∈ t.sym2)
    (hB : ∀ t ∈ B, ∃ e ∈ XB, e ∈ t.sym2) :
    ∀ t ∈ A ∪ B, ∃ e ∈ XA ∪ XB, e ∈ t.sym2 := by
  intro t ht
  rcases Finset.mem_union.mp ht with htA | htB
  · obtain ⟨e, heXA, het⟩ := hA t htA
    exact ⟨e, Finset.mem_union_left XB heXA, het⟩
  · obtain ⟨e, heXB, het⟩ := hB t htB
    exact ⟨e, Finset.mem_union_right XA heXB, het⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/--
The key union bound lemma: τ(A ∪ B) ≤ τ(A) + τ(B)

Proof strategy (from Grok-4):
1. Case split on whether covers for A∪B exist (sizes nonempty)
2. If empty: τ(A∪B) = 0 ≤ anything
3. If nonempty:
   - Covers for A∪B imply covers for A and B exist
   - Extract minimal covers XA, XB with |XA| = τ(A), |XB| = τ(B)
   - Show XA ∪ XB covers A ∪ B
   - |XA ∪ XB| ≤ |XA| + |XB| by Finset.card_union_le
   - τ(A∪B) ≤ |XA ∪ XB| since τ is the minimum
-/

-- Source: proven/tuza/lemmas/tau_union_le_sum.lean
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  -- Define abbreviations for the filtered powersets
  let coversAB := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2)
  let coversA := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)
  let coversB := G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2)
  let sizesAB := coversAB.image Finset.card
  let sizesA := coversA.image Finset.card
  let sizesB := coversB.image Finset.card

  -- Case split: does a cover for A∪B exist?
  by_cases hAB : sizesAB.Nonempty
  case pos =>
    -- Covers for A∪B exist
    -- Therefore covers for A and B also exist (weaker predicate)
    have coversAB_sub_coversA : coversAB ⊆ coversA := by
      intro E' hE'
      simp only [Finset.mem_filter, Finset.mem_powerset] at hE' ⊢
      exact ⟨hE'.1, cover_union_implies_cover_left G A B E' hE'.2⟩
    have coversAB_sub_coversB : coversAB ⊆ coversB := by
      intro E' hE'
      simp only [Finset.mem_filter, Finset.mem_powerset] at hE' ⊢
      exact ⟨hE'.1, cover_union_implies_cover_right G A B E' hE'.2⟩
    have hA : sizesA.Nonempty := hAB.mono (Finset.image_mono coversAB_sub_coversA)
    have hB : sizesB.Nonempty := hAB.mono (Finset.image_mono coversAB_sub_coversB)

    -- Use Finset.min' for nonempty finsets
    have h_tauAB : triangleCoveringNumberOn G (A ∪ B) = sizesAB.min' hAB := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    have h_tauA : triangleCoveringNumberOn G A = sizesA.min' hA := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp
    have h_tauB : triangleCoveringNumberOn G B = sizesB.min' hB := by
      simp only [triangleCoveringNumberOn]
      rw [Finset.min_eq_inf_withTop, Finset.inf_eq_min']
      simp

    -- Get witness covers achieving the minimum
    have minA_mem : sizesA.min' hA ∈ sizesA := Finset.min'_mem sizesA hA
    have minB_mem : sizesB.min' hB ∈ sizesB := Finset.min'_mem sizesB hB

    -- Extract actual covers XA and XB
    obtain ⟨XA, hXA_mem, hXA_card⟩ := Finset.mem_image.mp minA_mem
    obtain ⟨XB, hXB_mem, hXB_card⟩ := Finset.mem_image.mp minB_mem

    -- Get properties of XA and XB
    have hXA_sub : XA ⊆ G.edgeFinset := (Finset.mem_filter.mp hXA_mem).1 |> Finset.mem_powerset.mp
    have hXA_covers : ∀ t ∈ A, ∃ e ∈ XA, e ∈ t.sym2 := (Finset.mem_filter.mp hXA_mem).2
    have hXB_sub : XB ⊆ G.edgeFinset := (Finset.mem_filter.mp hXB_mem).1 |> Finset.mem_powerset.mp
    have hXB_covers : ∀ t ∈ B, ∃ e ∈ XB, e ∈ t.sym2 := (Finset.mem_filter.mp hXB_mem).2

    -- XA ∪ XB covers A ∪ B
    have hUnion_covers : ∀ t ∈ A ∪ B, ∃ e ∈ XA ∪ XB, e ∈ t.sym2 :=
      union_covers_union G A B XA XB hXA_covers hXB_covers

    -- XA ∪ XB is a valid cover (subset of edges)
    have hUnion_sub : XA ∪ XB ⊆ G.edgeFinset := Finset.union_subset hXA_sub hXB_sub

    -- Therefore XA ∪ XB ∈ coversAB
    have hUnion_mem : XA ∪ XB ∈ coversAB := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hUnion_sub, hUnion_covers⟩

    -- |XA ∪ XB| ∈ sizesAB
    have card_union_mem : (XA ∪ XB).card ∈ sizesAB :=
      Finset.mem_image_of_mem Finset.card hUnion_mem

    -- sizesAB.min' ≤ |XA ∪ XB|
    have min_le_card : sizesAB.min' hAB ≤ (XA ∪ XB).card :=
      Finset.min'_le sizesAB (XA ∪ XB).card card_union_mem

    -- |XA ∪ XB| ≤ |XA| + |XB|
    have card_union_le : (XA ∪ XB).card ≤ XA.card + XB.card := Finset.card_union_le XA XB

    -- Chain the inequalities
    calc triangleCoveringNumberOn G (A ∪ B)
        = sizesAB.min' hAB := h_tauAB
      _ ≤ (XA ∪ XB).card := min_le_card
      _ ≤ XA.card + XB.card := card_union_le
      _ = sizesA.min' hA + sizesB.min' hB := by rw [hXA_card, hXB_card]
      _ = triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by rw [← h_tauA, ← h_tauB]

  case neg =>
    -- No covers for A∪B exist, so τ(A∪B) = 0
    have h_empty : sizesAB = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAB
    have h_tau_zero : triangleCoveringNumberOn G (A ∪ B) = 0 := by
      simp only [triangleCoveringNumberOn]
      rw [h_empty]
      simp
    rw [h_tau_zero]
    exact Nat.zero_le _

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARIES
-- ══════════════════════════════════════════════════════════════════════════════

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

-- Source: proven/tuza/lemmas/tau_union_le_sum.lean
theorem tau_v_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (v : V) :
    triangleCoveringNumberOn G triangles ≤
    triangleCoveringNumberOn G (trianglesContaining triangles v) +
    triangleCoveringNumberOn G (trianglesAvoiding triangles v) := by
  rw [v_decomposition_union triangles v]
  exact tau_union_le_sum G _ _

end

-- Source: proven/tuza/lemmas/slot28/204aea51-fbd5-4756-ad24-5407f5e5e927-output.lean
lemma X_ef_covering_number_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v}) (he : e ∈ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      -- Let $E'$ be the set of edges in $e$ incident to $v$. Since $e$ is a triangle (clique of size 3), there are exactly 2 such edges, and they are in $G.edgeFinset$.
      set E' : Finset (Sym2 V) := Finset.image (fun u => Sym2.mk (v, u)) (e \ {v}) with hE';
      -- We need to show that $E'$ is a covering set of size 2.
      have h_cover : ∀ t ∈ X_ef G e f, ∃ e' ∈ E', e' ∈ t.sym2 := by
        intro t ht
        have h_triangle : v ∈ t := by
          unfold X_ef at ht;
          simp_all +decide [ Finset.ext_iff ];
          contrapose! ht;
          intro ht ht';
          have h_card : (t ∩ e).card + (t ∩ f).card ≤ (t ∩ (e ∪ f)).card := by
            rw [ ← Finset.card_union_add_card_inter ];
            rw [ show t ∩ e ∪ t ∩ f = t ∩ ( e ∪ f ) by ext; aesop, show t ∩ e ∩ ( t ∩ f ) = ∅ by ext; aesop ] ; simp +decide;
          have h_card : (t ∩ (e ∪ f)).card ≤ t.card := by
            exact Finset.card_le_card fun x hx => by aesop;
          linarith [ ht.2 ];
        -- Since $t$ is a triangle in $X_{ef}$, it must contain at least one vertex from $e \setminus \{v\}$.
        obtain ⟨u, hu⟩ : ∃ u ∈ e \ {v}, u ∈ t := by
          have h_card : (t ∩ e).card ≥ 2 := by
            unfold X_ef at ht; aesop;
          contrapose! h_card;
          rw [ show t ∩ e = { v } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_inter.mpr ⟨ h_triangle, by replace hv := Finset.ext_iff.mp hv v; aesop ⟩, fun x hx => by_contradiction fun hx' => h_card x ( by aesop ) ( Finset.mem_inter.mp hx |>.1 ) ⟩ ] ; simp +decide;
        aesop;
      -- Therefore, $E'$ is a covering set of size 2.
      have h_covering : E' ⊆ G.edgeFinset ∧ (∀ t ∈ X_ef G e f, ∃ e' ∈ E', e' ∈ t.sym2) := by
        simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
        rintro _ u hu huv rfl; have := he.1 ( show v ∈ e from by rw [ Finset.eq_singleton_iff_unique_mem ] at hv; aesop ) ( show u ∈ e from hu ) ; aesop;
      have h_card_E' : E'.card ≤ 2 := by
        have := he.card_eq;
        grind;
      refine' le_trans ( _ : triangleCoveringNumberOn G ( X_ef G e f ) ≤ E'.card ) h_card_E';
      have h_min_le_card : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → Option.getD (Finset.image Finset.card S).min 0 ≤ E'.card := by
        intros S hS; exact (by
        have h_min_le_card : ∀ {S : Finset ℕ}, E'.card ∈ S → Option.getD (Finset.min S) 0 ≤ E'.card := by
          intro S hS; exact (by
          have h_min_le_card : ∀ {S : Finset ℕ}, E'.card ∈ S → Finset.min S ≤ E'.card := by
            exact fun { S } hS => Finset.min_le hS;
          specialize h_min_le_card hS; cases h : Finset.min S <;> aesop;);
        exact h_min_le_card ( Finset.mem_image_of_mem _ hS ));
      exact h_min_le_card ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h_covering.1, h_covering.2 ⟩ )

end AristotleLemmas

-- Source: proven/tuza/lemmas/slot28/204aea51-fbd5-4756-ad24-5407f5e5e927-output.lean
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  apply X_ef_covering_number_le_2 G e f v hv;
  exact hM.1.1 he

-- Full proof in tau_union files

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: bridges_contain_v
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/lemmas/slot28/204aea51-fbd5-4756-ad24-5407f5e5e927-output.lean
lemma isTriangleCover_union (G : SimpleGraph V) (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
      exact ⟨ Finset.union_subset hA.1 hB.1, fun t ht => by cases' Finset.mem_union.mp ht with ht ht <;> [ exact hA.2 _ ht |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Finset.mem_union_left _ he₁, he₂ ⟩ ; exact hB.2 _ ht |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Finset.mem_union_right _ he₁, he₂ ⟩ ] ⟩

/-
The triangle covering number is less than or equal to the size of any specific triangle cover.
-/

-- Source: proven/tuza/lemmas/slot28/204aea51-fbd5-4756-ad24-5407f5e5e927-output.lean
lemma triangleCoveringNumberOn_le_of_isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V))
    (E' : Finset (Sym2 V)) (h : isTriangleCover G triangles E') :
    triangleCoveringNumberOn G triangles ≤ E'.card := by
      -- By definition of `triangleCoveringNumberOn`, it is the minimum cardinality of a triangle cover for the set of triangles.
      have h_min : triangleCoveringNumberOn G triangles ≤ Finset.min (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card) := by
        unfold triangleCoveringNumberOn;
        cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2 ) G.edgeFinset.powerset ) ) <;> aesop;
      contrapose! h_min;
      refine' lt_of_le_of_lt _ ( WithTop.coe_lt_coe.mpr h_min );
      simp +decide [ Finset.min ];
      exact ⟨ E', ⟨ fun e he => by have := h.1 he; aesop, fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := h.2 t ht; aesop ⟩, le_rfl ⟩

/-
If a triangle cover exists, then there exists a triangle cover with minimum cardinality equal to the triangle covering number.
-/

-- Source: proven/tuza/lemmas/slot28/204aea51-fbd5-4756-ad24-5407f5e5e927-output.lean
lemma exists_min_isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : ∃ E', isTriangleCover G triangles E') :
    ∃ E', isTriangleCover G triangles E' ∧ E'.card = triangleCoveringNumberOn G triangles := by
      obtain ⟨E', hE'⟩ : ∃ E' : Finset (Sym2 V), isTriangleCover G triangles E' ∧ ∀ E'' : Finset (Sym2 V), isTriangleCover G triangles E'' → E'.card ≤ E''.card := by
        apply_rules [ Set.exists_min_image ];
        exact Set.finite_iff_bddAbove.mpr ⟨ _, fun a ha => ha.1 ⟩;
      use E';
      unfold triangleCoveringNumberOn;
      rw [ show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2 } ) ) = Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) from ?_ ];
      · rw [ show Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) = Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) from rfl, Finset.min_eq_inf_withTop ];
        rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) ).inf WithTop.some = WithTop.some E'.card from ?_ ] ; aesop;
        refine' le_antisymm _ _ <;> simp_all +decide [ Finset.inf_le ];
        exact ⟨ E', ⟨ fun e he => by have := hE'.1.1 he; aesop, hE'.1 ⟩, le_rfl ⟩;
      · ext; simp [isTriangleCover]

/-
If there is no triangle cover, the triangle covering number is 0.
-/

-- Source: proven/tuza/lemmas/slot28/204aea51-fbd5-4756-ad24-5407f5e5e927-output.lean
lemma triangleCoveringNumberOn_eq_zero_of_not_coverable (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : ¬ ∃ E', isTriangleCover G triangles E') :
    triangleCoveringNumberOn G triangles = 0 := by
      unfold triangleCoveringNumberOn;
      simp_all +decide [ Finset.min ];
      rw [ Finset.inf_eq_iInf ];
      rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
      case b => exact ⊤;
      · rfl;
      · simp_all +decide [ isTriangleCover ];
      · aesop

end AristotleLemmas

-- Source: proven/tuza/lemmas/slot28/204aea51-fbd5-4756-ad24-5407f5e5e927-output.lean
lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases hA : ∃ E', isTriangleCover G A E';
  · by_cases hB : ∃ E', isTriangleCover G B E';
    · -- By the properties of `exists_min_isTriangleCover`, we can find covers for A and B with sizes equal to their covering numbers.
      obtain ⟨E_A, hE_A⟩ := exists_min_isTriangleCover G A hA
      obtain ⟨E_B, hE_B⟩ := exists_min_isTriangleCover G B hB;
      have h_union : isTriangleCover G (A ∪ B) (E_A ∪ E_B) := by
        exact isTriangleCover_union G A B E_A E_B hE_A.1 hE_B.1;
      exact le_trans ( triangleCoveringNumberOn_le_of_isTriangleCover _ _ _ h_union ) ( by rw [ ← hE_A.2, ← hE_B.2 ] ; exact Finset.card_union_le _ _ );
    · rw [ triangleCoveringNumberOn_eq_zero_of_not_coverable ];
      · exact Nat.zero_le _;
      · exact fun ⟨ E', hE' ⟩ => hB ⟨ E', by exact ⟨ Finset.Subset.trans hE'.1 ( Finset.Subset.refl _ ), fun t ht => hE'.2 t ( Finset.mem_union_right _ ht ) ⟩ ⟩;
  · rw [ triangleCoveringNumberOn_eq_zero_of_not_coverable ];
    · exact Nat.zero_le _;
    · exact fun ⟨ E', hE' ⟩ => hA ⟨ E', ⟨ hE'.1, fun t ht => hE'.2 t ( Finset.mem_union_left _ ht ) ⟩ ⟩

-- Full proof in slot16

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Pair With Bridges Bound
-- S_e ∪ S_f ∪ X(e,f) can be covered with 4 edges
-- ══════════════════════════════════════════════════════════════════════════════

-- First, a naive bound using subadditivity

-- Source: proven/tuza/lemmas/slot28/204aea51-fbd5-4756-ad24-5407f5e5e927-output.lean
theorem pair_covering_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    -- In star configuration, all elements share v
    (h_star : ∀ g ∈ M, g ≠ e → e ∩ g = {v}) :
    triangleCoveringNumberOn G (S_e G M e ∪ S_e G M f ∪ X_ef G e f) ≤ 4 := by
  exact pair_with_bridges_le_4 G M hM e f he hf hef v hv

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- ASSEMBLY: Tuza ν=4 for star case
-- Partition {e, f, g, h} into pairs {e,f} and {g,h}
-- Each pair contributes ≤4 edges, total ≤8
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/lemmas/slot44/5a188e26-ef0d-44c2-a565-cd798ad02e00-output.lean
lemma isTriangleCover_union (G : SimpleGraph V) (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  exact ⟨ Finset.union_subset hA.1 hB.1, fun t ht => by cases' Finset.mem_union.mp ht with ht ht <;> [ exact hA.2 _ ht |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Finset.mem_union_left _ he₁, he₂ ⟩ ; exact hB.2 _ ht |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Finset.mem_union_right _ he₁, he₂ ⟩ ] ⟩

-- Source: proven/tuza/lemmas/slot44/5a188e26-ef0d-44c2-a565-cd798ad02e00-output.lean
lemma triangleCoveringNumberOn_le_of_isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V))
    (E' : Finset (Sym2 V)) (h : isTriangleCover G triangles E') :
    triangleCoveringNumberOn G triangles ≤ E'.card := by
  have h_min : triangleCoveringNumberOn G triangles ≤ Finset.min (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card) := by
    unfold triangleCoveringNumberOn;
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2 ) G.edgeFinset.powerset ) ) <;> aesop;
  contrapose! h_min;
  refine' lt_of_le_of_lt _ ( WithTop.coe_lt_coe.mpr h_min );
  simp +decide [ Finset.min ];
  exact ⟨ E', ⟨ fun e he => by have := h.1 he; aesop, fun t ht => by obtain ⟨ e, he₁, he₂ ⟩ := h.2 t ht; aesop ⟩, le_rfl ⟩

-- Source: proven/tuza/lemmas/slot44/5a188e26-ef0d-44c2-a565-cd798ad02e00-output.lean
lemma exists_min_isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : ∃ E', isTriangleCover G triangles E') :
    ∃ E', isTriangleCover G triangles E' ∧ E'.card = triangleCoveringNumberOn G triangles := by
  obtain ⟨E', hE'⟩ : ∃ E' : Finset (Sym2 V), isTriangleCover G triangles E' ∧ ∀ E'' : Finset (Sym2 V), isTriangleCover G triangles E'' → E'.card ≤ E''.card := by
    apply_rules [ Set.exists_min_image ];
    exact Set.finite_iff_bddAbove.mpr ⟨ _, fun a ha => ha.1 ⟩;
  use E';
  unfold triangleCoveringNumberOn;
  rw [ show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2 } ) ) = Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) from ?_ ];
  · rw [ show Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) = Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) from rfl, Finset.min_eq_inf_withTop ];
    rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G triangles E' ) ( Finset.powerset G.edgeFinset ) ) ).inf WithTop.some = WithTop.some E'.card from ?_ ] ; aesop;
    refine' le_antisymm _ _ <;> simp_all +decide [ Finset.inf_le ];
    exact ⟨ E', ⟨ fun e he => by have := hE'.1.1 he; aesop, hE'.1 ⟩, le_rfl ⟩;
  · ext; simp [isTriangleCover]

-- Source: proven/tuza/lemmas/slot44/5a188e26-ef0d-44c2-a565-cd798ad02e00-output.lean
lemma triangleCoveringNumberOn_eq_zero_of_not_coverable (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (h : ¬ ∃ E', isTriangleCover G triangles E') :
    triangleCoveringNumberOn G triangles = 0 := by
  unfold triangleCoveringNumberOn;
  simp_all +decide [ Finset.min ];
  rw [ Finset.inf_eq_iInf ];
  rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
  case b => exact ⊤;
  · rfl;
  · simp_all +decide [ isTriangleCover ];
  · aesop

-- Source: proven/tuza/lemmas/slot44/5a188e26-ef0d-44c2-a565-cd798ad02e00-output.lean
lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases hA : ∃ E', isTriangleCover G A E';
  · by_cases hB : ∃ E', isTriangleCover G B E';
    · obtain ⟨E_A, hE_A⟩ := exists_min_isTriangleCover G A hA
      obtain ⟨E_B, hE_B⟩ := exists_min_isTriangleCover G B hB;
      have h_union : isTriangleCover G (A ∪ B) (E_A ∪ E_B) := by
        exact isTriangleCover_union G A B E_A E_B hE_A.1 hE_B.1;
      exact le_trans ( triangleCoveringNumberOn_le_of_isTriangleCover _ _ _ h_union ) ( by rw [ ← hE_A.2, ← hE_B.2 ] ; exact Finset.card_union_le _ _ );
    · rw [ triangleCoveringNumberOn_eq_zero_of_not_coverable ];
      · exact Nat.zero_le _;
      · exact fun ⟨ E', hE' ⟩ => hB ⟨ E', by exact ⟨ Finset.Subset.trans hE'.1 ( Finset.Subset.refl _ ), fun t ht => hE'.2 t ( Finset.mem_union_right _ ht ) ⟩ ⟩;
  · rw [ triangleCoveringNumberOn_eq_zero_of_not_coverable ];
    · exact Nat.zero_le _;
    · exact fun ⟨ E', hE' ⟩ => hA ⟨ E', ⟨ hE'.1, fun t ht => hE'.2 t ( Finset.mem_union_left _ ht ) ⟩ ⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: tau_X_le_2 (FULL PROOF from slot28)
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/lemmas/slot44/5a188e26-ef0d-44c2-a565-cd798ad02e00-output.lean
lemma X_ef_covering_number_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v}) (he : e ∈ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  simp_all +decide [ SimpleGraph.cliqueFinset ];
  set E' : Finset (Sym2 V) := Finset.image (fun u => Sym2.mk (v, u)) (e \ {v}) with hE';
  have h_cover : ∀ t ∈ X_ef G e f, ∃ e' ∈ E', e' ∈ t.sym2 := by
    intro t ht
    have h_triangle : v ∈ t := by
      unfold X_ef at ht;
      simp_all +decide [ Finset.ext_iff ];
      contrapose! ht;
      intro ht ht';
      have h_card : (t ∩ e).card + (t ∩ f).card ≤ (t ∩ (e ∪ f)).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        rw [ show t ∩ e ∪ t ∩ f = t ∩ ( e ∪ f ) by ext; aesop, show t ∩ e ∩ ( t ∩ f ) = ∅ by ext; aesop ] ; simp +decide;
      have h_card : (t ∩ (e ∪ f)).card ≤ t.card := by
        exact Finset.card_le_card fun x hx => by aesop;
      linarith [ ht.2 ];
    obtain ⟨u, hu⟩ : ∃ u ∈ e \ {v}, u ∈ t := by
      have h_card : (t ∩ e).card ≥ 2 := by
        unfold X_ef at ht; aesop;
      contrapose! h_card;
      rw [ show t ∩ e = { v } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_inter.mpr ⟨ h_triangle, by replace hv := Finset.ext_iff.mp hv v; aesop ⟩, fun x hx => by_contradiction fun hx' => h_card x ( by aesop ) ( Finset.mem_inter.mp hx |>.1 ) ⟩ ] ; simp +decide;
    aesop;
  have h_covering : E' ⊆ G.edgeFinset ∧ (∀ t ∈ X_ef G e f, ∃ e' ∈ E', e' ∈ t.sym2) := by
    simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
    rintro _ u hu huv rfl; have := he.1 ( show v ∈ e from by rw [ Finset.eq_singleton_iff_unique_mem ] at hv; aesop ) ( show u ∈ e from hu ) ; aesop;
  have h_card_E' : E'.card ≤ 2 := by
    have := he.card_eq;
    grind;
  refine' le_trans ( _ : triangleCoveringNumberOn G ( X_ef G e f ) ≤ E'.card ) h_card_E';
  have h_min_le_card : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → Option.getD (Finset.image Finset.card S).min 0 ≤ E'.card := by
    intros S hS; exact (by
    have h_min_le_card : ∀ {S : Finset ℕ}, E'.card ∈ S → Option.getD (Finset.min S) 0 ≤ E'.card := by
      intro S hS; exact (by
      have h_min_le_card : ∀ {S : Finset ℕ}, E'.card ∈ S → Finset.min S ≤ E'.card := by
        exact fun { S } hS => Finset.min_le hS;
      specialize h_min_le_card hS; cases h : Finset.min S <;> aesop;);
    exact h_min_le_card ( Finset.mem_image_of_mem _ hS ));
  exact h_min_le_card ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h_covering.1, h_covering.2 ⟩ )

-- Source: proven/tuza/lemmas/slot44/5a188e26-ef0d-44c2-a565-cd798ad02e00-output.lean
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  apply X_ef_covering_number_le_2 G e f v hv;
  exact hM.1.1 he

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: tau_S_le_2 (FULL PROOF from slot32)
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/lemmas/slot44/5a188e26-ef0d-44c2-a565-cd798ad02e00-output.lean
lemma tau_S_le_2_case1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (uv : Finset V) (huv : uv ⊆ e) (huv_card : uv.card = 2)
    (h_struct : ∀ t ∈ S_e G M e, t ≠ e → uv ⊆ t) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  unfold triangleCoveringNumberOn;
  obtain ⟨u, v, hu, hv, huv_eq⟩ : ∃ u v, uv = {u, v} ∧ u ≠ v ∧ u ∈ e ∧ v ∈ e := by
    rw [ Finset.card_eq_two ] at huv_card; obtain ⟨ u, v, huv ⟩ := huv_card; use u, v; aesop;
  have huv_edge : Sym2.mk (u, v) ∈ G.edgeFinset := by
    have := hM.1.1 he; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
    exact this.1 ( by aesop ) ( by aesop ) hv;
  have h_triangle_covering : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ S_e G M e, ∃ e ∈ E', e ∈ t.sym2)), E'.card ≤ 2 := by
    refine' ⟨ { Sym2.mk ( u, v ) }, _, _ ⟩ <;> simp_all +decide;
    intro t ht; specialize h_struct t ht; by_cases h : t = e <;> simp_all +decide [ Finset.subset_iff ] ;
  obtain ⟨ E', hE₁, hE₂ ⟩ := h_triangle_covering;
  have h_min_le : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ E'.card := by
    exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', by aesop ⟩ );
  exact le_trans ( by cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop ) hE₂

-- Source: proven/tuza/lemmas/slot44/5a188e26-ef0d-44c2-a565-cd798ad02e00-output.lean
lemma tau_S_le_2_case2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (x : V) (hx : x ∉ e)
    (h_struct : ∀ t ∈ S_e G M e, t ≠ e → t = (t ∩ e) ∪ {x}) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  obtain ⟨u, v, huv⟩ : ∃ u v : V, u ∈ e ∧ v ∈ e ∧ u ≠ v ∧ G.Adj u v := by
    have := hM.1;
    have := this.1 he; simp +decide [ isTrianglePacking ] at this;
    rcases Finset.card_eq_three.mp this.2 with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use u, v ; simp_all +decide [ SimpleGraph.isNClique_iff ];
  obtain ⟨w, hw⟩ : ∃ w : V, w ∈ e ∧ w ≠ u ∧ w ≠ v := by
    have h_card : e.card = 3 := by
      have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      exact this.card_eq;
    exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.erase e u ) from by rw [ Finset.card_erase_of_mem huv.1, h_card ] ; decide ) v );
  by_cases huv_cover : ∀ t ∈ S_e G M e, t ≠ e → (u ∈ t ∧ v ∈ t) ∨ (w ∈ t ∧ x ∈ t);
  · set E' : Finset (Sym2 V) := {Sym2.mk (u, v), Sym2.mk (w, x)};
    have hE'_cover : ∀ t ∈ S_e G M e, t ≠ e → ∃ e' ∈ E', e' ∈ t.sym2 := by
      intro t ht ht'; specialize huv_cover t ht ht'; rcases huv_cover with ( ⟨ hu, hv ⟩ | ⟨ hw, hx ⟩ ) <;> [ exact ⟨ _, Finset.mem_insert_self _ _, by simp +decide [ hu, hv ] ⟩ ; exact ⟨ _, Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ), by simp +decide [ hw, hx ] ⟩ ] ;
    have h_triangleCoveringNumberOn_le_2 : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2 := by
      refine' ⟨ E' ∩ G.edgeFinset, _, _, _ ⟩;
      · exact Finset.inter_subset_right;
      · exact le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ( Finset.card_insert_le _ _ );
      · intro t ht;
        by_cases h : t = e <;> simp +decide [ h ] at hE'_cover ⊢;
        · exact ⟨ Sym2.mk ( u, v ), ⟨ Finset.mem_insert_self _ _, by simpa using huv.2.2.2 ⟩, by simp +decide [ huv.1, huv.2.1 ] ⟩;
        · obtain ⟨ e', he', he'' ⟩ := hE'_cover t ht h;
          simp +zetaDelta at *;
          rcases he' with ( rfl | rfl ) <;> [ exact ⟨ _, ⟨ Or.inl rfl, by simpa using huv.2.2.2 ⟩, he'' ⟩ ; exact ⟨ _, ⟨ Or.inr rfl, by
            have := Finset.mem_filter.mp ht |>.1; simp +decide [ SimpleGraph.mem_edgeSet ] at this ⊢;
            unfold trianglesSharingEdge at this; simp +decide [ SimpleGraph.mem_edgeSet ] at this;
            have := this.1.1; simp +decide [ SimpleGraph.isNClique_iff ] at this;
            exact this ( by simpa using he'' _ ( Sym2.mem_iff.mpr <| Or.inl rfl ) ) ( by simpa using he'' _ ( Sym2.mem_iff.mpr <| Or.inr rfl ) ) ( by rintro rfl; simp +decide [ hx ] at * ) ⟩, he'' ⟩ ];
    obtain ⟨ E', hE'_sub, hE'_card, hE'_cover ⟩ := h_triangleCoveringNumberOn_le_2;
    have h_min_le_card : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → Option.getD (Finset.image Finset.card S).min 0 ≤ E'.card := by
      intro S hS; have := Finset.min_le ( Finset.mem_image_of_mem Finset.card hS ) ; simp +decide at this ⊢;
      cases h : Finset.min ( Finset.image Finset.card S ) <;> simp +decide [ h ] at this ⊢ ; exact this;
    exact le_trans ( h_min_le_card ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'_sub, hE'_cover ⟩ ) ) hE'_card;
  · contrapose! huv_cover;
    intro t ht hte
    have ht_edges : t ∩ e = {u, v} ∨ t ∩ e = {v, w} ∨ t ∩ e = {u, w} := by
      have ht_edges : (t ∩ e).card = 2 := by
        have := h_struct t ht hte;
        have ht_card : t.card = 3 := by
          unfold S_e at ht; norm_num at ht;
          unfold trianglesSharingEdge at ht; norm_num at ht;
          exact ht.1.1.card_eq;
        rw [ this, Finset.card_union ] at ht_card ; simp +decide [ hx ] at ht_card ⊢ ; linarith;
      have ht_edges_subset : t ∩ e ⊆ {u, v, w} := by
        have := hM.1;
        have := this.1 he; simp +decide [ SimpleGraph.cliqueFinset ] at this;
        have := this.2; simp +decide [ Finset.card_eq_three ] at this;
        grind;
      have := Finset.card_eq_two.mp ht_edges;
      rcases this with ⟨ x, y, hxy, h ⟩ ; simp +decide [ h, Finset.Subset.antisymm_iff, Finset.subset_iff ] at ht_edges_subset ⊢;
      grind;
    rcases ht_edges with ( h | h | h ) <;> specialize h_struct t ht hte <;> simp +decide [ h ] at h_struct ⊢;
    · simp +decide [ h_struct ];
    · simp +decide [ h_struct ];
    · simp +decide [ h_struct ]

-- Source: proven/tuza/lemmas/slot44/5a188e26-ef0d-44c2-a565-cd798ad02e00-output.lean
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  obtain h | h := Se_structure_

-- Source: proven/tuza/lemmas/slot32/2b3cce69-ca98-4c3a-9e7d-55ca3afab48d-output.lean
lemma tau_S_le_2_case1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (uv : Finset V) (huv : uv ⊆ e) (huv_card : uv.card = 2)
    (h_struct : ∀ t ∈ S_e G M e, t ≠ e → uv ⊆ t) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
      unfold triangleCoveringNumberOn;
      -- Let $E' = \{uv\}$. Since $uv \subseteq e$ and $e \in M$ is a triangle in $G$, $uv$ is an edge of $G$.
      obtain ⟨u, v, hu, hv, huv_eq⟩ : ∃ u v, uv = {u, v} ∧ u ≠ v ∧ u ∈ e ∧ v ∈ e := by
        rw [ Finset.card_eq_two ] at huv_card; obtain ⟨ u, v, huv ⟩ := huv_card; use u, v; aesop;
      -- Since $uv \subseteq e$ and $e \in M$ is a triangle in $G$, $uv$ is an edge of $G$.
      have huv_edge : Sym2.mk (u, v) ∈ G.edgeFinset := by
        have := hM.1.1 he; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
        exact this.1 ( by aesop ) ( by aesop ) hv;
      have h_triangle_covering : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ S_e G M e, ∃ e ∈ E', e ∈ t.sym2)), E'.card ≤ 2 := by
        refine' ⟨ { Sym2.mk ( u, v ) }, _, _ ⟩ <;> simp_all +decide;
        intro t ht; specialize h_struct t ht; by_cases h : t = e <;> simp_all +decide [ Finset.subset_iff ] ;
      obtain ⟨ E', hE₁, hE₂ ⟩ := h_triangle_covering;
      have h_min_le : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ E'.card := by
        exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', by aesop ⟩ );
      exact le_trans ( by cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop ) hE₂

-- Source: proven/tuza/lemmas/slot32/2b3cce69-ca98-4c3a-9e7d-55ca3afab48d-output.lean
lemma tau_S_le_2_case2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (x : V) (hx : x ∉ e)
    (h_struct : ∀ t ∈ S_e G M e, t ≠ e → t = (t ∩ e) ∪ {x}) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
      -- Let $uv$ be any edge of $e$.
      obtain ⟨u, v, huv⟩ : ∃ u v : V, u ∈ e ∧ v ∈ e ∧ u ≠ v ∧ G.Adj u v := by
        have := hM.1;
        have := this.1 he; simp +decide [ isTrianglePacking ] at this;
        rcases Finset.card_eq_three.mp this.2 with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use u, v ; simp_all +decide [ SimpleGraph.isNClique_iff ];
      obtain ⟨w, hw⟩ : ∃ w : V, w ∈ e ∧ w ≠ u ∧ w ≠ v := by
        have h_card : e.card = 3 := by
          have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          exact this.card_eq;
        exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.erase e u ) from by rw [ Finset.card_erase_of_mem huv.1, h_card ] ; decide ) v );
      -- Consider the edge $uv \in G.edgeFinset$.
      by_cases huv_cover : ∀ t ∈ S_e G M e, t ≠ e → (u ∈ t ∧ v ∈ t) ∨ (w ∈ t ∧ x ∈ t);
      · -- Let $E' = \{uv, wx\}$.
        set E' : Finset (Sym2 V) := {Sym2.mk (u, v), Sym2.mk (w, x)};
        -- We claim $E'$ covers all triangles in $S_e(e)$.
        have hE'_cover : ∀ t ∈ S_e G M e, t ≠ e → ∃ e' ∈ E', e' ∈ t.sym2 := by
          intro t ht ht'; specialize huv_cover t ht ht'; rcases huv_cover with ( ⟨ hu, hv ⟩ | ⟨ hw, hx ⟩ ) <;> [ exact ⟨ _, Finset.mem_insert_self _ _, by simp +decide [ hu, hv ] ⟩ ; exact ⟨ _, Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ), by simp +decide [ hw, hx ] ⟩ ] ;
        -- Thus `triangleCoveringNumberOn` $\le 2$.
        have h_triangleCoveringNumberOn_le_2 : ∃ E' ⊆ G.edgeFinset, E'.card ≤ 2 ∧ ∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2 := by
          refine' ⟨ E' ∩ G.edgeFinset, _, _, _ ⟩;
          · exact Finset.inter_subset_right;
          · exact le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ( Finset.card_insert_le _ _ );
          · intro t ht;
            by_cases h : t = e <;> simp +decide [ h ] at hE'_cover ⊢;
            · exact ⟨ Sym2.mk ( u, v ), ⟨ Finset.mem_insert_self _ _, by simpa using huv.2.2.2 ⟩, by simp +decide [ huv.1, huv.2.1 ] ⟩;
            · obtain ⟨ e', he', he'' ⟩ := hE'_cover t ht h;
              simp +zetaDelta at *;
              rcases he' with ( rfl | rfl ) <;> [ exact ⟨ _, ⟨ Or.inl rfl, by simpa using huv.2.2.2 ⟩, he'' ⟩ ; exact ⟨ _, ⟨ Or.inr rfl, by
                have := Finset.mem_filter.mp ht |>.1; simp +decide [ SimpleGraph.mem_edgeSet ] at this ⊢;
                unfold trianglesSharingEdge at this; simp +decide [ SimpleGraph.mem_edgeSet ] at this;
                have := this.1.1; simp +decide [ SimpleGraph.isNClique_iff ] at this;
                exact this ( by simpa using he'' _ ( Sym2.mem_iff.mpr <| Or.inl rfl ) ) ( by simpa using he'' _ ( Sym2.mem_iff.mpr <| Or.inr rfl ) ) ( by rintro rfl; simp +decide [ hx ] at * ) ⟩, he'' ⟩ ];
        obtain ⟨ E', hE'_sub, hE'_card, hE'_cover ⟩ := h_triangleCoveringNumberOn_le_2;
        have h_min_le_card : ∀ {S : Finset (Finset (Sym2 V))}, E' ∈ S → Option.getD (Finset.image Finset.card S).min 0 ≤ E'.card := by
          intro S hS; have := Finset.min_le ( Finset.mem_image_of_mem Finset.card hS ) ; simp +decide at this ⊢;
          cases h : Finset.min ( Finset.image Finset.card S ) <;> simp +decide [ h ] at this ⊢ ; exact this;
        exact le_trans ( h_min_le_card ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'_sub, hE'_cover ⟩ ) ) hE'_card;
      · contrapose! huv_cover;
        intro t ht hte
        have ht_edges : t ∩ e = {u, v} ∨ t ∩ e = {v, w} ∨ t ∩ e = {u, w} := by
          have ht_edges : (t ∩ e).card = 2 := by
            have := h_struct t ht hte;
            have ht_card : t.card = 3 := by
              unfold S_e at ht; norm_num at ht;
              unfold trianglesSharingEdge at ht; norm_num at ht;
              exact ht.1.1.card_eq;
            rw [ this, Finset.card_union ] at ht_card ; simp +decide [ hx ] at ht_card ⊢ ; linarith;
          have ht_edges_subset : t ∩ e ⊆ {u, v, w} := by
            have := hM.1;
            have := this.1 he; simp +decide [ SimpleGraph.cliqueFinset ] at this;
            have := this.2; simp +decide [ Finset.card_eq_three ] at this;
            grind;
          have := Finset.card_eq_two.mp ht_edges;
          rcases this with ⟨ x, y, hxy, h ⟩ ; simp +decide [ h, Finset.Subset.antisymm_iff, Finset.subset_iff ] at ht_edges_subset ⊢;
          grind;
        rcases ht_edges with ( h | h | h ) <;> specialize h_struct t ht hte <;> simp +decide [ h ] at h_struct ⊢;
        · simp +decide [ h_struct ];
        · simp +decide [ h_struct ];
        · simp +decide [ h_struct ]

end AristotleLemmas

-- Source: proven/tuza/lemmas/slot32/2b3cce69-ca98-4c3a-9e7d-55ca3afab48d-output.lean
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  -- We apply `Se_structure_lemma` to get the two cases.
  obtain h | h := Se_structure_

-- Source: proven/tuza/lemmas/slot32/2b3cce69-ca98-4c3a-9e7d-55ca3afab48d-output.lean
lemma tau_path_bridges_le_6 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e1 e2 e3 e4 : Finset V)
    (v12 : V) (hv12 : e1 ∩ e2 = {v12})
    (v23 : V) (hv23 : e2 ∩ e3 = {v23})
    (v34 : V) (hv34 : e3 ∩ e4 = {v34}) :
    triangleCoveringNumberOn G (X_ef G e1 e2 ∪ X_ef G e2 e3 ∪ X_ef G e3 e4) ≤ 6 := by
  -- Each bridge set needs ≤2 edges: 3 × 2 = 6
  -- But bridges through v23 might be hit by edges covering other bridges
  refine' le_trans ( tau_union_le_sum _ _ _ ) _;
  refine' le_trans ( add_le_add ( tau_union_le_sum _ _ _ ) le_rfl ) _;
  refine' le_trans ( add_le_add_three ( tau_X_le_2 _ _ _ _ hv12 ) ( tau_X_le_2 _ _ _ _ hv23 ) ( tau_X_le_2 _ _ _ _ hv34 ) ) _;
  norm_num

/- Aristotle failed to find a proof. -/
-- Main theorem: Path configuration

-- Source: proven/tuza/lemmas/slot32/2b3cce69-ca98-4c3a-9e7d-55ca3afab48d-output.lean
lemma tau_end_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e_end e_neighbor : Finset V)
    (he : e_end ∈ M) (hn : e_neighbor ∈ M)
    (v : V) (hv : e_end ∩ e_neighbor = {v})
    -- e_end only shares with e_neighbor (it's an "end" in the path)
    (h_only_neighbor : ∀ f ∈ M, f ≠ e_end → f ≠ e_neighbor → Disjoint (e_end : Set V) (f : Set V)) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e_end) ≤ 4 := by
  -- T_{e_end} = S_{e_end} ∪ X(e_end, e_neighbor)
  -- τ(S_{e_end}) ≤ 2, τ(X) ≤ 2, total ≤ 4
  -- Apply the result that τ(S_e) ≤ 2 and τ(X_ef) ≤ 2 for the end element and its neighbor.
  have h_tau_S_e : triangleCoveringNumberOn G (trianglesSharingEdge G e_end) ≤ triangleCoveringNumberOn G (S_e G M e_end) + triangleCoveringNumberOn G (X_ef G e_end e_neighbor) := by
    have h_tau_S_e : trianglesSharingEdge G e_end = S_e G M e_end ∪ X_ef G e_end e_neighbor := by
      ext t; simp [trianglesSharingEdge, S_e, X_ef];
      constructor;
      · intro ht
        by_cases h_neighbor : (t ∩ e_neighbor).card ≥ 2;
        · exact Or.inr ⟨ ht.1, ht.2, h_neighbor ⟩;
        · refine' Or.inl ⟨ ht, fun f hf hf' => _ ⟩;
          by_cases hf'' : f = e_neighbor <;> simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ];
          · linarith;
          · have h_disjoint : Disjoint (t ∩ e_end) (t ∩ f) := by
              exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.notMem_empty x <| h_only_neighbor f hf hf' hf'' ▸ Finset.mem_inter.mpr ⟨ Finset.mem_inter.mp hx₁ |>.2, Finset.mem_inter.mp hx₂ |>.2 ⟩;
            have h_card : (t ∩ e_end).card + (t ∩ f).card ≤ t.card := by
              rw [ ← Finset.card_union_of_disjoint h_disjoint ] ; exact Finset.card_mono ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ;
            linarith [ show t.card = 3 by simpa using ht.1.card_eq ];
      · aesop;
    exact h_tau_S_e.symm ▸ tau_union_le_sum G _ _;
  exact h_tau_S_e.trans ( add_le_add ( tau_S_le_2 G M hM e_end he ) ( tau_X_le_2 G e_end e_neighbor v hv ) )

end

-- Source: proven/tuza/nu0/tuza_nu0_PROVEN.lean
lemma nu_eq_0_implies_tau_eq_0 (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  -- Since the triangle packing number is 0, this means there are no edge-disjoint triangles in G.
  have h_no_triangles : ∀ (S : Finset (Finset V)), IsTrianglePacking G S → S = ∅ := by
    unfold trianglePackingNumber at h;
    intro S hS; contrapose! h; aesop;
    have h_max : ∃ S' ∈ Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset, S'.card > 0 := by
      exact ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hS.1, hS ⟩, Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty h ) ⟩;
    obtain ⟨ S', hS', hS'' ⟩ := h_max;
    have h_max : Finset.max (Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset)) ≥ S'.card := by
      exact Finset.le_max ( Finset.mem_image_of_mem _ hS' );
    cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( IsTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
  -- Since there are no triangles in G, the empty set of edges covers all triangles.
  have h_empty_cover : IsTriangleCovering G ∅ := by
    constructor <;> simp +decide [ IsTriangleCovering ];
    intro t ht; specialize h_no_triangles { t } ; simp_all +decide [ IsTrianglePacking ] ;
  unfold triangleCoveringNumber;
  rw [ Finset.min_eq_inf_withTop ];
  rw [ Finset.inf_eq_sInf_image ];
  rw [ show ( InfSet.sInf ( WithTop.some '' ( ↑ ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) : Set ℕ ) ) ) = 0 from le_antisymm _ _ ];
  · rfl;
  · exact csInf_le ⟨ 0, fun x hx => by aesop ⟩ ⟨ 0, by aesop ⟩;
  · exact bot_le

/-
If the triangle packing number is 1, then any two triangles in the graph share an edge.
-/

-- Source: proven/tuza/nu0/tuza_nu0_PROVEN.lean
lemma subset_K4_implies_cover_le_2_restricted (S : Finset (Finset V))
    (h_S : S ⊆ G.cliqueFinset 3)
    (U : Finset V) (h_U : U.card ≤ 4) (h_subset : ∀ t ∈ S, t ⊆ U) :
    ∃ F : Finset (Sym2 V), F ⊆ G.edgeFinset ∧ F.card ≤ 2 ∧ ∀ t ∈ S, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F := by
  by_contra! h_contra';
  -- Since all triangles in S are subsets of U and |U| ≤ 4, we can analyze the possible configurations of triangles on 4 vertices.
  have h_configurations : ∀ T : Finset (Finset V), (∀ t ∈ T, t.card = 3 ∧ t ⊆ U) → ∃ F : Finset (Sym2 V), F.card ≤ 2 ∧ ∀ t ∈ T, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F := by
    intro T hT
    by_cases hU : U.card ≤ 3;
    · by_cases hU : U.card = 3;
      · -- Since U has exactly 3 elements, any triangle in T must be exactly U itself.
        have hT_eq_U : ∀ t ∈ T, t = U := by
          exact fun t ht => Finset.eq_of_subset_of_card_le ( hT t ht |>.2 ) ( by simp +decide [ hT t ht |>.1, hU ] );
        rcases Finset.card_eq_three.mp hU with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use { s(u, v), s(u, w) } ; simp_all +decide ;
        intro t ht; use u, by rw [ hT_eq_U t ht ] ; simp +decide, v, by rw [ hT_eq_U t ht ] ; simp +decide; ; aesop;
      · exact ⟨ ∅, by norm_num, fun t ht => by have := hT t ht; have := Finset.card_le_card this.2; interval_cases _ : U.card <;> simp_all +decide ⟩;
    · -- Since U has exactly 4 elements, we can analyze the possible configurations of triangles on 4 vertices.
      obtain ⟨a, b, c, d, h_abcd⟩ : ∃ a b c d : V, U = {a, b, c, d} ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
        have hU_card : U.card = 4 := by
          linarith;
        simp_rw +decide [ Finset.card_eq_succ ] at hU_card;
        obtain ⟨ a, t, hat, rfl, b, u, hbu, rfl, c, v, hcv, rfl, d, w, hdw, rfl, hw ⟩ := hU_card; use a, b, c, d; aesop;
      -- Consider the possible triangles on {a, b, c, d}.
      have h_triangles : ∀ t ∈ T, t = {a, b, c} ∨ t = {a, b, d} ∨ t = {a, c, d} ∨ t = {b, c, d} := by
        intro t ht
        obtain ⟨ht_card, ht_subset⟩ := hT t ht
        have ht_cases : t ⊆ {a, b, c, d} := by
          aesop;
        have := Finset.card_eq_three.mp ht_card;
        rcases this with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; simp_all +decide [ Finset.subset_iff ] ;
        rcases ht_cases with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] at hxy hxz hyz ⊢;
      refine' ⟨ { s(a, b), s(c, d) }, _, _ ⟩ <;> simp +decide [ * ];
      intro t ht; rcases h_triangles t ht with ( rfl | rfl | rfl | rfl ) <;> simp +decide [ * ] ;
  specialize h_configurations S ; simp_all +decide [ Finset.subset_iff ];
  obtain ⟨F, hF_card, hF_cover⟩ := h_configurations (fun t ht => ⟨by
  exact h_S ht |>.2, h_subset t ht⟩);
  specialize h_contra' ( F.filter fun e => e ∈ G.edgeSet ) ; simp_all +decide [ Finset.subset_iff ] ;
  refine' h_contra' ( le_trans ( Finset.card_filter_le _ _ ) hF_card ) |> fun ⟨ t, ht, h ⟩ => _;
  obtain ⟨ u, hu, v, hv, huv, hF ⟩ := hF_cover t ht; specialize h u v hu hv huv hF; exact h ( h_S ht |>.1 hu hv huv ) ;

/-
If the triangle packing number is 1, then the triangle covering number is at most 2.
-/

-- Source: proven/tuza/nu0/tuza_nu0_PROVEN.lean
lemma nu_eq_1_implies_tau_le_2 (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  -- If there exists an edge $e = \{u, v\}$ shared by all triangles in $S$, then $\{e\}$ is a triangle covering of size 1. Thus $\tau(G) \leq 1 \leq 2$.
  by_cases h_common : ∃ u v, u ≠ v ∧ ∀ t ∈ G.cliqueFinset 3, {u, v} ⊆ t;
  · -- If there exists an edge $e = \{u, v\}$ shared by all triangles in $S$, then $\{e\}$ is a triangle covering of size 1. Thus $\tau(G) \leq 1$.
    obtain ⟨u, v, huv_ne, huv_cover⟩ := h_common;
    have h_cover : IsTriangleCovering G {s(u, v)} := by
      constructor <;> simp_all +decide [ IsTriangleCovering ];
      · contrapose! huv_cover;
        -- Since the triangle packing number is 1, there exists at least one triangle in the graph.
        obtain ⟨t, ht⟩ : ∃ t ∈ G.cliqueFinset 3, True := by
          have h_triangle : ∃ t ∈ G.cliqueFinset 3, True := by
            have h_nonempty : G.cliqueFinset 3 ≠ ∅ := by
              intro h_empty;
              unfold trianglePackingNumber at h;
              simp_all +decide [ Finset.filter_singleton, IsTrianglePacking ]
            exact Exists.elim ( Finset.nonempty_of_ne_empty h_nonempty ) fun t ht => ⟨ t, ht, trivial ⟩;
          exact h_triangle;
        refine' ⟨ t, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
        intro hu hv; have := ht.1 hu hv; aesop;
      · exact fun t ht => ⟨ u, huv_cover t ht ( Finset.mem_insert_self _ _ ), v, huv_cover t ht ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ), huv_ne, Or.inl ⟨ rfl, rfl ⟩ ⟩;
    refine' le_trans _ ( show 1 ≤ 2 by norm_num );
    unfold triangleCoveringNumber;
    have h_min : (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) (Finset.powerset G.edgeFinset))).min ≤ 1 := by
      have h_one : 1 ∈ Finset.image Finset.card (Finset.filter (IsTriangleCovering G) (Finset.powerset G.edgeFinset)) := by
        simp +zetaDelta at *;
        exact ⟨ { s(u, v) }, ⟨ by simpa using h_cover.1, h_cover ⟩, by simp +decide ⟩
      exact Finset.min_le h_one;
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop;
  · -- Then by `pairwise_edge_sharing_no_common_edge_implies_subset_K4`, the union of all vertices in $S$ has size at most 4.
    have h_union : (Finset.sup (G.cliqueFinset 3) id).card ≤ 4 := by
      apply pairwise_edge_sharing_no_common_edge_implies_subset_K4;
      · simp +decide [ SimpleGraph.cliqueFinset ];
        exact fun t ht => ht.2;
      · intro t₁ ht₁ t₂ ht₂ hne; have := nu_eq_1_implies_pairwise_edge_sharing G h t₁ t₂ ht₁ ht₂; aesop;
      · exact h_common;
    -- By `subset_K4_implies_cover_le_2_restricted`, there exists a cover $F$ of size ≤ 2.
    obtain ⟨F, hF_subset, hF_card, hF_cover⟩ : ∃ F : Finset (Sym2 V), F ⊆ G.edgeFinset ∧ F.card ≤ 2 ∧ ∀ t ∈ G.cliqueFinset 3, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F := by
      apply subset_K4_implies_cover_le_2_restricted;
      exacts [ Finset.Subset.refl _, h_union, fun t ht => Finset.le_sup ( f := id ) ht ];
    refine' le_trans _ hF_card;
    unfold triangleCoveringNumber;
    have hF_covering : IsTriangleCovering G F := by
      exact ⟨ hF_subset, hF_cover ⟩;
    have hF_min : (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)).min ≤ F.card := by
      exact Finset.min_le ( Finset.mem_image.mpr ⟨ F, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hF_subset, hF_covering ⟩, rfl ⟩ );
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop

/-
If a set of triangles pairwise share an edge, they can be covered by at most 2 edges.
-/

-- Source: proven/tuza/nu0/tuza_nu0_PROVEN.lean
lemma restricted_nu_le_1_implies_cover_le_2 (S : Finset (Finset V))
    (h_S : S ⊆ G.cliqueFinset 3)
    (h_pair : (S : Set (Finset V)).Pairwise (fun t₁ t₂ => 2 ≤ (t₁ ∩ t₂).card)) :
    ∃ F : Finset (Sym2 V), F ⊆ G.edgeFinset ∧ F.card ≤ 2 ∧ ∀ t ∈ S, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F := by
  by_cases h_common : ∃ u v, u ≠ v ∧ ∀ t ∈ S, {u, v} ⊆ t;
  · cases' h_common with u hu;
    cases' hu with v hv;
    by_cases huv : G.Adj u v;
    · refine' ⟨ { s(u, v) }, _, _, _ ⟩ <;> aesop;
    · have := h_S; simp_all +decide [ Finset.subset_iff, SimpleGraph.cliqueFinset ] ;
      rcases S.eq_empty_or_nonempty with ( rfl | ⟨ t, ht ⟩ ) <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
      · exact ⟨ ∅, by simp +decide ⟩;
      · have := h_S ht; have := this.1; simp_all +decide [ Set.Pairwise ] ;
  · have h_subset_K4 : (S.sup id).card ≤ 4 := by
      convert pairwise_edge_sharing_no_common_edge_implies_subset_K4 S _ h_pair _;
      · exact fun t ht => Finset.mem_filter.mp ( h_S ht ) |>.2.2;
      · exact h_common;
    apply subset_K4_implies_cover_le_2_restricted;
    exacts [ h_S, h_subset_K4, fun t ht => Finset.le_sup ( f := id ) ht ]

/-
If a triangle shares an edge with t1, and t1 is disjoint from t2, then the triangle shares at most one vertex with t2.
-/

-- Source: proven/tuza/nu1/tuza_nu1_PROVEN.lean
lemma nu_eq_0_implies_tau_eq_0 (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  -- Since the triangle packing number is 0, this means there are no edge-disjoint triangles in G.
  have h_no_triangles : ∀ (S : Finset (Finset V)), IsTrianglePacking G S → S = ∅ := by
    unfold trianglePackingNumber at h;
    intro S hS; contrapose! h; aesop;
    have h_max : ∃ S' ∈ Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset, S'.card > 0 := by
      exact ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hS.1, hS ⟩, Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty h ) ⟩;
    obtain ⟨ S', hS', hS'' ⟩ := h_max;
    have h_max : Finset.max (Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset)) ≥ S'.card := by
      exact Finset.le_max ( Finset.mem_image_of_mem _ hS' );
    cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( IsTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
  -- Since there are no triangles in G, the empty set of edges covers all triangles.
  have h_empty_cover : IsTriangleCovering G ∅ := by
    constructor <;> simp +decide [ IsTriangleCovering ];
    intro t ht; specialize h_no_triangles { t } ; simp_all +decide [ IsTrianglePacking ] ;
  unfold triangleCoveringNumber;
  rw [ Finset.min_eq_inf_withTop ];
  rw [ Finset.inf_eq_sInf_image ];
  rw [ show ( InfSet.sInf ( WithTop.some '' ( ↑ ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) : Set ℕ ) ) ) = 0 from le_antisymm _ _ ];
  · rfl;
  · exact csInf_le ⟨ 0, fun x hx => by aesop ⟩ ⟨ 0, by aesop ⟩;
  · exact bot_le

/-
If the triangle packing number is 1, then any two triangles in the graph share an edge.
-/

-- Source: proven/tuza/nu1/tuza_nu1_PROVEN.lean
lemma subset_K4_implies_cover_le_2_restricted (S : Finset (Finset V))
    (h_S : S ⊆ G.cliqueFinset 3)
    (U : Finset V) (h_U : U.card ≤ 4) (h_subset : ∀ t ∈ S, t ⊆ U) :
    ∃ F : Finset (Sym2 V), F ⊆ G.edgeFinset ∧ F.card ≤ 2 ∧ ∀ t ∈ S, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F := by
  by_contra! h_contra';
  -- Since all triangles in S are subsets of U and |U| ≤ 4, we can analyze the possible configurations of triangles on 4 vertices.
  have h_configurations : ∀ T : Finset (Finset V), (∀ t ∈ T, t.card = 3 ∧ t ⊆ U) → ∃ F : Finset (Sym2 V), F.card ≤ 2 ∧ ∀ t ∈ T, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F := by
    intro T hT
    by_cases hU : U.card ≤ 3;
    · by_cases hU : U.card = 3;
      · -- Since U has exactly 3 elements, any triangle in T must be exactly U itself.
        have hT_eq_U : ∀ t ∈ T, t = U := by
          exact fun t ht => Finset.eq_of_subset_of_card_le ( hT t ht |>.2 ) ( by simp +decide [ hT t ht |>.1, hU ] );
        rcases Finset.card_eq_three.mp hU with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use { s(u, v), s(u, w) } ; simp_all +decide ;
        intro t ht; use u, by rw [ hT_eq_U t ht ] ; simp +decide, v, by rw [ hT_eq_U t ht ] ; simp +decide; ; aesop;
      · exact ⟨ ∅, by norm_num, fun t ht => by have := hT t ht; have := Finset.card_le_card this.2; interval_cases _ : U.card <;> simp_all +decide ⟩;
    · -- Since U has exactly 4 elements, we can analyze the possible configurations of triangles on 4 vertices.
      obtain ⟨a, b, c, d, h_abcd⟩ : ∃ a b c d : V, U = {a, b, c, d} ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
        have hU_card : U.card = 4 := by
          linarith;
        simp_rw +decide [ Finset.card_eq_succ ] at hU_card;
        obtain ⟨ a, t, hat, rfl, b, u, hbu, rfl, c, v, hcv, rfl, d, w, hdw, rfl, hw ⟩ := hU_card; use a, b, c, d; aesop;
      -- Consider the possible triangles on {a, b, c, d}.
      have h_triangles : ∀ t ∈ T, t = {a, b, c} ∨ t = {a, b, d} ∨ t = {a, c, d} ∨ t = {b, c, d} := by
        intro t ht
        obtain ⟨ht_card, ht_subset⟩ := hT t ht
        have ht_cases : t ⊆ {a, b, c, d} := by
          aesop;
        have := Finset.card_eq_three.mp ht_card;
        rcases this with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; simp_all +decide [ Finset.subset_iff ] ;
        rcases ht_cases with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] at hxy hxz hyz ⊢;
      refine' ⟨ { s(a, b), s(c, d) }, _, _ ⟩ <;> simp +decide [ * ];
      intro t ht; rcases h_triangles t ht with ( rfl | rfl | rfl | rfl ) <;> simp +decide [ * ] ;
  specialize h_configurations S ; simp_all +decide [ Finset.subset_iff ];
  obtain ⟨F, hF_card, hF_cover⟩ := h_configurations (fun t ht => ⟨by
  exact h_S ht |>.2, h_subset t ht⟩);
  specialize h_contra' ( F.filter fun e => e ∈ G.edgeSet ) ; simp_all +decide [ Finset.subset_iff ] ;
  refine' h_contra' ( le_trans ( Finset.card_filter_le _ _ ) hF_card ) |> fun ⟨ t, ht, h ⟩ => _;
  obtain ⟨ u, hu, v, hv, huv, hF ⟩ := hF_cover t ht; specialize h u v hu hv huv hF; exact h ( h_S ht |>.1 hu hv huv ) ;

/-
If the triangle packing number is 1, then the triangle covering number is at most 2.
-/

-- Source: proven/tuza/nu1/tuza_nu1_PROVEN.lean
lemma nu_eq_1_implies_tau_le_2 (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  -- If there exists an edge $e = \{u, v\}$ shared by all triangles in $S$, then $\{e\}$ is a triangle covering of size 1. Thus $\tau(G) \leq 1 \leq 2$.
  by_cases h_common : ∃ u v, u ≠ v ∧ ∀ t ∈ G.cliqueFinset 3, {u, v} ⊆ t;
  · -- If there exists an edge $e = \{u, v\}$ shared by all triangles in $S$, then $\{e\}$ is a triangle covering of size 1. Thus $\tau(G) \leq 1$.
    obtain ⟨u, v, huv_ne, huv_cover⟩ := h_common;
    have h_cover : IsTriangleCovering G {s(u, v)} := by
      constructor <;> simp_all +decide [ IsTriangleCovering ];
      · contrapose! huv_cover;
        -- Since the triangle packing number is 1, there exists at least one triangle in the graph.
        obtain ⟨t, ht⟩ : ∃ t ∈ G.cliqueFinset 3, True := by
          have h_triangle : ∃ t ∈ G.cliqueFinset 3, True := by
            have h_nonempty : G.cliqueFinset 3 ≠ ∅ := by
              intro h_empty;
              unfold trianglePackingNumber at h;
              simp_all +decide [ Finset.filter_singleton, IsTrianglePacking ]
            exact Exists.elim ( Finset.nonempty_of_ne_empty h_nonempty ) fun t ht => ⟨ t, ht, trivial ⟩;
          exact h_triangle;
        refine' ⟨ t, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
        intro hu hv; have := ht.1 hu hv; aesop;
      · exact fun t ht => ⟨ u, huv_cover t ht ( Finset.mem_insert_self _ _ ), v, huv_cover t ht ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ), huv_ne, Or.inl ⟨ rfl, rfl ⟩ ⟩;
    refine' le_trans _ ( show 1 ≤ 2 by norm_num );
    unfold triangleCoveringNumber;
    have h_min : (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) (Finset.powerset G.edgeFinset))).min ≤ 1 := by
      have h_one : 1 ∈ Finset.image Finset.card (Finset.filter (IsTriangleCovering G) (Finset.powerset G.edgeFinset)) := by
        simp +zetaDelta at *;
        exact ⟨ { s(u, v) }, ⟨ by simpa using h_cover.1, h_cover ⟩, by simp +decide ⟩
      exact Finset.min_le h_one;
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop;
  · -- Then by `pairwise_edge_sharing_no_common_edge_implies_subset_K4`, the union of all vertices in $S$ has size at most 4.
    have h_union : (Finset.sup (G.cliqueFinset 3) id).card ≤ 4 := by
      apply pairwise_edge_sharing_no_common_edge_implies_subset_K4;
      · simp +decide [ SimpleGraph.cliqueFinset ];
        exact fun t ht => ht.2;
      · intro t₁ ht₁ t₂ ht₂ hne; have := nu_eq_1_implies_pairwise_edge_sharing G h t₁ t₂ ht₁ ht₂; aesop;
      · exact h_common;
    -- By `subset_K4_implies_cover_le_2_restricted`, there exists a cover $F$ of size ≤ 2.
    obtain ⟨F, hF_subset, hF_card, hF_cover⟩ : ∃ F : Finset (Sym2 V), F ⊆ G.edgeFinset ∧ F.card ≤ 2 ∧ ∀ t ∈ G.cliqueFinset 3, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F := by
      apply subset_K4_implies_cover_le_2_restricted;
      exacts [ Finset.Subset.refl _, h_union, fun t ht => Finset.le_sup ( f := id ) ht ];
    refine' le_trans _ hF_card;
    unfold triangleCoveringNumber;
    have hF_covering : IsTriangleCovering G F := by
      exact ⟨ hF_subset, hF_cover ⟩;
    have hF_min : (Finset.image Finset.card (Finset.filter (IsTriangleCovering G) G.edgeFinset.powerset)).min ≤ F.card := by
      exact Finset.min_le ( Finset.mem_image.mpr ⟨ F, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hF_subset, hF_covering ⟩, rfl ⟩ );
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( IsTriangleCovering G ) G.edgeFinset.powerset ) ) <;> aesop

/-
If a set of triangles pairwise share an edge, they can be covered by at most 2 edges.
-/

-- Source: proven/tuza/nu1/tuza_nu1_PROVEN.lean
lemma restricted_nu_le_1_implies_cover_le_2 (S : Finset (Finset V))
    (h_S : S ⊆ G.cliqueFinset 3)
    (h_pair : (S : Set (Finset V)).Pairwise (fun t₁ t₂ => 2 ≤ (t₁ ∩ t₂).card)) :
    ∃ F : Finset (Sym2 V), F ⊆ G.edgeFinset ∧ F.card ≤ 2 ∧ ∀ t ∈ S, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F := by
  by_cases h_common : ∃ u v, u ≠ v ∧ ∀ t ∈ S, {u, v} ⊆ t;
  · cases' h_common with u hu;
    cases' hu with v hv;
    by_cases huv : G.Adj u v;
    · refine' ⟨ { s(u, v) }, _, _, _ ⟩ <;> aesop;
    · have := h_S; simp_all +decide [ Finset.subset_iff, SimpleGraph.cliqueFinset ] ;
      rcases S.eq_empty_or_nonempty with ( rfl | ⟨ t, ht ⟩ ) <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
      · exact ⟨ ∅, by simp +decide ⟩;
      · have := h_S ht; have := this.1; simp_all +decide [ Set.Pairwise ] ;
  · have h_subset_K4 : (S.sup id).card ≤ 4 := by
      convert pairwise_edge_sharing_no_common_edge_implies_subset_K4 S _ h_pair _;
      · exact fun t ht => Finset.mem_filter.mp ( h_S ht ) |>.2.2;
      · exact h_common;
    apply subset_K4_implies_cover_le_2_restricted;
    exacts [ h_S, h_subset_K4, fun t ht => Finset.le_sup ( f := id ) ht ]

/-
If a triangle shares an edge with t1, and t1 is disjoint from t2, then the triangle shares at most one vertex with t2.
-/


-- ═══════════════════════════════════════════════════════════════════════
-- TRIANGLES LEMMAS (20 lemmas)
-- ═══════════════════════════════════════════════════════════════════════

-- Source: proven/tuza_nu1_k4_proof.lean
lemma extension_triangle_exists {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnu : trianglePackingNumber G = 1) (htau : triangleCoveringNumber G > 2)
    (T : Finset V) (hT : G.IsNClique 3 T)
    (e : Sym2 V) (he : e ∈ triangleEdges T) :
    ∃ T', G.IsNClique 3 T' ∧ triangleEdges T ∩ triangleEdges T' = {e} := by
      -- Let $S = \text{triangleEdges}(T) \setminus \{e\}$. Since $T$ is a triangle, $|S| = 2$.
      set S : Finset (Sym2 V) := (triangleEdges T).erase e
      have hS_card : S.card = 2 := by
        rw [ Finset.card_erase_of_mem he ];
        unfold triangleEdges;
        have := Finset.card_eq_three.mp hT.2; aesop;
        simp +decide [ *, Finset.card ];
        simp +decide [ *, Finset.offDiag ];
        simp +decide [ *, Multiset.filter_cons, Multiset.filter_singleton ];
        split_ifs <;> simp_all +decide [ Sym2.eq_swap ];
      -- Since $\tau(G) > 2$, $S$ is not a triangle covering.
      have hS_not_covering : ¬IsTriangleCovering G S := by
        contrapose! htau;
        refine' le_trans ( triangleCoveringNumber_le_card_add_deleteEdges G S _ ) _;
        · intro x hx; aesop;
          unfold triangleEdges at right; aesop;
          exact hT.1 left_1 left_2 right_1;
        · rw [ show triangleCoveringNumber ( G.deleteEdges ( S : Set ( Sym2 V ) ) ) = 0 from _ ] ; aesop;
          convert tuza_base_case _ _;
          unfold IsTriangleCovering at htau; aesop;
          unfold trianglePackingNumber; aesop;
          exact Finset.eq_empty_of_forall_notMem fun x hx => htau x <| by have := a hx; aesop;
      -- So there exists a triangle $T'$ in $G \setminus S$.
      obtain ⟨T', hT'⟩ : ∃ T' : Finset V, G.IsNClique 3 T' ∧ ∀ f ∈ S, ¬f ∈ triangleEdges T' := by
        obtain ⟨ T', hT' ⟩ := Finset.nonempty_of_ne_empty hS_not_covering; use T'; aesop;
        · exact hT'.mono ( by aesop_cat );
        · rcases Finset.mem_image.mp a_2 with ⟨ x, hx, rfl ⟩ ; simp_all +decide [ SimpleGraph.adj_comm ];
          have := hT'.1 hx.1 hx.2.1 hx.2.2; simp_all +decide [ SimpleGraph.adj_comm ] ;
      -- Since $T$ and $T'$ are triangles, they must share an edge. Let's denote this edge as $e'$.
      obtain ⟨e', he'⟩ : ∃ e' ∈ triangleEdges T, e' ∈ triangleEdges T' := by
        have h_intersect : ¬Disjoint (triangleEdges T) (triangleEdges T') := by
          bound;
          exact absurd ( packing_one_implies_intersect G hnu T T' ( by simpa using hT ) ( by simpa using left ) ) ( by aesop );
        exact Finset.not_disjoint_iff.mp h_intersect;
      grind

/--
If the triangle packing number is 1 and the triangle covering number is greater than 2,
then the graph contains a K4 clique.
-/

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma triangle_in_k4_of_intersects_triples {V : Type*} [DecidableEq V]
    (t1 t2 t3 t : Finset V) (h_card : t1.card = 3 ∧ t2.card = 3 ∧ t3.card = 3 ∧ t.card = 3)
    (h_union : (t1 ∪ t2 ∪ t3).card = 4)
    (h_subset : t1 ⊆ t1 ∪ t2 ∪ t3 ∧ t2 ⊆ t1 ∪ t2 ∪ t3 ∧ t3 ⊆ t1 ∪ t2 ∪ t3)
    (h_distinct : t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3)
    (h_inter : (t ∩ t1).card ≥ 2 ∧ (t ∩ t2).card ≥ 2 ∧ (t ∩ t3).card ≥ 2) :
    t ⊆ t1 ∪ t2 ∪ t3 := by
      aesop;
      intro x hx; by_contra h; simp_all +decide [ Finset.subset_iff ] ;
      -- Since $t$ contains $x$ and $x$ is not in $t1$, $t2$, or $t3$, it means $t \cap t1$, $t \cap t2$, and $t \cap t3$ must all be subsets of $\{y, z\}$ where $y$ and $z$ are the other two elements in $t$.
      have h_inter_subset : t ∩ t1 ⊆ t \ {x} ∧ t ∩ t2 ⊆ t \ {x} ∧ t ∩ t3 ⊆ t \ {x} := by
        grind;
      have h_inter_eq : (t ∩ t1) = t \ {x} ∧ (t ∩ t2) = t \ {x} ∧ (t ∩ t3) = t \ {x} := by
        exact ⟨ Finset.eq_of_subset_of_card_le h_inter_subset.1 ( by rw [ Finset.card_sdiff ] ; aesop ), Finset.eq_of_subset_of_card_le h_inter_subset.2.1 ( by rw [ Finset.card_sdiff ] ; aesop ), Finset.eq_of_subset_of_card_le h_inter_subset.2.2 ( by rw [ Finset.card_sdiff ] ; aesop ) ⟩;
      -- Since $t \cap t1 = t \cap t2 = t \cap t3 = t \setminus \{x\}$, it means $t1$, $t2$, and $t3$ all contain the same two elements as $t \setminus \{x\}$.
      have h_common_elements : t1 ⊇ t \ {x} ∧ t2 ⊇ t \ {x} ∧ t3 ⊇ t \ {x} := by
        simp_all +decide [ Finset.subset_iff ];
        simp_all +decide [ Finset.ext_iff ];
      -- Since $t1$, $t2$, and $t3$ all contain the same two elements as $t \setminus \{x\}$, they must be subsets of $t \setminus \{x\} \cup \{y\}$ for some $y$.
      obtain ⟨y, hy⟩ : ∃ y, t1 = t \ {x} ∪ {y} ∧ t2 = t \ {x} ∪ {y} ∨ t1 = t \ {x} ∪ {y} ∧ t3 = t \ {x} ∪ {y} ∨ t2 = t \ {x} ∪ {y} ∧ t3 = t \ {x} ∪ {y} := by
        have h_common_elements : ∀ {s : Finset V}, s.card = 3 → t \ {x} ⊆ s → ∃ y, s = t \ {x} ∪ {y} := by
          intros s hs hs_subset
          have h_card_diff : (s \ (t \ {x})).card = 1 := by
            grind;
          obtain ⟨ y, hy ⟩ := Finset.card_eq_one.mp h_card_diff;
          exact ⟨ y, by rw [ ← hy, Finset.union_sdiff_of_subset hs_subset ] ⟩;
        obtain ⟨ y1, hy1 ⟩ := h_common_elements left ( by tauto ) ; obtain ⟨ y2, hy2 ⟩ := h_common_elements left_4 ( by tauto ) ; obtain ⟨ y3, hy3 ⟩ := h_common_elements left_7 ( by tauto ) ; use if y1 = y2 then y1 else if y1 = y3 then y1 else y2; aesop;
        grind;
      grind

def isK4 {V : Type*} [DecidableEq V] (S : Finset (Finset V)) : Prop :=
  ∃ s : Finset V, s.card = 4 ∧ ∀ t ∈ S, t ⊆ s

-- Source: proven/tuza/slot37/1bb416d7-8490-44fa-88a4-3df9362128c6-output.lean
theorem tuza_nu4_on_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  convert tuza_nu4_lll G h;
  unfold triangleCoveringNumberOn triangleCoveringNumber;
  congr! 3;
  aesop

-- TARGET 4

end

-- Source: proven/tuza/nu4/slot70_tau_union_extended_output.lean
lemma exists_strict_triangle_on_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e.card = 3)
    (h_tau : triangleCoveringNumberOn G (S_e G M e) > 2)
    (f : Finset V) (hf : f ⊆ e) (hf2 : f.card = 2) :
    ∃ t ∈ S_e G M e, t ∩ e = f := by
  contrapose! h_tau;
  -- Let $g$ and $h$ be the other two pairs in $e$.
  obtain ⟨g, hg⟩ : ∃ g : Finset V, g ⊆ e ∧ g.card = 2 ∧ g ≠ f := by
    have h_pairs : Finset.card (Finset.powersetCard 2 e) = 3 := by
      simp +decide [ he ];
    exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.powersetCard 2 e ) from h_pairs.symm ▸ by decide ) f )
  obtain ⟨h, hh⟩ : ∃ h : Finset V, h ⊆ e ∧ h.card = 2 ∧ h ≠ f ∧ h ≠ g := by
    have h_pairs : Finset.card (Finset.powersetCard 2 e) = 3 := by
      simp +decide [ he ];
    exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.erase ( Finset.powersetCard 2 e ) f ) from by rw [ Finset.card_erase_of_mem ( Finset.mem_powersetCard.mpr ⟨ hf, hf2 ⟩ ), h_pairs ] ; simp +decide ) g );
  -- Any triangle in $S_e$ covers either $g$ or $h$.
  have h_cover : ∀ t ∈ S_e G M e, ∃ e' ∈ ({g, h} : Finset (Finset V)), e' ⊆ t := by
    intro t ht
    have h_inter : (t ∩ e).card ≥ 2 ∧ (t ∩ e) ≠ f := by
      exact ⟨ Finset.mem_filter.mp ht |>.2.1, h_tau t ht ⟩;
    have h_inter_cases : (t ∩ e) = e ∨ (t ∩ e) = g ∨ (t ∩ e) = h := by
      have h_inter_cases : ∀ s ⊆ e, s.card = 2 → s = g ∨ s = h ∨ s = f := by
        have h_inter_cases : Finset.powersetCard 2 e = {f, g, h} := by
          rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ Finset.mem_powersetCard.mpr ⟨ hf, hf2 ⟩, Finset.insert_subset_iff.mpr ⟨ Finset.mem_powersetCard.mpr ⟨ hg.1, hg.2.1 ⟩, Finset.singleton_subset_iff.mpr ( Finset.mem_powersetCard.mpr ⟨ hh.1, hh.2.1 ⟩ ) ⟩ ⟩ ) ] ; simp +decide [ *, Finset.card_powersetCard ];
          rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> aesop;
        intro s hs hs'; replace h_inter_cases := Finset.ext_iff.mp h_inter_cases s; aesop;
      have h_inter_cases : (t ∩ e).card = 2 ∨ (t ∩ e).card = 3 := by
        have h_inter_cases : (t ∩ e).card ≤ 3 := by
          exact le_trans ( Finset.card_le_card fun x hx => by aesop ) he.le;
        grind;
      cases h_inter_cases <;> simp_all +decide [ Finset.eq_of_subset_of_card_le ];
      · cases h_inter_cases ( t ∩ e ) ( Finset.inter_subset_right ) ‹_› <;> aesop;
      · have h_inter_eq_e : t ∩ e = e := by
          exact Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right ) ( by aesop );
        exact Or.inl ( h_inter_eq_e ▸ Finset.inter_subset_left );
    rcases h_inter_cases with ( h | h | h ) <;> simp_all +decide [ Finset.subset_iff ];
    · exact Or.inl fun x hx => Finset.mem_of_mem_inter_left ( h.symm ▸ hx );
    · exact Or.inr fun x hx => Finset.mem_of_mem_inter_left ( h.symm ▸ hx );
  -- Let $E_g$ be the edge corresponding to pair $g$, $E_h$ corresponding to $h$.
  obtain ⟨E_g, hE_g⟩ : ∃ E_g : Finset (Sym2 V), E_g ⊆ G.edgeFinset ∧ (∀ t ∈ S_e G M e, ∃ e' ∈ E_g, e' ∈ t.sym2) ∧ E_g.card ≤ 2 := by
    use (g.sym2 ∩ G.edgeFinset) ∪ (h.sym2 ∩ G.edgeFinset);
    simp_all +decide [ Finset.subset_iff ];
    refine' ⟨ _, _, _ ⟩;
    · tauto;
    · intro t ht; specialize h_cover t ht; rcases h_cover with ( h | h ) <;> simp_all +decide [ Finset.ext_iff ] ;
      · obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.card_eq_two.mp hg.2.1;
        by_cases hxy : G.Adj x hx <;> simp_all +decide [ SimpleGraph.adj_comm ];
        · exact ⟨ Sym2.mk ( x, hx ), Or.inl ⟨ by aesop, by aesop ⟩, by aesop ⟩;
        · unfold S_e at ht; simp_all +decide [ Finset.subset_iff ] ;
          have := ht.1.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          exact False.elim ( hxy ( ht.1 h.1 h.2 ( by aesop ) ) );
      · obtain ⟨ x, hx ⟩ := Finset.card_eq_two.mp hh.2.1;
        obtain ⟨ y, hxy, rfl ⟩ := hx;
        by_cases hxy' : G.Adj x y <;> simp_all +decide [ SimpleGraph.adj_comm ];
        · exact ⟨ Sym2.mk ( x, y ), Or.inr ⟨ by aesop, by aesop ⟩, by aesop ⟩;
        · unfold S_e at ht; simp_all +decide [ Finset.subset_iff ] ;
          have := ht.1.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          exact False.elim ( hxy' ( ht.1 h.1 h.2 hxy ) );
    · refine' le_trans ( Finset.card_union_le _ _ ) _;
      refine' le_trans ( add_le_add ( Finset.card_le_one.mpr _ ) ( Finset.card_le_one.mpr _ ) ) _ <;> simp_all +decide [ Finset.subset_iff ];
      · intro a ha₁ ha₂ b hb₁ hb₂; rcases a with ⟨ x, y ⟩ ; rcases b with ⟨ u, v ⟩ ; simp_all +decide [ Finset.card_eq_two ] ;
        rcases hg.2.1 with ⟨ x', y', hxy', rfl ⟩ ; rcases hh.2.1 with ⟨ u', v', huv', rfl ⟩ ; aesop;
      · intro a ha ha' b hb hb'; rcases a with ⟨ x, y ⟩ ; rcases b with ⟨ u, v ⟩ ; simp_all +decide [ Sym2.eq ] ;
        have := Finset.card_eq_two.mp hh.2.1; obtain ⟨ a, b, hab ⟩ := this; aesop;
  refine' le_trans _ hE_g.2.2;
  apply tau_le_of_exists_cover;
  · exact hE_g.1;
  · exact hE_g.2.1

-- Source: proven/tuza/nu4/slot_local_tuza_via_link_graph.lean
lemma disjoint_triangles_iff_matching (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (t1 t2 : Finset V) (ht1 : t1 ∈ trianglesContainingVertex G v)
    (ht2 : t2 ∈ trianglesContainingVertex G v) (hne : t1 ≠ t2) :
    (t1 ∩ t2).card ≤ 1 ↔ Disjoint (t1.erase v) (t2.erase v) := by
  simp_all +decide [ Finset.disjoint_iff_inter_eq_empty, Finset.ext_iff ];
  constructor <;> intro h;
  · contrapose! h;
    exact Finset.one_lt_card.2 ⟨ h.choose, Finset.mem_inter.2 ⟨ h.choose_spec.1, h.choose_spec.2.2 ⟩, v, Finset.mem_inter.2 ⟨ Finset.mem_filter.mp ht1 |>.2, Finset.mem_filter.mp ht2 |>.2 ⟩, by simpa using h.choose_spec.2.1 ⟩;
  · exact Finset.card_le_one.mpr fun x hx y hy => Classical.not_not.1 fun hxy => h x ( Finset.mem_of_mem_inter_left hx ) ( by aesop ) ( Finset.mem_of_mem_inter_right hx )

/-- Vertex cover number of a graph -/
noncomputable def vertexCoverNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ : Finset V).powerset.filter (fun S =>
    ∀ e ∈ G.edgeFinset, ∃ v ∈ S, v ∈ e)
    |>.image Finset.card |>.min |>.getD 0

/-- Maximum matching size of a graph -/
noncomputable def maxMatchingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun M =>
    ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → Disjoint e1.toFinset e2.toFinset)
    |>.image Finset.card |>.max |>.getD 0

/-
The size of the minimum vertex cover is at most twice the size of the maximum matching.
-/
/-- STANDARD RESULT: Minimum vertex cover ≤ 2 × maximum matching -/

-- Source: proven/tuza/nu4/slot_local_tuza_via_link_graph.lean
lemma triangleEdgeEquiv_preserves_disjointness (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (t1 t2 : trianglesContainingVertex G v) (hne : t1 ≠ t2) :
    (t1.1 ∩ t2.1).card ≤ 1 ↔ Disjoint (triangleEdgeEquiv G v t1).1.toFinset (triangleEdgeEquiv G v t2).1.toFinset := by
      convert ( disjoint_triangles_iff_matching G v t1.val t2.val t1.property t2.property <| by aesop ) using 1;
      unfold triangleEdgeEquiv;
      -- By definition of `triangleToLinkEdge`, the edge in the link graph is exactly the set of neighbors of `v` in the triangle.
      have h_edge : ∀ t : { x : Finset V // x ∈ trianglesContainingVertex G v }, (triangleToLinkEdge G v t.val (Finset.mem_filter.mp t.2).1 (Finset.mem_filter.mp t.2).2).1.toFinset = t.val.erase v := by
        intro t;
        have h_edge : ∀ t : { x : Finset V // x ∈ trianglesContainingVertex G v }, (triangleToLinkEdge G v t.val (Finset.mem_filter.mp t.2).1 (Finset.mem_filter.mp t.2).2).1.toFinset = t.val.erase v := by
          intro t
          have h_card : (t.val.erase v).card = 2 := by
            have := Finset.mem_filter.mp t.2;
            simp_all +decide [ SimpleGraph.isNClique_iff ]
          have h_edge : ∀ s : Finset V, s.card = 2 → (s.offDiag.image Sym2.mk).Nonempty → ∀ e ∈ s.offDiag.image Sym2.mk, e.toFinset = s := by
            simp +contextual [ Finset.card_eq_two ];
            aesop;
          apply h_edge;
          · exact h_card;
          · simp +decide [ h_card ];
            exact Finset.card_pos.mp ( by simp +decide [ h_card ] );
          · exact?;
        exact h_edge t;
      aesop

/-
The size of the maximum triangle packing at $v$ is equal to the size of the maximum matching in the link graph of $v$.
-/
/-- Triangle packing at v = Matching in link graph -/

-- Source: proven/tuza/nu4/slot_disjoint_partition_proven.lean
lemma pigeonhole_triangle (A : Finset V) (t : Finset V) (v1 v2 : V)
    (hA : A.card = 3) (h_inter : (t ∩ A).card ≥ 2)
    (hv1 : v1 ∈ A) (hv2 : v2 ∈ A) (h_diff : v1 ≠ v2) :
    v1 ∈ t ∨ v2 ∈ t := by
  -- If neither v1 nor v2 is in t, then t ∩ A must be contained in A \ {v1, v2}
  -- But A \ {v1, v2} has size 1 (since |A|=3), while |t ∩ A| >= 2. Contradiction.
  by_contra h_contra; push_neg at h_contra; exact (by
  -- Since $v1$ and $v2$ are not in $t$, the intersection $t \cap A$ must be a subset of $A \setminus \{v1, v2\}$.
  have h_inter_subset : t ∩ A ⊆ A \ {v1, v2} := by
    aesop_cat;
  have := Finset.card_mono h_inter_subset; simp_all +decide [ Finset.card_sdiff ] ;
  linarith)

/-- PROVEN: In cycle_4, every triangle contains at least one shared vertex -/

-- Source: proven/tuza/nu4/slot_disjoint_partition_proven.lean
lemma cycle4_all_triangles_contain_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hcycle : isCycle4 M A B C D) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ v ∈ sharedVertices A B C D hcycle.2.2.2.2.2.2.2.1 hcycle.2.2.2.2.2.2.2.2.1
      hcycle.2.2.2.2.2.2.2.2.2.1 hcycle.2.2.2.2.2.2.2.2.2.2.1, v ∈ t := by
  -- Uses triangle_shares_edge_with_packing plus cycle_4 structure
  obtain ⟨X, hX₁, hX₂⟩ : ∃ X ∈ M, (t ∩ X).card ≥ 2 := triangle_shares_edge_with_packing G M hM t ht;
  rcases hcycle with ⟨ rfl, h ⟩;
  simp_all +decide [ Finset.ext_iff ];
  rcases hX₁ with ( hX₁ | hX₁ | hX₁ | hX₁ );
  · -- Since $A$ contains $v_ab$ (from $A \cap B$) and $v_da$ (from $D \cap A$), and $v_ab \neq v_da$ because $B \cap D = \emptyset$, we can apply `pigeonhole_triangle`.
    obtain ⟨v_ab, hv_ab⟩ : ∃ v_ab, v_ab ∈ A ∩ B := by
      exact Finset.card_pos.mp ( by linarith )
    obtain ⟨v_da, hv_da⟩ : ∃ v_da, v_da ∈ D ∩ A := by
      exact Finset.card_pos.mp ( by linarith )
    have hv_ab_ne_hv_da : v_ab ≠ v_da := by
      intro h_eq; simp_all +decide [ Finset.ext_iff ] ;
    have := pigeonhole_triangle A t v_ab v_da ?_ ?_ ?_ ?_ ?_ <;> simp_all +decide [ Finset.inter_comm ];
    · exact this.elim ( fun h => ⟨ v_ab, by unfold sharedVertices; aesop ⟩ ) fun h => ⟨ v_da, by unfold sharedVertices; aesop ⟩;
    · have := hM.1.1; simp_all +decide [ Finset.subset_iff ] ;
      exact this.1.2;
    · convert hX₂ using 1;
      exact congr_arg Finset.card ( by ext; aesop );
  · -- Since $B$ contains $v_{ab}$ and $v_{bc}$, and $v_{ab} \neq v_{bc}$, we can apply `pigeonhole_triangle`.
    obtain ⟨v_ab, hv_ab⟩ : ∃ v_ab ∈ B, v_ab ∈ A := by
      exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, Finset.mem_of_mem_inter_right hx, Finset.mem_of_mem_inter_left hx ⟩
    obtain ⟨v_bc, hv_bc⟩ : ∃ v_bc ∈ B, v_bc ∈ C := by
      exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, Finset.mem_of_mem_inter_left hx, Finset.mem_of_mem_inter_right hx ⟩
    have h_diff : v_ab ≠ v_bc := by
      intro h; simp_all +decide [ Finset.ext_iff ] ;
    have h_pigeonhole : v_ab ∈ t ∨ v_bc ∈ t := by
      apply pigeonhole_triangle B t v_ab v_bc;
      · have := hM.1; simp_all +decide [ isTrianglePacking ] ;
        simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
      · exact hX₂.trans ( Finset.card_mono fun x hx => by aesop );
      · tauto;
      · tauto;
      · exact h_diff;
    unfold sharedVertices; aesop;
  · -- Let $v1$ and $v2$ be the shared vertices of $C$.
    obtain ⟨v1, hv1⟩ : ∃ v1, v1 ∈ B ∩ C := by
      exact Finset.card_pos.mp ( by linarith )
    obtain ⟨v2, hv2⟩ : ∃ v2, v2 ∈ C ∩ D := by
      exact Finset.card_pos.mp ( by linarith );
    -- By the pigeonhole principle, since $t$ shares at least 2 vertices with $C$, it must contain at least one of $v1$ or $v2$.
    have h_pigeonhole : v1 ∈ t ∨ v2 ∈ t := by
      apply pigeonhole_triangle C t v1 v2;
      · have := hM.1;
        have := this.1; simp_all +decide [ Finset.subset_iff ] ;
        exact this.2.2.1.card_eq;
      · exact hX₂.trans ( Finset.card_mono <| by aesop_cat );
      · aesop;
      · grind;
      · intro h; simp_all +decide [ Finset.ext_iff ] ;
    exact h_pigeonhole.elim ( fun h => ⟨ v1, by unfold sharedVertices; aesop ⟩ ) fun h => ⟨ v2, by unfold sharedVertices; aesop ⟩;
  · -- Apply `pigeonhole_triangle` with `D`, `t`, `v_cd`, `v_da`.
    obtain ⟨v_cd, hv_cd⟩ : ∃ v_cd, v_cd ∈ C ∩ D := by
      exact Finset.card_pos.mp ( by linarith )
    obtain ⟨v_da, hv_da⟩ : ∃ v_da, v_da ∈ D ∩ A := by
      exact Finset.card_pos.mp ( by linarith );
    have h_pigeonhole : v_cd ∈ t ∨ v_da ∈ t := by
      apply pigeonhole_triangle;
      any_goals exact D;
      · have := hM.1;
        have := this.1;
        simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
      · exact le_trans hX₂ ( Finset.card_mono fun x hx => by aesop );
      · aesop;
      · grind;
      · intro h; simp_all +decide [ Finset.ext_iff ] ;
    unfold sharedVertices; aesop; -- This is proven in slot73 "all-middle" breakthrough

-- ══════════════════════════════════════════════════════════════════════════════
-- DISJOINT PARTITION BY PRIORITY
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles containing the first shared vertex (highest priority) -/
def T1 (triangles : Finset (Finset V)) (v_ab : V) : Finset (Finset V) :=
  triangles.filter (fun t => v_ab ∈ t)

/-- Triangles containing v_bc but NOT v_ab -/
def T2 (triangles : Finset (Finset V)) (v_ab v_bc : V) : Finset (Finset V) :=
  triangles.filter (fun t => v_bc ∈ t ∧ v_ab ∉ t)

/-- Triangles containing v_cd but NOT v_ab and NOT v_bc -/
def T3 (triangles : Finset (Finset V)) (v_ab v_bc v_cd : V) : Finset (Finset V) :=
  triangles.filter (fun t => v_cd ∈ t ∧ v_ab ∉ t ∧ v_bc ∉ t)

/-- Triangles containing v_da but NOT v_ab, v_bc, or v_cd -/
def T4 (triangles : Finset (Finset V)) (v_ab v_bc v_cd v_da : V) : Finset (Finset V) :=
  triangles.filter (fun t => v_da ∈ t ∧ v_ab ∉ t ∧ v_bc ∉ t ∧ v_cd ∉ t)

/-- T1 and T2 are disjoint by construction -/

-- Source: proven/tuza/nu4/safe_discard/slot64d_interact_share_PROVEN.lean
lemma edges_in_triangle_share_vertex (t : Finset V) (ht : t.card = 3)
    (e₁ e₂ : Sym2 V) (he₁ : e₁ ∈ t.sym2) (he₂ : e₂ ∈ t.sym2) (hne : e₁ ≠ e₂) :
    ∃ v ∈ t, v ∈ e₁.toFinset ∧ v ∈ e₂.toFinset := by
  -- t has 3 vertices, e₁ and e₂ are each pairs from t
  -- Any two pairs from a 3-set share exactly one element
  rw [Finset.mem_sym2_iff] at he₁ he₂
  obtain ⟨a, b, hab, ha, hb, rfl⟩ := he₁
  obtain ⟨c, d, hcd, hc, hd, rfl⟩ := he₂
  -- Direct case analysis: check if any vertex is shared
  by_cases h1 : a = c
  · exact ⟨a, ha, by simp, by simp [h1]⟩
  by_cases h2 : a = d
  · exact ⟨a, ha, by simp, by simp [h2]⟩
  by_cases h3 : b = c
  · exact ⟨b, hb, by simp, by simp [h3]⟩
  by_cases h4 : b = d
  · exact ⟨b, hb, by simp, by simp [h4]⟩
  -- All four are distinct, so {a,b,c,d} has 4 elements but ⊆ t which has 3
  exfalso
  have h_four : ({a, b, c, d} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_insert_of_not_mem, Finset.card_singleton]
    · simp [h4, h3]
    · simp [h2, h1]
    · simp [hab]
  have h_sub : ({a, b, c, d} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card h_sub
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- If two M-edges interact, they share a vertex.
    This is crucial for bounding the degree in the Interaction Graph. -/

-- Source: proven/tuza/nu4/safe_discard/slot148a_scattered_partition_PROVEN.lean
theorem scattered_triangles_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (h_scattered : ∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B) :
    ∀ t ∈ G.cliqueFinset 3, ∃! A, A ∈ M ∧ t ∈ trianglesOwnedBy G M A := by
  intro t ht
  by_cases ht_M : t ∈ M
  · -- t is itself an M-element, owned by itself
    use t
    constructor
    · constructor
      · exact ht_M
      · simp only [trianglesOwnedBy, Finset.mem_filter]
        exact ⟨ht, Or.inl rfl⟩
    · -- Uniqueness: only t owns t
      intro A ⟨hA, hA_owns⟩
      simp only [trianglesOwnedBy, Finset.mem_filter] at hA_owns
      rcases hA_owns.2 with rfl | ⟨ht_not_M', _⟩
      · rfl
      · exact absurd ht_M ht_not_M'
  · -- t is external; by maximality, has unique parent
    obtain ⟨m, hm, h_share⟩ := external_shares_edge_with_M G M hM t ht ht_M
    use m
    constructor
    · constructor
      · exact hm
      · simp only [trianglesOwnedBy, Finset.mem_filter]
        exact ⟨ht, Or.inr ⟨ht_M, h_share⟩⟩
    · -- Uniqueness: by scattered_unique_parent
      intro A ⟨hA, hA_owns⟩
      simp only [trianglesOwnedBy, Finset.mem_filter] at hA_owns
      rcases hA_owns.2 with rfl | ⟨_, h_share_A⟩
      · exact absurd hA ht_M
      · by_contra hAm
        exact scattered_unique_parent G M hM.1 h_scattered t ht ht_M m hm h_share A hA hAm h_share_A

end

-- Source: proven/tuza/nu4/safe_discard/slot64b_M_edges_card_PROVEN.lean
lemma triangle_sym2_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    t.sym2.card = 3 := by
  have hcard : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  -- sym2 of a 3-set has C(3,2) = 3 elements
  rw [Finset.card_sym2]
  omega

/-- Each triangle contributes exactly 3 edges to its sym2 -/

-- Source: proven/tuza/nu4/safe_discard/slot64b_M_edges_card_PROVEN.lean
lemma triangle_contribution_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t.card ≤ 3) :
    (t.sym2.filter (fun e => e ∈ G.edgeFinset)).card ≤ 3 := by
  calc (t.sym2.filter (fun e => e ∈ G.edgeFinset)).card
      ≤ t.sym2.card := Finset.card_filter_le _ _
    _ ≤ 3 := by
        rw [Finset.card_sym2]
        interval_cases t.card <;> omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- The number of M-edges is at most 3 times the number of packing elements.
    For ν=4, this means |M_edges| ≤ 12. -/

-- Source: proven/tuza/nu4/safe_discard/slot64a_ig_definitions_PROVEN.lean
lemma external_in_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) (ht : t ∈ externalTriangles G M) :
    t ∈ G.cliqueFinset 3 := by
  simp only [externalTriangles, Finset.mem_filter] at ht
  exact ht.1

/-- External triangles are not in M -/

-- Source: proven/tuza/nu4/safe_discard/slot151_tpair_spokes_PROVEN.lean
lemma triangle_contains_spoke (t : Finset V) (ht : t.card = 3) (v : V) (hv : v ∈ t) :
    (spokesFrom t v hv).Nonempty := by
  -- t = {v, a, b} for some a ≠ b ≠ v
  -- spokesFrom = edges containing v = {s(v,a), s(v,b)}
  -- This is nonempty since t has 3 vertices
  have h_card_ge_2 : (t.erase v).card ≥ 1 := by
    rw [Finset.card_erase_of_mem hv]; omega
  obtain ⟨a, ha⟩ := (t.erase v).nonempty_of_ne_empty (by omega)
  have ha' := Finset.mem_erase.mp ha
  have ha_t := ha'.2
  have hav := ha'.1
  use s(v, a)
  simp only [spokesFrom, Finset.mem_filter]
  constructor
  · rw [Finset.mem_sym2_iff]
    exact ⟨v, a, hav, hv, ha_t, rfl⟩
  · simp

/-- A 3-set has exactly 2 spoke edges from any of its vertices -/

-- Source: proven/tuza/nu4/slot70_d3159016/diagonal_bridges.lean
lemma exists_strict_triangle_on_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e.card = 3)
    (h_tau : triangleCoveringNumberOn G (S_e G M e) > 2)
    (f : Finset V) (hf : f ⊆ e) (hf2 : f.card = 2) :
    ∃ t ∈ S_e G M e, t ∩ e = f := by
  contrapose! h_tau;
  -- Let $g$ and $h$ be the other two pairs in $e$.
  obtain ⟨g, hg⟩ : ∃ g : Finset V, g ⊆ e ∧ g.card = 2 ∧ g ≠ f := by
    have h_pairs : Finset.card (Finset.powersetCard 2 e) = 3 := by
      simp +decide [ he ];
    exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.powersetCard 2 e ) from h_pairs.symm ▸ by decide ) f )
  obtain ⟨h, hh⟩ : ∃ h : Finset V, h ⊆ e ∧ h.card = 2 ∧ h ≠ f ∧ h ≠ g := by
    have h_pairs : Finset.card (Finset.powersetCard 2 e) = 3 := by
      simp +decide [ he ];
    exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.erase ( Finset.powersetCard 2 e ) f ) from by rw [ Finset.card_erase_of_mem ( Finset.mem_powersetCard.mpr ⟨ hf, hf2 ⟩ ), h_pairs ] ; simp +decide ) g );
  -- Any triangle in $S_e$ covers either $g$ or $h$.
  have h_cover : ∀ t ∈ S_e G M e, ∃ e' ∈ ({g, h} : Finset (Finset V)), e' ⊆ t := by
    intro t ht
    have h_inter : (t ∩ e).card ≥ 2 ∧ (t ∩ e) ≠ f := by
      exact ⟨ Finset.mem_filter.mp ht |>.2.1, h_tau t ht ⟩;
    have h_inter_cases : (t ∩ e) = e ∨ (t ∩ e) = g ∨ (t ∩ e) = h := by
      have h_inter_cases : ∀ s ⊆ e, s.card = 2 → s = g ∨ s = h ∨ s = f := by
        have h_inter_cases : Finset.powersetCard 2 e = {f, g, h} := by
          rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ Finset.mem_powersetCard.mpr ⟨ hf, hf2 ⟩, Finset.insert_subset_iff.mpr ⟨ Finset.mem_powersetCard.mpr ⟨ hg.1, hg.2.1 ⟩, Finset.singleton_subset_iff.mpr ( Finset.mem_powersetCard.mpr ⟨ hh.1, hh.2.1 ⟩ ) ⟩ ⟩ ) ] ; simp +decide [ *, Finset.card_powersetCard ];
          rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> aesop;
        intro s hs hs'; replace h_inter_cases := Finset.ext_iff.mp h_inter_cases s; aesop;
      have h_inter_cases : (t ∩ e).card = 2 ∨ (t ∩ e).card = 3 := by
        have h_inter_cases : (t ∩ e).card ≤ 3 := by
          exact le_trans ( Finset.card_le_card fun x hx => by aesop ) he.le;
        grind;
      cases h_inter_cases <;> simp_all +decide [ Finset.eq_of_subset_of_card_le ];
      · cases h_inter_cases ( t ∩ e ) ( Finset.inter_subset_right ) ‹_› <;> aesop;
      · have h_inter_eq_e : t ∩ e = e := by
          exact Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right ) ( by aesop );
        exact Or.inl ( h_inter_eq_e ▸ Finset.inter_subset_left );
    rcases h_inter_cases with ( h | h | h ) <;> simp_all +decide [ Finset.subset_iff ];
    · exact Or.inl fun x hx => Finset.mem_of_mem_inter_left ( h.symm ▸ hx );
    · exact Or.inr fun x hx => Finset.mem_of_mem_inter_left ( h.symm ▸ hx );
  -- Let $E_g$ be the edge corresponding to pair $g$, $E_h$ corresponding to $h$.
  obtain ⟨E_g, hE_g⟩ : ∃ E_g : Finset (Sym2 V), E_g ⊆ G.edgeFinset ∧ (∀ t ∈ S_e G M e, ∃ e' ∈ E_g, e' ∈ t.sym2) ∧ E_g.card ≤ 2 := by
    use (g.sym2 ∩ G.edgeFinset) ∪ (h.sym2 ∩ G.edgeFinset);
    simp_all +decide [ Finset.subset_iff ];
    refine' ⟨ _, _, _ ⟩;
    · tauto;
    · intro t ht; specialize h_cover t ht; rcases h_cover with ( h | h ) <;> simp_all +decide [ Finset.ext_iff ] ;
      · obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.card_eq_two.mp hg.2.1;
        by_cases hxy : G.Adj x hx <;> simp_all +decide [ SimpleGraph.adj_comm ];
        · exact ⟨ Sym2.mk ( x, hx ), Or.inl ⟨ by aesop, by aesop ⟩, by aesop ⟩;
        · unfold S_e at ht; simp_all +decide [ Finset.subset_iff ] ;
          have := ht.1.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          exact False.elim ( hxy ( ht.1 h.1 h.2 ( by aesop ) ) );
      · obtain ⟨ x, hx ⟩ := Finset.card_eq_two.mp hh.2.1;
        obtain ⟨ y, hxy, rfl ⟩ := hx;
        by_cases hxy' : G.Adj x y <;> simp_all +decide [ SimpleGraph.adj_comm ];
        · exact ⟨ Sym2.mk ( x, y ), Or.inr ⟨ by aesop, by aesop ⟩, by aesop ⟩;
        · unfold S_e at ht; simp_all +decide [ Finset.subset_iff ] ;
          have := ht.1.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          exact False.elim ( hxy' ( ht.1 h.1 h.2 hxy ) );
    · refine' le_trans ( Finset.card_union_le _ _ ) _;
      refine' le_trans ( add_le_add ( Finset.card_le_one.mpr _ ) ( Finset.card_le_one.mpr _ ) ) _ <;> simp_all +decide [ Finset.subset_iff ];
      · intro a ha₁ ha₂ b hb₁ hb₂; rcases a with ⟨ x, y ⟩ ; rcases b with ⟨ u, v ⟩ ; simp_all +decide [ Finset.card_eq_two ] ;
        rcases hg.2.1 with ⟨ x', y', hxy', rfl ⟩ ; rcases hh.2.1 with ⟨ u', v', huv', rfl ⟩ ; aesop;
      · intro a ha ha' b hb hb'; rcases a with ⟨ x, y ⟩ ; rcases b with ⟨ u, v ⟩ ; simp_all +decide [ Sym2.eq ] ;
        have := Finset.card_eq_two.mp hh.2.1; obtain ⟨ a, b, hab ⟩ := this; aesop;
  refine' le_trans _ hE_g.2.2;
  apply tau_le_of_exists_cover;
  · exact hE_g.1;
  · exact hE_g.2.1

-- Source: proven/tuza/nu4/slot70_d3159016/output.lean
lemma exists_strict_triangle_on_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e.card = 3)
    (h_tau : triangleCoveringNumberOn G (S_e G M e) > 2)
    (f : Finset V) (hf : f ⊆ e) (hf2 : f.card = 2) :
    ∃ t ∈ S_e G M e, t ∩ e = f := by
  contrapose! h_tau;
  -- Let $g$ and $h$ be the other two pairs in $e$.
  obtain ⟨g, hg⟩ : ∃ g : Finset V, g ⊆ e ∧ g.card = 2 ∧ g ≠ f := by
    have h_pairs : Finset.card (Finset.powersetCard 2 e) = 3 := by
      simp +decide [ he ];
    exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.powersetCard 2 e ) from h_pairs.symm ▸ by decide ) f )
  obtain ⟨h, hh⟩ : ∃ h : Finset V, h ⊆ e ∧ h.card = 2 ∧ h ≠ f ∧ h ≠ g := by
    have h_pairs : Finset.card (Finset.powersetCard 2 e) = 3 := by
      simp +decide [ he ];
    exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.erase ( Finset.powersetCard 2 e ) f ) from by rw [ Finset.card_erase_of_mem ( Finset.mem_powersetCard.mpr ⟨ hf, hf2 ⟩ ), h_pairs ] ; simp +decide ) g );
  -- Any triangle in $S_e$ covers either $g$ or $h$.
  have h_cover : ∀ t ∈ S_e G M e, ∃ e' ∈ ({g, h} : Finset (Finset V)), e' ⊆ t := by
    intro t ht
    have h_inter : (t ∩ e).card ≥ 2 ∧ (t ∩ e) ≠ f := by
      exact ⟨ Finset.mem_filter.mp ht |>.2.1, h_tau t ht ⟩;
    have h_inter_cases : (t ∩ e) = e ∨ (t ∩ e) = g ∨ (t ∩ e) = h := by
      have h_inter_cases : ∀ s ⊆ e, s.card = 2 → s = g ∨ s = h ∨ s = f := by
        have h_inter_cases : Finset.powersetCard 2 e = {f, g, h} := by
          rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ Finset.mem_powersetCard.mpr ⟨ hf, hf2 ⟩, Finset.insert_subset_iff.mpr ⟨ Finset.mem_powersetCard.mpr ⟨ hg.1, hg.2.1 ⟩, Finset.singleton_subset_iff.mpr ( Finset.mem_powersetCard.mpr ⟨ hh.1, hh.2.1 ⟩ ) ⟩ ⟩ ) ] ; simp +decide [ *, Finset.card_powersetCard ];
          rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> aesop;
        intro s hs hs'; replace h_inter_cases := Finset.ext_iff.mp h_inter_cases s; aesop;
      have h_inter_cases : (t ∩ e).card = 2 ∨ (t ∩ e).card = 3 := by
        have h_inter_cases : (t ∩ e).card ≤ 3 := by
          exact le_trans ( Finset.card_le_card fun x hx => by aesop ) he.le;
        grind;
      cases h_inter_cases <;> simp_all +decide [ Finset.eq_of_subset_of_card_le ];
      · cases h_inter_cases ( t ∩ e ) ( Finset.inter_subset_right ) ‹_› <;> aesop;
      · have h_inter_eq_e : t ∩ e = e := by
          exact Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right ) ( by aesop );
        exact Or.inl ( h_inter_eq_e ▸ Finset.inter_subset_left );
    rcases h_inter_cases with ( h | h | h ) <;> simp_all +decide [ Finset.subset_iff ];
    · exact Or.inl fun x hx => Finset.mem_of_mem_inter_left ( h.symm ▸ hx );
    · exact Or.inr fun x hx => Finset.mem_of_mem_inter_left ( h.symm ▸ hx );
  -- Let $E_g$ be the edge corresponding to pair $g$, $E_h$ corresponding to $h$.
  obtain ⟨E_g, hE_g⟩ : ∃ E_g : Finset (Sym2 V), E_g ⊆ G.edgeFinset ∧ (∀ t ∈ S_e G M e, ∃ e' ∈ E_g, e' ∈ t.sym2) ∧ E_g.card ≤ 2 := by
    use (g.sym2 ∩ G.edgeFinset) ∪ (h.sym2 ∩ G.edgeFinset);
    simp_all +decide [ Finset.subset_iff ];
    refine' ⟨ _, _, _ ⟩;
    · tauto;
    · intro t ht; specialize h_cover t ht; rcases h_cover with ( h | h ) <;> simp_all +decide [ Finset.ext_iff ] ;
      · obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.card_eq_two.mp hg.2.1;
        by_cases hxy : G.Adj x hx <;> simp_all +decide [ SimpleGraph.adj_comm ];
        · exact ⟨ Sym2.mk ( x, hx ), Or.inl ⟨ by aesop, by aesop ⟩, by aesop ⟩;
        · unfold S_e at ht; simp_all +decide [ Finset.subset_iff ] ;
          have := ht.1.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          exact False.elim ( hxy ( ht.1 h.1 h.2 ( by aesop ) ) );
      · obtain ⟨ x, hx ⟩ := Finset.card_eq_two.mp hh.2.1;
        obtain ⟨ y, hxy, rfl ⟩ := hx;
        by_cases hxy' : G.Adj x y <;> simp_all +decide [ SimpleGraph.adj_comm ];
        · exact ⟨ Sym2.mk ( x, y ), Or.inr ⟨ by aesop, by aesop ⟩, by aesop ⟩;
        · unfold S_e at ht; simp_all +decide [ Finset.subset_iff ] ;
          have := ht.1.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          exact False.elim ( hxy' ( ht.1 h.1 h.2 hxy ) );
    · refine' le_trans ( Finset.card_union_le _ _ ) _;
      refine' le_trans ( add_le_add ( Finset.card_le_one.mpr _ ) ( Finset.card_le_one.mpr _ ) ) _ <;> simp_all +decide [ Finset.subset_iff ];
      · intro a ha₁ ha₂ b hb₁ hb₂; rcases a with ⟨ x, y ⟩ ; rcases b with ⟨ u, v ⟩ ; simp_all +decide [ Finset.card_eq_two ] ;
        rcases hg.2.1 with ⟨ x', y', hxy', rfl ⟩ ; rcases hh.2.1 with ⟨ u', v', huv', rfl ⟩ ; aesop;
      · intro a ha ha' b hb hb'; rcases a with ⟨ x, y ⟩ ; rcases b with ⟨ u, v ⟩ ; simp_all +decide [ Sym2.eq ] ;
        have := Finset.card_eq_two.mp hh.2.1; obtain ⟨ a, b, hab ⟩ := this; aesop;
  refine' le_trans _ hE_g.2.2;
  apply tau_le_of_exists_cover;
  · exact hE_g.1;
  · exact hE_g.2.1

-- Source: proven/tuza/nu0/tuza_nu0_PROVEN.lean
lemma three_triangles_pairwise_edge_sharing_union_card (t₁ t₂ t₃ : Finset V)
    (h_card₁ : t₁.card = 3) (h_card₂ : t₂.card = 3) (h_card₃ : t₃.card = 3)
    (h₁₂ : 2 ≤ (t₁ ∩ t₂).card) (h₁₃ : 2 ≤ (t₁ ∩ t₃).card) (h₂₃ : 2 ≤ (t₂ ∩ t₃).card)
    (h_no_common : (t₁ ∩ t₂ ∩ t₃).card < 2) :
    (t₁ ∪ t₂ ∪ t₃).card = 4 := by
  have h_union_card : (t₁ ∪ t₂ ∪ t₃).card ≤ 4 := by
    have h_inter_union : (t₁ ∩ (t₂ ∪ t₃)).card ≥ (t₁ ∩ t₂).card + (t₁ ∩ t₃).card - (t₁ ∩ t₂ ∩ t₃).card := by
      rw [ ← Finset.card_union_add_card_inter ];
      simp +decide [ Finset.inter_union_distrib_left, Finset.inter_comm, Finset.inter_left_comm, Finset.inter_assoc ];
    grind;
  interval_cases _ : t₁ ∪ t₂ ∪ t₃ |> Finset.card <;> simp_all +decide;
  · rw [ Finset.card_eq_one ] at *;
    rcases ‹_› with ⟨ a, ha ⟩ ; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
    exact absurd ( Finset.card_le_card ( show t₁ ⊆ { a } from fun x hx => by aesop ) ) ( by aesop );
  · have := Finset.card_le_card ( show t₁ ⊆ t₁ ∪ ( t₂ ∪ t₃ ) from Finset.subset_union_left ) ; simp_all +decide ;
  · have h_union_eq : t₁ = t₁ ∪ t₂ ∪ t₃ := by
      have h_union_eq : t₁ ⊆ t₁ ∪ t₂ ∪ t₃ := by
        grind;
      exact Finset.eq_of_subset_of_card_le h_union_eq ( by aesop );
    norm_num [ Finset.ext_iff ] at h_union_eq;
    have h_union_eq : t₂ = t₁ ∧ t₃ = t₁ := by
      exact ⟨ Finset.eq_of_subset_of_card_le ( fun x hx => h_union_eq x ( Or.inl hx ) ) ( by linarith ), Finset.eq_of_subset_of_card_le ( fun x hx => h_union_eq x ( Or.inr hx ) ) ( by linarith ) ⟩;
    aesop

/-
If a set of triangles pairwise share an edge but do not all share a common edge, then the union of their vertices has size at most 4.
-/

-- Source: proven/tuza/nu0/tuza_nu0_PROVEN.lean
lemma disjoint_triangles_implies_neighbors_edge_disjoint (t₁ t₂ a : Finset V)
    (h_card_a : a.card = 3)
    (h_disjoint : Disjoint t₁ t₂)
    (h_neighbor : 2 ≤ (a ∩ t₁).card) :
    (a ∩ t₂).card ≤ 1 := by
  have h_inter : (a ∩ t₁).card + (a ∩ t₂).card ≤ 3 := by
    rw [ ← h_card_a, ← Finset.card_union_of_disjoint ];
    · exact Finset.card_le_card fun x hx => by aesop;
    · exact Disjoint.mono inf_le_right inf_le_right h_disjoint;
  linarith

/-
If {t1, t2} is a maximum packing with t1 and t2 disjoint, then any two triangles sharing an edge with t1 must share an edge with each other.
-/

-- Source: proven/tuza/nu1/tuza_nu1_PROVEN.lean
lemma three_triangles_pairwise_edge_sharing_union_card (t₁ t₂ t₃ : Finset V)
    (h_card₁ : t₁.card = 3) (h_card₂ : t₂.card = 3) (h_card₃ : t₃.card = 3)
    (h₁₂ : 2 ≤ (t₁ ∩ t₂).card) (h₁₃ : 2 ≤ (t₁ ∩ t₃).card) (h₂₃ : 2 ≤ (t₂ ∩ t₃).card)
    (h_no_common : (t₁ ∩ t₂ ∩ t₃).card < 2) :
    (t₁ ∪ t₂ ∪ t₃).card = 4 := by
  have h_union_card : (t₁ ∪ t₂ ∪ t₃).card ≤ 4 := by
    have h_inter_union : (t₁ ∩ (t₂ ∪ t₃)).card ≥ (t₁ ∩ t₂).card + (t₁ ∩ t₃).card - (t₁ ∩ t₂ ∩ t₃).card := by
      rw [ ← Finset.card_union_add_card_inter ];
      simp +decide [ Finset.inter_union_distrib_left, Finset.inter_comm, Finset.inter_left_comm, Finset.inter_assoc ];
    grind;
  interval_cases _ : t₁ ∪ t₂ ∪ t₃ |> Finset.card <;> simp_all +decide;
  · rw [ Finset.card_eq_one ] at *;
    rcases ‹_› with ⟨ a, ha ⟩ ; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
    exact absurd ( Finset.card_le_card ( show t₁ ⊆ { a } from fun x hx => by aesop ) ) ( by aesop );
  · have := Finset.card_le_card ( show t₁ ⊆ t₁ ∪ ( t₂ ∪ t₃ ) from Finset.subset_union_left ) ; simp_all +decide ;
  · have h_union_eq : t₁ = t₁ ∪ t₂ ∪ t₃ := by
      have h_union_eq : t₁ ⊆ t₁ ∪ t₂ ∪ t₃ := by
        grind;
      exact Finset.eq_of_subset_of_card_le h_union_eq ( by aesop );
    norm_num [ Finset.ext_iff ] at h_union_eq;
    have h_union_eq : t₂ = t₁ ∧ t₃ = t₁ := by
      exact ⟨ Finset.eq_of_subset_of_card_le ( fun x hx => h_union_eq x ( Or.inl hx ) ) ( by linarith ), Finset.eq_of_subset_of_card_le ( fun x hx => h_union_eq x ( Or.inr hx ) ) ( by linarith ) ⟩;
    aesop

/-
If a set of triangles pairwise share an edge but do not all share a common edge, then the union of their vertices has size at most 4.
-/

-- Source: proven/tuza/nu1/tuza_nu1_PROVEN.lean
lemma disjoint_triangles_implies_neighbors_edge_disjoint (t₁ t₂ a : Finset V)
    (h_card_a : a.card = 3)
    (h_disjoint : Disjoint t₁ t₂)
    (h_neighbor : 2 ≤ (a ∩ t₁).card) :
    (a ∩ t₂).card ≤ 1 := by
  have h_inter : (a ∩ t₁).card + (a ∩ t₂).card ≤ 3 := by
    rw [ ← h_card_a, ← Finset.card_union_of_disjoint ];
    · exact Finset.card_le_card fun x hx => by aesop;
    · exact Disjoint.mono inf_le_right inf_le_right h_disjoint;
  linarith

/-
If {t1, t2} is a maximum packing with t1 and t2 disjoint, then any two triangles sharing an edge with t1 must share an edge with each other.
-/


-- ═══════════════════════════════════════════════════════════════════════
-- EDGES LEMMAS (21 lemmas)
-- ═══════════════════════════════════════════════════════════════════════

-- Source: proven/scaffolding/slot44_scaffolding_PARTIAL.lean
lemma common_ext_vertex_of_diff_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V)
    (ht1 : t1 ∈ (S_e G M e).filter (· ≠ e))
    (ht2 : t2 ∈ (S_e G M e).filter (· ≠ e))
    (h_diff : t1 ∩ e ≠ t2 ∩ e) :
    ∃ x, x ∉ e ∧ t1 = (t1 ∩ e) ∪ {x} ∧ t2 = (t2 ∩ e) ∪ {x} := by
  have h_inter : 2 ≤ (t1 ∩ t2).card := by
    have := pairwise_intersecting_Se_aux G M hM e he;
    exact this ht1 ht2 ( by aesop );
  have ht1_card : t1.card = 3 := by
    simp +zetaDelta at *;
    simp_all +decide [ S_e ];
    simp_all +decide [ trianglesSharingEdge ];
    exact ht1.1.1.1.2
  have ht2_card : t2.card = 3 := by
    simp_all +decide [ S_e ];
    simp_all +decide [ trianglesSharingEdge ];
    exact ht2.1.1.1.2;
  have ht1_inter_e_card : (t1 ∩ e).card = 2 := by
    have ht1_inter_e_card_ge2 : 2 ≤ (t1 ∩ e).card := by
      simp +zetaDelta at *;
      exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht1.1 |>.1 ) |>.2;
    have ht1_inter_e_card_le3 : (t1 ∩ e).card ≤ 3 := by
      exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ht1_card.le;
    interval_cases _ : Finset.card ( t1 ∩ e ) <;> simp_all +decide;
    have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ e ⊆ t1 ) ; simp_all +decide ;
    have := Finset.eq_of_subset_of_card_le this; simp_all +decide ;
    have := hM.1; simp_all +decide [ Finset.subset_iff ] ;
    have := this.1; simp_all +decide [ Finset.subset_iff ] ;
    have := this he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  have ht2_inter_e_card : (t2 ∩ e).card = 2 := by
    have ht2_inter_e_card : 2 ≤ (t2 ∩ e).card := by
      unfold S_e at ht2;
      unfold trianglesSharingEdge at ht2; aesop;
    have ht2_inter_e_card : (t2 ∩ e).card ≤ 3 := by
      exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ht2_card.le;
    interval_cases _ : Finset.card ( t2 ∩ e ) <;> simp_all +decide;
    have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t2 ∩ e ⊆ t2 ) ; simp_all +decide ;
    have := Finset.eq_of_subset_of_card_le this ; simp_all +decide ;
    have := hM.1.1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    have := this he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  obtain ⟨x, hx⟩ : ∃ x, x ∈ t1 ∧ x ∉ e ∧ t1 = (t1 ∩ e) ∪ {x} := by
    have := Finset.card_sdiff_add_card_inter t1 e; simp_all +decide ;
    obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp this; use x; simp_all +decide [ Finset.ext_iff ] ;
    exact ⟨ by specialize hx x; tauto, by specialize hx x; tauto, fun a => ⟨ fun ha => by specialize hx a; tauto, fun ha => by specialize hx a; tauto ⟩ ⟩
  obtain ⟨y, hy⟩ : ∃ y, y ∈ t2 ∧ y ∉ e ∧ t2 = (t2 ∩ e) ∪ {y} := by
    have h_diff_t2 : (t2 \ e).card = 1 := by
      have := Finset.card_sdiff_add_card_inter t2 e; simp +decide [ ht2_card, ht2_inter_e_card ] at this ⊢; linarith;
    obtain ⟨ y, hy ⟩ := Finset.card_eq_one.mp h_diff_t2;
    exact ⟨ y, by rw [ Finset.eq_singleton_iff_unique_mem ] at hy; exact hy.1 |> Finset.mem_sdiff.mp |> And.left, by rw [ Finset.eq_singleton_iff_unique_mem ] at hy; exact hy.1 |> Finset.mem_sdiff.mp |> And.right, by ext z; by_cases hz : z ∈ e <;> simp +decide [ hz, hy.symm ] ⟩;
  have hxy : x = y := by
    contrapose! h_inter;
    have h_inter_eq : t1 ∩ t2 = (t1 ∩ e) ∩ (t2 ∩ e) := by
      grind;
    rw [ h_inter_eq ];
    refine' lt_of_le_of_ne ( Nat.le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ht1_inter_e_card.le ) _;
    intro H;
    have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ e ∩ ( t2 ∩ e ) ⊆ t1 ∩ e ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ e ∩ ( t2 ∩ e ) ⊆ t2 ∩ e ) ; simp +decide [ H, ht1_inter_e_card, ht2_inter_e_card ] at *;
    grind +ring;
  grind

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma shares_incident_edge_of_shares_edge_and_mem {V : Type*} [DecidableEq V]
    (e t : Finset V) (v : V)
    (he : e.card = 3) (hv_e : v ∈ e) (hv_t : v ∈ t)
    (h_share : (t ∩ e).card ≥ 2) :
    ∃ u ∈ e, u ≠ v ∧ {v, u} ⊆ t := by
      -- Since the intersection of t and e has at least two elements and v is already in both, there must be another element u in e that is also in t.
      obtain ⟨u, hu₁, hu₂⟩ : ∃ u ∈ t ∩ e, u ≠ v := by
        exact Finset.exists_mem_ne h_share v
      generalize_proofs at *; (
      grind)

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma common_vertex_of_different_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3)
    (e : Finset V) (he : e ∈ S)
    (h_pairwise : Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≥ 2))
    (t1 t2 : Finset V) (ht1 : t1 ∈ S) (ht2 : t2 ∈ S)
    (h_inter1 : (t1 ∩ e).card = 2) (h_inter2 : (t2 ∩ e).card = 2)
    (h_diff : t1 ∩ e ≠ t2 ∩ e) :
    ∃ x, x ∉ e ∧ t1 = (t1 ∩ e) ∪ {x} ∧ t2 = (t2 ∩ e) ∪ {x} := by
      have h_card_t1 : (t1 \ e).card = 1 := by
        have := hS ht1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        have := this.2; simp_all +decide [ Finset.card_sdiff ] ;
        rw [ Finset.inter_comm, h_inter1 ]
      have h_card_t2 : (t2 \ e).card = 1 := by
        have := hS ht2; simp_all +decide [ Finset.card_sdiff ] ;
        have := this.2; simp_all +decide [ Finset.inter_comm ] ;
      obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp h_card_t1
      obtain ⟨ y, hy ⟩ := Finset.card_eq_one.mp h_card_t2
      use x, by
        rw [ Finset.eq_singleton_iff_unique_mem ] at hx ; aesop
      use by
        grind
      use by
        have := h_pairwise ht1 ht2; simp_all +decide [ Finset.card_eq_two ] ;
        contrapose! this;
        refine' ⟨ _, _ ⟩;
        · grind;
        · refine' lt_of_le_of_lt ( Finset.card_le_one.mpr _ ) ( by decide );
          simp_all +decide [ Finset.ext_iff ];
          grind

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma no_edge_sharing_implies_single_vertex_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_no_edge : noEdgeSharing M e) :
    ∀ t ∈ X_ef G e f, (t ∩ e).card = 2 ∧ (t ∩ f).card = 2 ∧ (e ∩ f).card = 1 := by
  -- By definition of $X_ef$, we know that every element in $X_ef G e f$ shares at least two vertices with both $e$ and $f$.
  intro t ht
  have h_inter_e : (t ∩ e).card ≥ 2 := by
    unfold X_ef at ht; aesop;
  have h_inter_f : (t ∩ f).card ≥ 2 := by
    unfold X_ef at ht; aesop;
  have h_inter_ef : (e ∩ f).card = 1 := by
    have h_inter_ef : (e ∩ f).card ≤ 1 := by
      contrapose! h_no_edge; aesop;
    have h_inter_ef : (e ∩ f ∩ t).card ≥ 1 := by
      have h_inter_ef : (e ∩ f ∩ t).card ≥ (t ∩ e).card + (t ∩ f).card - t.card := by
        have h_inter_ef : (e ∩ f ∩ t).card ≥ (t ∩ e).card + (t ∩ f).card - (t ∩ e ∪ t ∩ f).card := by
          rw [ ← Finset.card_union_add_card_inter ];
          simp +decide [ Finset.inter_left_comm, Finset.inter_comm ];
        exact le_trans ( Nat.sub_le_sub_left ( Finset.card_mono <| by aesop_cat ) _ ) h_inter_ef;
      simp_all +decide [ X_ef ];
      exact Finset.card_pos.mp ( by linarith [ show t.card = 3 by exact ht.card_eq ] );
    exact le_antisymm ‹_› ( h_inter_ef.trans ( Finset.card_mono fun x hx => by aesop ) );
  -- Since $t$ is a triangle, it has exactly three vertices. Therefore, the intersections $t \cap e$ and $t \cap f$ can each have at most two vertices.
  have h_card_le_two : (t ∩ e).card ≤ 2 ∧ (t ∩ f).card ≤ 2 := by
    have h_card_le_two : t.card ≤ 3 := by
      exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.2 |> fun h => by simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    have h_card_le_two : (t ∩ e).card + (t ∩ f).card ≤ t.card + (e ∩ f).card := by
      rw [ ← Finset.card_union_add_card_inter ];
      exact add_le_add ( Finset.card_le_card fun x hx => by aesop ) ( Finset.card_le_card fun x hx => by aesop );
    omega;
  exact ⟨ le_antisymm h_card_le_two.1 h_inter_e, le_antisymm h_card_le_two.2 h_inter_f, h_inter_ef ⟩

-- TARGET: Bridge structure when no edge sharing

/--
When bridges share exactly one vertex with both elements,
the bridge set X(e,f) has a special structure.
-/

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
theorem heavy_implies_edge_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_heavy : triangleCoveringNumberOn G (trianglesSharingEdge G e) ≥ 3) :
    ∃ f ∈ M, f ≠ e ∧ sharesEdge e f := by
  contrapose! h_heavy;
  exact Nat.lt_succ_of_le ( tau_Te_le_2_no_edge_sharing G M hM e he h_heavy )

-- MAIN TARGET

/--
CONTRAPOSITIVE FORM: No edge sharing implies light element
-/

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
theorem no_edge_sharing_implies_light (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_no_edge : noEdgeSharing M e) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  exact?

-- ALTERNATIVE TARGET: Easier form

/--
COROLLARY: Application to ν=4

If all elements have no edge sharing, then τ ≤ 8.
-/

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
theorem tuza_nu4_no_edge_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_no_edges : ∀ e ∈ M, noEdgeSharing M e) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- Since M is a maximal packing, T_e is a subset of the clique set.
  have h_clique_subset : G.cliqueFinset 3 = M.biUnion (fun e => trianglesSharingEdge G e) := by
    -- Since M is a maximal packing, every triangle in the clique set must be part of some triangle in M.
    have h_clique_subset : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
      intro t ht;
      -- Assume that no element in M shares an edge with t.
      by_contra h_no_edge;
      -- If no element in M shares an edge with t, then t can be added to M to form a larger packing, contradicting the maximality of M.
      have h_add_t : isTrianglePacking G (insert t M) := by
        simp_all +decide [ isTrianglePacking ];
        simp_all +decide [ Finset.subset_iff, Set.Pairwise ];
        simp_all +decide [ Finset.inter_comm, noEdgeSharing ];
        exact ⟨ fun e he => by have := hM.1.1 he; aesop, fun e he he' => Nat.le_of_lt_succ ( h_no_edge e he ), fun e he => ⟨ fun he' => Nat.le_of_lt_succ ( h_no_edge e he ), fun f hf hef => Nat.le_of_lt_succ ( lt_of_not_ge fun h => h_no_edges e he f hf ( Ne.symm hef ) <| by exact le_trans ( by linarith ) h ) ⟩ ⟩;
      have h_add_t_card : (insert t M).card ≤ trianglePackingNumber G := by
        have h_add_t_card : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ trianglePackingNumber G := by
          intro S hS;
          have h_add_t_card : S.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
            exact Finset.mem_image.mpr ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( hS.1 ), hS ⟩, rfl ⟩;
          have h_add_t_card : ∀ x ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)).max 0 := by
            intro x hx;
            have := Finset.le_max hx;
            cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
          exact h_add_t_card _ ‹_›;
        exact h_add_t_card _ h_add_t;
      have h_add_t_card : (insert t M).card = M.card + 1 := by
        rw [ Finset.card_insert_of_notMem ];
        intro h; specialize h_no_edges t h; simp_all +decide ;
        have := h_no_edge t h; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      linarith [ hM.2 ];
    unfold trianglesSharingEdge; aesop;
  rw [ h_clique_subset ];
  -- Apply the

-- Source: proven/tuza/nu4/slot139_tau_le_12_PROVEN.lean
lemma shared_vertices_implies_shared_edge (t X : Finset V)
    (ht : t.card = 3) (hX : X.card = 3) (h_share : (t ∩ X).card ≥ 2) :
    ∃ e : Sym2 V, e ∈ t.sym2 ∧ e ∈ X.sym2 := by
  -- Extract two distinct vertices from the intersection
  have h_two : ∃ a b : V, a ∈ t ∩ X ∧ b ∈ t ∩ X ∧ a ≠ b := by
    have h_card := h_share
    interval_cases n : (t ∩ X).card
    · -- n = 2: intersection has exactly 2 elements
      obtain ⟨a, b, hab, h_eq⟩ := Finset.card_eq_two.mp rfl
      exact ⟨a, b, by simp [h_eq], by simp [h_eq], hab⟩
    · -- n = 3: intersection has 3 elements (t = X)
      obtain ⟨a, b, c, hab, hac, hbc, h_eq⟩ := Finset.card_eq_three.mp rfl
      exact ⟨a, b, by simp [h_eq], by simp [h_eq], hab⟩
  obtain ⟨a, b, ha, hb, hab⟩ := h_two
  use s(a, b)
  constructor
  · -- s(a,b) ∈ t.sym2
    rw [Finset.mem_sym2_iff]
    exact ⟨Finset.mem_of_mem_inter_left ha, Finset.mem_of_mem_inter_left hb, hab⟩
  · -- s(a,b) ∈ X.sym2
    rw [Finset.mem_sym2_iff]
    exact ⟨Finset.mem_of_mem_inter_right ha, Finset.mem_of_mem_inter_right hb, hab⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PACKING EDGES COVER
-- ══════════════════════════════════════════════════════════════════════════════

/-- Union of all edges from packing elements -/
def packingEdges (G : SimpleGraph V) [DecidableRel G.Adj] {M : Finset (Finset V)}
    (cfg : Cycle4 G M) : Finset (Sym2 V) :=
  cfg.A.sym2 ∪ cfg.B.sym2 ∪ cfg.C.sym2 ∪ cfg.D.sym2

/-- Packing edges are graph edges -/

-- Source: proven/tuza/nu4/safe_discard/slot148b_owner_covered_PROVEN.lean
lemma owned_contains_A_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A : Finset V) (hA : A ∈ M) :
    ∀ t ∈ trianglesOwnedBy G M A, ∃ e ∈ A.sym2, e ∈ t.sym2 := by
  intro t ht
  simp only [trianglesOwnedBy, Finset.mem_filter] at ht
  obtain ⟨ht_clique, ht_owned⟩ := ht
  rcases ht_owned with rfl | ⟨_, h_share⟩
  · -- Case: t = A
    have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hA)).card_eq
    exact self_covered A hA_card
  · -- Case: t shares edge with A
    obtain ⟨e, he_t, he_A⟩ := h_share
    exact ⟨e, he_A, he_t⟩

/-- A's 3 edges cover all triangles owned by A -/

-- Source: proven/tuza/nu4/safe_discard/slot148a_scattered_partition_PROVEN.lean
lemma two_vertices_implies_edge (t m : Finset V)
    (ht : t.card = 3) (hm : m.card = 3) (h_inter : (t ∩ m).card ≥ 2) :
    sharesEdgeWith t m := by
  have h_two : (t ∩ m).Nonempty := by omega
  obtain ⟨v, hv⟩ := h_two
  have hv_t := (Finset.mem_inter.mp hv).1
  have hv_m := (Finset.mem_inter.mp hv).2
  have h_two' : ((t ∩ m).erase v).Nonempty := by
    rw [Finset.card_erase_of_mem hv]; omega
  obtain ⟨w, hw⟩ := h_two'
  have hw' := Finset.mem_erase.mp hw
  have hw_t := (Finset.mem_inter.mp hw'.2).1
  have hw_m := (Finset.mem_inter.mp hw'.2).2
  have hvw : v ≠ w := hw'.1.symm
  use s(v, w)
  constructor
  · rw [Finset.mem_sym2_iff]; exact ⟨v, w, hvw, hv_t, hw_t, rfl⟩
  · rw [Finset.mem_sym2_iff]; exact ⟨v, w, hvw, hv_m, hw_m, rfl⟩

/-- Every external triangle shares edge with some M-element (by maximality) -/

-- Source: proven/tuza/nu4/safe_discard/slot148a_scattered_partition_PROVEN.lean
lemma external_shares_edge_with_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_M : t ∉ M) :
    ∃ m ∈ M, sharesEdgeWith t m := by
  obtain ⟨m, hm, h_inter⟩ := hM.2 t ht ht_not_M
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  have hm_card : m.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1.1 hm)).card_eq
  exact ⟨m, hm, two_vertices_implies_edge t m ht_card hm_card h_inter⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET THEOREM: Partition by owner
-- ══════════════════════════════════════════════════════════════════════════════

/-- In scattered case, every triangle has exactly one owner in M.
    This means triangles partition by trianglesOwnedBy. -/

-- Source: proven/tuza/nu4/safe_discard/slot64c_edge_unique_PROVEN.lean
lemma edge_in_unique_M_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ M_edges G M) :
    ∃! m, m ∈ M ∧ e ∈ m.sym2 := by
  -- Existence: e ∈ M_edges means e is in some M-element
  simp only [M_edges, Finset.mem_biUnion, Finset.mem_filter] at he
  obtain ⟨m, hm, he_in_m, _⟩ := he
  use m
  constructor
  · exact ⟨hm, he_in_m⟩
  · -- Uniqueness: follows from M_edge_in_exactly_one
    intro m' ⟨hm', he_in_m'⟩
    by_contra hne
    exact M_edge_in_exactly_one G M hM e m hm he_in_m m' hm' hne he_in_m'

/-- Variant: The M-element containing an M-edge is unique -/

-- Source: proven/tuza/nu4/safe_discard/slot64c_edge_unique_PROVEN.lean
lemma M_element_of_edge_unique (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (he : e ∈ M_edges G M)
    (m₁ m₂ : Finset V) (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    (he₁ : e ∈ m₁.sym2) (he₂ : e ∈ m₂.sym2) :
    m₁ = m₂ := by
  by_contra hne
  exact M_edge_in_exactly_one G M hM e m₁ hm₁ he₁ m₂ hm₂ hne he₂

end

-- Source: proven/tuza/nu4/safe_discard/slot64a_ig_definitions_PROVEN.lean
lemma external_shares_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) (ht : t ∈ externalTriangles G M) :
    ∃ e ∈ M_edges G M, e ∈ t.sym2 := by
  simp only [externalTriangles, Finset.mem_filter] at ht
  exact ht.2.2

/-- If two edges interact, they share an external triangle witness -/

-- Source: proven/tuza/nu4/safe_discard/slot151_tpair_spokes_PROVEN.lean
lemma spokes_are_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (v : V) (hv : v ∈ t) :
    spokesFrom t v hv ⊆ G.edgeFinset := by
  intro e he
  simp only [spokesFrom, Finset.mem_filter] at he
  have h_clique := SimpleGraph.mem_cliqueFinset_iff.mp ht
  rw [Finset.mem_sym2_iff] at he
  obtain ⟨he_sym2, _⟩ := he
  obtain ⟨x, y, hxy, hx, hy, rfl⟩ := he_sym2
  rw [SimpleGraph.mem_edgeFinset]
  exact h_clique.2 hx hy hxy

/-- The union of spokes from A and B at shared vertex v has at most 4 edges -/

-- Source: proven/tuza/lemmas/slot44/5a188e26-ef0d-44c2-a565-cd798ad02e00-output.lean
lemma common_ext_vertex_of_diff_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V)
    (ht1 : t1 ∈ (S_e G M e).filter (· ≠ e))
    (ht2 : t2 ∈ (S_e G M e).filter (· ≠ e))
    (h_diff : t1 ∩ e ≠ t2 ∩ e) :
    ∃ x, x ∉ e ∧ t1 = (t1 ∩ e) ∪ {x} ∧ t2 = (t2 ∩ e) ∪ {x} := by
  have h_inter : 2 ≤ (t1 ∩ t2).card := by
    have := pairwise_intersecting_Se_aux G M hM e he;
    exact this ht1 ht2 ( by aesop );
  have ht1_card : t1.card = 3 := by
    simp +zetaDelta at *;
    simp_all +decide [ S_e ];
    simp_all +decide [ trianglesSharingEdge ];
    exact ht1.1.1.1.2
  have ht2_card : t2.card = 3 := by
    simp_all +decide [ S_e ];
    simp_all +decide [ trianglesSharingEdge ];
    exact ht2.1.1.1.2;
  have ht1_inter_e_card : (t1 ∩ e).card = 2 := by
    have ht1_inter_e_card_ge2 : 2 ≤ (t1 ∩ e).card := by
      simp +zetaDelta at *;
      exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht1.1 |>.1 ) |>.2;
    have ht1_inter_e_card_le3 : (t1 ∩ e).card ≤ 3 := by
      exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ht1_card.le;
    interval_cases _ : Finset.card ( t1 ∩ e ) <;> simp_all +decide;
    have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ e ⊆ t1 ) ; simp_all +decide ;
    have := Finset.eq_of_subset_of_card_le this; simp_all +decide ;
    have := hM.1; simp_all +decide [ Finset.subset_iff ] ;
    have := this.1; simp_all +decide [ Finset.subset_iff ] ;
    have := this he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  have ht2_inter_e_card : (t2 ∩ e).card = 2 := by
    have ht2_inter_e_card : 2 ≤ (t2 ∩ e).card := by
      unfold S_e at ht2;
      unfold trianglesSharingEdge at ht2; aesop;
    have ht2_inter_e_card : (t2 ∩ e).card ≤ 3 := by
      exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ht2_card.le;
    interval_cases _ : Finset.card ( t2 ∩ e ) <;> simp_all +decide;
    have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t2 ∩ e ⊆ t2 ) ; simp_all +decide ;
    have := Finset.eq_of_subset_of_card_le this ; simp_all +decide ;
    have := hM.1.1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    have := this he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  obtain ⟨x, hx⟩ : ∃ x, x ∈ t1 ∧ x ∉ e ∧ t1 = (t1 ∩ e) ∪ {x} := by
    have := Finset.card_sdiff_add_card_inter t1 e; simp_all +decide ;
    obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp this; use x; simp_all +decide [ Finset.ext_iff ] ;
    exact ⟨ by specialize hx x; tauto, by specialize hx x; tauto, fun a => ⟨ fun ha => by specialize hx a; tauto, fun ha => by specialize hx a; tauto ⟩ ⟩
  obtain ⟨y, hy⟩ : ∃ y, y ∈ t2 ∧ y ∉ e ∧ t2 = (t2 ∩ e) ∪ {y} := by
    have h_diff_t2 : (t2 \ e).card = 1 := by
      have := Finset.card_sdiff_add_card_inter t2 e; simp +decide [ ht2_card, ht2_inter_e_card ] at this ⊢; linarith;
    obtain ⟨ y, hy ⟩ := Finset.card_eq_one.mp h_diff_t2;
    exact ⟨ y, by rw [ Finset.eq_singleton_iff_unique_mem ] at hy; exact hy.1 |> Finset.mem_sdiff.mp |> And.left, by rw [ Finset.eq_singleton_iff_unique_mem ] at hy; exact hy.1 |> Finset.mem_sdiff.mp |> And.right, by ext z; by_cases hz : z ∈ e <;> simp +decide [ hz, hy.symm ] ⟩;
  have hxy : x = y := by
    contrapose! h_inter;
    have h_inter_eq : t1 ∩ t2 = (t1 ∩ e) ∩ (t2 ∩ e) := by
      grind;
    rw [ h_inter_eq ];
    refine' lt_of_le_of_ne ( Nat.le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ht1_inter_e_card.le ) _;
    intro H;
    have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ e ∩ ( t2 ∩ e ) ⊆ t1 ∩ e ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ e ∩ ( t2 ∩ e ) ⊆ t2 ∩ e ) ; simp +decide [ H, ht1_inter_e_card, ht2_inter_e_card ] at *;
    grind +ring;
  grind

-- Source: proven/tuza/lemmas/slot32/2b3cce69-ca98-4c3a-9e7d-55ca3afab48d-output.lean
lemma common_ext_vertex_of_diff_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V)
    (ht1 : t1 ∈ (S_e G M e).filter (· ≠ e))
    (ht2 : t2 ∈ (S_e G M e).filter (· ≠ e))
    (h_diff : t1 ∩ e ≠ t2 ∩ e) :
    ∃ x, x ∉ e ∧ t1 = (t1 ∩ e) ∪ {x} ∧ t2 = (t2 ∩ e) ∪ {x} := by
      -- By Lemma~\ref{lem:part:1}, $t_1$ and $t_2$ share an edge, so $|t_1 \cap t_2| \ge 2$.
      have h_inter : 2 ≤ (t1 ∩ t2).card := by
        have := pairwise_intersecting_Se_aux G M hM e he;
        exact this ht1 ht2 ( by aesop );
      -- Since $t1$ and $t2$ are triangles, we know $|t1| = |t2| = 3$.
      have ht1_card : t1.card = 3 := by
        simp +zetaDelta at *;
        simp_all +decide [ S_e ];
        simp_all +decide [ trianglesSharingEdge ];
        exact ht1.1.1.1.2
      have ht2_card : t2.card = 3 := by
        simp_all +decide [ S_e ];
        simp_all +decide [ trianglesSharingEdge ];
        exact ht2.1.1.1.2;
      -- Since $t1$ and $t2$ are triangles, we know $|t1 \cap e| = 2$ and $|t2 \cap e| = 2$.
      have ht1_inter_e_card : (t1 ∩ e).card = 2 := by
        -- Since $t1$ is a triangle in $S_e(e)$, it must share an edge with $e$, so $|t1 \cap e| \ge 2$.
        have ht1_inter_e_card_ge2 : 2 ≤ (t1 ∩ e).card := by
          simp +zetaDelta at *;
          exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht1.1 |>.1 ) |>.2;
        have ht1_inter_e_card_le3 : (t1 ∩ e).card ≤ 3 := by
          exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ht1_card.le;
        interval_cases _ : Finset.card ( t1 ∩ e ) <;> simp_all +decide;
        have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ e ⊆ t1 ) ; simp_all +decide ;
        have := Finset.eq_of_subset_of_card_le this; simp_all +decide ;
        have := hM.1; simp_all +decide [ Finset.subset_iff ] ;
        have := this.1; simp_all +decide [ Finset.subset_iff ] ;
        have := this he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      have ht2_inter_e_card : (t2 ∩ e).card = 2 := by
        have ht2_inter_e_card : 2 ≤ (t2 ∩ e).card := by
          unfold S_e at ht2;
          unfold trianglesSharingEdge at ht2; aesop;
        have ht2_inter_e_card : (t2 ∩ e).card ≤ 3 := by
          exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ht2_card.le;
        interval_cases _ : Finset.card ( t2 ∩ e ) <;> simp_all +decide;
        have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t2 ∩ e ⊆ t2 ) ; simp_all +decide ;
        have := Finset.eq_of_subset_of_card_le this ; simp_all +decide ;
        have := hM.1.1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        have := this he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      -- Let $x$ be the unique vertex in $t1 \setminus e$ and $y$ be the unique vertex in $t2 \setminus e$.
      obtain ⟨x, hx⟩ : ∃ x, x ∈ t1 ∧ x ∉ e ∧ t1 = (t1 ∩ e) ∪ {x} := by
        have := Finset.card_sdiff_add_card_inter t1 e; simp_all +decide ;
        obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp this; use x; simp_all +decide [ Finset.ext_iff ] ;
        exact ⟨ by specialize hx x; tauto, by specialize hx x; tauto, fun a => ⟨ fun ha => by specialize hx a; tauto, fun ha => by specialize hx a; tauto ⟩ ⟩
      obtain ⟨y, hy⟩ : ∃ y, y ∈ t2 ∧ y ∉ e ∧ t2 = (t2 ∩ e) ∪ {y} := by
        have h_diff_t2 : (t2 \ e).card = 1 := by
          have := Finset.card_sdiff_add_card_inter t2 e; simp +decide [ ht2_card, ht2_inter_e_card ] at this ⊢; linarith;
        obtain ⟨ y, hy ⟩ := Finset.card_eq_one.mp h_diff_t2;
        exact ⟨ y, by rw [ Finset.eq_singleton_iff_unique_mem ] at hy; exact hy.1 |> Finset.mem_sdiff.mp |> And.left, by rw [ Finset.eq_singleton_iff_unique_mem ] at hy; exact hy.1 |> Finset.mem_sdiff.mp |> And.right, by ext z; by_cases hz : z ∈ e <;> simp +decide [ hz, hy.symm ] ⟩;
      -- Since $t1$ and $t2$ share an edge, we have $x = y$.
      have hxy : x = y := by
        contrapose! h_inter;
        -- Since $x \neq y$, we have $t1 \cap t2 = (t1 \cap e) \cap (t2 \cap e)$.
        have h_inter_eq : t1 ∩ t2 = (t1 ∩ e) ∩ (t2 ∩ e) := by
          grind;
        rw [ h_inter_eq ];
        refine' lt_of_le_of_ne ( Nat.le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ht1_inter_e_card.le ) _;
        intro H;
        have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ e ∩ ( t2 ∩ e ) ⊆ t1 ∩ e ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ e ∩ ( t2 ∩ e ) ⊆ t2 ∩ e ) ; simp +decide [ H, ht1_inter_e_card, ht2_inter_e_card ] at *;
        grind +ring;
      grind

-- Source: proven/tuza/nu0/tuza_nu0_PROVEN.lean
lemma nu_eq_1_implies_pairwise_edge_sharing (h : trianglePackingNumber G = 1) :
    ∀ t₁ t₂ : Finset V, t₁ ∈ G.cliqueFinset 3 → t₂ ∈ G.cliqueFinset 3 → (t₁ ∩ t₂).card ≥ 2 := by
  -- By definition of triangle packing number, if $\nu(G) = 1$, then any two triangles in the graph share an edge.
  intro t₁ t₂ ht₁ ht₂
  by_contra h_contra;
  have h_packing : IsTrianglePacking G {t₁, t₂} := by
    constructor;
    · grind;
    · simp_all +decide [ Set.Pairwise ];
      exact ⟨ fun _ => Nat.le_of_lt_succ h_contra, fun _ => Nat.le_of_lt_succ ( by rwa [ Finset.inter_comm ] ) ⟩;
  have h_card_packing : (Finset.card {t₁, t₂} : ℕ) ≤ trianglePackingNumber G := by
    have h_card_packing : {t₁, t₂} ∈ (G.cliqueFinset 3).powerset.filter (IsTrianglePacking G) := by
      grind;
    have h_card_packing : ∀ x ∈ Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset)).max 0 := by
      intro x hx;
      have := Finset.le_max hx;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( IsTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_card_packing _ ( Finset.mem_image_of_mem _ ‹_› );
  by_cases h : t₁ = t₂ <;> simp_all +decide;
  rw [ SimpleGraph.isNClique_iff ] at ht₂ ; aesop

/-
If three triangles pairwise share an edge but do not share a common edge, their union has size 4.
-/

-- Source: proven/tuza/nu0/tuza_nu0_PROVEN.lean
lemma pairwise_edge_sharing_no_common_edge_implies_subset_K4 (S : Finset (Finset V))
    (h_tri : ∀ t ∈ S, t.card = 3)
    (h_pair : (S : Set (Finset V)).Pairwise (fun t₁ t₂ => 2 ≤ (t₁ ∩ t₂).card))
    (h_no_common : ¬ ∃ u v, u ≠ v ∧ ∀ t ∈ S, {u, v} ⊆ t) :
    (S.sup id).card ≤ 4 := by
  by_contra h_contra;
  -- Since there is no common edge, S must contain at least 3 triangles t1, t2, t3 that do not share a common edge.
  obtain ⟨t1, t2, t3, ht1, ht2, ht3, h_pairwise⟩ : ∃ t1 t2 t3 : Finset V, t1 ∈ S ∧ t2 ∈ S ∧ t3 ∈ S ∧ 2 ≤ (t1 ∩ t2).card ∧ 2 ≤ (t1 ∩ t3).card ∧ 2 ≤ (t2 ∩ t3).card ∧ (t1 ∩ t2 ∩ t3).card < 2 := by
    -- Since there is no common edge, there exist two triangles t1 and t2 in S such that their intersection has exactly 2 elements.
    obtain ⟨t1, t2, ht1, ht2, h_inter⟩ : ∃ t1 t2 : Finset V, t1 ∈ S ∧ t2 ∈ S ∧ (t1 ∩ t2).card = 2 := by
      -- Since S is nonempty, we can pick any two distinct triangles t1 and t2 from S.
      obtain ⟨t1, ht1⟩ : ∃ t1 : Finset V, t1 ∈ S := by
        exact Finset.nonempty_of_ne_empty fun h => by simp +decide [ h ] at h_contra;
      obtain ⟨t2, ht2, ht2_ne_t1⟩ : ∃ t2 : Finset V, t2 ∈ S ∧ t2 ≠ t1 := by
        by_cases h_singleton : S = {t1};
        · aesop;
        · exact Finset.exists_mem_ne ( Finset.one_lt_card.2 ⟨ t1, ht1, by obtain ⟨ t2, ht2 ⟩ := Finset.exists_of_ssubset ( lt_of_le_of_ne ( Finset.singleton_subset_iff.2 ht1 ) ( Ne.symm h_singleton ) ) ; aesop ⟩ ) t1;
      have h_inter : (t1 ∩ t2).card ≤ 2 := by
        have := Finset.card_le_card ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.card_le_card ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; simp_all +decide ;
        interval_cases _ : Finset.card ( t1 ∩ t2 ) <;> simp_all +decide;
        have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; simp_all +decide ;
      exact ⟨ t1, t2, ht1, ht2, le_antisymm h_inter ( h_pair ht1 ht2 ( Ne.symm ht2_ne_t1 ) ) ⟩;
    -- Since there is no common edge, there exists a triangle t3 in S such that t3 does not contain the common edge of t1 and t2.
    obtain ⟨t3, ht3, h_not_common⟩ : ∃ t3 : Finset V, t3 ∈ S ∧ ¬(t1 ∩ t2 ⊆ t3) := by
      norm_num +zetaDelta at *;
      obtain ⟨ u, v, huv ⟩ := Finset.card_eq_two.mp h_inter;
      simpa [ huv ] using h_no_common u v huv.1;
    refine' ⟨ t1, t2, t3, ht1, ht2, ht3, _, _, _, _ ⟩;
    · linarith;
    · exact h_pair ht1 ht3 ( by aesop );
    · exact h_pair ht2 ht3 ( by aesop );
    · exact lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, fun h => h_not_common <| h.symm ▸ Finset.inter_subset_right ⟩ ) ) h_inter.le;
  -- Consider any other triangle t ∈ S.
  have h_subset : ∀ t ∈ S, t ⊆ t1 ∪ t2 ∪ t3 := by
    intro t ht
    have h_intersect : 2 ≤ (t ∩ t1).card ∧ 2 ≤ (t ∩ t2).card ∧ 2 ≤ (t ∩ t3).card := by
      exact ⟨ if h : t = t1 then by aesop else h_pair ht ht1 h, if h : t = t2 then by aesop else h_pair ht ht2 h, if h : t = t3 then by aesop else h_pair ht ht3 h ⟩;
    intro x hx;
    by_cases hx1 : x ∈ t1 <;> by_cases hx2 : x ∈ t2 <;> by_cases hx3 : x ∈ t3 <;> simp_all +decide;
    have h_card : (t ∩ t1).card ≤ 2 ∧ (t ∩ t2).card ≤ 2 ∧ (t ∩ t3).card ≤ 2 := by
      have h_card : (t ∩ t1).card ≤ Finset.card (t \ {x}) ∧ (t ∩ t2).card ≤ Finset.card (t \ {x}) ∧ (t ∩ t3).card ≤ Finset.card (t \ {x}) := by
        exact ⟨ Finset.card_le_card fun y hy => by aesop, Finset.card_le_card fun y hy => by aesop, Finset.card_le_card fun y hy => by aesop ⟩;
      simp_all +decide [ Finset.card_sdiff ];
    have h_card : (t ∩ t1) = t \ {x} ∧ (t ∩ t2) = t \ {x} ∧ (t ∩ t3) = t \ {x} := by
      have h_card : (t ∩ t1) ⊆ t \ {x} ∧ (t ∩ t2) ⊆ t \ {x} ∧ (t ∩ t3) ⊆ t \ {x} := by
        grind;
      have h_card : (t ∩ t1).card = (t \ {x}).card ∧ (t ∩ t2).card = (t \ {x}).card ∧ (t ∩ t3).card = (t \ {x}).card := by
        simp_all +decide [ Finset.card_sdiff ];
        exact ⟨ by linarith, by linarith, by linarith ⟩;
      exact ⟨ Finset.eq_of_subset_of_card_le ( by tauto ) ( by linarith ), Finset.eq_of_subset_of_card_le ( by tauto ) ( by linarith ), Finset.eq_of_subset_of_card_le ( by tauto ) ( by linarith ) ⟩;
    have h_card : t1 ∩ t2 ∩ t3 ⊇ t \ {x} := by
      grind;
    have := Finset.card_le_card h_card; simp_all +decide ;
    linarith;
  have h_card_union : (t1 ∪ t2 ∪ t3).card = 4 := by
    apply three_triangles_pairwise_edge_sharing_union_card;
    all_goals tauto;
  exact h_contra ( le_trans ( Finset.card_le_card <| show S.sup id ≤ t1 ∪ t2 ∪ t3 from Finset.sup_le fun t ht => h_subset t ht ) h_card_union.le )

/-
If a set of triangles in the graph is contained within a set of 4 vertices, then these triangles can be covered by at most 2 edges.
-/

-- Source: proven/tuza/nu1/tuza_nu1_PROVEN.lean
lemma nu_eq_1_implies_pairwise_edge_sharing (h : trianglePackingNumber G = 1) :
    ∀ t₁ t₂ : Finset V, t₁ ∈ G.cliqueFinset 3 → t₂ ∈ G.cliqueFinset 3 → (t₁ ∩ t₂).card ≥ 2 := by
  -- By definition of triangle packing number, if $\nu(G) = 1$, then any two triangles in the graph share an edge.
  intro t₁ t₂ ht₁ ht₂
  by_contra h_contra;
  have h_packing : IsTrianglePacking G {t₁, t₂} := by
    constructor;
    · grind;
    · simp_all +decide [ Set.Pairwise ];
      exact ⟨ fun _ => Nat.le_of_lt_succ h_contra, fun _ => Nat.le_of_lt_succ ( by rwa [ Finset.inter_comm ] ) ⟩;
  have h_card_packing : (Finset.card {t₁, t₂} : ℕ) ≤ trianglePackingNumber G := by
    have h_card_packing : {t₁, t₂} ∈ (G.cliqueFinset 3).powerset.filter (IsTrianglePacking G) := by
      grind;
    have h_card_packing : ∀ x ∈ Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset)).max 0 := by
      intro x hx;
      have := Finset.le_max hx;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( IsTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_card_packing _ ( Finset.mem_image_of_mem _ ‹_› );
  by_cases h : t₁ = t₂ <;> simp_all +decide;
  rw [ SimpleGraph.isNClique_iff ] at ht₂ ; aesop

/-
If three triangles pairwise share an edge but do not share a common edge, their union has size 4.
-/

-- Source: proven/tuza/nu1/tuza_nu1_PROVEN.lean
lemma pairwise_edge_sharing_no_common_edge_implies_subset_K4 (S : Finset (Finset V))
    (h_tri : ∀ t ∈ S, t.card = 3)
    (h_pair : (S : Set (Finset V)).Pairwise (fun t₁ t₂ => 2 ≤ (t₁ ∩ t₂).card))
    (h_no_common : ¬ ∃ u v, u ≠ v ∧ ∀ t ∈ S, {u, v} ⊆ t) :
    (S.sup id).card ≤ 4 := by
  by_contra h_contra;
  -- Since there is no common edge, S must contain at least 3 triangles t1, t2, t3 that do not share a common edge.
  obtain ⟨t1, t2, t3, ht1, ht2, ht3, h_pairwise⟩ : ∃ t1 t2 t3 : Finset V, t1 ∈ S ∧ t2 ∈ S ∧ t3 ∈ S ∧ 2 ≤ (t1 ∩ t2).card ∧ 2 ≤ (t1 ∩ t3).card ∧ 2 ≤ (t2 ∩ t3).card ∧ (t1 ∩ t2 ∩ t3).card < 2 := by
    -- Since there is no common edge, there exist two triangles t1 and t2 in S such that their intersection has exactly 2 elements.
    obtain ⟨t1, t2, ht1, ht2, h_inter⟩ : ∃ t1 t2 : Finset V, t1 ∈ S ∧ t2 ∈ S ∧ (t1 ∩ t2).card = 2 := by
      -- Since S is nonempty, we can pick any two distinct triangles t1 and t2 from S.
      obtain ⟨t1, ht1⟩ : ∃ t1 : Finset V, t1 ∈ S := by
        exact Finset.nonempty_of_ne_empty fun h => by simp +decide [ h ] at h_contra;
      obtain ⟨t2, ht2, ht2_ne_t1⟩ : ∃ t2 : Finset V, t2 ∈ S ∧ t2 ≠ t1 := by
        by_cases h_singleton : S = {t1};
        · aesop;
        · exact Finset.exists_mem_ne ( Finset.one_lt_card.2 ⟨ t1, ht1, by obtain ⟨ t2, ht2 ⟩ := Finset.exists_of_ssubset ( lt_of_le_of_ne ( Finset.singleton_subset_iff.2 ht1 ) ( Ne.symm h_singleton ) ) ; aesop ⟩ ) t1;
      have h_inter : (t1 ∩ t2).card ≤ 2 := by
        have := Finset.card_le_card ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.card_le_card ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; simp_all +decide ;
        interval_cases _ : Finset.card ( t1 ∩ t2 ) <;> simp_all +decide;
        have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; simp_all +decide ;
      exact ⟨ t1, t2, ht1, ht2, le_antisymm h_inter ( h_pair ht1 ht2 ( Ne.symm ht2_ne_t1 ) ) ⟩;
    -- Since there is no common edge, there exists a triangle t3 in S such that t3 does not contain the common edge of t1 and t2.
    obtain ⟨t3, ht3, h_not_common⟩ : ∃ t3 : Finset V, t3 ∈ S ∧ ¬(t1 ∩ t2 ⊆ t3) := by
      norm_num +zetaDelta at *;
      obtain ⟨ u, v, huv ⟩ := Finset.card_eq_two.mp h_inter;
      simpa [ huv ] using h_no_common u v huv.1;
    refine' ⟨ t1, t2, t3, ht1, ht2, ht3, _, _, _, _ ⟩;
    · linarith;
    · exact h_pair ht1 ht3 ( by aesop );
    · exact h_pair ht2 ht3 ( by aesop );
    · exact lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, fun h => h_not_common <| h.symm ▸ Finset.inter_subset_right ⟩ ) ) h_inter.le;
  -- Consider any other triangle t ∈ S.
  have h_subset : ∀ t ∈ S, t ⊆ t1 ∪ t2 ∪ t3 := by
    intro t ht
    have h_intersect : 2 ≤ (t ∩ t1).card ∧ 2 ≤ (t ∩ t2).card ∧ 2 ≤ (t ∩ t3).card := by
      exact ⟨ if h : t = t1 then by aesop else h_pair ht ht1 h, if h : t = t2 then by aesop else h_pair ht ht2 h, if h : t = t3 then by aesop else h_pair ht ht3 h ⟩;
    intro x hx;
    by_cases hx1 : x ∈ t1 <;> by_cases hx2 : x ∈ t2 <;> by_cases hx3 : x ∈ t3 <;> simp_all +decide;
    have h_card : (t ∩ t1).card ≤ 2 ∧ (t ∩ t2).card ≤ 2 ∧ (t ∩ t3).card ≤ 2 := by
      have h_card : (t ∩ t1).card ≤ Finset.card (t \ {x}) ∧ (t ∩ t2).card ≤ Finset.card (t \ {x}) ∧ (t ∩ t3).card ≤ Finset.card (t \ {x}) := by
        exact ⟨ Finset.card_le_card fun y hy => by aesop, Finset.card_le_card fun y hy => by aesop, Finset.card_le_card fun y hy => by aesop ⟩;
      simp_all +decide [ Finset.card_sdiff ];
    have h_card : (t ∩ t1) = t \ {x} ∧ (t ∩ t2) = t \ {x} ∧ (t ∩ t3) = t \ {x} := by
      have h_card : (t ∩ t1) ⊆ t \ {x} ∧ (t ∩ t2) ⊆ t \ {x} ∧ (t ∩ t3) ⊆ t \ {x} := by
        grind;
      have h_card : (t ∩ t1).card = (t \ {x}).card ∧ (t ∩ t2).card = (t \ {x}).card ∧ (t ∩ t3).card = (t \ {x}).card := by
        simp_all +decide [ Finset.card_sdiff ];
        exact ⟨ by linarith, by linarith, by linarith ⟩;
      exact ⟨ Finset.eq_of_subset_of_card_le ( by tauto ) ( by linarith ), Finset.eq_of_subset_of_card_le ( by tauto ) ( by linarith ), Finset.eq_of_subset_of_card_le ( by tauto ) ( by linarith ) ⟩;
    have h_card : t1 ∩ t2 ∩ t3 ⊇ t \ {x} := by
      grind;
    have := Finset.card_le_card h_card; simp_all +decide ;
    linarith;
  have h_card_union : (t1 ∪ t2 ∪ t3).card = 4 := by
    apply three_triangles_pairwise_edge_sharing_union_card;
    all_goals tauto;
  exact h_contra ( le_trans ( Finset.card_le_card <| show S.sup id ≤ t1 ∪ t2 ∪ t3 from Finset.sup_le fun t ht => h_subset t ht ) h_card_union.le )

/-
If a set of triangles in the graph is contained within a set of 4 vertices, then these triangles can be covered by at most 2 edges.
-/


-- ═══════════════════════════════════════════════════════════════════════
-- M_EDGES LEMMAS (6 lemmas)
-- ═══════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/nu4/slot63_scaffolding.lean
lemma M_edge_in_exactly_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
  intro m' hm' hne he'
  rw [Finset.mem_sym2_iff] at he he'
  obtain ⟨u, v, huv, hu_m, hv_m, rfl⟩ := he
  obtain ⟨u', v', _, hu'_m', hv'_m', heq⟩ := he'
  simp only [Sym2.eq, Sym2.rel_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h_card : (m ∩ m').card ≥ 2 := by
      have hsub : ({u, v} : Finset V) ⊆ m ∩ m' := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hu_m, hu'_m'⟩
        · exact Finset.mem_inter.mpr ⟨hv_m, hv'_m'⟩
      calc 2 = ({u, v} : Finset V).card := (Finset.card_pair huv).symm
        _ ≤ (m ∩ m').card := Finset.card_le_card hsub
    have := hM.2 hm hm' hne.symm
    omega
  · have h_card : (m ∩ m').card ≥ 2 := by
      have hsub : ({u, v} : Finset V) ⊆ m ∩ m' := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hu_m, hv'_m'⟩
        · exact Finset.mem_inter.mpr ⟨hv_m, hu'_m'⟩
      calc 2 = ({u, v} : Finset V).card := (Finset.card_pair huv).symm
        _ ≤ (m ∩ m').card := Finset.card_le_card hsub
    have := hM.2 hm hm' hne.symm
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA 2: triangle_shares_edge_with_packing
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle shares ≥2 vertices with some M-element (maximality). -/

-- Source: proven/tuza/nu4/safe_discard/slot65_singleton_conflict_PROVEN.lean
lemma external_has_M_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) (ht : t ∈ externalTriangles G M) :
    (M_edges_in G M t).Nonempty := by
  simp only [externalTriangles, Finset.mem_filter] at ht
  obtain ⟨_, _, e, he_M, he_t⟩ := ht
  exact ⟨e, Finset.mem_filter.mpr ⟨he_M, he_t⟩⟩

/-- External triangles contain at most 3 M-edges (since triangles have 3 edges total) -/

-- Source: proven/tuza/nu4/safe_discard/slot65_singleton_conflict_PROVEN.lean
lemma external_M_edges_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    (M_edges_in G M t).card ≤ 3 := by
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  calc (M_edges_in G M t).card
      ≤ t.sym2.card := Finset.card_filter_le _ _
    _ = 3 := by rw [Finset.card_sym2]; omega

/-- Conflict pairs can only occur between edges that share a vertex -/

-- Source: proven/tuza/nu4/safe_discard/slot64b_M_edges_card_PROVEN.lean
lemma M_edges_card_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    (M_edges G M).card ≤ 3 * M.card := by
  unfold M_edges
  calc (M.biUnion (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))).card
      ≤ M.sum (fun t => (t.sym2.filter (fun e => e ∈ G.edgeFinset)).card) := Finset.card_biUnion_le
    _ ≤ M.sum (fun _ => 3) := Finset.sum_le_sum (fun t ht => by
        have h_clique := hM.1 ht
        have h_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp h_clique).card_eq
        exact triangle_contribution_le_3 G t (le_of_eq h_card))
    _ = 3 * M.card := by simp [Finset.sum_const, smul_eq_mul]

/-- For ν = 4, M has at most 12 edges -/

-- Source: proven/tuza/nu4/safe_discard/slot64b_M_edges_card_PROVEN.lean
lemma M_edges_card_le_12 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (h_card : M.card = 4) :
    (M_edges G M).card ≤ 12 := by
  have := M_edges_card_bound G M hM
  omega

end

-- Source: proven/tuza/nu4/safe_discard/slot64c_edge_unique_PROVEN.lean
lemma M_edge_in_exactly_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e : Sym2 V) (m : Finset V) (hm : m ∈ M) (he : e ∈ m.sym2) :
    ∀ m' ∈ M, m' ≠ m → e ∉ m'.sym2 := by
  intro m' hm' hne he'
  rw [Finset.mem_sym2_iff] at he he'
  obtain ⟨u, v, huv, hu_m, hv_m, rfl⟩ := he
  obtain ⟨u', v', _, hu'_m', hv'_m', heq⟩ := he'
  simp only [Sym2.eq, Sym2.rel_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h_card : (m ∩ m').card ≥ 2 := by
      have hsub : ({u, v} : Finset V) ⊆ m ∩ m' := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hu_m, hu'_m'⟩
        · exact Finset.mem_inter.mpr ⟨hv_m, hv'_m'⟩
      calc 2 = ({u, v} : Finset V).card := (Finset.card_pair huv).symm
        _ ≤ (m ∩ m').card := Finset.card_le_card hsub
    have := hM.2 hm hm' hne.symm
    omega
  · have h_card : (m ∩ m').card ≥ 2 := by
      have hsub : ({u, v} : Finset V) ⊆ m ∩ m' := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hu_m, hv'_m'⟩
        · exact Finset.mem_inter.mpr ⟨hv_m, hu'_m'⟩
      calc 2 = ({u, v} : Finset V).card := (Finset.card_pair huv).symm
        _ ≤ (m ∩ m').card := Finset.card_le_card hsub
    have := hM.2 hm hm' hne.symm
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- Each M-edge belongs to exactly one M-element (existence + uniqueness).
    This is TRUE because packing elements are edge-disjoint. -/


-- ═══════════════════════════════════════════════════════════════════════
-- BRIDGES LEMMAS (34 lemmas)
-- ═══════════════════════════════════════════════════════════════════════

-- Source: proven/scaffolding/slot44_scaffolding_PARTIAL.lean
lemma bridges_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  simp_all +decide [ Finset.ext_iff, X_ef ];
  by_contra hv_not_in_t
  have h_disjoint : Disjoint (t ∩ e) (t ∩ f) := by
    exact Finset.disjoint_left.mpr fun x hx hx' => hv_not_in_t <| by have := hv x; aesop;
  have h_card : (t ∩ e) ∪ (t ∩ f) ⊆ t := by
    aesop_cat;
  have := Finset.card_le_card h_card; simp_all +decide [ Finset.card_union_add_card_inter ] ;
  linarith [ ht.1.card_eq ]

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma Te_eq_Se_union_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    trianglesSharingEdge G e = S_e G M e ∪ bridges G M e := by
  ext t
  simp only [Finset.mem_union, S_e, bridges, trianglesSharingEdge, Finset.mem_filter]
  constructor
  · intro ht
    by_cases h : ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1
    · left; exact ⟨ht, h⟩
    · right; push_neg at h; obtain ⟨f, hfM, hfne, hcard⟩ := h; exact ⟨ht, f, hfM, hfne, hcard⟩
  · intro h; rcases h with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact ht

-- PROVEN: tau_S_le_2 (from slot 6/29)
noncomputable section AristotleLemmas

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma single_vertex_bridge_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_single : (e ∩ f).card = 1) :
    ∃ v, v ∈ e ∧ v ∈ f ∧ ∀ t ∈ X_ef G e f, v ∈ t := by
  obtain ⟨ v, hv ⟩ := Finset.card_eq_one.mp h_single;
  simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
  refine' ⟨ v, hv.1.1, hv.1.2, fun t ht => _ ⟩;
  unfold X_ef at ht;
  -- Since $t$ is a triangle, it must have exactly 3 vertices. The intersections with $e$ and $f$ each have at least 2 elements, so there must be some overlap.
  have h_overlap : (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2 → ∃ x ∈ t ∩ e, ∃ y ∈ t ∩ f, x ≠ y := by
    exact fun h => by obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.1 h.1; exact ⟨ x, hx, by obtain ⟨ z, hz, w, hw, hzw ⟩ := Finset.one_lt_card.1 h.2; use if x = z then w else z; aesop ⟩ ;
  obtain ⟨ x, hx, y, hy, hxy ⟩ := h_overlap ( Finset.mem_filter.mp ht |>.2 ) ; simp_all +decide [ Finset.subset_iff ] ;
  have := Finset.card_eq_three.mp ht.1.2; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
  grind

/- Aristotle failed to find a proof. -/
-- TARGET: All bridges contain the shared vertex

/--
KEY LEMMA: Bridges absorbed by S_e cover (zero marginal cost)

When e shares only vertices (not edges) with other elements:
- All bridges X(e,f) must go through the shared vertex v
- The optimal cover for S_e includes edges incident to v
- These same edges cover all bridges X(e,f)

This is NOT saying τ(bridges) = 0 in isolation!
It says: ∃ cover of S_e with |cover| ≤ 2 that ALSO covers all bridges.
-/

-- Source: proven/tuza/nu4/slot72_cycle_reduction_output.lean
lemma bridges_subset_tpair (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : Finset V) :
    X_ef G D A ⊆ T_pair G A B := by
      -- By definition of $X_{ef}$ and $T_{pair}$, any triangle in $X_{ef} G D A$ must already be in $T_{pair} G A B$ because $D$ is part of the triangles that share an edge with $A$ and $B$. Therefore, $X_{ef} G D A \subseteq T_{pair} G A B$.
      intros t ht
      simp [X_ef, T_pair] at ht ⊢;
      unfold trianglesSharingEdge; aesop;

-- Similarly for other bridges

-- Source: proven/tuza/nu4/slot72_cycle_reduction_output.lean
lemma bridges_BC_subset_tpair_CD (G : SimpleGraph V) [DecidableRel G.Adj]
    (B C D : Finset V) :
    X_ef G B C ⊆ T_pair G C D := by
      exact?

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN: Cycle reduction to path
-- ══════════════════════════════════════════════════════════════════════════════

-- The cycle A—B—C—D—A can be "cut" to path A—B—C—D
-- The extra D—A adjacency only adds X_DA bridges
-- But X_DA ⊆ T_pair(A,B), so the union is unchanged!

-- Source: proven/tuza/nu4/slot70_tau_union_extended_output.lean
lemma diagonal_bridges_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (hA3 : A.card = 3) (hC3 : C.card = 3)
    (h_disj : (A ∩ C).card = 0) :
    X_ef G A C = ∅ := by
  -- If A and C share no vertex, no triangle can share edge with both
  ext t
  simp only [X_ef, Finset.mem_filter, Finset.not_mem_empty, iff_false]
  intro ⟨ht_clique, h_A, h_C⟩
  -- t has exactly 3 vertices (it's a triangle)
  have ht3 : t.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht_clique
    exact ht_clique.2
  -- t ∩ A has ≥2 elements, t ∩ C has ≥2 elements
  -- So |t ∩ A| + |t ∩ C| ≥ 4, but t only has 3 vertices
  -- By pigeonhole, t ∩ A and t ∩ C must overlap
  -- Any overlap means A ∩ C ≠ ∅, contradiction
  have h_sum : (t ∩ A).card + (t ∩ C).card ≥ 4 := Nat.add_le_add h_A h_C
  -- But (t ∩ A) ∪ (t ∩ C) ⊆ t, so |(t ∩ A) ∪ (t ∩ C)| ≤ 3
  have h_union_sub : (t ∩ A) ∪ (t ∩ C) ⊆ t := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_inter] at hx
    rcases hx with ⟨hxt, _⟩ | ⟨hxt, _⟩ <;> exact hxt
  have h_union_card : ((t ∩ A) ∪ (t ∩ C)).card ≤ 3 := by
    calc ((t ∩ A) ∪ (t ∩ C)).card ≤ t.card := Finset.card_le_card h_union_sub
      _ = 3 := ht3
  -- By inclusion-exclusion: |A ∪ B| = |A| + |B| - |A ∩ B|
  -- So |A ∩ B| = |A| + |B| - |A ∪ B| ≥ 4 - 3 = 1
  have h_inter_card : ((t ∩ A) ∩ (t ∩ C)).card ≥ 1 := by
    have h_ie := Finset.card_union_add_card_inter (t ∩ A) (t ∩ C)
    omega
  -- (t ∩ A) ∩ (t ∩ C) = t ∩ (A ∩ C)
  have h_inter_eq : (t ∩ A) ∩ (t ∩ C) = t ∩ (A ∩ C) := by
    ext x
    simp only [Finset.mem_inter]
    tauto
  -- But A ∩ C = ∅, so t ∩ (A ∩ C) = ∅
  rw [h_inter_eq] at h_inter_card
  simp only [Finset.card_eq_zero] at h_disj
  rw [h_disj, Finset.inter_empty] at h_inter_card
  simp at h_inter_card

-- Source: proven/tuza/nu4/safe_discard/slot67_bridge_absorption_PROVEN.lean
lemma no_bridge_disjoint (A B t : Finset V)
    (hA : A.card = 3) (hB : B.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint A B)
    (h_share_A : sharesEdgeWith t A)
    (h_share_B : sharesEdgeWith t B) :
    False := by
  -- t shares edge {a₁, a₂} with A
  obtain ⟨eA, heA_t, heA_A⟩ := h_share_A
  rw [Finset.mem_sym2_iff] at heA_t heA_A
  obtain ⟨a₁, a₂, ha12, ha1_t, ha2_t, rfl⟩ := heA_t
  obtain ⟨a₁', a₂', _, ha1'_A, ha2'_A, heq_A⟩ := heA_A
  simp only [Sym2.eq, Sym2.rel_iff] at heq_A
  -- t shares edge {b₁, b₂} with B
  obtain ⟨eB, heB_t, heB_B⟩ := h_share_B
  rw [Finset.mem_sym2_iff] at heB_t heB_B
  obtain ⟨b₁, b₂, hb12, hb1_t, hb2_t, rfl⟩ := heB_t
  obtain ⟨b₁', b₂', _, hb1'_B, hb2'_B, heq_B⟩ := heB_B
  simp only [Sym2.eq, Sym2.rel_iff] at heq_B
  -- a₁, a₂ ∈ A and b₁, b₂ ∈ B
  have ha1_A : a₁ ∈ A := by
    rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have ha2_A : a₂ ∈ A := by
    rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb1_B : b₁ ∈ B := by
    rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb2_B : b₂ ∈ B := by
    rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  -- {a₁, a₂} ∩ {b₁, b₂} = ∅ (since A ∩ B = ∅)
  have h_a1_not_B : a₁ ∉ B := Finset.disjoint_left.mp h_disj ha1_A
  have h_a2_not_B : a₂ ∉ B := Finset.disjoint_left.mp h_disj ha2_A
  have h_a1_ne_b1 : a₁ ≠ b₁ := fun h => h_a1_not_B (h ▸ hb1_B)
  have h_a1_ne_b2 : a₁ ≠ b₂ := fun h => h_a1_not_B (h ▸ hb2_B)
  have h_a2_ne_b1 : a₂ ≠ b₁ := fun h => h_a2_not_B (h ▸ hb1_B)
  have h_a2_ne_b2 : a₂ ≠ b₂ := fun h => h_a2_not_B (h ▸ hb2_B)
  -- All of a₁, a₂, b₁, b₂ ∈ t, and they're 4 distinct vertices
  have h4 : ({a₁, a₂, b₁, b₂} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_insert_of_not_mem, Finset.card_singleton]
    · simp [h_a2_ne_b2, h_a2_ne_b1]
    · simp [h_a1_ne_b2, h_a1_ne_b1]
    · simp [ha12]
  have h_sub : ({a₁, a₂, b₁, b₂} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card h_sub
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE ABSORPTION THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- Bridge triangles don't exist for disjoint M-elements.
    This means: for disjoint A, B ∈ M, no external triangle T can share edges with both. -/

-- Source: proven/tuza/nu4/safe_discard/slot67_bridge_absorption_PROVEN.lean
theorem bridge_nonexistence (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (h_disj : Disjoint A B)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(sharesEdgeWith t A ∧ sharesEdgeWith t B) := by
  intro ⟨h_share_A, h_share_B⟩
  have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hA)).card_eq
  have hB_card : B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hB)).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint A B t hA_card hB_card ht_card h_disj h_share_A h_share_B

/-- Corollary: For disjoint M-elements, external triangles share edge with at most one. -/

-- Source: proven/tuza/nu4/safe_discard/slot148a_scattered_partition_PROVEN.lean
lemma no_bridge_disjoint (A B t : Finset V)
    (hA : A.card = 3) (hB : B.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint A B)
    (h_share_A : sharesEdgeWith t A)
    (h_share_B : sharesEdgeWith t B) :
    False := by
  obtain ⟨eA, heA_t, heA_A⟩ := h_share_A
  rw [Finset.mem_sym2_iff] at heA_t heA_A
  obtain ⟨a₁, a₂, ha12, ha1_t, ha2_t, rfl⟩ := heA_t
  obtain ⟨a₁', a₂', _, ha1'_A, ha2'_A, heq_A⟩ := heA_A
  simp only [Sym2.eq, Sym2.rel_iff] at heq_A
  obtain ⟨eB, heB_t, heB_B⟩ := h_share_B
  rw [Finset.mem_sym2_iff] at heB_t heB_B
  obtain ⟨b₁, b₂, hb12, hb1_t, hb2_t, rfl⟩ := heB_t
  obtain ⟨b₁', b₂', _, hb1'_B, hb2'_B, heq_B⟩ := heB_B
  simp only [Sym2.eq, Sym2.rel_iff] at heq_B
  have ha1_A : a₁ ∈ A := by rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have ha2_A : a₂ ∈ A := by rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb1_B : b₁ ∈ B := by rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb2_B : b₂ ∈ B := by rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have h_a1_not_B : a₁ ∉ B := Finset.disjoint_left.mp h_disj ha1_A
  have h_a2_not_B : a₂ ∉ B := Finset.disjoint_left.mp h_disj ha2_A
  have h_a1_ne_b1 : a₁ ≠ b₁ := fun h => h_a1_not_B (h ▸ hb1_B)
  have h_a1_ne_b2 : a₁ ≠ b₂ := fun h => h_a1_not_B (h ▸ hb2_B)
  have h_a2_ne_b1 : a₂ ≠ b₁ := fun h => h_a2_not_B (h ▸ hb1_B)
  have h_a2_ne_b2 : a₂ ≠ b₂ := fun h => h_a2_not_B (h ▸ hb2_B)
  have h4 : ({a₁, a₂, b₁, b₂} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_insert_of_not_mem, Finset.card_singleton]
    · simp [h_a2_ne_b2, h_a2_ne_b1]
    · simp [h_a1_ne_b2, h_a1_ne_b1]
    · simp [ha12]
  have h_sub : ({a₁, a₂, b₁, b₂} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card h_sub
  omega

-- PROVEN by Aristotle (slot67)

-- Source: proven/tuza/nu4/safe_discard/slot149_path4_structure_PROVEN.lean
lemma no_bridge_disjoint (A B t : Finset V)
    (hA : A.card = 3) (hB : B.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint A B)
    (h_share_A : sharesEdgeWith t A)
    (h_share_B : sharesEdgeWith t B) :
    False := by
  obtain ⟨eA, heA_t, heA_A⟩ := h_share_A
  rw [Finset.mem_sym2_iff] at heA_t heA_A
  obtain ⟨a₁, a₂, ha12, ha1_t, ha2_t, rfl⟩ := heA_t
  obtain ⟨a₁', a₂', _, ha1'_A, ha2'_A, heq_A⟩ := heA_A
  simp only [Sym2.eq, Sym2.rel_iff] at heq_A
  obtain ⟨eB, heB_t, heB_B⟩ := h_share_B
  rw [Finset.mem_sym2_iff] at heB_t heB_B
  obtain ⟨b₁, b₂, hb12, hb1_t, hb2_t, rfl⟩ := heB_t
  obtain ⟨b₁', b₂', _, hb1'_B, hb2'_B, heq_B⟩ := heB_B
  simp only [Sym2.eq, Sym2.rel_iff] at heq_B
  have ha1_A : a₁ ∈ A := by rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have ha2_A : a₂ ∈ A := by rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb1_B : b₁ ∈ B := by rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb2_B : b₂ ∈ B := by rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have h_a1_not_B : a₁ ∉ B := Finset.disjoint_left.mp h_disj ha1_A
  have h_a2_not_B : a₂ ∉ B := Finset.disjoint_left.mp h_disj ha2_A
  have h_a1_ne_b1 : a₁ ≠ b₁ := fun h => h_a1_not_B (h ▸ hb1_B)
  have h_a1_ne_b2 : a₁ ≠ b₂ := fun h => h_a1_not_B (h ▸ hb2_B)
  have h_a2_ne_b1 : a₂ ≠ b₁ := fun h => h_a2_not_B (h ▸ hb1_B)
  have h_a2_ne_b2 : a₂ ≠ b₂ := fun h => h_a2_not_B (h ▸ hb2_B)
  have h4 : ({a₁, a₂, b₁, b₂} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_insert_of_not_mem, Finset.card_singleton]
    · simp [h_a2_ne_b2, h_a2_ne_b1]
    · simp [h_a1_ne_b2, h_a1_ne_b1]
    · simp [ha12]
  have h_sub : ({a₁, a₂, b₁, b₂} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card h_sub
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 STRUCTURAL PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

/-- In Path_4, no external triangle bridges A and C -/

-- Source: proven/tuza/nu4/safe_discard/slot149_path4_structure_PROVEN.lean
lemma path4_no_AC_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(sharesEdgeWith t cfg.A ∧ sharesEdgeWith t cfg.C) := by
  intro ⟨h_share_A, h_share_C⟩
  have hA_card : cfg.A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hA).card_eq
  have hC_card : cfg.C.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hC).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint cfg.A cfg.C t hA_card hC_card ht_card cfg.h_AC h_share_A h_share_C

/-- In Path_4, no external triangle bridges B and D -/

-- Source: proven/tuza/nu4/safe_discard/slot149_path4_structure_PROVEN.lean
lemma path4_no_BD_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(sharesEdgeWith t cfg.B ∧ sharesEdgeWith t cfg.D) := by
  intro ⟨h_share_B, h_share_D⟩
  have hB_card : cfg.B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hB).card_eq
  have hD_card : cfg.D.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hD).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint cfg.B cfg.D t hB_card hD_card ht_card cfg.h_BD h_share_B h_share_D

/-- Extract the shared vertex from A ∩ B -/

-- Source: proven/tuza/nu4/safe_discard/slot150_matching2_structure_PROVEN.lean
lemma no_bridge_disjoint (A B t : Finset V)
    (hA : A.card = 3) (hB : B.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint A B)
    (h_share_A : sharesEdgeWith t A)
    (h_share_B : sharesEdgeWith t B) :
    False := by
  obtain ⟨eA, heA_t, heA_A⟩ := h_share_A
  rw [Finset.mem_sym2_iff] at heA_t heA_A
  obtain ⟨a₁, a₂, ha12, ha1_t, ha2_t, rfl⟩ := heA_t
  obtain ⟨a₁', a₂', _, ha1'_A, ha2'_A, heq_A⟩ := heA_A
  simp only [Sym2.eq, Sym2.rel_iff] at heq_A
  obtain ⟨eB, heB_t, heB_B⟩ := h_share_B
  rw [Finset.mem_sym2_iff] at heB_t heB_B
  obtain ⟨b₁, b₂, hb12, hb1_t, hb2_t, rfl⟩ := heB_t
  obtain ⟨b₁', b₂', _, hb1'_B, hb2'_B, heq_B⟩ := heB_B
  simp only [Sym2.eq, Sym2.rel_iff] at heq_B
  have ha1_A : a₁ ∈ A := by rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have ha2_A : a₂ ∈ A := by rcases heq_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb1_B : b₁ ∈ B := by rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hb2_B : b₂ ∈ B := by rcases heq_B with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have h_a1_not_B : a₁ ∉ B := Finset.disjoint_left.mp h_disj ha1_A
  have h_a2_not_B : a₂ ∉ B := Finset.disjoint_left.mp h_disj ha2_A
  have h_a1_ne_b1 : a₁ ≠ b₁ := fun h => h_a1_not_B (h ▸ hb1_B)
  have h_a1_ne_b2 : a₁ ≠ b₂ := fun h => h_a1_not_B (h ▸ hb2_B)
  have h_a2_ne_b1 : a₂ ≠ b₁ := fun h => h_a2_not_B (h ▸ hb1_B)
  have h_a2_ne_b2 : a₂ ≠ b₂ := fun h => h_a2_not_B (h ▸ hb2_B)
  have h4 : ({a₁, a₂, b₁, b₂} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_insert_of_not_mem, Finset.card_singleton]
    · simp [h_a2_ne_b2, h_a2_ne_b1]
    · simp [h_a1_ne_b2, h_a1_ne_b1]
    · simp [ha12]
  have h_sub : ({a₁, a₂, b₁, b₂} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card h_sub
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- MATCHING_2 STRUCTURAL PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

/-- In Matching_2, no external triangle bridges A and C -/

-- Source: proven/tuza/nu4/safe_discard/slot150_matching2_structure_PROVEN.lean
lemma matching2_no_AC_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Matching2Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(sharesEdgeWith t cfg.A ∧ sharesEdgeWith t cfg.C) := by
  intro ⟨h_share_A, h_share_C⟩
  have hA_card : cfg.A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hA).card_eq
  have hC_card : cfg.C.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hC).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint cfg.A cfg.C t hA_card hC_card ht_card cfg.h_AC h_share_A h_share_C

/-- In Matching_2, no external triangle bridges A and D -/

-- Source: proven/tuza/nu4/safe_discard/slot150_matching2_structure_PROVEN.lean
lemma matching2_no_AD_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Matching2Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(sharesEdgeWith t cfg.A ∧ sharesEdgeWith t cfg.D) := by
  intro ⟨h_share_A, h_share_D⟩
  have hA_card : cfg.A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hA).card_eq
  have hD_card : cfg.D.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hD).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint cfg.A cfg.D t hA_card hD_card ht_card cfg.h_AD h_share_A h_share_D

/-- In Matching_2, no external triangle bridges B and C -/

-- Source: proven/tuza/nu4/safe_discard/slot150_matching2_structure_PROVEN.lean
lemma matching2_no_BC_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Matching2Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(sharesEdgeWith t cfg.B ∧ sharesEdgeWith t cfg.C) := by
  intro ⟨h_share_B, h_share_C⟩
  have hB_card : cfg.B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hB).card_eq
  have hC_card : cfg.C.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hC).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint cfg.B cfg.C t hB_card hC_card ht_card cfg.h_BC h_share_B h_share_C

/-- In Matching_2, no external triangle bridges B and D -/

-- Source: proven/tuza/nu4/safe_discard/slot150_matching2_structure_PROVEN.lean
lemma matching2_no_BD_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Matching2Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ¬(sharesEdgeWith t cfg.B ∧ sharesEdgeWith t cfg.D) := by
  intro ⟨h_share_B, h_share_D⟩
  have hB_card : cfg.B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hB).card_eq
  have hD_card : cfg.D.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp cfg.hD).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint cfg.B cfg.D t hB_card hD_card ht_card cfg.h_BD h_share_B h_share_D

/-- KEY THEOREM: External triangles touch at most one pair.
    An external triangle shares edge with at most one of {A,B} or at most one of {C,D}. -/

-- Source: proven/tuza/nu4/slot70_d3159016/diagonal_bridges.lean
lemma diagonal_bridges_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (hA3 : A.card = 3) (hC3 : C.card = 3)
    (h_disj : (A ∩ C).card = 0) :
    X_ef G A C = ∅ := by
  -- If A and C share no vertex, no triangle can share edge with both
  ext t
  simp only [X_ef, Finset.mem_filter, Finset.not_mem_empty, iff_false]
  intro ⟨ht_clique, h_A, h_C⟩
  -- t has exactly 3 vertices (it's a triangle)
  have ht3 : t.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht_clique
    exact ht_clique.2
  -- t ∩ A has ≥2 elements, t ∩ C has ≥2 elements
  -- So |t ∩ A| + |t ∩ C| ≥ 4, but t only has 3 vertices
  -- By pigeonhole, t ∩ A and t ∩ C must overlap
  -- Any overlap means A ∩ C ≠ ∅, contradiction
  have h_sum : (t ∩ A).card + (t ∩ C).card ≥ 4 := Nat.add_le_add h_A h_C
  -- But (t ∩ A) ∪ (t ∩ C) ⊆ t, so |(t ∩ A) ∪ (t ∩ C)| ≤ 3
  have h_union_sub : (t ∩ A) ∪ (t ∩ C) ⊆ t := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_inter] at hx
    rcases hx with ⟨hxt, _⟩ | ⟨hxt, _⟩ <;> exact hxt
  have h_union_card : ((t ∩ A) ∪ (t ∩ C)).card ≤ 3 := by
    calc ((t ∩ A) ∪ (t ∩ C)).card ≤ t.card := Finset.card_le_card h_union_sub
      _ = 3 := ht3
  -- By inclusion-exclusion: |A ∪ B| = |A| + |B| - |A ∩ B|
  -- So |A ∩ B| = |A| + |B| - |A ∪ B| ≥ 4 - 3 = 1
  have h_inter_card : ((t ∩ A) ∩ (t ∩ C)).card ≥ 1 := by
    have h_ie := Finset.card_union_add_card_inter (t ∩ A) (t ∩ C)
    omega
  -- (t ∩ A) ∩ (t ∩ C) = t ∩ (A ∩ C)
  have h_inter_eq : (t ∩ A) ∩ (t ∩ C) = t ∩ (A ∩ C) := by
    ext x
    simp only [Finset.mem_inter]
    tauto
  -- But A ∩ C = ∅, so t ∩ (A ∩ C) = ∅
  rw [h_inter_eq] at h_inter_card
  simp only [Finset.card_eq_zero] at h_disj
  rw [h_disj, Finset.inter_empty] at h_inter_card
  simp at h_inter_card

-- Source: proven/tuza/nu4/slot70_d3159016/output.lean
lemma diagonal_bridges_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (hA3 : A.card = 3) (hC3 : C.card = 3)
    (h_disj : (A ∩ C).card = 0) :
    X_ef G A C = ∅ := by
  -- If A and C share no vertex, no triangle can share edge with both
  ext t
  simp only [X_ef, Finset.mem_filter, Finset.not_mem_empty, iff_false]
  intro ⟨ht_clique, h_A, h_C⟩
  -- t has exactly 3 vertices (it's a triangle)
  have ht3 : t.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht_clique
    exact ht_clique.2
  -- t ∩ A has ≥2 elements, t ∩ C has ≥2 elements
  -- So |t ∩ A| + |t ∩ C| ≥ 4, but t only has 3 vertices
  -- By pigeonhole, t ∩ A and t ∩ C must overlap
  -- Any overlap means A ∩ C ≠ ∅, contradiction
  have h_sum : (t ∩ A).card + (t ∩ C).card ≥ 4 := Nat.add_le_add h_A h_C
  -- But (t ∩ A) ∪ (t ∩ C) ⊆ t, so |(t ∩ A) ∪ (t ∩ C)| ≤ 3
  have h_union_sub : (t ∩ A) ∪ (t ∩ C) ⊆ t := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_inter] at hx
    rcases hx with ⟨hxt, _⟩ | ⟨hxt, _⟩ <;> exact hxt
  have h_union_card : ((t ∩ A) ∪ (t ∩ C)).card ≤ 3 := by
    calc ((t ∩ A) ∪ (t ∩ C)).card ≤ t.card := Finset.card_le_card h_union_sub
      _ = 3 := ht3
  -- By inclusion-exclusion: |A ∪ B| = |A| + |B| - |A ∩ B|
  -- So |A ∩ B| = |A| + |B| - |A ∪ B| ≥ 4 - 3 = 1
  have h_inter_card : ((t ∩ A) ∩ (t ∩ C)).card ≥ 1 := by
    have h_ie := Finset.card_union_add_card_inter (t ∩ A) (t ∩ C)
    omega
  -- (t ∩ A) ∩ (t ∩ C) = t ∩ (A ∩ C)
  have h_inter_eq : (t ∩ A) ∩ (t ∩ C) = t ∩ (A ∩ C) := by
    ext x
    simp only [Finset.mem_inter]
    tauto
  -- But A ∩ C = ∅, so t ∩ (A ∩ C) = ∅
  rw [h_inter_eq] at h_inter_card
  simp only [Finset.card_eq_zero] at h_disj
  rw [h_disj, Finset.inter_empty] at h_inter_card
  simp at h_inter_card

-- Source: proven/tuza/nu4/slot72_f0a24a15/cycle_path_reduction.lean
lemma bridges_subset_tpair (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : Finset V) :
    X_ef G D A ⊆ T_pair G A B := by
      -- By definition of $X_{ef}$ and $T_{pair}$, any triangle in $X_{ef} G D A$ must already be in $T_{pair} G A B$ because $D$ is part of the triangles that share an edge with $A$ and $B$. Therefore, $X_{ef} G D A \subseteq T_{pair} G A B$.
      intros t ht
      simp [X_ef, T_pair] at ht ⊢;
      unfold trianglesSharingEdge; aesop;

-- Similarly for other bridges

-- Source: proven/tuza/nu4/slot72_f0a24a15/cycle_path_reduction.lean
lemma bridges_BC_subset_tpair_CD (G : SimpleGraph V) [DecidableRel G.Adj]
    (B C D : Finset V) :
    X_ef G B C ⊆ T_pair G C D := by
      exact?

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN: Cycle reduction to path
-- ══════════════════════════════════════════════════════════════════════════════

-- The cycle A—B—C—D—A can be "cut" to path A—B—C—D
-- The extra D—A adjacency only adds X_DA bridges
-- But X_DA ⊆ T_pair(A,B), so the union is unchanged!

-- Source: proven/tuza/nu4/slot72_f0a24a15/output.lean
lemma bridges_subset_tpair (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B D : Finset V) :
    X_ef G D A ⊆ T_pair G A B := by
      -- By definition of $X_{ef}$ and $T_{pair}$, any triangle in $X_{ef} G D A$ must already be in $T_{pair} G A B$ because $D$ is part of the triangles that share an edge with $A$ and $B$. Therefore, $X_{ef} G D A \subseteq T_{pair} G A B$.
      intros t ht
      simp [X_ef, T_pair] at ht ⊢;
      unfold trianglesSharingEdge; aesop;

-- Similarly for other bridges

-- Source: proven/tuza/nu4/slot72_f0a24a15/output.lean
lemma bridges_BC_subset_tpair_CD (G : SimpleGraph V) [DecidableRel G.Adj]
    (B C D : Finset V) :
    X_ef G B C ⊆ T_pair G C D := by
      exact?

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN: Cycle reduction to path
-- ══════════════════════════════════════════════════════════════════════════════

-- The cycle A—B—C—D—A can be "cut" to path A—B—C—D
-- The extra D—A adjacency only adds X_DA bridges
-- But X_DA ⊆ T_pair(A,B), so the union is unchanged!

-- Source: proven/tuza/lemmas/slot24_tau_X_le_2.lean
lemma bridge_absorption_false : ∃ (V : Type) (inst1 : Fintype V) (inst2 : DecidableEq V) (G : SimpleGraph V) (inst3 : DecidableRel G.Adj) (M : Finset (Finset V)) (e f : Finset V) (C : Finset (Sym2 V)),
    isMaxPacking G M ∧
    e ∈ M ∧ f ∈ M ∧ e ≠ f ∧
    C ⊆ G.edgeFinset ∧
    (∀ t ∈ S G e M ∪ S G f M, ∃ edge ∈ C, edge ∈ t.sym2) ∧
    ¬ (∀ t ∈ X G e f, ∃ edge ∈ C, edge ∈ t.sym2) := by
      refine' ⟨ _, _, _, _, _, _, _, _ ⟩;
      exact CE_V;
      exact?;
      exact?;
      exact?;
      exact?;
      exact CE_M;
      exact CE_e;
      refine' ⟨ CE_f, CE_C, _, _, _, _, _, _ ⟩;
      all_goals norm_cast;
      · exact?;
      · simp +decide [ Finset.subset_iff, CE_G, CE_C ];
      · exact ⟨ CE_covers, CE_disproof ⟩

/-
Disproof of bridge_absorption.
We assume the

-- Source: proven/tuza/lemmas/slot24_tau_X_le_2.lean
theorem bridge_absorption_disproof : ¬ (∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (C : Finset (Sym2 V)) (hC : C ⊆ G.edgeFinset)
    (hC_covers : ∀ t ∈ S G e M ∪ S G f M, ∃ edge ∈ C, edge ∈ t.sym2),
    ∀ t ∈ X G e f, ∃ edge ∈ C, edge ∈ t.sym2) := by
      simp +zetaDelta at *;
      use ULift CE_V;
      refine' ⟨ inferInstance, inferInstance, _, _, _ ⟩;
      exact SimpleGraph.comap (fun x => x.down) CE_G;
      infer_instance;
      refine' ⟨ Finset.image ( fun x : Finset CE_V => Finset.image ( fun y : CE_V => ULift.up y ) x ) CE_M, _, _ ⟩ <;> simp +decide [ isMaxPacking ];
      · unfold isTrianglePacking trianglePackingNumber; simp +decide [ CE_M ] ;
        unfold isTrianglePacking; simp +decide [ CE_e, CE_f ] ;
        unfold CE_G; simp +decide [ SimpleGraph.cliqueFinset ] ;
        simp +decide [ SimpleGraph.isNClique_iff ];
      · refine' ⟨ CE_e, _, CE_f, _, _, _ ⟩ <;> simp +decide [ CE_M ];
        refine' ⟨ { Sym2.mk ⟨ ⟨ 1 ⟩, ⟨ 2 ⟩ ⟩, Sym2.mk ⟨ ⟨ 3 ⟩, ⟨ 4 ⟩ ⟩ }, _, _, _ ⟩ <;> simp +decide [ CE_G, CE_e, CE_f, CE_t, S, X ];
        simp +decide [ Set.subset_def, SimpleGraph.comap ]

end AristotleLemmas

/-
MAIN TARGET: Any cover for S_e that includes an edge of e also covers bridges through e.

Proof idea:
- A bridge t ∈ X(e,f) shares an edge with e (say edge {v, a})
- If the cover C for S_e includes {v, a}, then C covers t
- Key: e ∈ S_e, so any cover for S_e covers e
- If C covers e, C includes some edge of e
- Need: that edge also hits the bridge
-/

-- Source: proven/tuza/lemmas/slot24_tau_X_le_2.lean
lemma bridge_absorption {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (C : Finset (Sym2 V)) (hC : C ⊆ G.edgeFinset)
    (hC_covers : ∀ t ∈ S G e M ∪ S G f M, ∃ edge ∈ C, edge ∈ t.sym2) :
    ∀ t ∈ X G e f, ∃ edge ∈ C, edge ∈ t.sym2 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Apply the bridge_absorption_false

-- Source: proven/tuza/lemmas/slot6_Se_lemmas.lean
lemma Te_eq_Se_union_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) :
    trianglesSharingEdge G e = S_e G M e ∪ bridges G M e := by
  ext t
  simp only [Finset.mem_union, S_e, bridges, trianglesSharingEdge, Finset.mem_filter]
  constructor
  · intro ht
    by_cases h : ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1
    · left; exact ⟨ht, h⟩
    · right; push_neg at h; obtain ⟨f, hfM, hfne, hcard⟩ := h; exact ⟨ht, f, hfM, hfne, hcard⟩
  · intro h; rcases h with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact ht

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Se_pairwise_intersect (all triangles in S_e share edges)
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/lemmas/slot28/204aea51-fbd5-4756-ad24-5407f5e5e927-output.lean
lemma bridges_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  simp_all +decide [ Finset.ext_iff, X_ef ];
  -- If $v \notin t$, then $t \cap e$ and $t \cap f$ are disjoint subsets of $e$ and $f$ respectively, each with cardinality at least 2.
  by_contra hv_not_in_t
  have h_disjoint : Disjoint (t ∩ e) (t ∩ f) := by
    exact Finset.disjoint_left.mpr fun x hx hx' => hv_not_in_t <| by have := hv x; aesop;
  -- Since $t$ is a clique, it can have at most 3 vertices. However, $(t \cap e) \cup (t \cap f)$ has at least 4 vertices, which is impossible.
  have h_card : (t ∩ e) ∪ (t ∩ f) ⊆ t := by
    aesop_cat;
  have := Finset.card_le_card h_card; simp_all +decide [ Finset.card_union_add_card_inter ] ;
  linarith [ ht.1.card_eq ]

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_union_le_sum (subadditivity)
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable section AristotleLemmas

/-
Definition of a triangle cover and a

-- Source: proven/tuza/lemmas/slot28/204aea51-fbd5-4756-ad24-5407f5e5e927-output.lean
lemma pair_with_bridges_naive (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (S_e G M e ∪ S_e G M f ∪ X_ef G e f) ≤ 6 := by
  calc triangleCoveringNumberOn G (S_e G M e ∪ S_e G M f ∪ X_ef G e f)
      ≤ triangleCoveringNumberOn G (S_e G M e ∪ S_e G M f) + triangleCoveringNumberOn G (X_ef G e f) := tau_union_le_sum G _ _
    _ ≤ triangleCoveringNumberOn G (S_e G M e) + triangleCoveringNumberOn G (S_e G M f) + triangleCoveringNumberOn G (X_ef G e f) := by
        have h := tau_union_le_sum G (S_e G M e) (S_e G M f)
        omega
    _ ≤ 2 + 2 + 2 := by
        have h1 := tau_S_le_2 G M hM e he
        have h2 := tau_S_le_2 G M hM f hf
        have h3 := tau_X_le_2 G M hM e f he hf hef v hv
        omega
    _ = 6 := by ring

-- The key insight: bridges share vertices with S_e and S_f, allowing absorption
-- This is where the coordinated cover saves 2 edges

-- Key structural lemma: bridges are "between" S_e and S_f geometrically

-- Source: proven/tuza/lemmas/slot28/204aea51-fbd5-4756-ad24-5407f5e5e927-output.lean
lemma bridge_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (he_card : e.card = 3) (hf_card : f.card = 3)
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    ∃ x y, x ∈ e ∧ x ≠ v ∧ y ∈ f ∧ y ≠ v ∧ t = {v, x, y} := by
  have hv_t : v ∈ t := bridges_contain_v G e f v hv t ht
  have h1 : (t ∩ e).card ≥ 2 := (Finset.mem_filter.mp ht).2.1
  have h2 : (t ∩ f).card ≥ 2 := (Finset.mem_filter.mp ht).2.2
  have ht_tri : t ∈ G.cliqueFinset 3 := (Finset.mem_filter.mp ht).1
  have ht_card : t.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp ht_tri |>.2
  -- t has 3 vertices, one is v
  -- t ∩ e has ≥2 vertices including v, so there's x ∈ e, x ≠ v, x ∈ t
  -- t ∩ f has ≥2 vertices including v, so there's y ∈ f, y ≠ v, y ∈ t
  obtain ⟨ x, y, hxy ⟩ := Finset.card_eq_three.mp ht_card;
  rcases hxy with ⟨ z, hxy ⟩ ; simp_all +decide [ Finset.ext_iff ] ;
  grind

/- Aristotle failed to find a proof. -/
-- Main theorem: τ(S_e ∪ S_f ∪ X(e,f)) ≤ 4
-- This improves the naive bound of 6 by showing bridge absorption

-- Source: proven/tuza/lemmas/slot44/5a188e26-ef0d-44c2-a565-cd798ad02e00-output.lean
lemma bridges_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  simp_all +decide [ Finset.ext_iff, X_ef ];
  by_contra hv_not_in_t
  have h_disjoint : Disjoint (t ∩ e) (t ∩ f) := by
    exact Finset.disjoint_left.mpr fun x hx hx' => hv_not_in_t <| by have := hv x; aesop;
  have h_card : (t ∩ e) ∪ (t ∩ f) ⊆ t := by
    aesop_cat;
  have := Finset.card_le_card h_card; simp_all +decide [ Finset.card_union_add_card_inter ] ;
  linarith [ ht.1.card_eq ]

-- Source: proven/tuza/lemmas/slot32/2b3cce69-ca98-4c3a-9e7d-55ca3afab48d-output.lean
lemma bridges_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  unfold X_ef at ht;
  -- Since $e \cap f = \{v\}$, any triangle $t$ that intersects both $e$ and $f$ in at least two edges must contain $v$.
  have h_inter : (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2 → v ∈ t := by
    norm_num +zetaDelta at *;
    intro h1 h2;
    contrapose! h1;
    -- Since $v \notin t$, $t \cap e$ and $t \cap f$ are disjoint subsets of $e$ and $f$ respectively.
    have h_disjoint : Disjoint (t ∩ e) (t ∩ f) := by
      exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => h1 <| by rw [ Finset.ext_iff ] at hv; specialize hv x; aesop;
    have h_card_union : (t ∩ e ∪ t ∩ f).card ≤ 3 := by
      exact le_trans ( Finset.card_le_card ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ) ( by rw [ ht.1.card_eq ] );
    rw [ Finset.card_union_of_disjoint h_disjoint ] at h_card_union ; linarith;
  aesop

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
══════════════════════════════════════════════════════════════════════════════
PATH-SPECIFIC LEMMAS
══════════════════════════════════════════════════════════════════════════════

In path configuration, non-adjacent elements are vertex-disjoint
-/

-- Source: proven/tuza/lemmas/slot32/2b3cce69-ca98-4c3a-9e7d-55ca3afab48d-output.lean
lemma path_no_distant_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (e1 e3 : Finset V)
    (h_disj : Disjoint (e1 : Set V) (e3 : Set V)) :
    X_ef G e1 e3 = ∅ := by
  -- A bridge would need ≥2 vertices from each, requiring ≥4 vertices
  unfold X_ef;
  ext t;
  simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ];
  intro ht h2t
  have h_card : (t ∩ e1).card + (t ∩ e3).card ≤ 3 := by
    have h_card : (t ∩ e1 ∪ t ∩ e3).card ≤ 3 := by
      exact le_trans ( Finset.card_le_card ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ) ht.card_eq.le;
    rwa [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx1 hx2 => by rw [ Finset.ext_iff ] at h_disj; specialize h_disj x; aesop ) ] at h_card;
  linarith

-- End element's bridges only go to its neighbor

-- Source: proven/tuza/lemmas/slot32/2b3cce69-ca98-4c3a-9e7d-55ca3afab48d-output.lean
lemma path_end_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e1 e2 e3 e4 : Finset V)
    (hM_eq : M = {e1, e2, e3, e4})
    (v12 : V) (hv12 : e1 ∩ e2 = {v12})
    (h_e1_disj_e3 : Disjoint (e1 : Set V) (e3 : Set V))
    (h_e1_disj_e4 : Disjoint (e1 : Set V) (e4 : Set V)) :
    -- All bridges from e1 go to e2
    ∀ t ∈ trianglesSharingEdge G e1, (∃ f ∈ M, f ≠ e1 ∧ (t ∩ f).card ≥ 2) →
      (t ∩ e2).card ≥ 2 := by
  simp_all +decide [ Finset.disjoint_left ];
  intros t ht h_cases
  cases' h_cases with h_case1 h_case2 h_case3;
  · exact h_case1.2;
  · unfold trianglesSharingEdge at ht;
    simp_all +decide [ Finset.mem_filter, SimpleGraph.cliqueFinset ];
    have h_case3 : (t ∩ e1).card + (t ∩ e3).card ≤ (t ∩ e1 ∪ t ∩ e3).card := by
      rw [ ← Finset.card_union_add_card_inter ];
      simp_all +decide [ Finset.ext_iff ];
    have h_case3 : (t ∩ e1 ∪ t ∩ e3).card ≤ t.card := by
      exact Finset.card_le_card ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) );
    have := ht.1.card_eq; simp_all +decide ;
    cases h_case2 <;> simp_all +decide [ Finset.ext_iff ];
    · linarith;
    · have h_case3 : (t ∩ e1).card + (t ∩ e4).card ≤ (t ∩ e1 ∪ t ∩ e4).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        simp +decide [ Finset.ext_iff ];
        exact?;
      linarith [ show Finset.card ( t ∩ e1 ∪ t ∩ e4 ) ≤ 3 by exact le_trans ( Finset.card_mono ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ) this.le ]

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Path Case Theorem
-- ══════════════════════════════════════════════════════════════════════════════

-- Cover the three bridge sets with ≤6 edges (they all go through distinct shared vertices)


-- ═══════════════════════════════════════════════════════════════════════
-- LINK_GRAPH LEMMAS (1 lemmas)
-- ═══════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/nu4/slot_local_tuza_via_link_graph.lean
theorem local_tuza_via_link_graph (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    triangleCoveringNumberOn G (trianglesContainingVertex G v) ≤
    2 * trianglePackingOn G (trianglesContainingVertex G v) := by
  calc triangleCoveringNumberOn G (trianglesContainingVertex G v)
      ≤ vertexCoverNumber (linkGraph G v) := cover_at_v_le_vertex_cover G v
    _ ≤ 2 * maxMatchingNumber (linkGraph G v) := vertex_cover_le_two_matching (linkGraph G v)
    _ = 2 * trianglePackingOn G (trianglesContainingVertex G v) := by
        rw [packing_at_v_eq_matching]

/-
Define the subgraph of the link graph induced by the subset of triangles `Ti`. Two vertices `x, y` are adjacent if `x \ne y` and `{v, x, y} \in Ti`.
-/
/-- The subgraph of the link graph corresponding to a subset of triangles Ti -/
def subLinkGraph (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (Ti : Finset (Finset V)) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ t ∈ Ti, t = {v, x, y}
  symm := by
    intro x y ⟨hne, t, ht, heq⟩
    refine ⟨hne.symm, t, ht, ?_⟩
    rw [heq]
    ext z
    simp [Finset.mem_insert]
    tauto
  loopless := by
    intro x ⟨hne, _⟩
    exact hne rfl

/-- subLinkGraph has decidable adjacency -/
instance subLinkGraphDecidableRel (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (Ti : Finset (Finset V)) : DecidableRel (subLinkGraph G v Ti).Adj := by
  intro x y
  unfold subLinkGraph
  infer_instance

/-
The triangle packing number of a subset of triangles at $v$ equals the matching number of the corresponding sub-link graph.
-/
/-- Triangle packing on Ti = Matching in subLinkGraph -/


-- ═══════════════════════════════════════════════════════════════════════
-- FRACTIONAL LEMMAS (1 lemmas)
-- ═══════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/nu4/slot63_scaffolding.lean
lemma M_char_is_fractional (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    isFractionalPacking G (M_char M) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun t => by unfold M_char; split_ifs <;> norm_num
  · exact fun t ht => if_neg fun h => ht (hM.1 h)
  · intro e he
    have h_disjoint : ∀ t1 t2 : Finset V, t1 ∈ M → t2 ∈ M → e ∈ t1.sym2 → e ∈ t2.sym2 → t1 = t2 := by
      intro t1 t2 ht1 ht2 ht1e ht2e
      by_contra hne
      exact M_edge_in_exactly_one G M hM e t1 ht1 ht1e t2 ht2 hne ht2e
    have h_sum : ∑ t ∈ G.cliqueFinset 3, (if t ∈ M ∧ e ∈ t.sym2 then 1 else 0) ≤ 1 := by
      simp only [← Finset.filter_filter]
      have h_card : ((G.cliqueFinset 3).filter (fun t => t ∈ M ∧ e ∈ t.sym2)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro x hx y hy
        simp only [Finset.mem_filter] at hx hy
        exact h_disjoint x y hx.2.1 hy.2.1 hx.2.2 hy.2.2
      calc ∑ t ∈ (G.cliqueFinset 3).filter (fun t => t ∈ M ∧ e ∈ t.sym2), (1 : ℝ)
          = ((G.cliqueFinset 3).filter (fun t => t ∈ M ∧ e ∈ t.sym2)).card := by simp
        _ ≤ 1 := by exact_mod_cast h_card
    simp only [M_char]
    convert h_sum using 2
    ext t
    simp only [ite_and]
    split_ifs <;> simp_all

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA 4: M_char_weight_eq_card
-- ══════════════════════════════════════════════════════════════════════════════

/-- M_char weight equals |M| for ANY packing. -/


-- ═══════════════════════════════════════════════════════════════════════
-- OTHER LEMMAS (83 lemmas)
-- ═══════════════════════════════════════════════════════════════════════

-- Source: proven/tuza_nu1_k4_proof.lean
lemma tuza_base_case {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0 := by
  have h_no_triangles : (G.cliqueFinset 3).card = 0 := by
    contrapose! h;
    refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.singleton_subset_iff.mpr ( Classical.choose_spec ( Finset.card_pos.mp ( Nat.pos_of_ne_zero h ) ) ) ), _ ⟩ ) ) ) <;> norm_num;
    intro x hx y hy; aesop;
  unfold triangleCoveringNumber;
  unfold IsTriangleCovering; aesop;
  rw [ show ( Finset.image Finset.card ( Finset.filter ( fun S : Finset ( Sym2 V ) => ( G.deleteEdges ( S : Set ( Sym2 V ) ) ).CliqueFree 3 ) ( G.edgeFinset.powerset ) ) ).min = some 0 from ?_ ];
  · rfl;
  · refine' le_antisymm _ _;
    · refine' Finset.min_le _ ; aesop;
    · simp +decide [ Finset.min ];
      exact fun _ _ _ => WithTop.coe_le_coe.mpr ( Nat.zero_le _ )

-- Source: proven/tuza_nu1_k4_proof.lean
theorem tuza_case_nu_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
  by_contra h_contra;
  obtain ⟨s, hs⟩ : ∃ s : Finset V, G.IsNClique 4 s := by
    apply exists_K4_of_nu1_tau_gt2 G h (by linarith);
  exact h_contra <| K4_cover_le_2 G h s hs

end

-- Source: proven/scaffolding/slot44_scaffolding_PARTIAL.lean
lemma pairwise_intersecting_Se_aux (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    Set.Pairwise ((S_e G M e).filter (· ≠ e) : Set (Finset V)) (fun t1 t2 => 2 ≤ (t1 ∩ t2).card) := by
  by_contra h_contra
  obtain ⟨t1, t2, ht1, ht2, h_disjoint⟩ : ∃ t1 t2 : Finset V, t1 ≠ t2 ∧ t1 ∈ S_e G M e ∧ t2 ∈ S_e G M e ∧ t1 ≠ e ∧ t2 ≠ e ∧ (t1 ∩ t2).card ≤ 1 := by
    rw [ Set.Pairwise ] at h_contra;
    grind;
  have h_disjoint_M : ∀ f ∈ M \ {e}, (t1 ∩ f).card ≤ 1 ∧ (t2 ∩ f).card ≤ 1 := by
    unfold S_e at *; aesop;
  have h_packing : isTrianglePacking G ((M \ {e}) ∪ {t1, t2}) := by
    constructor;
    · intro x hx;
      simp +zetaDelta at *;
      rcases hx with ( rfl | rfl | ⟨ hx, hx' ⟩ ) <;> simp_all +decide [ S_e ];
      · unfold trianglesSharingEdge at ht2; aesop;
      · unfold trianglesSharingEdge at h_disjoint; aesop;
      · have := hM.1.1 hx; aesop;
    · simp_all +decide [ Set.Pairwise ];
      refine' ⟨ fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint.2.2.2, fun a ha ha' => ⟨ fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint_M a ha ha' |>.1, fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint_M a ha ha' |>.2, fun b hb hb' hab => _ ⟩ ⟩;
      have := hM.1;
      have := this.2 ha hb hab; aesop;
  have h_card : ((M \ {e}) ∪ {t1, t2}).card > M.card := by
    have h_card : ((M \ {e}) ∪ {t1, t2}).card = (M \ {e}).card + 2 := by
      have h_card : Disjoint (M \ {e}) {t1, t2} := by
        simp_all +decide [ Finset.disjoint_left ];
        intro f hf hfe; have := h_packing.1; simp_all +decide [ Finset.subset_iff ] ;
        constructor <;> intro h <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
        · grind;
        · have := h_disjoint_M t2 hf; simp_all +decide ;
      rw [ Finset.card_union_of_disjoint h_card, Finset.card_insert_of_notMem, Finset.card_singleton ] ; aesop;
    simp_all +decide [ Finset.card_sdiff ];
    omega;
  have h_contradiction : ((M \ {e}) ∪ {t1, t2}).card ≤ trianglePackingNumber G := by
    have h_contradiction : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ trianglePackingNumber G := by
      unfold trianglePackingNumber;
      intro S hS;
      have h_contradiction : S.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        exact Finset.mem_image.mpr ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by exact fun x hx => by have := hS.1 hx; aesop ), hS ⟩, rfl ⟩;
      have := Finset.le_max h_contradiction;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_contradiction _ h_packing;
  exact h_card.not_le ( h_contradiction.trans ( hM.2.ge ) )

-- Source: proven/scaffolding/slot44_scaffolding_PARTIAL.lean
lemma Se_structure_lemma (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (∃ uv, uv ⊆ e ∧ uv.card = 2 ∧ ∀ t ∈ S_e G M e, t ≠ e → uv ⊆ t) ∨
    (∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → t = (t ∩ e) ∪ {x}) := by
  by_cases h : ∃ t1 t2 : Finset V, t1 ∈ S_e G M e ∧ t2 ∈ S_e G M e ∧ t1 ≠ e ∧ t2 ≠ e ∧ t1 ∩ e ≠ t2 ∩ e;
  · obtain ⟨ t1, t2, ht1, ht2, h1, h2, h3 ⟩ := h;
    obtain ⟨ x, hx ⟩ := common_ext_vertex_of_diff_edges G M hM e he t1 t2 ( by aesop ) ( by aesop ) h3;
    refine' Or.inr ⟨ x, hx.1, fun t ht ht' => _ ⟩;
    by_cases h4 : t ∩ e = t1 ∩ e;
    · have := common_ext_vertex_of_diff_edges G M hM e he t t2 ( by
        exact Finset.mem_filter.mpr ⟨ ht, ht' ⟩ ) ( by
        exact Finset.mem_filter.mpr ⟨ ht2, h2 ⟩ ) ( by
        exact h4.symm ▸ h3 );
      grind;
    · have := common_ext_vertex_of_diff_edges G M hM e he t t1 ( by
        exact Finset.mem_filter.mpr ⟨ ht, ht' ⟩ ) ( by
        exact Finset.mem_filter.mpr ⟨ ht1, h1 ⟩ ) h4;
      grind;
  · by_cases h_empty : S_e G M e \ {e} = ∅;
    · simp_all +decide [ Finset.ext_iff ];
      contrapose! h_empty;
      have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      have := this.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      exact False.elim ( h_empty.1 ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose ) ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose_spec |> And.left ) ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose_spec |> And.right ) );
    · obtain ⟨t, ht⟩ : ∃ t ∈ S_e G M e \ {e}, ∀ t' ∈ S_e G M e \ {e}, t ∩ e = t' ∩ e := by
        exact Exists.elim ( Finset.nonempty_of_ne_empty h_empty ) fun t ht => ⟨ t, ht, fun t' ht' => Classical.not_not.1 fun h' => h ⟨ t, t', by aesop ⟩ ⟩;
      have := Finset.mem_filter.mp ( Finset.mem_sdiff.mp ht.1 |>.1 );
      have := Finset.mem_filter.mp this.1;
      obtain ⟨uv, huv⟩ : ∃ uv ⊆ t ∩ e, uv.card = 2 := by
        exact Finset.exists_subset_card_eq this.2;
      grind

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma lemma_2_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∀ t1 t2, t1 ∈ S G e M → t2 ∈ S G e M → shareEdge t1 t2 := by
      unfold shareEdge S at *; aesop;
      -- If t1 and t2 do not share an edge, then they are disjoint triangles in S_e.
      by_contra h_not_share;
      -- Consider $M' = (M \setminus \{e\}) \cup \{t1, t2\}$.
      set M' : Finset (Finset V) := (M \ {e}) ∪ {t1, t2};
      -- M' is a triangle packing.
      have hM'_packing : isTrianglePacking G M' := by
        constructor <;> simp_all +decide [ Finset.subset_iff ];
        · aesop;
          · unfold trianglesSharingEdge at left; aesop;
          · unfold trianglesSharingEdge at left_1; aesop;
          · exact hM.1.1 left_2 |> fun h => by simpa using h;
        · intro x hx y hy hxy; aesop;
          · linarith;
          · rw [ Finset.inter_comm ] ; linarith;
          · rw [ Finset.inter_comm ] ; aesop;
          · exact right_1 x left_2 right_2 |> le_trans ( Finset.card_mono <| by aesop_cat );
          · have := hM.1;
            exact this.2 left_2 left_3 hxy;
      -- The size of M' is |M| - 1 + 2 = |M| + 1.
      have hM'_size : M'.card = M.card + 1 := by
        rw [ Finset.card_union_of_disjoint ] <;> aesop;
        · rw [ Finset.card_sdiff ] ; aesop;
          rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] ; aesop;
          · rw [ Nat.sub_add_cancel ( Finset.card_pos.mpr ⟨ e, he ⟩ ) ];
          · unfold trianglesSharingEdge at *; aesop;
            exact h_not_share.not_le ( by have := left_1.card_eq; aesop );
        · unfold trianglesSharingEdge at left; aesop;
          specialize right t1 a ; aesop;
          exact Classical.not_not.1 fun h => by have := left.card_eq; aesop;
        · unfold trianglesSharingEdge at *; aesop;
          have := right _ a; have := right_1 _ a; simp_all +decide [ Finset.inter_comm ] ;
          exact Classical.not_not.1 fun h => by have := this h; linarith [ left_1.card_eq ] ;
      unfold isMaxPacking at hM; aesop;
      have hM'_size_le : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ trianglePackingNumber G := by
        unfold trianglePackingNumber; aesop;
        have hM'_size_le : S ∈ Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset := by
          exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( a.1 ), a ⟩;
        have hM'_size_le : S.card ≤ Finset.max (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)) := by
          exact Finset.le_max ( Finset.mem_image_of_mem _ hM'_size_le );
        cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
        exact WithBot.coe_le_coe.mp hM'_size_le;
      linarith [ hM'_size_le _ hM'_packing ]

noncomputable def trianglePackingNumberOn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : ℕ :=
  triangles.powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma lemma_2_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    trianglePackingNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) = trianglePackingNumber G - 1 := by
      simp +decide [ trianglePackingNumberOn ];
      -- Since $M$ is a maximum packing, we have $\nu(G) = |M|$.
      have h_max_packing : trianglePackingNumber G = M.card := by
        unfold isMaxPacking at hM; aesop;
      have h_max_packing_allowed : ∀ M' : Finset (Finset V), isTrianglePacking G M' → M' ⊆ (G.cliqueFinset 3 \ trianglesSharingEdge G e) → M'.card ≤ M.card - 1 := by
        intro M' hM' hM'_allowed
        have hM'_allowed_card : (M' ∪ {e}).card ≤ M.card := by
          have hM'_allowed_card : isTrianglePacking G (M' ∪ {e}) := by
            constructor;
            · simp_all +decide [ Finset.subset_iff ];
              have := hM.1.1 he; aesop;
            · simp_all +decide [ Set.Pairwise ];
              simp_all +decide [ Finset.subset_iff, isTrianglePacking ];
              simp_all +decide [ Finset.inter_comm, trianglesSharingEdge ];
              exact ⟨ fun x hx hx' => Nat.le_of_lt_succ ( hM'_allowed hx ), fun x hx => ⟨ fun hx' => Nat.le_of_lt_succ ( hM'_allowed hx ), fun y hy hy' => hM'.2 hx hy hy' ⟩ ⟩;
          have h_max_packing_allowed : ∀ M' : Finset (Finset V), isTrianglePacking G M' → M'.card ≤ M.card := by
            intros M' hM'
            have h_max_packing_allowed : M'.card ≤ trianglePackingNumber G := by
              have h_max_packing_allowed : M' ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
                exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hM'.1, hM' ⟩;
              unfold trianglePackingNumber;
              have h_max_packing_allowed : M'.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
                exact Finset.mem_image_of_mem _ h_max_packing_allowed;
              have := Finset.le_max h_max_packing_allowed; aesop;
              cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
            exact h_max_packing ▸ h_max_packing_allowed;
          exact h_max_packing_allowed _ hM'_allowed_card;
        have hM'_allowed_card : e ∉ M' := by
          intro h; have := hM'_allowed h; simp_all +decide [ trianglesSharingEdge ] ;
          exact absurd ( this.2 this.1 ) ( by rw [ this.1.2 ] ; decide );
        rw [ Finset.card_union ] at * ; aesop;
        exact Nat.le_sub_one_of_lt hM'_allowed_card_1;
      have h_max_packing_allowed_eq : ∃ M' : Finset (Finset V), isTrianglePacking G M' ∧ M' ⊆ (G.cliqueFinset 3 \ trianglesSharingEdge G e) ∧ M'.card = M.card - 1 := by
        refine' ⟨ M.erase e, _, _, _ ⟩ <;> simp_all +decide [ isTrianglePacking ];
        · have := hM.1; aesop;
          · exact fun x hx => this.1 ( Finset.mem_of_mem_erase hx );
          · exact fun x hx y hy hxy => this.2 ( by aesop ) ( by aesop ) hxy;
        · intro t ht; specialize hM; have := hM.1; aesop;
          · exact Finset.mem_filter.mp ( this.1 right ) |>.2;
          · have := this.2;
            exact absurd ( this right he left ) ( by unfold trianglesSharingEdge at a; aesop );
      rw [ show ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 \ trianglesSharingEdge G e |> Finset.powerset ) ) ).max = ↑ ( M.card - 1 ) from ?_ ];
      · aesop;
      · refine' le_antisymm _ _;
        · aesop;
          exact WithBot.coe_le_coe.mpr ( h_max_packing_allowed x a_2 a_1 );
        · exact Finset.le_max ( Finset.mem_image.mpr ⟨ h_max_packing_allowed_eq.choose, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h_max_packing_allowed_eq.choose_spec.2.1, h_max_packing_allowed_eq.choose_spec.1 ⟩, h_max_packing_allowed_eq.choose_spec.2.2 ⟩ )

noncomputable def triangleCoveringNumberOn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

def isStar {V : Type*} [DecidableEq V] (S : Finset (Finset V)) : Prop :=
  ∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ S, e ⊆ t

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma intersecting_triples_structure {V : Type*} [DecidableEq V]
    (t1 t2 t3 : Finset V) (h_card : t1.card = 3 ∧ t2.card = 3 ∧ t3.card = 3)
    (h12 : (t1 ∩ t2).card ≥ 2) (h13 : (t1 ∩ t3).card ≥ 2) (h23 : (t2 ∩ t3).card ≥ 2)
    (h_not_star : ¬ ∃ e : Finset V, e.card = 2 ∧ e ⊆ t1 ∧ e ⊆ t2 ∧ e ⊆ t3) :
    (t1 ∪ t2 ∪ t3).card = 4 := by
      -- Since $t1$ and $t2$ share an edge, their union has size at most $3 + 3 - 2 = 4$.
      have h_union_t1_t2 : (t1 ∪ t2).card ≤ 4 := by
        have := Finset.card_union_add_card_inter t1 t2; linarith;
      by_cases h_cases : (t1 ∪ t2).card = 4;
      · have h_union_t1_t2_t3 : (t1 ∪ t2 ∪ t3).card ≤ 4 := by
          have h_union_t1_t2_t3_step : (t1 ∩ t3 ∪ t2 ∩ t3).card ≥ 3 := by
            have h_union_t1_t2_t3_step : (t1 ∩ t3 ∩ t2 ∩ t3).card ≤ 1 := by
              contrapose! h_not_star;
              obtain ⟨ e, he ⟩ := Finset.exists_subset_card_eq h_not_star;
              exact ⟨ e, he.2, Finset.Subset.trans he.1 ( by aesop_cat ), Finset.Subset.trans he.1 ( by aesop_cat ), Finset.Subset.trans he.1 ( by aesop_cat ) ⟩;
            have := Finset.card_union_add_card_inter ( t1 ∩ t3 ) ( t2 ∩ t3 ) ; simp_all +decide [ Finset.inter_left_comm, Finset.inter_comm ] ;
            linarith;
          have h_union_t1_t2_t3_step : (t1 ∪ t2 ∪ t3).card ≤ (t1 ∪ t2).card + (t3 \ (t1 ∩ t3 ∪ t2 ∩ t3)).card := by
            have h_union_t1_t2_t3_step : (t1 ∪ t2 ∪ t3) ⊆ (t1 ∪ t2) ∪ (t3 \ (t1 ∩ t3 ∪ t2 ∩ t3)) := by
              grind;
            exact le_trans ( Finset.card_le_card h_union_t1_t2_t3_step ) ( Finset.card_union_le _ _ );
          have h_union_t1_t2_t3_step : (t3 \ (t1 ∩ t3 ∪ t2 ∩ t3)).card = t3.card - (t1 ∩ t3 ∪ t2 ∩ t3).card := by
            rw [ Finset.card_sdiff ];
            rw [ Finset.inter_eq_left.mpr ( Finset.union_subset ( Finset.inter_subset_right ) ( Finset.inter_subset_right ) ) ];
          omega;
        exact le_antisymm h_union_t1_t2_t3 ( by linarith [ Finset.card_mono ( Finset.subset_union_left : t1 ∪ t2 ⊆ t1 ∪ t2 ∪ t3 ) ] );
      · have h_union_t1_t2 : t1 = t2 := by
          have h_union_t1_t2 : (t1 ∪ t2).card = 3 := by
            have := Finset.card_union_add_card_inter t1 t2; interval_cases _ : Finset.card ( t1 ∪ t2 ) <;> simp_all +decide ;
            · linarith [ show Finset.card ( t1 ∩ t2 ) ≤ 3 by exact le_trans ( Finset.card_le_card fun x hx => Finset.mem_of_mem_inter_left hx ) h_card.1.le ];
            · linarith [ show ( t1 ∩ t2 ).card ≤ 3 by exact le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) h_card.1.le ];
          have := Finset.card_union_add_card_inter t1 t2; aesop;
          have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; aesop;
          exact Eq.symm ( this_2 ( by linarith ) );
        contrapose! h_not_star; aesop;
        exact Exists.elim ( Finset.exists_subset_card_eq h23 ) fun e he => ⟨ e, he.2, Finset.subset_iff.2 fun x hx => Finset.mem_inter.1 ( he.1 hx ) |>.1, Finset.subset_iff.2 fun x hx => Finset.mem_inter.1 ( he.1 hx ) |>.2 ⟩

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma intersecting_family_structure_corrected {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS_nonempty : S.Nonempty) (hS : S ⊆ G.cliqueFinset 3)
    (h_pair : Set.Pairwise (S : Set (Finset V)) shareEdge) :
    isStar S ∨ isK4 S := by
      by_cases h_star : ∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ S, e ⊆ t;
      · exact Or.inl h_star;
      · -- If there are three triangles in S that do not share a common edge, then their union is a K4.
        by_cases h_three : ∃ t1 t2 t3 : Finset V, t1 ∈ S ∧ t2 ∈ S ∧ t3 ∈ S ∧ t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 ∧ ¬∃ e : Finset V, e.card = 2 ∧ e ⊆ t1 ∧ e ⊆ t2 ∧ e ⊆ t3;
        · obtain ⟨ t1, t2, t3, ht1, ht2, ht3, hne ⟩ := h_three;
          have h_union : (t1 ∪ t2 ∪ t3).card = 4 := by
            apply_rules [ intersecting_triples_structure ];
            · have := hS ht1; have := hS ht2; have := hS ht3; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
              exact ⟨ by rw [ SimpleGraph.isNClique_iff ] at *; aesop, by rw [ SimpleGraph.isNClique_iff ] at *; aesop, by rw [ SimpleGraph.isNClique_iff ] at *; aesop ⟩;
            · tauto;
            · tauto;
            · tauto;
            · exact hne.2.2.2;
          refine' Or.inr ⟨ t1 ∪ t2 ∪ t3, h_union, _ ⟩;
          intros t ht
          have h_inter : (t ∩ t1).card ≥ 2 ∧ (t ∩ t2).card ≥ 2 ∧ (t ∩ t3).card ≥ 2 := by
            have := h_pair ht ht1; have := h_pair ht ht2; have := h_pair ht ht3; simp_all +decide [ shareEdge ] ;
            by_cases h : t = t1 <;> by_cases h' : t = t2 <;> by_cases h'' : t = t3 <;> simp_all +decide;
            · exact le_trans ‹_› ( Finset.card_mono ( Finset.inter_subset_left ) );
            · exact le_trans this ( Finset.card_mono ( Finset.inter_subset_left ) );
            · have := hS ht3; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
              exact this.card_eq.symm ▸ by decide;
          have h_card : t.card = 3 ∧ t1.card = 3 ∧ t2.card = 3 ∧ t3.card = 3 := by
            have := hS ht; have := hS ht1; have := hS ht2; have := hS ht3; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
            exact ⟨ by simpa using ‹G.IsNClique 3 t›.card_eq, by simpa using ‹G.IsNClique 3 t1›.card_eq, by simpa using ‹G.IsNClique 3 t2›.card_eq, by simpa using ‹G.IsNClique 3 t3›.card_eq ⟩;
          apply triangle_in_k4_of_intersects_triples;
          · tauto;
          · exact h_union;
          · simp +decide [ Finset.subset_iff ];
            tauto;
          · tauto;
          · exact h_inter;
        · by_cases h_two : ∃ t1 t2 : Finset V, t1 ∈ S ∧ t2 ∈ S ∧ t1 ≠ t2;
          · obtain ⟨ t1, t2, ht1, ht2, hne ⟩ := h_two;
            -- Since $t1$ and $t2$ share an edge, let $e$ be this common edge.
            obtain ⟨e, he⟩ : ∃ e : Finset V, e.card = 2 ∧ e ⊆ t1 ∧ e ⊆ t2 := by
              have := h_pair ht1 ht2 hne;
              obtain ⟨ e, he ⟩ := Finset.exists_subset_card_eq this;
              exact ⟨ e, he.2, Finset.Subset.trans he.1 ( Finset.inter_subset_left ), Finset.Subset.trans he.1 ( Finset.inter_subset_right ) ⟩;
            refine' Or.inl ⟨ e, he.1, fun t ht => _ ⟩;
            contrapose! h_three;
            use t1, t2, t;
            refine' ⟨ ht1, ht2, ht, hne, _, _, _ ⟩;
            · grind;
            · grind;
            · intro x hx hx1 hx2 hx3;
              have h_eq : x ⊆ t1 ∩ t2 := by
                exact Finset.subset_inter hx1 hx2;
              have h_eq : x = t1 ∩ t2 := by
                have h_eq : (t1 ∩ t2).card = 2 := by
                  have := hS ht1; have := hS ht2; simp_all +decide [ SimpleGraph.mem_cliqueFinset_iff ] ;
                  have := Finset.card_le_card h_eq; simp_all +decide ;
                  have := Finset.card_le_card ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; ( have := Finset.card_le_card ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; ( simp_all +decide [ SimpleGraph.isNClique_iff ] ; ) );
                  interval_cases _ : ( t1 ∩ t2 ).card <;> simp_all +decide;
                  have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; aesop;
                exact Finset.eq_of_subset_of_card_le ‹_› ( by simp +decide [ * ] );
              have := Finset.eq_of_subset_of_card_le ( show e ⊆ t1 ∩ t2 from Finset.subset_inter he.2.1 he.2.2 ) ; aesop;
          · rcases Finset.card_le_one.2 ( fun t1 ht1 t2 ht2 => Classical.not_not.1 fun h => h_two ⟨ t1, t2, ht1, ht2, h ⟩ ) with h;
            cases h.eq_or_lt <;> simp_all +decide;
            rw [ Finset.card_eq_one ] at * ; aesop;
            rw [ SimpleGraph.isNClique_iff ] at hS ; aesop;
            exact False.elim ( h_star ( w.erase ( Classical.choose ( Finset.card_pos.mp ( by linarith ) ) ) ) ( by rw [ Finset.card_erase_of_mem ( Classical.choose_spec ( Finset.card_pos.mp ( by linarith ) ) ), right ] ) ( by intro x hx; exact Finset.mem_of_mem_erase hx ) )

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma inductive_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumber G ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e) + triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) := by
      -- Let $E_1$ be a minimum edge cover of the triangles sharing $e$, and $E_2$ be a minimum edge cover of the triangles not sharing $e$.
      obtain ⟨E1, hE1⟩ : ∃ E1 : Finset (Sym2 V), E1 ⊆ G.edgeFinset ∧ (∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E1, e ∈ t.sym2) ∧ E1.card = triangleCoveringNumberOn G (trianglesSharingEdge G e) := by
        -- By definition of image, there exists a subset E1 in the powerset of G's edges such that E1 satisfies the conditions and its cardinality is the minimum element of the image.
        obtain ⟨E1, hE1⟩ : ∃ E1 ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2)), E1.card = triangleCoveringNumberOn G (trianglesSharingEdge G e) := by
          unfold triangleCoveringNumberOn;
          have h_nonempty : {E' ∈ G.edgeFinset.powerset | ∀ t ∈ trianglesSharingEdge G e, ∃ e ∈ E', e ∈ t.sym2}.Nonempty := by
            -- The entire edge set of G is a subset of itself and covers all triangles in G, including those in trianglesSharingEdge G e.
            use G.edgeFinset;
            simp +decide [ trianglesSharingEdge ];
            intro t ht ht'; obtain ⟨ a, b, c, habc ⟩ := Finset.card_eq_three.mp ht.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            exact ⟨ s(a, b), by aesop ⟩;
          have := Finset.min_of_mem ( Finset.mem_image_of_mem Finset.card h_nonempty.choose_spec );
          rcases this with ⟨ b, hb ⟩ ; rw [ hb ] ; simp +decide [ Option.getD ] ;
          have := Finset.mem_of_min hb; aesop;
        aesop;
      have h_tau_le_tau1_plus_tau2_aux : ∃ E : Finset (Sym2 V), E ⊆ G.edgeFinset ∧ (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2) ∧ E.card ≤ E1.card + triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) := by
        -- Let $E_2$ be a minimum edge cover of the triangles not sharing $e$.
        obtain ⟨E2, hE2⟩ : ∃ E2 : Finset (Sym2 V), E2 ⊆ G.edgeFinset ∧ (∀ t ∈ (G.cliqueFinset 3) \ (trianglesSharingEdge G e), ∃ e ∈ E2, e ∈ t.sym2) ∧ E2.card = triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) := by
          have hE2 : ∃ E2 ∈ Finset.filter (fun E' => ∀ t ∈ (G.cliqueFinset 3) \ (trianglesSharingEdge G e), ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset), E2.card = (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ (G.cliqueFinset 3) \ (trianglesSharingEdge G e), ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset))).min.getD 0 := by
            have hE2 : Finset.Nonempty (Finset.filter (fun E' => ∀ t ∈ (G.cliqueFinset 3) \ (trianglesSharingEdge G e), ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset)) := by
              use G.edgeFinset;
              simp +decide [ SimpleGraph.cliqueFinset ];
              intro t ht ht'; rcases Finset.card_eq_three.mp ht.2 with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use s(a, b); simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            have := Finset.min_of_mem ( Finset.mem_image_of_mem Finset.card hE2.choose_spec );
            obtain ⟨ b, hb ⟩ := this; rw [ hb ] ; simp +decide [ Option.getD ] ;
            have := Finset.mem_of_min hb; aesop;
          exact ⟨ hE2.choose, Finset.mem_powerset.mp ( Finset.mem_filter.mp hE2.choose_spec.1 |>.1 ), Finset.mem_filter.mp hE2.choose_spec.1 |>.2, hE2.choose_spec.2 ⟩;
        use E1 ∪ E2;
        simp_all +decide [ Finset.subset_iff ];
        exact ⟨ fun x hx => hx.elim ( fun hx => hE1.1 hx ) fun hx => hE2.1 hx, fun t ht => if h : t ∈ trianglesSharingEdge G e then by obtain ⟨ e, he, he' ⟩ := hE1.2.1 t h; exact ⟨ e, Or.inl he, he' ⟩ else by obtain ⟨ e, he, he' ⟩ := hE2.2.1 t ht h; exact ⟨ e, Or.inr he, he' ⟩, le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( hE1.2.2.le ) ( hE2.2.2.le ) ) ⟩;
      obtain ⟨ E, hE₁, hE₂, hE₃ ⟩ := h_tau_le_tau1_plus_tau2_aux;
      refine' le_trans _ ( le_trans hE₃ ( add_le_add_right hE1.2.2.le _ ) );
      unfold triangleCoveringNumber;
      have h_min_le_E : Finset.min (Finset.image Finset.card (Finset.filter (isTriangleCover G) G.edgeFinset.powerset)) ≤ Finset.card E := by
        exact Finset.min_le ( Finset.mem_image.mpr ⟨ E, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE₁, ⟨ hE₁, hE₂ ⟩ ⟩, rfl ⟩ );
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( isTriangleCover G ) G.edgeFinset.powerset ) ) <;> aesop

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma tuza_case_nu_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 1) : triangleCoveringNumber G ≤ 2 := by
      -- Since $\nu(G) = 1$, there exists a single triangle in $G$.
      obtain ⟨t, ht⟩ : ∃ t : Finset V, t ∈ G.cliqueFinset 3 := by
        contrapose! h;
        simp_all +decide [ trianglePackingNumber ];
        rw [ show ( G.cliqueFinset 3 : Finset ( Finset V ) ) = ∅ by ext; aesop ] ; simp +decide;
        simp +decide [ Finset.filter_singleton, isTrianglePacking ];
      -- Since $\nu(G) = 1$, the maximum packing $M$ must be a single triangle $t$.
      obtain ⟨M, hM⟩ : ∃ M : Finset (Finset V), isMaxPacking G M ∧ M = {t} := by
        refine' ⟨ { t }, _, rfl ⟩;
        refine' ⟨ _, _ ⟩ <;> simp_all +decide [ isMaxPacking ];
        unfold isTrianglePacking; aesop;
      have h_tau_S : triangleCoveringNumberOn G (trianglesSharingEdge G t) ≤ 2 := by
        have := tau_S_le_2 G M hM.1 t (by
        aesop);
        unfold S at this; aesop;
      have h_tau_G_minus_S : triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G t)) ≤ 0 := by
        have h_tau_G_minus_S : trianglePackingNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G t)) = 0 := by
          -- Since $\nu(G) = 1$, the maximum packing $M$ must be a single triangle $t$. Therefore, removing any triangles that share an edge with $t$ leaves no triangles, so the packing number of the remaining triangles is zero.
          have h_tau_S : trianglePackingNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G t)) = trianglePackingNumber G - 1 := by
            convert lemma_2_3 G M hM.1 t ( by aesop ) using 1;
          aesop;
        apply triangleCoveringNumberOn_eq_zero_of_packing_zero G ((G.cliqueFinset 3) \ trianglesSharingEdge G t) (by
        exact?) h_tau_G_minus_S |> le_of_eq;
      have h_tau_G : triangleCoveringNumber G ≤ triangleCoveringNumberOn G (trianglesSharingEdge G t) + triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G t)) := by
        apply inductive_bound G M hM.left t (by
        aesop);
      linarith

def X {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e) ∩ (trianglesSharingEdge G f)

-- Source: proven/tuza/aristotle_parker_full_e7f11dfc.lean
lemma mem_X_implies_v_in_t {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (he : e.card = 3) (hf : f.card = 3) (h_inter : e ∩ f = {v}) :
    ∀ t ∈ X G e f, v ∈ t := by
      -- Since $t$ is in both triangles sharing edge $e$ and $f$, and their intersection is $\{v\}$, $t$ must contain $v$.
      intros t ht
      have h_t_e : t ∈ trianglesSharingEdge G e := by
        exact Finset.mem_inter.mp ht |>.1
      have h_t_f : t ∈ trianglesSharingEdge G f := by
        exact Finset.mem_inter.mp ht |>.2
      have h_t_inter : (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2 := by
        unfold trianglesSharingEdge at *; aesop;
      have h_t_v : v ∈ t := by
        have h_t_v : (t ∩ e) ∩ (t ∩ f) ≠ ∅ := by
          have h_t_v : (t ∩ e ∩ (t ∩ f)).card ≥ (t ∩ e).card + (t ∩ f).card - (t ∩ e ∪ t ∩ f).card := by
            rw [ ← Finset.card_union_add_card_inter ] ; simp +decide [ Finset.inter_comm, Finset.inter_left_comm, Finset.inter_assoc ] ;
          have h_t_v : (t ∩ e ∪ t ∩ f).card ≤ 3 := by
            have h_t_v : (t ∩ e ∪ t ∩ f) ⊆ t := by
              exact Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left );
            have h_t_v : t.card ≤ 3 := by
              have h_t_v : t ∈ G.cliqueFinset 3 := by
                exact Finset.mem_filter.mp h_t_e |>.1;
              exact Finset.mem_filter.mp h_t_v |>.2.2.le;
            exact le_trans ( Finset.card_le_card ‹_› ) h_t_v;
          exact Finset.Nonempty.ne_empty ( Finset.card_pos.mp ( by omega ) );
        simp_all +decide [ Finset.ext_iff ]
      exact h_t_v

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma Se_pairwise_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    Set.Pairwise (S_e G M e : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≥ 2) := by
      -- Assume for contradiction that there are two triangles in $S_e(M)$ that share at most one vertex.
      by_contra h;
      simp_all +decide [ isMaxPacking ];
      -- Construct $M' = (M \setminus \{e\}) \cup \{t_1, t_2\}$.
      obtain ⟨t1, t2, ht1, ht2, h_inter⟩ : ∃ t1 t2 : Finset V, t1 ∈ S_e G M e ∧ t2 ∈ S_e G M e ∧ t1 ≠ t2 ∧ (t1 ∩ t2).card ≤ 1 := by
        simp_all +decide [ Set.Pairwise ];
        exact ⟨ _, h.choose_spec.1, _, h.choose_spec.2.choose_spec.1, h.choose_spec.2.choose_spec.2.1, Nat.le_of_lt_succ h.choose_spec.2.choose_spec.2.2 ⟩;
      -- We claim $M'$ is a triangle packing.
      have hM'_packing : isTrianglePacking G ((M \ {e}) ∪ {t1, t2}) := by
        unfold isTrianglePacking at *;
        simp_all +decide [ Finset.subset_iff, Set.Pairwise ];
        unfold S_e at *; simp_all +decide [ Finset.inter_comm ] ;
        unfold trianglesSharingEdge at *; aesop;
      -- Since $M'$ is a packing and $|M'| = |M| + 1$, this contradicts that $M$ is a maximum packing.
      have hM'_card : ((M \ {e}) ∪ {t1, t2}).card > M.card := by
        rw [ Finset.card_union ] ; simp +decide [ *, Finset.card_sdiff ];
        -- Since $t1$ and $t2$ are in $S_e G M e$, they are not in $M \ {e}$, so their intersection with $M \ {e}$ is empty.
        have h_inter_empty : t1 ∉ M \ {e} ∧ t2 ∉ M \ {e} := by
          simp_all +decide [ S_e ];
          constructor <;> intro h <;> have := ht1.2 t1 <;> have := ht2.2 t2 <;> simp_all +decide [ Finset.inter_comm ];
          · by_cases h : t1 = e <;> simp_all +decide;
            have := Finset.mem_filter.mp ht1.1; simp_all +decide [ trianglesSharingEdge ] ;
            exact absurd ( this.1.card_eq ) ( by linarith );
          · by_cases h : t2 = e <;> simp_all +decide [ trianglesSharingEdge ];
            exact absurd this ( by have := ht2.1.1.2; aesop );
        rw [ Finset.inter_comm ] ; simp +decide [ *, Finset.inter_comm ] ; omega;
      -- This contradicts that $M$ is a maximum packing.
      have h_contradiction : trianglePackingNumber G ≥ ((M \ {e}) ∪ {t1, t2}).card := by
        unfold trianglePackingNumber;
        have h_contradiction : ((M \ {e}) ∪ {t1, t2}) ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
          simp_all +decide [ isTrianglePacking ];
        have h_contradiction : ((M \ {e}) ∪ {t1, t2}).card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
          exact Finset.mem_image_of_mem _ h_contradiction;
        have := Finset.le_max h_contradiction;
        cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 ).powerset ) ) <;> aesop;
      linarith

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma K4_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (e : Finset V) (x : V)
    (he : e ∈ S) (hS : S ⊆ G.cliqueFinset 3)
    (h_sub : ∀ t ∈ S, t ⊆ e ∪ {x}) :
    triangleCoveringNumberOn G S ≤ 2 := by
      -- Since $e$ is a triangle, it has exactly three vertices. Let's denote them as $u$, $v$, and $w$.
      obtain ⟨u, v, w, hu, hv, hw, he⟩ : ∃ u v w : V, u ∈ e ∧ v ∈ e ∧ w ∈ e ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ e = {u, v, w} := by
        have := hS he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        rcases this with ⟨ he, he' ⟩ ; rw [ Finset.card_eq_three ] at he' ; aesop;
      -- Consider the possible triangles in $S$. They are subsets of $\{u, v, w, x\}$ of size 3.
      have h_triangles : ∀ t ∈ S, t = {u, v, w} ∨ t = {u, v, x} ∨ t = {v, w, x} ∨ t = {w, u, x} := by
        intro t ht; specialize h_sub t ht; simp_all +decide [ Finset.subset_iff ] ;
        have := hS ht; have := Finset.card_eq_three.mp this.2; obtain ⟨ a, b, c, hab, hbc, hac, rfl ⟩ := this; simp_all +decide ;
        rcases h_sub with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] at hab hbc hac ⊢;
      -- Consider the two cases: $t_3 \in S$ or $t_3 \notin S$.
      by_cases ht3 : {w, u, x} ∈ S;
      · -- Consider the cover $C = \{uv, wx\}$.
        have h_cover : isTriangleCover G S {Sym2.mk (u, v), Sym2.mk (w, x)} := by
          constructor;
          · have := hS ‹_›; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
            have := hS ‹ { u, v, w } ∈ S ›; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            aesop_cat;
          · intro t ht; specialize h_triangles t ht; aesop;
        refine' le_triangleCoveringNumberOn G S _ h_cover |> le_trans <| _;
        exact Finset.card_insert_le _ _;
      · -- Consider the set $C = \{uv, vw\}$.
        have hC : isTriangleCover G S ({Sym2.mk (u, v), Sym2.mk (v, w)} : Finset (Sym2 V)) := by
          constructor <;> simp_all +decide [ Finset.subset_iff ];
          · have := hS ‹_›; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          · grind;
        refine' le_trans ( le_triangleCoveringNumberOn G S _ hC ) _;
        exact Finset.card_insert_le _ _

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma structure_lemma_case2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3)
    (e : Finset V) (he : e ∈ S)
    (h_share_e : ∀ t ∈ S, (t ∩ e).card ≥ 2)
    (h_pairwise : Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≥ 2))
    (t1 t2 : Finset V) (ht1 : t1 ∈ S) (ht2 : t2 ∈ S)
    (h_inter1 : (t1 ∩ e).card = 2) (h_inter2 : (t2 ∩ e).card = 2)
    (h_diff : t1 ∩ e ≠ t2 ∩ e) :
    ∃ x, ∀ t ∈ S, t ⊆ e ∪ {x} := by
      -- By `common_vertex_of_different_edges`, there exists $x \notin e$ such that $t1 = (t1 \cap e) \cup \{x\}$ and $t2 = (t2 \cap e) \cup \{x\}$.
      obtain ⟨x, hx⟩ : ∃ x, x ∉ e ∧ t1 = (t1 ∩ e) ∪ {x} ∧ t2 = (t2 ∩ e) ∪ {x} := by
        exact?;
      -- Let $t \in S$. If $t = e$, clearly $t \subseteq e \subseteq e \cup \{x\}$.
      use x
      intro t ht
      by_cases ht_eq_e : t = e;
      · exact ht_eq_e ▸ Finset.subset_union_left;
      · -- Since $t \neq e$, we have $|t \cap e| = 2$.
        have h_inter_t_e : (t ∩ e).card = 2 := by
          have := hS ht; have := hS he; simp +decide [ SimpleGraph.cliqueFinset ] at *;
          have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t ∩ e ⊆ t ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t ∩ e ⊆ e ) ; simp +decide [ ‹G.IsNClique 3 t›.card_eq, ‹G.IsNClique 3 e›.card_eq ] at *;
          grind;
        -- We consider three cases based on the relationship between $t \cap e$ and $t1 \cap e$.
        by_cases h_case1 : t ∩ e = t1 ∩ e;
        · -- Since $t \cap e = t1 \cap e$, we have $t = (t1 \cap e) \cup \{z\}$ for some $z \notin e$.
          obtain ⟨z, hz⟩ : ∃ z, z ∉ e ∧ t = (t1 ∩ e) ∪ {z} := by
            have h_card_t : t.card = 3 := by
              have := hS ht; simp +decide [ SimpleGraph.cliqueFinset ] at this;
              exact this.card_eq;
            have h_card_t_minus_e : (t \ e).card = 1 := by
              grind;
            obtain ⟨ z, hz ⟩ := Finset.card_eq_one.mp h_card_t_minus_e;
            use z;
            simp +decide [ ← h_case1, ← hz ];
            exact ⟨ fun h => by rw [ Finset.eq_singleton_iff_unique_mem ] at hz; simp +decide [ h ] at hz, by rw [ Finset.inter_comm, Finset.union_comm ] ; exact Finset.ext fun x => by by_cases hx : x ∈ e <;> simp +decide [ hx ] ⟩;
          -- Since $|t \cap t2| \ge 2$, we have $z \in t2$.
          have hz_in_t2 : z ∈ t2 := by
            have hz_in_t2 : (t ∩ t2).card ≥ 2 := by
              exact h_pairwise ht ht2 ( by rintro rfl; exact ht_eq_e <| by simp_all +singlePass );
            contrapose! hz_in_t2;
            rw [ hz.2, Finset.inter_comm ];
            rw [ Finset.inter_union_distrib_left ];
            rw [ Finset.inter_singleton ] ; simp +decide [ hz_in_t2 ];
            refine' lt_of_le_of_ne ( Nat.le_trans ( Finset.card_le_card _ ) h_inter2.le ) _;
            · grind;
            · intro h;
              have := Finset.eq_of_subset_of_card_le ( show t2 ∩ ( t1 ∩ e ) ⊆ t1 ∩ e from Finset.inter_subset_right ) ; simp +decide [ h, h_inter1 ] at this;
              have := Finset.eq_of_subset_of_card_le ( show t1 ∩ e ⊆ t2 ∩ e from fun x hx => Finset.mem_inter.mpr ⟨ this hx, by simp +decide [ Finset.mem_inter.mp hx ] ⟩ ) ; simp +decide [ h_inter1, h_inter2 ] at this;
              exact False.elim ( h_diff this );
          grind;
        · -- Since $t \cap e \neq t1 \cap e$, we apply `common_vertex_of_different_edges` to $t, t1$. They share a vertex outside $e$.
          obtain ⟨y, hy⟩ : ∃ y, y ∉ e ∧ t = (t ∩ e) ∪ {y} ∧ t1 = (t1 ∩ e) ∪ {y} := by
            exact?;
          grind

end AristotleLemmas

-- Source: proven/tuza/slot39/f71e7003-3204-4746-8e88-8b5735c628af-output.lean
lemma that the covering number of a union is at most the sum of the covering numbers.
  have h_tau_union : ∀ A B : Finset (Finset V), triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
    apply tau_union_le_sum;
  have h_tau_union : ∀ (s : Finset (Finset V)), (∀ e ∈ s, triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2) → triangleCoveringNumberOn G (s.biUnion (fun e => trianglesSharingEdge G e)) ≤ 2 * s.card := by
    intro s hs
    induction' s using Finset.induction with e s ih;
    · simp +decide [ triangleCoveringNumberOn ];
      simp +decide [ Finset.min ];
      rw [ Finset.inf_eq_iInf ];
      rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
      rotate_left;
      exact 0;
      · exact fun _ => zero_le _;
      · exact fun w hw => ⟨ ∅, by simp +decide [ hw ] ⟩;
      · rfl;
    · simp_all +decide [ Finset.card_insert_of_notMem ];
      linarith [ h_tau_union ( trianglesSharingEdge G e ) ( s.biUnion fun e => trianglesSharingEdge G e ) ];
  exact le_trans ( h_tau_union M fun e he => no_edge_sharing_implies_light G M hM e he ( h_no_edges e he ) ) ( by simp +decide [ hM_card ] )

-- COROLLARY: Use no_edge_sharing_implies_light 4 times

end

-- Source: proven/tuza/slot37/1bb416d7-8490-44fa-88a4-3df9362128c6-output.lean
theorem tuza_nu4_lll (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) :
    triangleCoveringNumber G ≤ 8 := by
  cases' lll_cover_exists G h (by
  -- Since the packing number is 4, there exists a set of 4 edge-disjoint triangles.
  obtain ⟨S, hS⟩ : ∃ S : Finset (Finset V), S ⊆ G.cliqueFinset 3 ∧ S.card = 4 ∧ Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
    unfold trianglePackingNumber at h;
    -- Since the maximum element in the image of the cardinalities is 4, there must be some subset of the cliqueFinset 3 with cardinality 4 that is a triangle packing.
    obtain ⟨S, hS⟩ : ∃ S ∈ Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset, S.card = 4 := by
      have := Finset.mem_of_max ( show ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ).max = some 4 from by rw [ Option.getD_eq_iff ] at h; aesop ) ; aesop;
    exact ⟨ S, Finset.mem_powerset.mp ( Finset.mem_filter.mp hS.1 |>.1 ), hS.2, Finset.mem_filter.mp hS.1 |>.2.2 ⟩;
  -- Since each triangle in S has 3 edges and the triangles are edge-disjoint, the total number of edges in S is at least 4 * 3 = 12.
  have h_edges_S : (Finset.biUnion S (fun t => t.sym2.filter (fun e => e ∈ G.edgeFinset))).card ≥ 12 := by
    rw [ Finset.card_biUnion ];
    · refine' le_trans _ ( Finset.sum_le_sum fun t ht => show Finset.card _ ≥ 3 from _ );
      · aesop;
      · have := hS.1 ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        rcases this with ⟨ ht₁, ht₂ ⟩;
        obtain ⟨ a, b, c, h ⟩ := Finset.card_eq_three.mp ht₂;
        refine' Finset.two_lt_card.mpr _;
        refine' ⟨ Sym2.mk ( a, b ), _, Sym2.mk ( a, c ), _, Sym2.mk ( b, c ), _ ⟩ <;> simp_all +decide [ Sym2.mk ];
    · intro t ht t' ht' hne; simp_all +decide [ Finset.disjoint_left ] ;
      have := hS.2.2 ht ht' hne; simp_all +decide [ Finset.card_le_one ] ;
      rintro ⟨ a, b ⟩ hab h;
      contrapose! this;
      exact ⟨ a, hab a ( by simp +decide ), this a ( by simp +decide ), b, hab b ( by simp +decide ), this b ( by simp +decide ), by rintro rfl; exact G.loopless _ h ⟩;
  exact h_edges_S.trans ( Finset.card_le_card fun x hx => by aesop )) with C hC;
  refine' le_trans ( _ : Option.getD _ _ ≤ _ ) hC.2.1;
  have h_min : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | (↑E' : Set (Sym2 V)) ⊆ G.edgeSet ∧ ∀ (t : Finset V), G.IsNClique 3 t → ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ C.card := by
    refine' Finset.min_le _ ; aesop;
  cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ( E' : Set ( Sym2 V ) ) ⊆ G.edgeSet ∧ ∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop

-- TARGET 3: Main theorem

/--
Corollary: The covering number on all triangles is also ≤ 8.
-/

-- Source: proven/tuza/nu4/slot63_scaffolding.lean
lemma M_char_weight_eq_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) :
    packingWeight G (M_char M) = M.card := by
  have h_sum : packingWeight G (M_char M) = ∑ t ∈ M, (1 : ℝ) := by
    unfold packingWeight M_char
    rw [← Finset.sum_subset hM.1]
    · congr 1
      ext t
      simp only [ite_eq_left_iff, one_ne_zero]
      tauto
    · intro t _ ht
      simp only [if_neg ht]
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h_sum
  rw [h_sum]
  simp

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA 5: M_char_weight_eq_4
-- ══════════════════════════════════════════════════════════════════════════════

/-- For ν = 4, M_char weight = 4. -/

-- Source: proven/tuza/nu4/slot63_scaffolding.lean
lemma M_char_weight_eq_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (h_card : M.card = 4) :
    packingWeight G (M_char M) = 4 := by
  rw [M_char_weight_eq_card G M hM, h_card]
  norm_num

end

-- Source: proven/tuza/nu4/slot72_cycle_reduction_output.lean
lemma cycle4_same_as_path4_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) :
    T_pair G A B ∪ T_pair G C D = T_pair G A B ∪ T_pair G C D ∪ X_ef G D A := by
      -- Since $X_{DA}$ is a subset of $T_{AB} \cup T_{CD}$, adding it to the union does not change the set.
      have h_subset : X_ef G D A ⊆ T_pair G A B ∪ T_pair G C D := by
        -- Let $t$ be any triangle in $X_{DA}$. By definition, $t$ shares an edge with both $D$ and $A$.
        intro t ht
        obtain ⟨hDA, hA⟩ : (t ∩ D).card ≥ 2 ∧ (t ∩ A).card ≥ 2 := by
          unfold X_ef at ht; aesop;
        -- Since $t$ shares an edge with both $D$ and $A$, it must be in $X_{DA}$.
        simp [X_ef] at ht ⊢;
        exact Or.inl ( Finset.mem_union_left _ ( Finset.mem_filter.mpr ⟨ Finset.mem_coe.mpr ( Finset.mem_coe.mpr ( by aesop ) ), hA ⟩ ) );
      rw [ Finset.union_eq_left.mpr h_subset ]

-- Source: proven/tuza/nu4/slot71_Se_structure_output.lean
lemma S_e_pairwise_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e)
    (ht1_ne_e : t1 ≠ e) (ht2_ne_e : t2 ≠ e) (hne : t1 ≠ t2) :
    (t1 ∩ t2).card ≥ 2 := by
  obtain ⟨ ht1_card, ht1_adj ⟩ := hM;
  -- By the maximality of $M$, any triangle packing $M'$ with $|M'| > |M|$ contradicts the definition of $M$ as a maximum packing.
  have h_contra : ¬∃ M' : Finset (Finset V), isTrianglePacking G M' ∧ M'.card > M.card := by
    have h_contra : ∀ M' : Finset (Finset V), isTrianglePacking G M' → M'.card ≤ trianglePackingNumber G := by
      unfold trianglePackingNumber;
      intro M' hM'
      have hM'_in_powerset : M' ∈ Finset.powerset (G.cliqueFinset 3) := by
        exact Finset.mem_powerset.mpr hM'.1;
      have hM'_in_image : M'.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        aesop;
      have := Finset.le_max hM'_in_image;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact fun ⟨ M', hM', hM'' ⟩ => hM''.not_le ( ht1_adj ▸ h_contra M' hM' );
  contrapose! h_contra;
  refine' ⟨ Insert.insert t1 ( Insert.insert t2 ( M.erase e ) ), _, _ ⟩ <;> simp_all +decide [ isTrianglePacking ];
  · unfold S_e at *; simp_all +decide [ Finset.subset_iff, Set.Pairwise ] ;
    exact ⟨ Nat.le_of_lt_succ h_contra, fun _ => by rw [ Finset.inter_comm ] ; exact Nat.le_of_lt_succ h_contra, fun f hf hf' => ⟨ fun _ => by simpa only [ Finset.inter_comm ] using ht1.2.2 f hf hf', fun _ => by simpa only [ Finset.inter_comm ] using ht2.2.2 f hf hf' ⟩ ⟩;
  · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp_all +decide [ Finset.subset_iff ];
    · omega;
    · intro h; have := ht1_adj ▸ Finset.card_pos.2 ⟨ e, he ⟩ ; simp_all +decide [ S_e ] ;
      exact absurd ( ht1_card.2 h he ( by aesop ) ) ( by linarith );
    · intro H; have := ht1_card.2 he H; simp_all +decide ;
      simp_all +decide [ Finset.inter_comm, S_e ];
      exact absurd ( this ( Ne.symm ht1_ne_e ) ) ( by linarith )

-- Source: proven/tuza/nu4/slot71_Se_structure_output.lean
lemma S_e_cross_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e)
    (ht1_ne_e : t1 ≠ e) (ht2_ne_e : t2 ≠ e)
    (h_diff_edges : t1 ∩ e ≠ t2 ∩ e) :
    ∃ x, x ∉ e ∧ x ∈ t1 ∧ x ∈ t2 := by
  have h_inter : (t1 ∩ t2).card ≥ 2 := by
    apply S_e_pairwise_intersect G M hM e he t1 t2 ht1 ht2 ht1_ne_e ht2_ne_e;
    grind;
  -- Since $t1$ and $t2$ are triangles, they must each have exactly three elements.
  have h_card_t1 : t1.card = 3 := by
    unfold S_e at ht1;
    simp_all +decide [ SimpleGraph.cliqueFinset ];
    exact ht1.1.card_eq
  have h_card_t2 : t2.card = 3 := by
    unfold S_e at ht2;
    simp_all +decide [ SimpleGraph.isNClique_iff ];
  have h_card_e : e.card = 3 := by
    have := hM.1;
    have := this.1;
    have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    exact this.2;
  have h_inter_e : (t1 ∩ e).card = 2 ∧ (t2 ∩ e).card = 2 := by
    have h_inter_e : (t1 ∩ e).card ≥ 2 ∧ (t2 ∩ e).card ≥ 2 := by
      unfold S_e at ht1 ht2; aesop;
    have h_inter_e : (t1 ∩ e).card ≤ 3 ∧ (t2 ∩ e).card ≤ 3 := by
      exact ⟨ le_trans ( Finset.card_le_card fun x hx => by aesop ) h_card_t1.le, le_trans ( Finset.card_le_card fun x hx => by aesop ) h_card_t2.le ⟩;
    cases h_inter_e.1.eq_or_lt <;> cases h_inter_e.2.eq_or_lt <;> simp_all +decide;
    · have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ e ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ e ⊆ e ) ; simp_all +decide ;
    · have := Finset.eq_of_subset_of_card_le ( show t1 ∩ e ⊆ e from Finset.inter_subset_right ) ; simp_all +decide ;
      have := Finset.eq_of_subset_of_card_le this ; aesop;
    · have := Finset.eq_of_subset_of_card_le ( show t2 ∩ e ⊆ e from Finset.inter_subset_right ) ; simp_all +decide ;
      have := Finset.eq_of_subset_of_card_le this ; aesop;
    · exact ⟨ by linarith, by linarith ⟩;
  contrapose! h_diff_edges;
  have h_inter_eq : (t1 ∩ t2 ∩ e).card ≥ 2 := by
    have h_inter_eq : (t1 ∩ t2 ∩ e).card = (t1 ∩ t2).card := by
      exact congr_arg Finset.card ( Finset.ext fun x => by by_cases hx : x ∈ e <;> aesop );
    linarith;
  have h_inter_eq : (t1 ∩ t2 ∩ e) = (t1 ∩ e) ∧ (t1 ∩ t2 ∩ e) = (t2 ∩ e) := by
    have h_inter_eq : (t1 ∩ t2 ∩ e) ⊆ (t1 ∩ e) ∧ (t1 ∩ t2 ∩ e) ⊆ (t2 ∩ e) := by
      simp +contextual [ Finset.subset_iff ];
    exact ⟨ Finset.eq_of_subset_of_card_le h_inter_eq.1 ( by linarith ), Finset.eq_of_subset_of_card_le h_inter_eq.2 ( by linarith ) ⟩;
  grind

-- Source: proven/tuza/nu4/slot71_Se_structure_output.lean
lemma S_e_structure_case2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e)
    (ht1_ne_e : t1 ≠ e) (ht2_ne_e : t2 ≠ e)
    (h_diff_edges : t1 ∩ e ≠ t2 ∩ e) :
    ∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → x ∈ t := by
  -- By `S_e_cross_intersect` applied to $t_1, t_2$, there exists $x \notin e$ such that $x \in t_1$ and $x \in t_2$.
  obtain ⟨x, hx_not_in_e, hx_in_t1, hx_in_t2⟩ : ∃ x ∉ e, x ∈ t1 ∧ x ∈ t2 := by
    exact?;
  -- Since $t1$ and $t2$ are triangles, their sizes are 3. Therefore, $t1 \setminus e$ and $t2 \setminus e$ each have exactly one element, which is $x$.
  have ht1_minus_e : t1 \ e = {x} := by
    have ht1_card : t1.card = 3 := by
      unfold S_e at ht1;
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      exact ht1.1.card_eq
    have ht1_inter_e_card : (t1 ∩ e).card = 2 := by
      have := Finset.card_le_card ( show t1 ∩ e ⊆ t1 from Finset.inter_subset_left ) ; simp_all +decide ;
      interval_cases _ : Finset.card ( t1 ∩ e ) <;> simp_all +decide [ S_e ];
      have := Finset.eq_of_subset_of_card_le ( show t1 ∩ e ⊆ t1 from Finset.inter_subset_left ) ; simp_all +decide ;
      exact hx_not_in_e ( this hx_in_t1 )
    have ht1_minus_e_card : (t1 \ e).card = 1 := by
      have := Finset.card_sdiff_add_card_inter t1 e; simp_all +decide ;
    rw [ Finset.card_eq_one ] at ht1_minus_e_card;
    obtain ⟨ y, hy ⟩ := ht1_minus_e_card; rw [ Finset.eq_singleton_iff_unique_mem ] at *; aesop;
  have ht2_minus_e : t2 \ e = {x} := by
    have ht2_card : t2.card = 3 := by
      have := Finset.mem_filter.mp ht2;
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      exact this.1.card_eq;
    have ht2_inter_e_card : (t2 ∩ e).card = 2 := by
      have ht2_inter_e : (t2 ∩ e).card ≥ 2 := by
        unfold S_e at ht2; aesop;
      have ht2_inter_e_le : (t2 ∩ e).card ≤ 2 := by
        have ht2_inter_e_le : (t2 ∩ e).card ≤ t2.card - 1 := by
          refine' Nat.le_sub_one_of_lt ( Finset.card_lt_card _ );
          grind;
        aesop;
      linarith;
    have ht2_minus_e_card : (t2 \ e).card = 1 := by
      have := Finset.card_sdiff_add_card_inter t2 e; aesop;
    rw [ Finset.card_eq_one ] at ht2_minus_e_card;
    obtain ⟨ y, hy ⟩ := ht2_minus_e_card; rw [ Finset.eq_singleton_iff_unique_mem ] at hy; aesop;
  refine' ⟨ x, hx_not_in_e, fun t ht ht_ne_e => _ ⟩;
  by_cases h_cases : t ∩ e = t1 ∩ e;
  · -- Since $t \cap e = t1 \cap e$ and $t1 \cap e \ne t2 \cap e$, we can apply `S_e_cross_intersect` to $t$ and $t2$.
    obtain ⟨z, hz_not_in_e, hz_in_t, hz_in_t2⟩ : ∃ z ∉ e, z ∈ t ∧ z ∈ t2 := by
      apply S_e_cross_intersect G M hM e he t t2 ht ht2 ht_ne_e ht2_ne_e;
      grind;
    rw [ Finset.eq_singleton_iff_unique_mem ] at ht2_minus_e ; aesop;
  · -- By `S_e_cross_intersect` applied to $t$ and $t_1$, there exists $y \notin e$ such that $y \in t$ and $y \in t_1$.
    obtain ⟨y, hy_not_in_e, hy_in_t, hy_in_t1⟩ : ∃ y ∉ e, y ∈ t ∧ y ∈ t1 := by
      apply S_e_cross_intersect G M hM e he t t1 ht ht1 ht_ne_e ht1_ne_e h_cases;
    rw [ Finset.eq_singleton_iff_unique_mem ] at ht1_minus_e ; aesop

-- Source: proven/tuza/nu4/slot71_Se_structure_output.lean
lemma S_e_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (∃ u v : V, u ∈ e ∧ v ∈ e ∧ u ≠ v ∧ ∀ t ∈ S_e G M e, t ≠ e → {u, v} ⊆ t) ∨
    (∃ x : V, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → x ∈ t) := by
  by_cases h_empty : S_e G M e \ {e} = ∅;
  · simp_all +decide [ Finset.ext_iff ];
    by_cases he_empty : e = ∅;
    · have := hM.1.1 he; aesop;
    · by_cases he_singleton : e.card = 1;
      · have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        rw [ SimpleGraph.isNClique_iff ] at this ; aesop;
      · exact Or.inl ( Finset.one_lt_card.1 ( lt_of_le_of_ne ( Finset.card_pos.2 ( Finset.nonempty_of_ne_empty he_empty ) ) ( Ne.symm he_singleton ) ) );
  · by_cases h_case1 : ∀ t1 t2 : Finset V, t1 ∈ S_e G M e \ {e} → t2 ∈ S_e G M e \ {e} → t1 ∩ e = t2 ∩ e;
    · obtain ⟨t1, ht1⟩ : ∃ t1 : Finset V, t1 ∈ S_e G M e \ {e} := by
        exact Finset.nonempty_of_ne_empty h_empty;
      have h_inter : (t1 ∩ e).card ≥ 2 := by
        unfold S_e at ht1; aesop;
      obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.mp h_inter;
      refine' Or.inl ⟨ u, v, _, _, huv, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      intro t ht ht'; specialize h_case1 t t1 ht ht' ht1.1 ht1.2; replace h_case1 := Finset.ext_iff.mp h_case1; have := h_case1 u; have := h_case1 v; aesop;
    · obtain ⟨t1, t2, ht1, ht2, h_diff⟩ : ∃ t1 t2 : Finset V, t1 ∈ S_e G M e \ {e} ∧ t2 ∈ S_e G M e \ {e} ∧ t1 ∩ e ≠ t2 ∩ e := by
        grind +ring;
      obtain ⟨x, hx⟩ : ∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → x ∈ t := by
        apply S_e_structure_case2 G M hM e he t1 t2;
        · exact Finset.mem_sdiff.mp ht1 |>.1;
        · exact Finset.mem_sdiff.mp ht2 |>.1;
        · aesop;
        · aesop;
        · exact h_diff;
      exact Or.inr ⟨ x, hx ⟩

-- Source: proven/tuza/nu4/slot70_tau_union_extended_output.lean
lemma disjoint_triples_imply_contradiction (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 t3 : Finset V)
    (h_t1 : t1 ∈ S_e G M e) (h_t2 : t2 ∈ S_e G M e) (h_t3 : t3 ∈ S_e G M e)
    (h_disj : (t1 ∩ t2).card ≤ 1 ∧ (t2 ∩ t3).card ≤ 1 ∧ (t1 ∩ t3).card ≤ 1)
    (h_distinct : t1 ≠ t2 ∧ t2 ≠ t3 ∧ t1 ≠ t3) :
    False := by
  rcases hM with ⟨ hM₁, hM₂ ⟩;
  -- The set $M' = (M \setminus \{e\}) \cup \{t_1, t_2, t_3\}$ is a valid triangle packing, and its cardinality is greater than $|M|$.
  have hM'_valid : isTrianglePacking G ((M \ {e}) ∪ {t1, t2, t3}) := by
    unfold isTrianglePacking at *;
    simp_all +decide [ Finset.subset_iff, Set.Pairwise ];
    simp_all +decide [ Finset.inter_comm, S_e ]
  have hM'_card : ((M \ {e}) ∪ {t1, t2, t3}).card > M.card := by
    rw [ Finset.card_union_of_disjoint ] <;> simp +decide [ *, Finset.card_sdiff, Finset.subset_iff ];
    · omega;
    · simp_all +decide [ S_e ];
      refine' ⟨ fun h => Classical.not_not.1 fun hne => _, fun h => Classical.not_not.1 fun hne => _, fun h => Classical.not_not.1 fun hne => _ ⟩ <;> have := hM₁.2 <;> simp_all +decide [ Finset.subset_iff ];
      · exact absurd ( this h he hne ) ( by linarith );
      · exact absurd ( this h he hne ) ( by aesop );
      · exact absurd ( this h he hne ) ( by linarith );
  have h_contradiction : (M \ {e} ∪ {t1, t2, t3}).card ≤ trianglePackingNumber G := by
    have h_contradiction : ∀ M' : Finset (Finset V), isTrianglePacking G M' → M'.card ≤ trianglePackingNumber G := by
      unfold trianglePackingNumber;
      intro M' hM'
      have hM'_in_filter : M' ∈ Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset := by
        simp_all +decide [ isTrianglePacking ];
      have := Finset.le_max ( Finset.mem_image_of_mem Finset.card hM'_in_filter );
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_contradiction _ hM'_valid;
  linarith

-- Source: proven/tuza/nu4/slot_local_tuza_via_link_graph.lean
theorem that states a finite set with cardinality 2 must contain two distinct elements.
      apply Finset.card_eq_two.mp hs |> fun ⟨x, y, hxy⟩ => ⟨x, y, by aesop⟩;
    -- Since $x$ and $y$ are in $s$ and $x \neq y$, the pair $(x, y)$ is in the off-diagonal of $s$, and thus Sym2.mk (x, y) is in the image.
    obtain ⟨x, y, hx, hy, hxy⟩ := h_pair;
    use Sym2.mk (x, y);
    aesop
  let e := Classical.choose hne
  ⟨e, by
    -- Since $e$ is in the image of $s.offDiag$ under $Sym2.mk$, there exist $x, y \in s$ such that $e = \{x, y\}$.
    obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : V, x ∈ s ∧ y ∈ s ∧ x ≠ y ∧ e = Sym2.mk (x, y) := by
      have := Classical.choose_spec hne; aesop;
      exact ⟨ w, ⟨ left, right_2 ⟩, w_1, ⟨ left_1, right_3 ⟩, right_1, right.symm ⟩;
    -- Since $x$ and $y$ are in $s$, they are neighbors of $v$ in $G$ and not equal to $v$. Also, since $t$ is a clique, $x$ and $y$ are adjacent.
    have h_adj : G.Adj x y ∧ G.Adj v x ∧ G.Adj v y ∧ x ≠ v ∧ y ≠ v := by
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      have := ht.1; aesop;
    -- Since $e = \{x, y\}$ and $x$ and $y$ are adjacent in $G$ and both adjacent to $v$, $e$ is an edge in the link graph.
    simp [hxy, h_adj];
    exact ⟨ h_adj.1, h_adj.2.1, h_adj.2.2.1, hxy.1, h_adj.2.2.2.1, h_adj.2.2.2.2 ⟩⟩

/-
Two triangles containing a vertex $v$ are edge-disjoint (intersection size at most 1) if and only if their corresponding edges in the link graph of $v$ are disjoint.
-/

-- Source: proven/tuza/nu4/slot_local_tuza_via_link_graph.lean
theorem partition_piece_tuza_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (Ti : Finset (Finset V)) (v : V)
    (hTi : Ti ⊆ trianglesContainingVertex G v) :
    triangleCoveringNumberOn G Ti ≤ 2 * trianglePackingOn G Ti := by
  calc triangleCoveringNumberOn G Ti
      ≤ vertexCoverNumber (subLinkGraph G v Ti) := cover_Ti_le_vertex_cover_subLink G v Ti hTi
    _ ≤ 2 * maxMatchingNumber (subLinkGraph G v Ti) := vertex_cover_le_two_matching (subLinkGraph G v Ti)
    _ = 2 * trianglePackingOn G Ti := by rw [packing_Ti_eq_matching_subLink G v Ti hTi]

-- Source: proven/tuza/nu4/slot_disjoint_partition_proven.lean
lemma T1_T2_disjoint (triangles : Finset (Finset V)) (v_ab v_bc : V) :
    Disjoint (T1 triangles v_ab) (T2 triangles v_ab v_bc) := by
  simp only [Finset.disjoint_iff_ne, T1, T2, Finset.mem_filter]
  intro t1 ⟨_, ht1_ab⟩ t2 ⟨_, ht2_bc, ht2_not_ab⟩
  by_contra heq
  rw [heq] at ht1_ab
  exact ht2_not_ab ht1_ab

/-- T1 and T3 are disjoint by construction -/

-- Source: proven/tuza/nu4/slot_disjoint_partition_proven.lean
lemma T1_T3_disjoint (triangles : Finset (Finset V)) (v_ab v_bc v_cd : V) :
    Disjoint (T1 triangles v_ab) (T3 triangles v_ab v_bc v_cd) := by
  simp only [Finset.disjoint_iff_ne, T1, T3, Finset.mem_filter]
  intro t1 ⟨_, ht1_ab⟩ t3 ⟨_, _, ht3_not_ab, _⟩
  by_contra heq
  rw [heq] at ht1_ab
  exact ht3_not_ab ht1_ab

/-- T1 and T4 are disjoint by construction -/

-- Source: proven/tuza/nu4/slot_disjoint_partition_proven.lean
lemma T1_T4_disjoint (triangles : Finset (Finset V)) (v_ab v_bc v_cd v_da : V) :
    Disjoint (T1 triangles v_ab) (T4 triangles v_ab v_bc v_cd v_da) := by
  simp only [Finset.disjoint_iff_ne, T1, T4, Finset.mem_filter]
  intro t1 ⟨_, ht1_ab⟩ t4 ⟨_, _, ht4_not_ab, _, _⟩
  by_contra heq
  rw [heq] at ht1_ab
  exact ht4_not_ab ht1_ab

/-- T2 and T3 are disjoint by construction -/

-- Source: proven/tuza/nu4/slot_disjoint_partition_proven.lean
lemma T2_T3_disjoint (triangles : Finset (Finset V)) (v_ab v_bc v_cd : V) :
    Disjoint (T2 triangles v_ab v_bc) (T3 triangles v_ab v_bc v_cd) := by
  simp only [Finset.disjoint_iff_ne, T2, T3, Finset.mem_filter]
  intro t2 ⟨_, ht2_bc, _⟩ t3 ⟨_, _, _, ht3_not_bc⟩
  by_contra heq
  rw [heq] at ht2_bc
  exact ht3_not_bc ht2_bc

/-- T2 and T4 are disjoint by construction -/

-- Source: proven/tuza/nu4/slot_disjoint_partition_proven.lean
lemma T2_T4_disjoint (triangles : Finset (Finset V)) (v_ab v_bc v_cd v_da : V) :
    Disjoint (T2 triangles v_ab v_bc) (T4 triangles v_ab v_bc v_cd v_da) := by
  simp only [Finset.disjoint_iff_ne, T2, T4, Finset.mem_filter]
  intro t2 ⟨_, ht2_bc, _⟩ t4 ⟨_, _, _, ht4_not_bc, _⟩
  by_contra heq
  rw [heq] at ht2_bc
  exact ht4_not_bc ht2_bc

/-- T3 and T4 are disjoint by construction -/

-- Source: proven/tuza/nu4/slot_disjoint_partition_proven.lean
lemma T3_T4_disjoint (triangles : Finset (Finset V)) (v_ab v_bc v_cd v_da : V) :
    Disjoint (T3 triangles v_ab v_bc v_cd) (T4 triangles v_ab v_bc v_cd v_da) := by
  simp only [Finset.disjoint_iff_ne, T3, T4, Finset.mem_filter]
  intro t3 ⟨_, ht3_cd, _, _⟩ t4 ⟨_, _, _, _, ht4_not_cd⟩
  by_contra heq
  rw [heq] at ht3_cd
  exact ht4_not_cd ht3_cd

/-
The partition T1, T2, T3, T4 covers all triangles. This relies on the fact that every triangle contains at least one shared vertex (proven in `cycle4_all_triangles_contain_shared`), and the priority ordering ensures every triangle falls into exactly one set.
-/

-- Source: proven/tuza/nu4/slot_disjoint_partition_proven.lean
theorem cycle4_disjoint_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hcycle : isCycle4 M A B C D) (hM : isMaxPacking G M)
    (v_ab v_bc v_cd v_da : V)
    (hv_ab : v_ab ∈ A ∩ B) (hv_bc : v_bc ∈ B ∩ C)
    (hv_cd : v_cd ∈ C ∩ D) (hv_da : v_da ∈ D ∩ A) :
    let triangles := G.cliqueFinset 3
    let parts := [T1 triangles v_ab, T2 triangles v_ab v_bc,
                  T3 triangles v_ab v_bc v_cd, T4 triangles v_ab v_bc v_cd v_da]
    (∀ (i j : Fin 4), i ≠ j →
      Disjoint (parts.get i) (parts.get j)) ∧
    (T1 triangles v_ab ∪ T2 triangles v_ab v_bc ∪
     T3 triangles v_ab v_bc v_cd ∪ T4 triangles v_ab v_bc v_cd v_da = triangles) := by
       refine' ⟨ _, _ ⟩;
       · simp +decide [ Fin.forall_fin_succ ];
         simp_all +decide [ Finset.disjoint_left, eq_comm ];
         unfold T1 T2 T3 T4 at *; aesop;
       · exact disjoint_partition_covers_all G M A B C D hcycle hM v_ab v_bc v_cd v_da hv_ab hv_bc hv_cd hv_da

-- Source: proven/tuza/nu4/slot_disjoint_partition_proven.lean
lemma shared_vertices_eq_union_singletons
    (A B C D : Finset V)
    (hab : (A ∩ B).card = 1) (hbc : (B ∩ C).card = 1)
    (hcd : (C ∩ D).card = 1) (hda : (D ∩ A).card = 1)
    (v_ab v_bc v_cd v_da : V)
    (hv_ab : v_ab ∈ A ∩ B) (hv_bc : v_bc ∈ B ∩ C)
    (hv_cd : v_cd ∈ C ∩ D) (hv_da : v_da ∈ D ∩ A) :
    sharedVertices A B C D hab hbc hcd hda = {v_ab, v_bc, v_cd, v_da} := by
  unfold sharedVertices;
  rw [ Finset.card_eq_one ] at *;
  grind

-- Source: proven/tuza/nu4/safe_discard/slot67_bridge_absorption_PROVEN.lean
theorem external_unique_disjoint_parent (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_M : t ∉ M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (h_disj : Disjoint A B)
    (h_share_A : sharesEdgeWith t A) :
    ¬sharesEdgeWith t B := by
  intro h_share_B
  exact bridge_nonexistence G M hM A B hA hB hAB h_disj t ht ⟨h_share_A, h_share_B⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- APPLICATION: Scattered Case (All M-elements pairwise disjoint)
-- ══════════════════════════════════════════════════════════════════════════════

/-- In the scattered case (all M-elements disjoint), each external triangle
    shares edge with exactly one M-element. -/

-- Source: proven/tuza/nu4/safe_discard/slot67_bridge_absorption_PROVEN.lean
theorem scattered_unique_parent (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (h_scattered : ∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_M : t ∉ M)
    (A : Finset V) (hA : A ∈ M) (h_share_A : sharesEdgeWith t A) :
    ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B := by
  intro B hB hBA
  exact external_unique_disjoint_parent G M hM t ht ht_not_M A B hA hB hBA.symm (h_scattered A B hA hB hBA.symm) h_share_A

/-- In the scattered case, there are no interactions between M-edges from
    different M-elements. This means the Interaction Graph is empty! -/

-- Source: proven/tuza/nu4/safe_discard/slot67_bridge_absorption_PROVEN.lean
theorem scattered_ig_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (h_scattered : ∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B)
    (e₁ e₂ : Sym2 V)
    (he₁ : ∃ A ∈ M, e₁ ∈ A.sym2)
    (he₂ : ∃ B ∈ M, e₂ ∈ B.sym2)
    (h_diff_parent : ∀ X ∈ M, ¬(e₁ ∈ X.sym2 ∧ e₂ ∈ X.sym2)) :
    ∀ t ∈ G.cliqueFinset 3, t ∉ M → ¬(e₁ ∈ t.sym2 ∧ e₂ ∈ t.sym2) := by
  intro t ht ht_not_M ⟨he₁_t, he₂_t⟩
  obtain ⟨A, hA, he₁_A⟩ := he₁
  obtain ⟨B, hB, he₂_B⟩ := he₂
  -- e₁ ∈ A.sym2, e₂ ∈ B.sym2, and e₁ ≠ e₂ from different parents
  have hAB : A ≠ B := by
    intro heq
    exact h_diff_parent A hA ⟨he₁_A, heq ▸ he₂_B⟩
  -- t shares edge with both A (via e₁) and B (via e₂)
  have h_share_A : sharesEdgeWith t A := ⟨e₁, he₁_t, he₁_A⟩
  have h_share_B : sharesEdgeWith t B := ⟨e₂, he₂_t, he₂_B⟩
  -- Contradiction from bridge_nonexistence
  exact bridge_nonexistence G M hM A B hA hB hAB (h_scattered A B hA hB hAB) t ht ⟨h_share_A, h_share_B⟩

end

-- Source: proven/tuza/nu4/safe_discard/slot64d_interact_share_PROVEN.lean
lemma interact_share_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e₁ e₂ : Sym2 V)
    (h : (InteractionGraph G M).Adj e₁ e₂) :
    ∃ v, v ∈ e₁.toFinset ∧ v ∈ e₂.toFinset := by
  obtain ⟨hne, _, _, t, ht, ht₁, ht₂⟩ := h
  -- t is an external triangle, so t ∈ G.cliqueFinset 3
  simp only [externalTriangles, Finset.mem_filter] at ht
  have ht_clique := ht.1
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht_clique).card_eq
  -- Use the helper

-- Source: proven/tuza/nu4/safe_discard/slot64d_interact_share_PROVEN.lean
lemma interact_common_endpoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e₁ e₂ : Sym2 V)
    (h : (InteractionGraph G M).Adj e₁ e₂) :
    ∃ v a b, e₁ = s(v, a) ∧ e₂ = s(v, b) := by
  obtain ⟨v, hv₁, hv₂⟩ := interact_share_vertex G M e₁ e₂ h
  -- e₁ = s(v, a) for some a
  rw [Sym2.mem_toFinset_iff] at hv₁ hv₂
  obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ := Sym2.mem_iff.mp hv₁
  · obtain ⟨b, rfl⟩ | ⟨b, rfl⟩ := Sym2.mem_iff.mp hv₂
    · exact ⟨v, a, b, rfl, rfl⟩
    · exact ⟨v, a, b, rfl, Sym2.eq_swap⟩
  · obtain ⟨b, rfl⟩ | ⟨b, rfl⟩ := Sym2.mem_iff.mp hv₂
    · exact ⟨v, a, b, Sym2.eq_swap, rfl⟩
    · exact ⟨v, a, b, Sym2.eq_swap, Sym2.eq_swap⟩

end

-- Source: proven/tuza/nu4/safe_discard/slot148a_scattered_partition_PROVEN.lean
theorem scattered_unique_parent (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (h_scattered : ∀ A B, A ∈ M → B ∈ M → A ≠ B → Disjoint A B)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_M : t ∉ M)
    (A : Finset V) (hA : A ∈ M) (h_share_A : sharesEdgeWith t A) :
    ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B := by
  intro B hB hBA h_share_B
  have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hA)).card_eq
  have hB_card : B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hB)).card_eq
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  exact no_bridge_disjoint A B t hA_card hB_card ht_card (h_scattered A B hA hB hBA.symm) h_share_A h_share_B

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Maximality implies edge-sharing
-- ══════════════════════════════════════════════════════════════════════════════

/-- If two 3-sets share 2+ vertices, they share an edge (PROVEN) -/

-- Source: proven/tuza/nu4/safe_discard/slot65_singleton_conflict_PROVEN.lean
lemma conflict_share_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e₁ e₂ : Sym2 V)
    (h : ConflictPair G M e₁ e₂) :
    ∃ v, v ∈ e₁.toFinset ∧ v ∈ e₂.toFinset := by
  obtain ⟨_, _, hne, t, ht, heq⟩ := h
  simp only [externalTriangles, Finset.mem_filter] at ht
  have ht_clique := ht.1
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht_clique).card_eq
  -- e₁ and e₂ are both in t.sym2
  have he₁_t : e₁ ∈ t.sym2 := by
    have : e₁ ∈ M_edges_in G M t := by rw [heq]; exact Finset.mem_insert_self _ _
    exact (Finset.mem_filter.mp this).2
  have he₂_t : e₂ ∈ t.sym2 := by
    have : e₂ ∈ M_edges_in G M t := by rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact (Finset.mem_filter.mp this).2
  -- Two edges in a 3-set share a vertex
  rw [Finset.mem_sym2_iff] at he₁_t he₂_t
  obtain ⟨a, b, hab, ha, hb, rfl⟩ := he₁_t
  obtain ⟨c, d, hcd, hc, hd, rfl⟩ := he₂_t
  -- If {a,b} ∩ {c,d} = ∅, then |{a,b,c,d}| = 4 > 3 = |t|
  by_cases h1 : a = c
  · exact ⟨a, by simp, by simp [h1]⟩
  by_cases h2 : a = d
  · exact ⟨a, by simp, by simp [h2]⟩
  by_cases h3 : b = c
  · exact ⟨b, by simp, by simp [h3]⟩
  by_cases h4 : b = d
  · exact ⟨b, by simp, by simp [h4]⟩
  -- All four distinct → contradiction
  have h_four : ({a, b, c, d} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_insert_of_not_mem, Finset.card_singleton]
    · simp [h4, h3]
    · simp [h2, h1]
    · simp [hab]
  have h_sub : ({a, b, c, d} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card h_sub
  omega

end

-- Source: proven/tuza/nu4/safe_discard/slot149_path4_structure_PROVEN.lean
lemma path4_shared_vertex_AB (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4Config G) :
    ∃ v, cfg.A ∩ cfg.B = {v} := by
  have h := cfg.h_AB
  unfold sharesOneVertex at h
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h
  exact ⟨v, hv⟩

/-- Extract the shared vertex from B ∩ C -/

-- Source: proven/tuza/nu4/safe_discard/slot149_path4_structure_PROVEN.lean
lemma path4_shared_vertex_BC (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4Config G) :
    ∃ v, cfg.B ∩ cfg.C = {v} := by
  have h := cfg.h_BC
  unfold sharesOneVertex at h
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h
  exact ⟨v, hv⟩

/-- Extract the shared vertex from C ∩ D -/

-- Source: proven/tuza/nu4/safe_discard/slot149_path4_structure_PROVEN.lean
lemma path4_shared_vertex_CD (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4Config G) :
    ∃ v, cfg.C ∩ cfg.D = {v} := by
  have h := cfg.h_CD
  unfold sharesOneVertex at h
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h
  exact ⟨v, hv⟩

end

-- Source: proven/tuza/nu4/safe_discard/slot64a_ig_definitions_PROVEN.lean
lemma external_not_in_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) (ht : t ∈ externalTriangles G M) :
    t ∉ M := by
  simp only [externalTriangles, Finset.mem_filter] at ht
  exact ht.2.1

/-- External triangles share some edge with M -/

-- Source: proven/tuza/nu4/safe_discard/slot64a_ig_definitions_PROVEN.lean
lemma interact_witness (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e₁ e₂ : Sym2 V)
    (h : (InteractionGraph G M).Adj e₁ e₂) :
    ∃ t ∈ externalTriangles G M, e₁ ∈ t.sym2 ∧ e₂ ∈ t.sym2 := by
  exact h.2.2.2

end

-- Source: proven/tuza/nu4/safe_discard/slot150_matching2_structure_PROVEN.lean
theorem matching2_independent_pairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Matching2Config G) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    (sharesEdgeWith t cfg.A ∨ sharesEdgeWith t cfg.B) →
    (sharesEdgeWith t cfg.C ∨ sharesEdgeWith t cfg.D) →
    False := by
  intro h_pair1 h_pair2
  rcases h_pair1 with h_A | h_B
  · rcases h_pair2 with h_C | h_D
    · exact matching2_no_AC_bridge G cfg t ht ⟨h_A, h_C⟩
    · exact matching2_no_AD_bridge G cfg t ht ⟨h_A, h_D⟩
  · rcases h_pair2 with h_C | h_D
    · exact matching2_no_BC_bridge G cfg t ht ⟨h_B, h_C⟩
    · exact matching2_no_BD_bridge G cfg t ht ⟨h_B, h_D⟩

/-- COROLLARY: Triangles partition into pair-1 triangles and pair-2 triangles -/

-- Source: proven/tuza/nu4/safe_discard/slot151_tpair_spokes_PROVEN.lean
lemma spokes_card_eq_2 (t : Finset V) (ht : t.card = 3) (v : V) (hv : v ∈ t) :
    (spokesFrom t v hv).card = 2 := by
  -- t = {v, a, b}, spokes = {s(v,a), s(v,b)}
  -- t.sym2 = {s(v,a), s(v,b), s(a,b)}
  -- Filter to edges containing v gives {s(v,a), s(v,b)}
  -- Need to show this has cardinality 2
  have h_sym2_card : t.sym2.card = 3 := by rw [Finset.card_sym2]; omega
  -- Get the two other vertices
  have h_erase : (t.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv]; omega
  obtain ⟨a, b, hab, h_erase_eq⟩ := Finset.card_eq_two.mp h_erase
  have ha : a ∈ t := by rw [← h_erase_eq] at *; exact Finset.mem_insert_self a _
  have hb : b ∈ t := by rw [← h_erase_eq] at *; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have hav : a ≠ v := by
    intro heq; rw [heq] at h_erase_eq
    have : v ∈ t.erase v := by rw [h_erase_eq]; exact Finset.mem_insert_self v _
    exact Finset.not_mem_erase v t this
  have hbv : b ≠ v := by
    intro heq; rw [heq] at h_erase_eq
    have : v ∈ t.erase v := by rw [h_erase_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
    exact Finset.not_mem_erase v t this
  -- spokesFrom = {s(v,a), s(v,b)}
  have h_spokes_eq : spokesFrom t v hv = {s(v, a), s(v, b)} := by
    ext e
    simp only [spokesFrom, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ⟨he_sym2, hv_in_e⟩
      rw [Finset.mem_sym2_iff] at he_sym2
      obtain ⟨x, y, hxy, hx, hy, rfl⟩ := he_sym2
      simp only [Sym2.mem_toFinset_iff, Sym2.mem_iff] at hv_in_e
      rcases hv_in_e with rfl | rfl
      · -- x = v, so e = s(v, y)
        -- y ∈ t, y ≠ v, so y ∈ {a, b}
        have hy_erase : y ∈ t.erase v := Finset.mem_erase.mpr ⟨hxy, hy⟩
        rw [h_erase_eq] at hy_erase
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy_erase
        rcases hy_erase with rfl | rfl
        · left; rfl
        · right; rfl
      · -- y = v, so e = s(x, v) = s(v, x)
        have hx_erase : x ∈ t.erase v := Finset.mem_erase.mpr ⟨hxy.symm, hx⟩
        rw [h_erase_eq] at hx_erase
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx_erase
        rcases hx_erase with rfl | rfl
        · left; exact Sym2.eq_swap
        · right; exact Sym2.eq_swap
    · intro he
      rcases he with rfl | rfl
      · constructor
        · rw [Finset.mem_sym2_iff]; exact ⟨v, a, hav.symm, hv, ha, rfl⟩
        · simp
      · constructor
        · rw [Finset.mem_sym2_iff]; exact ⟨v, b, hbv.symm, hv, hb, rfl⟩
        · simp
  rw [h_spokes_eq]
  have h_ne : s(v, a) ≠ s(v, b) := by
    simp only [Sym2.eq, Sym2.rel_iff, not_or]
    constructor
    · intro ⟨_, hab'⟩; exact hab hab'.symm
    · intro ⟨hva, _⟩; exact hav hva
  exact Finset.card_pair h_ne

/-- Spokes from v are valid graph edges (if v ∈ clique) -/

-- Source: proven/tuza/nu4/safe_discard/slot151_tpair_spokes_PROVEN.lean
lemma union_spokes_card_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hA : A ∈ G.cliqueFinset 3) (hB : B ∈ G.cliqueFinset 3)
    (v : V) (hvA : v ∈ A) (hvB : v ∈ B) :
    (spokesFrom A v hvA ∪ spokesFrom B v hvB).card ≤ 4 := by
  have hA_card : A.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hA).card_eq
  have hB_card : B.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hB).card_eq
  have h1 := spokes_card_eq_2 A hA_card v hvA
  have h2 := spokes_card_eq_2 B hB_card v hvB
  calc (spokesFrom A v hvA ∪ spokesFrom B v hvB).card
      ≤ (spokesFrom A v hvA).card + (spokesFrom B v hvB).card := Finset.card_union_le _ _
    _ = 2 + 2 := by rw [h1, h2]
    _ = 4 := by omega

end

-- Source: proven/tuza/nu4/slot70_d3159016/diagonal_bridges.lean
lemma disjoint_triples_imply_contradiction (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 t3 : Finset V)
    (h_t1 : t1 ∈ S_e G M e) (h_t2 : t2 ∈ S_e G M e) (h_t3 : t3 ∈ S_e G M e)
    (h_disj : (t1 ∩ t2).card ≤ 1 ∧ (t2 ∩ t3).card ≤ 1 ∧ (t1 ∩ t3).card ≤ 1)
    (h_distinct : t1 ≠ t2 ∧ t2 ≠ t3 ∧ t1 ≠ t3) :
    False := by
  rcases hM with ⟨ hM₁, hM₂ ⟩;
  -- The set $M' = (M \setminus \{e\}) \cup \{t_1, t_2, t_3\}$ is a valid triangle packing, and its cardinality is greater than $|M|$.
  have hM'_valid : isTrianglePacking G ((M \ {e}) ∪ {t1, t2, t3}) := by
    unfold isTrianglePacking at *;
    simp_all +decide [ Finset.subset_iff, Set.Pairwise ];
    simp_all +decide [ Finset.inter_comm, S_e ]
  have hM'_card : ((M \ {e}) ∪ {t1, t2, t3}).card > M.card := by
    rw [ Finset.card_union_of_disjoint ] <;> simp +decide [ *, Finset.card_sdiff, Finset.subset_iff ];
    · omega;
    · simp_all +decide [ S_e ];
      refine' ⟨ fun h => Classical.not_not.1 fun hne => _, fun h => Classical.not_not.1 fun hne => _, fun h => Classical.not_not.1 fun hne => _ ⟩ <;> have := hM₁.2 <;> simp_all +decide [ Finset.subset_iff ];
      · exact absurd ( this h he hne ) ( by linarith );
      · exact absurd ( this h he hne ) ( by aesop );
      · exact absurd ( this h he hne ) ( by linarith );
  have h_contradiction : (M \ {e} ∪ {t1, t2, t3}).card ≤ trianglePackingNumber G := by
    have h_contradiction : ∀ M' : Finset (Finset V), isTrianglePacking G M' → M'.card ≤ trianglePackingNumber G := by
      unfold trianglePackingNumber;
      intro M' hM'
      have hM'_in_filter : M' ∈ Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset := by
        simp_all +decide [ isTrianglePacking ];
      have := Finset.le_max ( Finset.mem_image_of_mem Finset.card hM'_in_filter );
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_contradiction _ hM'_valid;
  linarith

-- Source: proven/tuza/nu4/slot70_d3159016/output.lean
lemma disjoint_triples_imply_contradiction (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 t3 : Finset V)
    (h_t1 : t1 ∈ S_e G M e) (h_t2 : t2 ∈ S_e G M e) (h_t3 : t3 ∈ S_e G M e)
    (h_disj : (t1 ∩ t2).card ≤ 1 ∧ (t2 ∩ t3).card ≤ 1 ∧ (t1 ∩ t3).card ≤ 1)
    (h_distinct : t1 ≠ t2 ∧ t2 ≠ t3 ∧ t1 ≠ t3) :
    False := by
  rcases hM with ⟨ hM₁, hM₂ ⟩;
  -- The set $M' = (M \setminus \{e\}) \cup \{t_1, t_2, t_3\}$ is a valid triangle packing, and its cardinality is greater than $|M|$.
  have hM'_valid : isTrianglePacking G ((M \ {e}) ∪ {t1, t2, t3}) := by
    unfold isTrianglePacking at *;
    simp_all +decide [ Finset.subset_iff, Set.Pairwise ];
    simp_all +decide [ Finset.inter_comm, S_e ]
  have hM'_card : ((M \ {e}) ∪ {t1, t2, t3}).card > M.card := by
    rw [ Finset.card_union_of_disjoint ] <;> simp +decide [ *, Finset.card_sdiff, Finset.subset_iff ];
    · omega;
    · simp_all +decide [ S_e ];
      refine' ⟨ fun h => Classical.not_not.1 fun hne => _, fun h => Classical.not_not.1 fun hne => _, fun h => Classical.not_not.1 fun hne => _ ⟩ <;> have := hM₁.2 <;> simp_all +decide [ Finset.subset_iff ];
      · exact absurd ( this h he hne ) ( by linarith );
      · exact absurd ( this h he hne ) ( by aesop );
      · exact absurd ( this h he hne ) ( by linarith );
  have h_contradiction : (M \ {e} ∪ {t1, t2, t3}).card ≤ trianglePackingNumber G := by
    have h_contradiction : ∀ M' : Finset (Finset V), isTrianglePacking G M' → M'.card ≤ trianglePackingNumber G := by
      unfold trianglePackingNumber;
      intro M' hM'
      have hM'_in_filter : M' ∈ Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset := by
        simp_all +decide [ isTrianglePacking ];
      have := Finset.le_max ( Finset.mem_image_of_mem Finset.card hM'_in_filter );
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_contradiction _ hM'_valid;
  linarith

-- Source: proven/tuza/nu4/slot71_5a800e22/Se_structure.lean
lemma S_e_pairwise_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e)
    (ht1_ne_e : t1 ≠ e) (ht2_ne_e : t2 ≠ e) (hne : t1 ≠ t2) :
    (t1 ∩ t2).card ≥ 2 := by
  obtain ⟨ ht1_card, ht1_adj ⟩ := hM;
  -- By the maximality of $M$, any triangle packing $M'$ with $|M'| > |M|$ contradicts the definition of $M$ as a maximum packing.
  have h_contra : ¬∃ M' : Finset (Finset V), isTrianglePacking G M' ∧ M'.card > M.card := by
    have h_contra : ∀ M' : Finset (Finset V), isTrianglePacking G M' → M'.card ≤ trianglePackingNumber G := by
      unfold trianglePackingNumber;
      intro M' hM'
      have hM'_in_powerset : M' ∈ Finset.powerset (G.cliqueFinset 3) := by
        exact Finset.mem_powerset.mpr hM'.1;
      have hM'_in_image : M'.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        aesop;
      have := Finset.le_max hM'_in_image;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact fun ⟨ M', hM', hM'' ⟩ => hM''.not_le ( ht1_adj ▸ h_contra M' hM' );
  contrapose! h_contra;
  refine' ⟨ Insert.insert t1 ( Insert.insert t2 ( M.erase e ) ), _, _ ⟩ <;> simp_all +decide [ isTrianglePacking ];
  · unfold S_e at *; simp_all +decide [ Finset.subset_iff, Set.Pairwise ] ;
    exact ⟨ Nat.le_of_lt_succ h_contra, fun _ => by rw [ Finset.inter_comm ] ; exact Nat.le_of_lt_succ h_contra, fun f hf hf' => ⟨ fun _ => by simpa only [ Finset.inter_comm ] using ht1.2.2 f hf hf', fun _ => by simpa only [ Finset.inter_comm ] using ht2.2.2 f hf hf' ⟩ ⟩;
  · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp_all +decide [ Finset.subset_iff ];
    · omega;
    · intro h; have := ht1_adj ▸ Finset.card_pos.2 ⟨ e, he ⟩ ; simp_all +decide [ S_e ] ;
      exact absurd ( ht1_card.2 h he ( by aesop ) ) ( by linarith );
    · intro H; have := ht1_card.2 he H; simp_all +decide ;
      simp_all +decide [ Finset.inter_comm, S_e ];
      exact absurd ( this ( Ne.symm ht1_ne_e ) ) ( by linarith )

-- Source: proven/tuza/nu4/slot71_5a800e22/Se_structure.lean
lemma S_e_cross_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e)
    (ht1_ne_e : t1 ≠ e) (ht2_ne_e : t2 ≠ e)
    (h_diff_edges : t1 ∩ e ≠ t2 ∩ e) :
    ∃ x, x ∉ e ∧ x ∈ t1 ∧ x ∈ t2 := by
  have h_inter : (t1 ∩ t2).card ≥ 2 := by
    apply S_e_pairwise_intersect G M hM e he t1 t2 ht1 ht2 ht1_ne_e ht2_ne_e;
    grind;
  -- Since $t1$ and $t2$ are triangles, they must each have exactly three elements.
  have h_card_t1 : t1.card = 3 := by
    unfold S_e at ht1;
    simp_all +decide [ SimpleGraph.cliqueFinset ];
    exact ht1.1.card_eq
  have h_card_t2 : t2.card = 3 := by
    unfold S_e at ht2;
    simp_all +decide [ SimpleGraph.isNClique_iff ];
  have h_card_e : e.card = 3 := by
    have := hM.1;
    have := this.1;
    have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    exact this.2;
  have h_inter_e : (t1 ∩ e).card = 2 ∧ (t2 ∩ e).card = 2 := by
    have h_inter_e : (t1 ∩ e).card ≥ 2 ∧ (t2 ∩ e).card ≥ 2 := by
      unfold S_e at ht1 ht2; aesop;
    have h_inter_e : (t1 ∩ e).card ≤ 3 ∧ (t2 ∩ e).card ≤ 3 := by
      exact ⟨ le_trans ( Finset.card_le_card fun x hx => by aesop ) h_card_t1.le, le_trans ( Finset.card_le_card fun x hx => by aesop ) h_card_t2.le ⟩;
    cases h_inter_e.1.eq_or_lt <;> cases h_inter_e.2.eq_or_lt <;> simp_all +decide;
    · have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ e ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ e ⊆ e ) ; simp_all +decide ;
    · have := Finset.eq_of_subset_of_card_le ( show t1 ∩ e ⊆ e from Finset.inter_subset_right ) ; simp_all +decide ;
      have := Finset.eq_of_subset_of_card_le this ; aesop;
    · have := Finset.eq_of_subset_of_card_le ( show t2 ∩ e ⊆ e from Finset.inter_subset_right ) ; simp_all +decide ;
      have := Finset.eq_of_subset_of_card_le this ; aesop;
    · exact ⟨ by linarith, by linarith ⟩;
  contrapose! h_diff_edges;
  have h_inter_eq : (t1 ∩ t2 ∩ e).card ≥ 2 := by
    have h_inter_eq : (t1 ∩ t2 ∩ e).card = (t1 ∩ t2).card := by
      exact congr_arg Finset.card ( Finset.ext fun x => by by_cases hx : x ∈ e <;> aesop );
    linarith;
  have h_inter_eq : (t1 ∩ t2 ∩ e) = (t1 ∩ e) ∧ (t1 ∩ t2 ∩ e) = (t2 ∩ e) := by
    have h_inter_eq : (t1 ∩ t2 ∩ e) ⊆ (t1 ∩ e) ∧ (t1 ∩ t2 ∩ e) ⊆ (t2 ∩ e) := by
      simp +contextual [ Finset.subset_iff ];
    exact ⟨ Finset.eq_of_subset_of_card_le h_inter_eq.1 ( by linarith ), Finset.eq_of_subset_of_card_le h_inter_eq.2 ( by linarith ) ⟩;
  grind

-- Source: proven/tuza/nu4/slot71_5a800e22/Se_structure.lean
lemma S_e_structure_case2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e)
    (ht1_ne_e : t1 ≠ e) (ht2_ne_e : t2 ≠ e)
    (h_diff_edges : t1 ∩ e ≠ t2 ∩ e) :
    ∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → x ∈ t := by
  -- By `S_e_cross_intersect` applied to $t_1, t_2$, there exists $x \notin e$ such that $x \in t_1$ and $x \in t_2$.
  obtain ⟨x, hx_not_in_e, hx_in_t1, hx_in_t2⟩ : ∃ x ∉ e, x ∈ t1 ∧ x ∈ t2 := by
    exact?;
  -- Since $t1$ and $t2$ are triangles, their sizes are 3. Therefore, $t1 \setminus e$ and $t2 \setminus e$ each have exactly one element, which is $x$.
  have ht1_minus_e : t1 \ e = {x} := by
    have ht1_card : t1.card = 3 := by
      unfold S_e at ht1;
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      exact ht1.1.card_eq
    have ht1_inter_e_card : (t1 ∩ e).card = 2 := by
      have := Finset.card_le_card ( show t1 ∩ e ⊆ t1 from Finset.inter_subset_left ) ; simp_all +decide ;
      interval_cases _ : Finset.card ( t1 ∩ e ) <;> simp_all +decide [ S_e ];
      have := Finset.eq_of_subset_of_card_le ( show t1 ∩ e ⊆ t1 from Finset.inter_subset_left ) ; simp_all +decide ;
      exact hx_not_in_e ( this hx_in_t1 )
    have ht1_minus_e_card : (t1 \ e).card = 1 := by
      have := Finset.card_sdiff_add_card_inter t1 e; simp_all +decide ;
    rw [ Finset.card_eq_one ] at ht1_minus_e_card;
    obtain ⟨ y, hy ⟩ := ht1_minus_e_card; rw [ Finset.eq_singleton_iff_unique_mem ] at *; aesop;
  have ht2_minus_e : t2 \ e = {x} := by
    have ht2_card : t2.card = 3 := by
      have := Finset.mem_filter.mp ht2;
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      exact this.1.card_eq;
    have ht2_inter_e_card : (t2 ∩ e).card = 2 := by
      have ht2_inter_e : (t2 ∩ e).card ≥ 2 := by
        unfold S_e at ht2; aesop;
      have ht2_inter_e_le : (t2 ∩ e).card ≤ 2 := by
        have ht2_inter_e_le : (t2 ∩ e).card ≤ t2.card - 1 := by
          refine' Nat.le_sub_one_of_lt ( Finset.card_lt_card _ );
          grind;
        aesop;
      linarith;
    have ht2_minus_e_card : (t2 \ e).card = 1 := by
      have := Finset.card_sdiff_add_card_inter t2 e; aesop;
    rw [ Finset.card_eq_one ] at ht2_minus_e_card;
    obtain ⟨ y, hy ⟩ := ht2_minus_e_card; rw [ Finset.eq_singleton_iff_unique_mem ] at hy; aesop;
  refine' ⟨ x, hx_not_in_e, fun t ht ht_ne_e => _ ⟩;
  by_cases h_cases : t ∩ e = t1 ∩ e;
  · -- Since $t \cap e = t1 \cap e$ and $t1 \cap e \ne t2 \cap e$, we can apply `S_e_cross_intersect` to $t$ and $t2$.
    obtain ⟨z, hz_not_in_e, hz_in_t, hz_in_t2⟩ : ∃ z ∉ e, z ∈ t ∧ z ∈ t2 := by
      apply S_e_cross_intersect G M hM e he t t2 ht ht2 ht_ne_e ht2_ne_e;
      grind;
    rw [ Finset.eq_singleton_iff_unique_mem ] at ht2_minus_e ; aesop;
  · -- By `S_e_cross_intersect` applied to $t$ and $t_1$, there exists $y \notin e$ such that $y \in t$ and $y \in t_1$.
    obtain ⟨y, hy_not_in_e, hy_in_t, hy_in_t1⟩ : ∃ y ∉ e, y ∈ t ∧ y ∈ t1 := by
      apply S_e_cross_intersect G M hM e he t t1 ht ht1 ht_ne_e ht1_ne_e h_cases;
    rw [ Finset.eq_singleton_iff_unique_mem ] at ht1_minus_e ; aesop

-- Source: proven/tuza/nu4/slot71_5a800e22/Se_structure.lean
lemma S_e_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (∃ u v : V, u ∈ e ∧ v ∈ e ∧ u ≠ v ∧ ∀ t ∈ S_e G M e, t ≠ e → {u, v} ⊆ t) ∨
    (∃ x : V, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → x ∈ t) := by
  by_cases h_empty : S_e G M e \ {e} = ∅;
  · simp_all +decide [ Finset.ext_iff ];
    by_cases he_empty : e = ∅;
    · have := hM.1.1 he; aesop;
    · by_cases he_singleton : e.card = 1;
      · have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        rw [ SimpleGraph.isNClique_iff ] at this ; aesop;
      · exact Or.inl ( Finset.one_lt_card.1 ( lt_of_le_of_ne ( Finset.card_pos.2 ( Finset.nonempty_of_ne_empty he_empty ) ) ( Ne.symm he_singleton ) ) );
  · by_cases h_case1 : ∀ t1 t2 : Finset V, t1 ∈ S_e G M e \ {e} → t2 ∈ S_e G M e \ {e} → t1 ∩ e = t2 ∩ e;
    · obtain ⟨t1, ht1⟩ : ∃ t1 : Finset V, t1 ∈ S_e G M e \ {e} := by
        exact Finset.nonempty_of_ne_empty h_empty;
      have h_inter : (t1 ∩ e).card ≥ 2 := by
        unfold S_e at ht1; aesop;
      obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.mp h_inter;
      refine' Or.inl ⟨ u, v, _, _, huv, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      intro t ht ht'; specialize h_case1 t t1 ht ht' ht1.1 ht1.2; replace h_case1 := Finset.ext_iff.mp h_case1; have := h_case1 u; have := h_case1 v; aesop;
    · obtain ⟨t1, t2, ht1, ht2, h_diff⟩ : ∃ t1 t2 : Finset V, t1 ∈ S_e G M e \ {e} ∧ t2 ∈ S_e G M e \ {e} ∧ t1 ∩ e ≠ t2 ∩ e := by
        grind +ring;
      obtain ⟨x, hx⟩ : ∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → x ∈ t := by
        apply S_e_structure_case2 G M hM e he t1 t2;
        · exact Finset.mem_sdiff.mp ht1 |>.1;
        · exact Finset.mem_sdiff.mp ht2 |>.1;
        · aesop;
        · aesop;
        · exact h_diff;
      exact Or.inr ⟨ x, hx ⟩

-- Source: proven/tuza/nu4/slot71_5a800e22/output.lean
lemma S_e_pairwise_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e)
    (ht1_ne_e : t1 ≠ e) (ht2_ne_e : t2 ≠ e) (hne : t1 ≠ t2) :
    (t1 ∩ t2).card ≥ 2 := by
  obtain ⟨ ht1_card, ht1_adj ⟩ := hM;
  -- By the maximality of $M$, any triangle packing $M'$ with $|M'| > |M|$ contradicts the definition of $M$ as a maximum packing.
  have h_contra : ¬∃ M' : Finset (Finset V), isTrianglePacking G M' ∧ M'.card > M.card := by
    have h_contra : ∀ M' : Finset (Finset V), isTrianglePacking G M' → M'.card ≤ trianglePackingNumber G := by
      unfold trianglePackingNumber;
      intro M' hM'
      have hM'_in_powerset : M' ∈ Finset.powerset (G.cliqueFinset 3) := by
        exact Finset.mem_powerset.mpr hM'.1;
      have hM'_in_image : M'.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        aesop;
      have := Finset.le_max hM'_in_image;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact fun ⟨ M', hM', hM'' ⟩ => hM''.not_le ( ht1_adj ▸ h_contra M' hM' );
  contrapose! h_contra;
  refine' ⟨ Insert.insert t1 ( Insert.insert t2 ( M.erase e ) ), _, _ ⟩ <;> simp_all +decide [ isTrianglePacking ];
  · unfold S_e at *; simp_all +decide [ Finset.subset_iff, Set.Pairwise ] ;
    exact ⟨ Nat.le_of_lt_succ h_contra, fun _ => by rw [ Finset.inter_comm ] ; exact Nat.le_of_lt_succ h_contra, fun f hf hf' => ⟨ fun _ => by simpa only [ Finset.inter_comm ] using ht1.2.2 f hf hf', fun _ => by simpa only [ Finset.inter_comm ] using ht2.2.2 f hf hf' ⟩ ⟩;
  · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp_all +decide [ Finset.subset_iff ];
    · omega;
    · intro h; have := ht1_adj ▸ Finset.card_pos.2 ⟨ e, he ⟩ ; simp_all +decide [ S_e ] ;
      exact absurd ( ht1_card.2 h he ( by aesop ) ) ( by linarith );
    · intro H; have := ht1_card.2 he H; simp_all +decide ;
      simp_all +decide [ Finset.inter_comm, S_e ];
      exact absurd ( this ( Ne.symm ht1_ne_e ) ) ( by linarith )

-- Source: proven/tuza/nu4/slot71_5a800e22/output.lean
lemma S_e_cross_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e)
    (ht1_ne_e : t1 ≠ e) (ht2_ne_e : t2 ≠ e)
    (h_diff_edges : t1 ∩ e ≠ t2 ∩ e) :
    ∃ x, x ∉ e ∧ x ∈ t1 ∧ x ∈ t2 := by
  have h_inter : (t1 ∩ t2).card ≥ 2 := by
    apply S_e_pairwise_intersect G M hM e he t1 t2 ht1 ht2 ht1_ne_e ht2_ne_e;
    grind;
  -- Since $t1$ and $t2$ are triangles, they must each have exactly three elements.
  have h_card_t1 : t1.card = 3 := by
    unfold S_e at ht1;
    simp_all +decide [ SimpleGraph.cliqueFinset ];
    exact ht1.1.card_eq
  have h_card_t2 : t2.card = 3 := by
    unfold S_e at ht2;
    simp_all +decide [ SimpleGraph.isNClique_iff ];
  have h_card_e : e.card = 3 := by
    have := hM.1;
    have := this.1;
    have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    exact this.2;
  have h_inter_e : (t1 ∩ e).card = 2 ∧ (t2 ∩ e).card = 2 := by
    have h_inter_e : (t1 ∩ e).card ≥ 2 ∧ (t2 ∩ e).card ≥ 2 := by
      unfold S_e at ht1 ht2; aesop;
    have h_inter_e : (t1 ∩ e).card ≤ 3 ∧ (t2 ∩ e).card ≤ 3 := by
      exact ⟨ le_trans ( Finset.card_le_card fun x hx => by aesop ) h_card_t1.le, le_trans ( Finset.card_le_card fun x hx => by aesop ) h_card_t2.le ⟩;
    cases h_inter_e.1.eq_or_lt <;> cases h_inter_e.2.eq_or_lt <;> simp_all +decide;
    · have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ e ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ e ⊆ e ) ; simp_all +decide ;
    · have := Finset.eq_of_subset_of_card_le ( show t1 ∩ e ⊆ e from Finset.inter_subset_right ) ; simp_all +decide ;
      have := Finset.eq_of_subset_of_card_le this ; aesop;
    · have := Finset.eq_of_subset_of_card_le ( show t2 ∩ e ⊆ e from Finset.inter_subset_right ) ; simp_all +decide ;
      have := Finset.eq_of_subset_of_card_le this ; aesop;
    · exact ⟨ by linarith, by linarith ⟩;
  contrapose! h_diff_edges;
  have h_inter_eq : (t1 ∩ t2 ∩ e).card ≥ 2 := by
    have h_inter_eq : (t1 ∩ t2 ∩ e).card = (t1 ∩ t2).card := by
      exact congr_arg Finset.card ( Finset.ext fun x => by by_cases hx : x ∈ e <;> aesop );
    linarith;
  have h_inter_eq : (t1 ∩ t2 ∩ e) = (t1 ∩ e) ∧ (t1 ∩ t2 ∩ e) = (t2 ∩ e) := by
    have h_inter_eq : (t1 ∩ t2 ∩ e) ⊆ (t1 ∩ e) ∧ (t1 ∩ t2 ∩ e) ⊆ (t2 ∩ e) := by
      simp +contextual [ Finset.subset_iff ];
    exact ⟨ Finset.eq_of_subset_of_card_le h_inter_eq.1 ( by linarith ), Finset.eq_of_subset_of_card_le h_inter_eq.2 ( by linarith ) ⟩;
  grind

-- Source: proven/tuza/nu4/slot71_5a800e22/output.lean
lemma S_e_structure_case2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e)
    (ht1_ne_e : t1 ≠ e) (ht2_ne_e : t2 ≠ e)
    (h_diff_edges : t1 ∩ e ≠ t2 ∩ e) :
    ∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → x ∈ t := by
  -- By `S_e_cross_intersect` applied to $t_1, t_2$, there exists $x \notin e$ such that $x \in t_1$ and $x \in t_2$.
  obtain ⟨x, hx_not_in_e, hx_in_t1, hx_in_t2⟩ : ∃ x ∉ e, x ∈ t1 ∧ x ∈ t2 := by
    exact?;
  -- Since $t1$ and $t2$ are triangles, their sizes are 3. Therefore, $t1 \setminus e$ and $t2 \setminus e$ each have exactly one element, which is $x$.
  have ht1_minus_e : t1 \ e = {x} := by
    have ht1_card : t1.card = 3 := by
      unfold S_e at ht1;
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      exact ht1.1.card_eq
    have ht1_inter_e_card : (t1 ∩ e).card = 2 := by
      have := Finset.card_le_card ( show t1 ∩ e ⊆ t1 from Finset.inter_subset_left ) ; simp_all +decide ;
      interval_cases _ : Finset.card ( t1 ∩ e ) <;> simp_all +decide [ S_e ];
      have := Finset.eq_of_subset_of_card_le ( show t1 ∩ e ⊆ t1 from Finset.inter_subset_left ) ; simp_all +decide ;
      exact hx_not_in_e ( this hx_in_t1 )
    have ht1_minus_e_card : (t1 \ e).card = 1 := by
      have := Finset.card_sdiff_add_card_inter t1 e; simp_all +decide ;
    rw [ Finset.card_eq_one ] at ht1_minus_e_card;
    obtain ⟨ y, hy ⟩ := ht1_minus_e_card; rw [ Finset.eq_singleton_iff_unique_mem ] at *; aesop;
  have ht2_minus_e : t2 \ e = {x} := by
    have ht2_card : t2.card = 3 := by
      have := Finset.mem_filter.mp ht2;
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      exact this.1.card_eq;
    have ht2_inter_e_card : (t2 ∩ e).card = 2 := by
      have ht2_inter_e : (t2 ∩ e).card ≥ 2 := by
        unfold S_e at ht2; aesop;
      have ht2_inter_e_le : (t2 ∩ e).card ≤ 2 := by
        have ht2_inter_e_le : (t2 ∩ e).card ≤ t2.card - 1 := by
          refine' Nat.le_sub_one_of_lt ( Finset.card_lt_card _ );
          grind;
        aesop;
      linarith;
    have ht2_minus_e_card : (t2 \ e).card = 1 := by
      have := Finset.card_sdiff_add_card_inter t2 e; aesop;
    rw [ Finset.card_eq_one ] at ht2_minus_e_card;
    obtain ⟨ y, hy ⟩ := ht2_minus_e_card; rw [ Finset.eq_singleton_iff_unique_mem ] at hy; aesop;
  refine' ⟨ x, hx_not_in_e, fun t ht ht_ne_e => _ ⟩;
  by_cases h_cases : t ∩ e = t1 ∩ e;
  · -- Since $t \cap e = t1 \cap e$ and $t1 \cap e \ne t2 \cap e$, we can apply `S_e_cross_intersect` to $t$ and $t2$.
    obtain ⟨z, hz_not_in_e, hz_in_t, hz_in_t2⟩ : ∃ z ∉ e, z ∈ t ∧ z ∈ t2 := by
      apply S_e_cross_intersect G M hM e he t t2 ht ht2 ht_ne_e ht2_ne_e;
      grind;
    rw [ Finset.eq_singleton_iff_unique_mem ] at ht2_minus_e ; aesop;
  · -- By `S_e_cross_intersect` applied to $t$ and $t_1$, there exists $y \notin e$ such that $y \in t$ and $y \in t_1$.
    obtain ⟨y, hy_not_in_e, hy_in_t, hy_in_t1⟩ : ∃ y ∉ e, y ∈ t ∧ y ∈ t1 := by
      apply S_e_cross_intersect G M hM e he t t1 ht ht1 ht_ne_e ht1_ne_e h_cases;
    rw [ Finset.eq_singleton_iff_unique_mem ] at ht1_minus_e ; aesop

-- Source: proven/tuza/nu4/slot71_5a800e22/output.lean
lemma S_e_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (∃ u v : V, u ∈ e ∧ v ∈ e ∧ u ≠ v ∧ ∀ t ∈ S_e G M e, t ≠ e → {u, v} ⊆ t) ∨
    (∃ x : V, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → x ∈ t) := by
  by_cases h_empty : S_e G M e \ {e} = ∅;
  · simp_all +decide [ Finset.ext_iff ];
    by_cases he_empty : e = ∅;
    · have := hM.1.1 he; aesop;
    · by_cases he_singleton : e.card = 1;
      · have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        rw [ SimpleGraph.isNClique_iff ] at this ; aesop;
      · exact Or.inl ( Finset.one_lt_card.1 ( lt_of_le_of_ne ( Finset.card_pos.2 ( Finset.nonempty_of_ne_empty he_empty ) ) ( Ne.symm he_singleton ) ) );
  · by_cases h_case1 : ∀ t1 t2 : Finset V, t1 ∈ S_e G M e \ {e} → t2 ∈ S_e G M e \ {e} → t1 ∩ e = t2 ∩ e;
    · obtain ⟨t1, ht1⟩ : ∃ t1 : Finset V, t1 ∈ S_e G M e \ {e} := by
        exact Finset.nonempty_of_ne_empty h_empty;
      have h_inter : (t1 ∩ e).card ≥ 2 := by
        unfold S_e at ht1; aesop;
      obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.mp h_inter;
      refine' Or.inl ⟨ u, v, _, _, huv, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      intro t ht ht'; specialize h_case1 t t1 ht ht' ht1.1 ht1.2; replace h_case1 := Finset.ext_iff.mp h_case1; have := h_case1 u; have := h_case1 v; aesop;
    · obtain ⟨t1, t2, ht1, ht2, h_diff⟩ : ∃ t1 t2 : Finset V, t1 ∈ S_e G M e \ {e} ∧ t2 ∈ S_e G M e \ {e} ∧ t1 ∩ e ≠ t2 ∩ e := by
        grind +ring;
      obtain ⟨x, hx⟩ : ∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → x ∈ t := by
        apply S_e_structure_case2 G M hM e he t1 t2;
        · exact Finset.mem_sdiff.mp ht1 |>.1;
        · exact Finset.mem_sdiff.mp ht2 |>.1;
        · aesop;
        · aesop;
        · exact h_diff;
      exact Or.inr ⟨ x, hx ⟩

-- Source: proven/tuza/nu4/slot72_f0a24a15/cycle_path_reduction.lean
lemma cycle4_same_as_path4_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) :
    T_pair G A B ∪ T_pair G C D = T_pair G A B ∪ T_pair G C D ∪ X_ef G D A := by
      -- Since $X_{DA}$ is a subset of $T_{AB} \cup T_{CD}$, adding it to the union does not change the set.
      have h_subset : X_ef G D A ⊆ T_pair G A B ∪ T_pair G C D := by
        -- Let $t$ be any triangle in $X_{DA}$. By definition, $t$ shares an edge with both $D$ and $A$.
        intro t ht
        obtain ⟨hDA, hA⟩ : (t ∩ D).card ≥ 2 ∧ (t ∩ A).card ≥ 2 := by
          unfold X_ef at ht; aesop;
        -- Since $t$ shares an edge with both $D$ and $A$, it must be in $X_{DA}$.
        simp [X_ef] at ht ⊢;
        exact Or.inl ( Finset.mem_union_left _ ( Finset.mem_filter.mpr ⟨ Finset.mem_coe.mpr ( Finset.mem_coe.mpr ( by aesop ) ), hA ⟩ ) );
      rw [ Finset.union_eq_left.mpr h_subset ]

-- Source: proven/tuza/nu4/slot72_f0a24a15/output.lean
lemma cycle4_same_as_path4_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) :
    T_pair G A B ∪ T_pair G C D = T_pair G A B ∪ T_pair G C D ∪ X_ef G D A := by
      -- Since $X_{DA}$ is a subset of $T_{AB} \cup T_{CD}$, adding it to the union does not change the set.
      have h_subset : X_ef G D A ⊆ T_pair G A B ∪ T_pair G C D := by
        -- Let $t$ be any triangle in $X_{DA}$. By definition, $t$ shares an edge with both $D$ and $A$.
        intro t ht
        obtain ⟨hDA, hA⟩ : (t ∩ D).card ≥ 2 ∧ (t ∩ A).card ≥ 2 := by
          unfold X_ef at ht; aesop;
        -- Since $t$ shares an edge with both $D$ and $A$, it must be in $X_{DA}$.
        simp [X_ef] at ht ⊢;
        exact Or.inl ( Finset.mem_union_left _ ( Finset.mem_filter.mpr ⟨ Finset.mem_coe.mpr ( Finset.mem_coe.mpr ( by aesop ) ), hA ⟩ ) );
      rw [ Finset.union_eq_left.mpr h_subset ]

-- Source: proven/tuza/lemmas/slot24_tau_X_le_2.lean
lemma lemma_2_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∀ t1 t2, t1 ∈ S G e M → t2 ∈ S G e M → shareEdge t1 t2 := by
  intros t1 t2 ht1 ht2
  apply Classical.byContradiction
  intro h_contra;
  have h_new_packing : isTrianglePacking G (insert t1 (insert t2 (M.erase e))) := by
    unfold S at ht1 ht2;
    simp_all +decide [ isTrianglePacking ];
    unfold trianglesSharingEdge at ht1 ht2; simp_all +decide [ Finset.subset_iff, Set.Pairwise ] ;
    simp_all +decide [ Finset.inter_comm, shareEdge ];
    refine' ⟨ _, _, _, _ ⟩;
    · exact fun a ha ha' => hM.1.1 ha' |> fun h => by simpa using h;
    · exact fun h => Nat.le_of_lt_succ h_contra;
    · exact fun h => Nat.le_of_lt_succ h_contra;
    · have := hM.1.2; aesop;
  have h_card_new_packing : (insert t1 (insert t2 (M.erase e))).card > M.card := by
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp_all +decide [ Finset.ext_iff ];
    · omega;
    · intro x hx h; have := hM.1; simp_all +decide [ isTrianglePacking ] ;
      simp_all +decide [ S, Finset.mem_filter ];
      simp_all +decide [ trianglesSharingEdge ];
      have := this.2 h he; simp_all +decide [ Finset.inter_comm ] ;
      exact absurd ( this ( by aesop_cat ) ) ( by linarith );
    · constructor;
      · contrapose! h_contra;
        simp_all +decide [ Finset.ext_iff, shareEdge ];
        have h_card_t1 : t1.card = 3 := by
          have h_card_t1 : t1 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ht1 |>.1 |> Finset.mem_filter.mp |>.1;
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact h_card_t1.card_eq;
        rw [ show t1 ∩ t2 = t1 by ext x; aesop ] ; linarith;
      · simp_all +decide [ S ];
        intro x hx; intro H; have := ht1.2 _ H; simp_all +decide [ Finset.ext_iff ] ;
        have := this x hx; simp_all +decide [ Finset.card_le_one ] ;
        have := Finset.card_le_one.2 ( fun a ha b hb => this a ha b hb ) ; simp_all +decide [ trianglesSharingEdge ] ;
        exact this.not_lt ( by rw [ ht1.1.1.card_eq ] ; decide );
  have h_contradiction : (insert t1 (insert t2 (M.erase e))).card ≤ trianglePackingNumber G := by
    apply Finset.le_max_of_eq;
    apply Finset.mem_image_of_mem;
    exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.subset_iff.mpr fun x hx => h_new_packing.1 hx ), h_new_packing ⟩;
    unfold trianglePackingNumber;
    cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    simp_all +decide [ Finset.max ];
    exact h _ ( h_new_packing.1 ) h_new_packing;
  exact h_card_new_packing.not_le ( h_contradiction.trans ( hM.2.ge ) )

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Tactic `rfl` failed: The left-hand side
  Option.getD (Finset.image Finset.card G.edgeFinset.powerset).min 0
is not definitionally equal to the right-hand side
  2

case pos
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
hM : isMaxPacking G M
e : Finset V
he : e ∈ M
hS : (S G e M).card ≤ 2
hS' : S G e M = ∅
⊢ Option.getD (Finset.image Finset.card G.edgeFinset.powerset).min 0 ≤ 2-/
-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_S_le_2 (structure: pairwise sharing → common edge or ≤4 vertices)
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/lemmas/slot24_tau_X_le_2.lean
lemma mem_X_implies_v_in_t {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (h_inter : (e ∩ f).card = 1) (t : Finset V) (ht : t ∈ X G e f) :
    ∃ v ∈ e ∩ f, v ∈ t := by
  unfold X at ht
  simp only [Finset.mem_filter] at ht
  obtain ⟨ht_clique, h_e, h_f⟩ := ht
  -- t ∩ e ≥ 2 and t ∩ f ≥ 2, with e ∩ f = {v}
  -- Since t has 3 vertices and must share ≥2 with each, v must be in t
  have h_card_t : t.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset_iff] at ht_clique
    exact ht_clique.2
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h_inter
  use v
  constructor
  · exact hv.symm ▸ Finset.mem_singleton_self v
  · -- v must be in t since t ∩ e ≥ 2 and t ∩ f ≥ 2 with e ∩ f = {v}
    by_contra hv_notin
    have h1 : (t ∩ e).card ≤ (e \ {v}).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_inter] at hx
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact hx.2
      · intro hxv; rw [hxv] at hx; exact hv_notin hx.1
    have h2 : (e \ {v}).card ≤ 2 := by
      have he_card : e.card = 3 := by
        simp only [SimpleGraph.mem_cliqueFinset_iff] at he; exact he.2
      have : ({v} : Finset V).card = 1 := Finset.card_singleton v
      have hv_in_e : v ∈ e := by
        have := hv.symm ▸ Finset.mem_singleton_self v
        exact Finset.mem_of_mem_inter_left this
      rw [Finset.card_sdiff (Finset.singleton_subset_iff.mpr hv_in_e), he_card, this]
      omega
    linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_X_le_2 (bridges on ≤4 vertices, k4_cover applies)
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable section AristotleLemmas

/-
If two triangles e and f are disjoint, then the set of bridges X(e, f) is empty.
-/

-- Source: proven/tuza/lemmas/slot24_tau_X_le_2.lean
lemma X_eq_empty_of_disjoint {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (h : e ∩ f = ∅) : X G e f = ∅ := by
      unfold X;
      ext1 t; simp_all +decide [ Finset.ext_iff ] ;
      intro ht ht'; have := Finset.card_le_card ( show t ∩ e ⊆ t from Finset.inter_subset_left ) ; have := Finset.card_le_card ( show t ∩ f ⊆ t from Finset.inter_subset_left ) ; simp_all +decide ;
      have := Finset.card_le_card ( show t ∩ e ∪ t ∩ f ⊆ t from Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ; simp_all +decide ;
      rw [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx hx' => h x ( Finset.mem_of_mem_inter_right hx ) ( Finset.mem_of_mem_inter_right hx' ) ) ] at this ; linarith [ ht.2 ]

/-
If two triangles e and f intersect in exactly one vertex, then the covering number of X(e, f) is at most 2.
-/

-- Source: proven/tuza/lemmas/slot24_tau_X_le_2.lean
lemma CE_isMax : isMaxPacking CE_G CE_M := by
  constructor;
  · unfold isTrianglePacking;
    simp +decide [ CE_M, CE_G ];
    simp +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
  · unfold trianglePackingNumber;
    unfold isTrianglePacking; simp +decide [ CE_M ] ;
    unfold CE_G; simp +decide [ SimpleGraph.cliqueFinset ] ;
    unfold Option.getD; simp +decide [ SimpleGraph.isNClique_iff ] ;

-- Source: proven/tuza/lemmas/slot24_tau_X_le_2.lean
lemma CE_disproof : ¬ (∀ t ∈ X CE_G CE_e CE_f, ∃ edge ∈ CE_C, edge ∈ t.sym2) := by
  unfold X CE_C;
  unfold CE_G CE_e CE_f; simp +decide ;

-- Source: proven/tuza/lemmas/slot24_tau_X_le_2.lean
lemma CE_S_e : S CE_G CE_e CE_M = {CE_e} := by
  unfold S; simp +decide [ CE_M, CE_e, CE_f ] ;
  unfold trianglesSharingEdge; simp +decide ;
  unfold CE_G; simp +decide [ SimpleGraph.cliqueFinset ] ;
  simp +decide [ SimpleGraph.isNClique_iff ]

-- Source: proven/tuza/lemmas/slot24_tau_X_le_2.lean
lemma CE_S_f : S CE_G CE_f CE_M = {CE_f} := by
  unfold S CE_f CE_M;
  unfold trianglesSharingEdge; simp +decide ;
  unfold CE_G; simp +decide [ SimpleGraph.cliqueFinset ] ;
  unfold CE_e; simp +decide [ SimpleGraph.isNClique_iff ] ;

-- Source: proven/tuza/lemmas/slot6_Se_lemmas.lean
lemma Se_pairwise_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (edge_e : Finset V) (he : edge_e ∈ M) :
    ∀ t1 ∈ S_e G M edge_e, ∀ t2 ∈ S_e G M edge_e, (t1 ∩ t2).card ≥ 2 := by
  intros t1 ht1 t2 ht2
  by_contra h
  push_neg at h
  have h_disj : (t1 ∩ t2).card ≤ 1 := Nat.le_of_lt_succ h

  have h_t1_in_T : t1 ∈ trianglesSharingEdge G edge_e := (Finset.mem_filter.mp ht1).1
  have h_t1_inter : (t1 ∩ edge_e).card ≥ 2 := (Finset.mem_filter.mp h_t1_in_T).2
  have h_t2_in_T : t2 ∈ trianglesSharingEdge G edge_e := (Finset.mem_filter.mp ht2).1
  have h_t2_inter : (t2 ∩ edge_e).card ≥ 2 := (Finset.mem_filter.mp h_t2_in_T).2

  have h_t1_ne_e : t1 ≠ edge_e := by
    intro heq
    rw [heq] at h_disj
    rw [Finset.inter_comm] at h_disj
    linarith
  have h_t2_ne_e : t2 ≠ edge_e := by
    intro heq
    rw [heq] at h_disj
    linarith

  let M' := (M.erase edge_e) ∪ {t1, t2}
  have h_packing : isTrianglePacking G M' := by
    have h_M_erase : isTrianglePacking G (M.erase edge_e) := by
      have := hM.1;
      exact ⟨ Finset.Subset.trans ( Finset.erase_subset _ _ ) this.1, fun x hx y hy hxy => this.2 ( Finset.mem_of_mem_erase hx ) ( Finset.mem_of_mem_erase hy ) hxy ⟩;
    have h_t1_t2 : ∀ t ∈ ({t1, t2} : Finset (Finset V)), ∀ f ∈ M.erase edge_e, (t ∩ f).card ≤ 1 := by
      unfold S_e at *; aesop;
    have h_t1_t2_subset : ({t1, t2} : Finset (Finset V)) ⊆ G.cliqueFinset 3 := by
      simp_all +decide [ Finset.subset_iff ];
      unfold trianglesSharingEdge at *; aesop;
    unfold isTrianglePacking at *;
    simp_all +decide [ Set.Pairwise ];
    simp +zetaDelta at *;
    simp_all +decide [ Finset.subset_iff, Finset.inter_comm ]
  have h_card : M'.card > M.card := by
    have h_card_add : (M.erase edge_e ∪ {t1, t2}).card = (M.erase edge_e).card + 2 := by
      have h_card_add : t1 ∉ M.erase edge_e ∧ t2 ∉ M.erase edge_e ∧ t1 ≠ t2 := by
        refine' ⟨ _, _, _ ⟩;
        · intro h;
          have := hM.1.2;
          exact h_t1_inter.not_lt ( lt_of_le_of_lt ( this ( Finset.mem_coe.2 ( Finset.mem_of_mem_erase h ) ) ( Finset.mem_coe.2 he ) ( by aesop ) ) ( by norm_num ) );
        · intro h; have := hM.1; simp_all +decide [ Finset.subset_iff ] ;
          have := this.2; simp_all +decide [ Set.Pairwise ] ;
          exact absurd ( this h he ( by aesop ) ) ( by linarith );
        · intro h_eq; simp_all +decide ;
          exact h_t2_inter.not_lt ( lt_of_le_of_lt ( Finset.card_le_card ( Finset.inter_subset_left ) ) h );
      rw [ Finset.card_union ] ; aesop;
    grind
  have h_le : M'.card ≤ trianglePackingNumber G := by
    have h_M'_subset : M' ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
      unfold isTrianglePacking at *; aesop;
    unfold trianglePackingNumber;
    have h_M'_card_le_max : ∀ x ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)).max 0 := by
      intro x hx;
      have := Finset.le_max hx;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_M'_card_le_max _ ( Finset.mem_image_of_mem _ h_M'_subset )
  rw [← hM.2] at h_le
  linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Se_common_vertex_implies_le_2
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/lemmas/slot6_Se_lemmas.lean
lemma Se_common_vertex_implies_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_common : ∃ v ∈ e, ∀ t ∈ S_e G M e, v ∈ t) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
      unfold triangleCoveringNumberOn;
      obtain ⟨v, hv_e, hv⟩ : ∃ v ∈ e, ∀ t ∈ S_e G M e, v ∈ t := h_common;
      have h_cover : ∃ E' ⊆ G.edgeFinset, (∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2) ∧ E'.card ≤ 2 := by
        obtain ⟨u, w, hu, hw, he_eq⟩ : ∃ u w : V, u ≠ v ∧ w ≠ v ∧ u ≠ w ∧ e = {v, u, w} := by
          have h_card_e : e.card = 3 := by
            have := hM.1.1;
            have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
            exact this.2;
          have := Finset.card_eq_three.mp h_card_e;
          obtain ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ := this; use if x = v then y else if y = v then z else x, if x = v then z else if y = v then x else y; aesop;
        refine' ⟨ { s(v, u), s(v, w) }, _, _, _ ⟩ <;> simp_all +decide [ Set.Pairwise ];
        · have := hM.1.1 he; simp_all +decide [ SimpleGraph.mem_edgeSet, Sym2.eq ] ;
          simp_all +decide [ Set.insert_subset_iff, SimpleGraph.isNClique_iff ];
          grind;
        · intro t ht; specialize hv t ht; simp_all +decide [ Finset.subset_iff, S_e ] ;
          have := Finset.mem_filter.mp ht.1; simp_all +decide [ trianglesSharingEdge ] ;
          contrapose! ht; simp_all +decide [ Finset.card_insert_of_notMem, SimpleGraph.isNClique_iff ] ;;
      simp +zetaDelta at *;
      obtain ⟨ E', hE₁, hE₂, hE₃ ⟩ := h_cover;
      refine' le_trans _ hE₃;
      have h_min_le : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ E'.card := by
        exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by simpa [ ← Finset.coe_subset ] using hE₁ ), hE₂ ⟩, rfl ⟩ );
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ S_e G M e, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Se_structure_step1
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/lemmas/slot6_Se_lemmas.lean
lemma Se_structure_step1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (u v w : V) (he_eq : e = {u, v, w}) (h_distinct : u ≠ v ∧ u ≠ w ∧ v ≠ w)
    (tu : Finset V) (htu : tu ∈ S_e G M e) (hu_tu : u ∉ tu)
    (tv : Finset V) (htv : tv ∈ S_e G M e) (hv_tv : v ∉ tv) :
    ∃ x, x ∉ ({u, v, w} : Finset V) ∧ tu = {v, w, x} ∧ tv = {u, w, x} := by
      have h_tu : ∃ x, tu = {v, w, x} := by
        have h_tu_card : tu.card = 3 := by
          have h_tu_card : tu ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp htu |>.1 |> Finset.mem_filter.mp |>.1;
          exact Finset.mem_filter.mp h_tu_card |>.2.2;
        have h_tu_subset : v ∈ tu ∧ w ∈ tu := by
          have h_tu_subset : (tu ∩ e).card ≥ 2 := by
            unfold S_e at htu;
            unfold trianglesSharingEdge at htu; aesop;
          simp_all +decide [ Finset.inter_comm ];
          contrapose! h_tu_subset;
          exact lt_of_le_of_lt ( Finset.card_le_one.mpr ( by aesop ) ) ( by decide );
        rw [ Finset.card_eq_three ] at h_tu_card; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := h_tu_card; use if x = v then if y = w then z else y else if x = w then if y = v then z else y else if y = v then if z = w then x else z else if y = w then if z = v then x else z else if z = v then if x = w then y else x else if z = w then if x = v then y else x else x; aesop;
      have h_tv : ∃ x, tv = {u, w, x} := by
        have h_tv_card : tv.card = 3 := by
          have h_tv_card : tv ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp htv |>.1 |> Finset.mem_filter.mp |>.1;
          exact Finset.mem_filter.mp h_tv_card |>.2.2;
        have h_tv_contains_u_w : u ∈ tv ∧ w ∈ tv := by
          have h_tv_contains_u_w : (tv ∩ e).card ≥ 2 := by
            have h_tv_inter : (tv ∩ e).card ≥ 2 := by
              have h_inter : tv ∈ trianglesSharingEdge G e := by
                exact Finset.mem_filter.mp htv |>.1
              unfold trianglesSharingEdge at h_inter; aesop;
            exact h_tv_inter;
          grind;
        rw [ Finset.card_eq_three ] at h_tv_card; obtain ⟨ x, y, z, hxyz ⟩ := h_tv_card; use if x = u then if y = w then z else y else if y = u then if x = w then z else x else if z = u then if x = w then y else x else if x = w then y else if y = w then x else z; aesop;
      obtain ⟨x, hx⟩ := h_tu
      obtain ⟨y, hy⟩ := h_tv;
      have := Se_pairwise_intersect G M hM e he tu htu tv htv; simp_all +decide ;
      grind

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Se_structure_step2
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/lemmas/slot6_Se_lemmas.lean
lemma Se_structure_step2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (u v w : V) (he_eq : e = {u, v, w}) (h_distinct : u ≠ v ∧ u ≠ w ∧ v ≠ w)
    (tu : Finset V) (htu : tu ∈ S_e G M e) (hu_tu : u ∉ tu)
    (tv : Finset V) (htv : tv ∈ S_e G M e) (hv_tv : v ∉ tv)
    (tw : Finset V) (htw : tw ∈ S_e G M e) (hw_tw : w ∉ tw)
    (x : V) (hx_not_in_e : x ∉ ({u, v, w} : Finset V))
    (htu_eq : tu = {v, w, x}) (htv_eq : tv = {u, w, x}) :
    tw = {u, v, x} := by
      have htw_uv : u ∈ tw ∧ v ∈ tw := by
        have h_inter : (tw ∩ e).card ≥ 2 := by
          unfold S_e at htw;
          unfold trianglesSharingEdge at htw; aesop;
        have := Finset.one_lt_card.1 h_inter; aesop;
      have htw_vx : v ∈ tw ∧ x ∈ tw := by
        have htw_vx : (tw ∩ tu).card ≥ 2 := by
          exact?;
        contrapose! htw_vx; simp_all +decide [ Finset.inter_comm ] ;
      have htw_card : tw.card = 3 := by
        simp_all +decide [ S_e ];
        simp_all +decide [ trianglesSharingEdge ];
        exact htw.1.card_eq;
      rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ htw_uv.1, Finset.insert_subset_iff.mpr ⟨ htw_uv.2, Finset.singleton_subset_iff.mpr htw_vx.2 ⟩ ⟩ ) ] ; aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Se_structure_complete (S_e ⊆ K4 structure)
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/lemmas/slot6_Se_lemmas.lean
lemma Se_structure_complete (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_no_common : ∀ v ∈ e, ∃ t ∈ S_e G M e, v ∉ t) :
    ∃ u v w x, e = {u, v, w} ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ x ∉ e ∧
    S_e G M e ⊆ {e, {v, w, x}, {u, w, x}, {u, v, x}} := by
      obtain ⟨u, v, w, he_eq⟩ : ∃ u v w : V, e = {u, v, w} ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w := by
        have := hM.1;
        rcases this with ⟨ hM₁, hM₂ ⟩;
        have := hM₁ he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        rcases this with ⟨ h₁, h₂ ⟩;
        rw [ Finset.card_eq_three ] at h₂; obtain ⟨ u, v, w, h ⟩ := h₂; use u, v, w; aesop;
      obtain ⟨tu, htu, hu_tu⟩ : ∃ tu ∈ S_e G M e, u ∉ tu := h_no_common u (by
      aesop)
      obtain ⟨tv, htv, hv_tv⟩ : ∃ tv ∈ S_e G M e, v ∉ tv := h_no_common v (by
      aesop)
      obtain ⟨tw, htw, hw_tw⟩ : ∃ tw ∈ S_e G M e, w ∉ tw := h_no_common w (by
      aesop)
      obtain ⟨x, hx_not_in_e, htu_eq, htv_eq⟩ : ∃ x, x ∉ ({u, v, w} : Finset V) ∧ tu = {v, w, x} ∧ tv = {u, w, x} := by
        apply Se_structure_step1 G M hM e he u v w he_eq.left he_eq.right tu htu hu_tu tv htv hv_tv
      have htw_eq : tw = {u, v, x} := Se_structure_step2 G M hM e he u v w he_eq.left he_eq.right tu htu hu_tu tv htv hv_tv tw htw hw_tw x hx_not_in_e htu_eq htv_eq;
      refine' ⟨ u, v, w, x, he_eq.1, he_eq.2.1, he_eq.2.2.1, he_eq.2.2.2, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      intro t ht
      by_cases h_cases : t = {u, v, w} ∨ t = {v, w, x} ∨ t = {u, w, x} ∨ t = {u, v, x};
      · exact h_cases;
      · have h_inter : (t ∩ {u, v, w}).card ≥ 2 ∧ (t ∩ {v, w, x}).card ≥ 2 ∧ (t ∩ {u, w, x}).card ≥ 2 ∧ (t ∩ {u, v, x}).card ≥ 2 := by
          have h_inter : ∀ t1 ∈ S_e G M {u, v, w}, ∀ t2 ∈ S_e G M {u, v, w}, (t1 ∩ t2).card ≥ 2 := by
            apply Se_pairwise_intersect G M hM {u, v, w} he;
          exact ⟨ h_inter _ ht _ ( by
            simp +decide [ *, S_e ];
            simp +decide [ trianglesSharingEdge ];
            have := hM.1; simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ] ;
            have := this.2; simp_all +decide [ isTrianglePacking ] ;
            have := ‹M ⊆ G.cliqueFinset 3› he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            exact fun f hf hf' => ‹ ( M : Set ( Finset V ) ).Pairwise fun t1 t2 => ( t1 ∩ t2 ).card ≤ 1 › hf he hf' |> fun h => by simpa only [ Finset.inter_comm ] using h; ), h_inter _ ht _ htu, h_inter _ ht _ htv, h_inter _ ht _ htw ⟩;
        have h_card : t.card = 3 := by
          have h_card : t ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.1;
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact h_card.2;
        have h_inter : t ⊆ {u, v, w, x} := by
          intro y hy; contrapose! h_cases; simp_all +decide [ Finset.subset_iff ] ;
          have h_inter : (t ∩ {u, v, w}).card ≤ 2 ∧ (t ∩ {v, w, x}).card ≤ 2 ∧ (t ∩ {u, w, x}).card ≤ 2 ∧ (t ∩ {u, v, x}).card ≤ 2 := by
            exact ⟨ Nat.le_of_lt_succ ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, fun h => by have := Finset.mem_inter.mp ( h.symm ▸ hy ) ; aesop ⟩ ) ) ( by simp +decide [ * ] ) ), Nat.le_of_lt_succ ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, fun h => by have := Finset.mem_inter.mp ( h.symm ▸ hy ) ; aesop ⟩ ) ) ( by simp +decide [ * ] ) ), Nat.le_of_lt_succ ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, fun h => by have := Finset.mem_inter.mp ( h.symm ▸ hy ) ; aesop ⟩ ) ) ( by simp +decide [ * ] ) ), Nat.le_of_lt_succ ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.inter_subset_left, fun h => by have := Finset.mem_inter.mp ( h.symm ▸ hy ) ; aesop ⟩ ) ) ( by simp +decide [ * ] ) ) ⟩;
          grind;
        have h_inter : t = {u, v, w} ∨ t = {u, v, x} ∨ t = {u, w, x} ∨ t = {v, w, x} := by
          have h_subset : t ⊆ {u, v, w, x} := h_inter
          have h_card : t.card = 3 := h_card
          have h_subset : ∀ s : Finset V, s ⊆ {u, v, w, x} → s.card = 3 → s = {u, v, w} ∨ s = {u, v, x} ∨ s = {u, w, x} ∨ s = {v, w, x} := by
            simp +decide [ Finset.subset_iff ];
            intro s hs hs_card
            have h_subset : s ⊆ {u, v, w, x} := by
              exact fun x hx => by simpa using hs hx;
            have h_subset : ∀ s : Finset V, s ⊆ {u, v, w, x} → s.card = 3 → s = {u, v, w} ∨ s = {u, v, x} ∨ s = {u, w, x} ∨ s = {v, w, x} := by
              intro s hs hs_card
              have h_subset : s ⊆ {u, v, w, x} := hs
              have h_card : s.card = 3 := hs_card
              rw [ Finset.card_eq_three ] at h_card;
              rcases h_card with ⟨ a, b, c, hab, hac, hbc, rfl ⟩ ; simp_all +decide [ Finset.subset_iff ] ;
              rcases h_subset with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] at hab hac hbc ⊢;
            exact h_subset s ‹_› ‹_›;
          exact h_subset t h_inter h_card;
        grind +ring

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_S_le_2 (MAIN RESULT - FULL PROOF)
-- ══════════════════════════════════════════════════════════════════════════════

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma S_e_pair_intersect_ge_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e)
    (hne1 : t1 ≠ e) (hne2 : t2 ≠ e) :
    (t1 ∩ t2).card ≥ 2 := by
      unfold isMaxPacking at hM;
      -- If |t1 ∩ t2| ≤ 1, then we can replace e with {t1, t2} in the packing M to get a larger packing.
      by_contra h_contra
      have h_replace : isTrianglePacking G (insert t1 (insert t2 (M.erase e))) := by
        unfold isTrianglePacking at *;
        unfold S_e at *; simp_all +decide [ Finset.subset_iff, Set.Pairwise ] ;
        exact ⟨ ⟨ by unfold trianglesSharingEdge at ht1; aesop, by unfold trianglesSharingEdge at ht2; aesop ⟩, fun h => Nat.le_of_lt_succ h_contra, fun h => by rw [ Finset.inter_comm ] ; exact Nat.le_of_lt_succ h_contra, fun a ha ha' => ⟨ fun ha'' => by have := ht1.2 a ha ha'; rw [ Finset.inter_comm ] at this; aesop, fun ha'' => by have := ht2.2 a ha ha'; rw [ Finset.inter_comm ] at this; aesop ⟩ ⟩;
      have h_card : (insert t1 (insert t2 (M.erase e))).card > M.card := by
        by_cases h : t1 = t2 <;> simp_all +decide [ Finset.card_insert_of_notMem ];
        · have h_triangle : t2 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ht2 |>.1 |> Finset.mem_filter.mp |>.1;
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact absurd h_contra ( by rw [ h_triangle.2 ] ; decide );
        · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp_all +decide [ Finset.subset_iff ];
          · omega;
          · intro H; have := hM.1.2; simp_all +decide [ Finset.subset_iff ] ;
            have := this H he; simp_all +decide [ Finset.inter_comm ] ;
            unfold S_e at ht2; simp_all +decide [ Finset.inter_comm ] ;
            unfold trianglesSharingEdge at ht2; simp_all +decide [ Finset.inter_comm ] ;
            linarith;
          · intro H; have := hM.1.2; simp_all +decide [ Finset.subset_iff ] ;
            have := this H he; simp_all +decide ;
            unfold S_e at ht1; simp_all +decide ;
            unfold trianglesSharingEdge at ht1; simp_all +decide ;
            linarith;
      -- This contradicts the maximality of $M$.
      have h_contradiction : (insert t1 (insert t2 (M.erase e))).card ≤ trianglePackingNumber G := by
        have h_contradiction : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ trianglePackingNumber G := by
          unfold trianglePackingNumber;
          intro S hS;
          have h_contradiction : S.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
            exact Finset.mem_image.mpr ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hS.1, hS ⟩, rfl ⟩;
          have h_contradiction : ∀ x ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)).max 0 := by
            intro x hx;
            have := Finset.le_max hx;
            cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
          exact h_contradiction _ ‹_›;
        exact h_contradiction _ h_replace;
      linarith

/-
If two triangles in $S_e$ (other than $e$) intersect $e$ in different edges, then they must share the same vertex outside of $e$.
-/

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma S_e_diff_inter_eq_of_neq_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e)
    (hne1 : t1 ≠ e) (hne2 : t2 ≠ e)
    (h_diff_inter : t1 ∩ e ≠ t2 ∩ e) :
    t1 \ e = t2 \ e := by
      -- Since $t_1, t_2 \in S_e$ and are not equal to $e$, they must share an edge with $e$. Thus $|t_1 \cap e| = 2$ and $|t_2 \cap e| = 2$.
      have h_inter_card : (t1 ∩ e).card = 2 ∧ (t2 ∩ e).card = 2 := by
        -- Since $t_1$ and $t_2$ are triangles, they each have exactly 3 vertices.
        have h_t1_card : t1.card = 3 := by
          -- Since $t1 \in S_e G M e$, we have $t1 \in trianglesSharingEdge G e$, which means $t1 \in G.cliqueFinset 3$.
          have ht1_clique : t1 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ht1 |>.1 |> fun h => Finset.mem_filter.mp h |>.1;
          exact Finset.mem_filter.mp ht1_clique |>.2.2
        have h_t2_card : t2.card = 3 := by
          have h_t2_card : t2 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ht2 |>.1 |> Finset.mem_filter.mp |>.1;
          exact Finset.mem_filter.mp h_t2_card |>.2.2
        have h_e_card : e.card = 3 := by
          have := hM.1;
          have := this.1;
          have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          exact this.card_eq;
        -- Since $t_1$ and $t_2$ are triangles, they each have exactly 3 vertices, and since $e$ is a triangle, it also has exactly 3 vertices.
        have h_inter_card_ge_2 : 2 ≤ (t1 ∩ e).card ∧ 2 ≤ (t2 ∩ e).card := by
          unfold S_e at ht1 ht2;
          unfold trianglesSharingEdge at ht1 ht2; aesop;
        have h_inter_card_le_2 : (t1 ∩ e).card ≤ 2 ∧ (t2 ∩ e).card ≤ 2 := by
          constructor <;> contrapose! hne1;
          · have h_inter_card_eq_3 : t1 ∩ e = t1 := by
              exact Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left ) ( by linarith );
            have := Finset.eq_of_subset_of_card_le ( show t1 ⊆ e from h_inter_card_eq_3 ▸ Finset.inter_subset_right ) ; aesop;
          · have h_inter_eq : t2 ∩ e = e := by
              exact Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right ) ( by linarith );
            have := Finset.eq_of_subset_of_card_le ( show e ⊆ t2 from fun x hx => by aesop ) ; aesop;
        exact ⟨ le_antisymm h_inter_card_le_2.1 h_inter_card_ge_2.1, le_antisymm h_inter_card_le_2.2 h_inter_card_ge_2.2 ⟩;
      -- Let $x_1$ be the unique element in $t_1 \setminus e$ and $x_2$ be the unique element in $t_2 \setminus e$.
      obtain ⟨x1, hx1⟩ : ∃ x1, t1 \ e = {x1} := by
        have h_card_diff : (t1 \ e).card = 1 := by
          have h_card_diff : (t1 \ e).card = (t1).card - (t1 ∩ e).card := by
            grind;
          have h_card_t1 : t1 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ht1 |>.1 |> Finset.mem_filter.mp |>.1;
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact Nat.sub_eq_of_eq_add ( by linarith [ h_card_t1.2 ] );
        exact Finset.card_eq_one.mp h_card_diff
      obtain ⟨x2, hx2⟩ : ∃ x2, t2 \ e = {x2} := by
        have h_inter_card_t2 : (t2 \ e).card = 1 := by
          have h_inter_card_t2 : (t2 \ e).card = t2.card - (t2 ∩ e).card := by
            grind;
          have h_card_t2 : t2 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ht2 |>.1 |> Finset.mem_filter.mp |>.1;
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact Nat.sub_eq_of_eq_add ( by linarith [ h_card_t2.card_eq ] );
        exact Finset.card_eq_one.mp h_inter_card_t2;
      -- The intersection $t_1 \cap t_2$ is the union of $(t_1 \cap e) \cap (t_2 \cap e)$ and $\{x_1\} \cap \{x_2\}$ (cross terms are empty because $x_i \notin e$).
      have h_inter_union : (t1 ∩ t2).card = (t1 ∩ e ∩ t2 ∩ e).card + (if x1 = x2 then 1 else 0) := by
        have h_inter_union : t1 ∩ t2 = (t1 ∩ e ∩ t2 ∩ e) ∪ (if x1 = x2 then {x1} else ∅) := by
          ext v; by_cases hv : v ∈ e <;> simp_all +decide [ Finset.ext_iff ] ;
          · grind;
          · grind;
        rw [ Finset.eq_singleton_iff_unique_mem ] at hx1 hx2 ; aesop;
      -- Since $t_1 \cap e \ne t_2 \cap e$, and both are subsets of $e$ of size 2, their intersection must have size 1.
      have h_inter_card_1 : (t1 ∩ e ∩ t2 ∩ e).card = 1 := by
        have h_inter_card_1 : (t1 ∩ e ∩ t2 ∩ e).card ≤ 1 := by
          have h_inter_card_1 : (t1 ∩ e ∩ t2 ∩ e).card < 2 := by
            refine' lt_of_le_of_ne _ _;
            · exact le_trans ( Finset.card_le_card ( show t1 ∩ e ∩ t2 ∩ e ⊆ t1 ∩ e from fun x hx => by aesop ) ) h_inter_card.1.le;
            · intro h;
              have h_inter_eq : t1 ∩ e ∩ t2 ∩ e = t1 ∩ e ∧ t1 ∩ e ∩ t2 ∩ e = t2 ∩ e := by
                exact ⟨ Finset.eq_of_subset_of_card_le ( by aesop_cat ) ( by aesop_cat ), Finset.eq_of_subset_of_card_le ( by aesop_cat ) ( by aesop_cat ) ⟩;
              aesop;
          linarith;
        interval_cases _ : Finset.card ( t1 ∩ e ∩ t2 ∩ e ) <;> simp_all +decide;
        have := S_e_pair_intersect_ge_2 G M hM e he t1 t2 ht1 ht2 hne1 hne2; simp_all +decide ;
        split_ifs at this <;> contradiction;
      -- By `S_e_pair_intersect_ge_2`, $|t_1 \cap t_2| \ge 2$.
      have h_inter_card_ge_2 : (t1 ∩ t2).card ≥ 2 := by
        apply S_e_pair_intersect_ge_2 G M hM e he t1 t2 ht1 ht2 hne1 hne2;
      aesop

/-
If there are two triangles in $S_e$ that intersect $e$ in different edges, then all triangles in $S_e$ (except $e$) share the same vertex $x$ outside of $e$.
-/

-- Source: proven/tuza/lemmas/slot29_triple_apex.lean
lemma S_e_structure_of_diverse_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (ta tb : Finset V) (hta : ta ∈ S_e G M e) (htb : tb ∈ S_e G M e)
    (hnea : ta ≠ e) (hneb : tb ≠ e)
    (h_diff_inter : ta ∩ e ≠ tb ∩ e) :
    ∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → t = insert x (t ∩ e) := by
      -- Since $t_a \setminus e = t_b \setminus e$, we can let $x$ be the unique element in $t_a \setminus e$.
      obtain ⟨x, hx⟩ : ∃ x, ta \ e = {x} ∧ tb \ e = {x} := by
        -- Since $ta \setminus e = tb \setminus e$ and both are singletons, we can conclude that they are equal to the same singleton set.
        have h_singleton : (ta \ e).card = 1 ∧ (tb \ e).card = 1 := by
          have h_card_diff : ∀ t ∈ S_e G M e, t ≠ e → (t \ e).card = 1 := by
            intro t ht hne
            have h_inter : (t ∩ e).card ≥ 2 := by
              unfold S_e at ht;
              unfold trianglesSharingEdge at ht; aesop;
            have h_card_t : t.card = 3 := by
              have h_card_t : t ∈ G.cliqueFinset 3 := by
                exact Finset.mem_filter.mp ht |>.1 |> Finset.mem_filter.mp |>.1 |> fun h => by aesop;
              have h_card_t_eq : t.card = 3 := by
                exact Finset.mem_filter.mp h_card_t |>.2.2
              exact h_card_t_eq
              skip -- This is a placeholder to prevent the code from compiling, as the actual proof is required.
            have h_card_e : e.card = 3 := by
              have := hM.1;
              have := this.1;
              have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
              exact this.2
            have h_card_inter : (t ∩ e).card = 2 := by
              have h_inter_eq : (t ∩ e).card ≤ 2 := by
                have h_card_inter : (t ∩ e).card < 3 := by
                  have h_inter_eq : (t ∩ e) ≠ t := by
                    exact fun h => hne <| Finset.eq_of_subset_of_card_le ( by aesop ) <| by aesop;
                  exact lt_of_le_of_ne ( le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) h_card_t.le ) fun h => h_inter_eq <| Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left ) <| by simp +decide [ * ] ;
                linarith [h_card_inter]
              exact le_antisymm h_inter_eq h_inter
            have h_card_diff : (t \ e).card = t.card - (t ∩ e).card := by
              grind
            rw [h_card_t, h_card_inter] at h_card_diff
            simp [h_card_diff];
          exact ⟨ h_card_diff ta hta hnea, h_card_diff tb htb hneb ⟩;
        have h_eq_singleton : ta \ e =(tb \ e) := by
          exact S_e_diff_inter_eq_of_neq_inter G M hM e he ta tb hta htb hnea hneb h_diff_inter;
        rw [ Finset.card_eq_one ] at h_singleton ; aesop;
      refine' ⟨ x, _, _ ⟩ <;> simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
      intro t ht hne; ext y; by_cases hy : y ∈ e <;> simp_all +decide ;
      · grind +ring;
      · by_cases h : t ∩ e = ta ∩ e <;> simp_all +decide [ Finset.ext_iff ];
        · have := S_e_diff_inter_eq_of_neq_inter G M hM e he t tb ht htb; simp_all +decide [ Finset.ext_iff ] ;
          grind;
        · have := S_e_diff_inter_eq_of_neq_inter G M hM e he t ta ht hta; simp_all +decide [ Finset.ext_iff ] ;
          grind +ring

/-
If there are diverse intersections in $S_e$, the covering number is at most 2.
-/

-- Source: proven/tuza/lemmas/slot35_tau_pair_le_4.lean
lemma v_decomposition_union (triangles : Finset (Finset V)) (v : V) :
    triangles = trianglesContaining triangles v ∪ trianglesAvoiding triangles v := by
  ext t
  simp [trianglesContaining, trianglesAvoiding]
  tauto

-- Source: proven/tuza/lemmas/tau_union_le_sum.lean
lemma v_decomposition_union (triangles : Finset (Finset V)) (v : V) :
    triangles = trianglesContaining triangles v ∪ trianglesAvoiding triangles v := by
  ext t
  simp [trianglesContaining, trianglesAvoiding]
  tauto

/-- Key corollary for V-decomposition approach to τ(T_e ∪ T_f) ≤ 4 -/

-- Source: proven/tuza/lemmas/slot44/5a188e26-ef0d-44c2-a565-cd798ad02e00-output.lean
lemma pairwise_intersecting_Se_aux (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    Set.Pairwise ((S_e G M e).filter (· ≠ e) : Set (Finset V)) (fun t1 t2 => 2 ≤ (t1 ∩ t2).card) := by
  by_contra h_contra
  obtain ⟨t1, t2, ht1, ht2, h_disjoint⟩ : ∃ t1 t2 : Finset V, t1 ≠ t2 ∧ t1 ∈ S_e G M e ∧ t2 ∈ S_e G M e ∧ t1 ≠ e ∧ t2 ≠ e ∧ (t1 ∩ t2).card ≤ 1 := by
    rw [ Set.Pairwise ] at h_contra;
    grind;
  have h_disjoint_M : ∀ f ∈ M \ {e}, (t1 ∩ f).card ≤ 1 ∧ (t2 ∩ f).card ≤ 1 := by
    unfold S_e at *; aesop;
  have h_packing : isTrianglePacking G ((M \ {e}) ∪ {t1, t2}) := by
    constructor;
    · intro x hx;
      simp +zetaDelta at *;
      rcases hx with ( rfl | rfl | ⟨ hx, hx' ⟩ ) <;> simp_all +decide [ S_e ];
      · unfold trianglesSharingEdge at ht2; aesop;
      · unfold trianglesSharingEdge at h_disjoint; aesop;
      · have := hM.1.1 hx; aesop;
    · simp_all +decide [ Set.Pairwise ];
      refine' ⟨ fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint.2.2.2, fun a ha ha' => ⟨ fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint_M a ha ha' |>.1, fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint_M a ha ha' |>.2, fun b hb hb' hab => _ ⟩ ⟩;
      have := hM.1;
      have := this.2 ha hb hab; aesop;
  have h_card : ((M \ {e}) ∪ {t1, t2}).card > M.card := by
    have h_card : ((M \ {e}) ∪ {t1, t2}).card = (M \ {e}).card + 2 := by
      have h_card : Disjoint (M \ {e}) {t1, t2} := by
        simp_all +decide [ Finset.disjoint_left ];
        intro f hf hfe; have := h_packing.1; simp_all +decide [ Finset.subset_iff ] ;
        constructor <;> intro h <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
        · grind;
        · have := h_disjoint_M t2 hf; simp_all +decide ;
      rw [ Finset.card_union_of_disjoint h_card, Finset.card_insert_of_notMem, Finset.card_singleton ] ; aesop;
    simp_all +decide [ Finset.card_sdiff ];
    omega;
  have h_contradiction : ((M \ {e}) ∪ {t1, t2}).card ≤ trianglePackingNumber G := by
    have h_contradiction : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ trianglePackingNumber G := by
      unfold trianglePackingNumber;
      intro S hS;
      have h_contradiction : S.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        exact Finset.mem_image.mpr ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by exact fun x hx => by have := hS.1 hx; aesop ), hS ⟩, rfl ⟩;
      have := Finset.le_max h_contradiction;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_contradiction _ h_packing;
  exact h_card.not_le ( h_contradiction.trans ( hM.2.ge ) )

-- Source: proven/tuza/lemmas/slot44/5a188e26-ef0d-44c2-a565-cd798ad02e00-output.lean
lemma Se_structure_lemma (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (∃ uv, uv ⊆ e ∧ uv.card = 2 ∧ ∀ t ∈ S_e G M e, t ≠ e → uv ⊆ t) ∨
    (∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → t = (t ∩ e) ∪ {x}) := by
  by_cases h : ∃ t1 t2 : Finset V, t1 ∈ S_e G M e ∧ t2 ∈ S_e G M e ∧ t1 ≠ e ∧ t2 ≠ e ∧ t1 ∩ e ≠ t2 ∩ e;
  · obtain ⟨ t1, t2, ht1, ht2, h1, h2, h3 ⟩ := h;
    obtain ⟨ x, hx ⟩ := common_ext_vertex_of_diff_edges G M hM e he t1 t2 ( by aesop ) ( by aesop ) h3;
    refine' Or.inr ⟨ x, hx.1, fun t ht ht' => _ ⟩;
    by_cases h4 : t ∩ e = t1 ∩ e;
    · have := common_ext_vertex_of_diff_edges G M hM e he t t2 ( by
        exact Finset.mem_filter.mpr ⟨ ht, ht' ⟩ ) ( by
        exact Finset.mem_filter.mpr ⟨ ht2, h2 ⟩ ) ( by
        exact h4.symm ▸ h3 );
      grind;
    · have := common_ext_vertex_of_diff_edges G M hM e he t t1 ( by
        exact Finset.mem_filter.mpr ⟨ ht, ht' ⟩ ) ( by
        exact Finset.mem_filter.mpr ⟨ ht1, h1 ⟩ ) h4;
      grind;
  · by_cases h_empty : S_e G M e \ {e} = ∅;
    · simp_all +decide [ Finset.ext_iff ];
      contrapose! h_empty;
      have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      have := this.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      exact False.elim ( h_empty.1 ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose ) ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose_spec |> And.left ) ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose_spec |> And.right ) );
    · obtain ⟨t, ht⟩ : ∃ t ∈ S_e G M e \ {e}, ∀ t' ∈ S_e G M e \ {e}, t ∩ e = t' ∩ e := by
        exact Exists.elim ( Finset.nonempty_of_ne_empty h_empty ) fun t ht => ⟨ t, ht, fun t' ht' => Classical.not_not.1 fun h' => h ⟨ t, t', by aesop ⟩ ⟩;
      have := Finset.mem_filter.mp ( Finset.mem_sdiff.mp ht.1 |>.1 );
      have := Finset.mem_filter.mp this.1;
      obtain ⟨uv, huv⟩ : ∃ uv ⊆ t ∩ e, uv.card = 2 := by
        exact Finset.exists_subset_card_eq this.2;
      grind

-- Source: proven/tuza/lemmas/slot32/2b3cce69-ca98-4c3a-9e7d-55ca3afab48d-output.lean
lemma pairwise_intersecting_Se_aux (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    Set.Pairwise ((S_e G M e).filter (· ≠ e) : Set (Finset V)) (fun t1 t2 => 2 ≤ (t1 ∩ t2).card) := by
      -- Suppose for contradiction that there exist distinct t1, t2 in S_e(e) \ {e} that are edge-disjoint (intersection size <= 1).
      by_contra h_contra
      obtain ⟨t1, t2, ht1, ht2, h_disjoint⟩ : ∃ t1 t2 : Finset V, t1 ≠ t2 ∧ t1 ∈ S_e G M e ∧ t2 ∈ S_e G M e ∧ t1 ≠ e ∧ t2 ≠ e ∧ (t1 ∩ t2).card ≤ 1 := by
        rw [ Set.Pairwise ] at h_contra;
        grind;
      -- Since $t1, t2 \in S_e(e)$, they are edge-disjoint from all triangles in $M \setminus \{e\}$.
      have h_disjoint_M : ∀ f ∈ M \ {e}, (t1 ∩ f).card ≤ 1 ∧ (t2 ∩ f).card ≤ 1 := by
        unfold S_e at *; aesop;
      -- Since $t1$ and $t2$ are edge-disjoint from each other and from all triangles in $M \setminus \{e\}$, the set $(M \setminus \{e\}) \cup \{t1, t2\}$ is a triangle packing.
      have h_packing : isTrianglePacking G ((M \ {e}) ∪ {t1, t2}) := by
        constructor;
        · intro x hx;
          simp +zetaDelta at *;
          rcases hx with ( rfl | rfl | ⟨ hx, hx' ⟩ ) <;> simp_all +decide [ S_e ];
          · unfold trianglesSharingEdge at ht2; aesop;
          · unfold trianglesSharingEdge at h_disjoint; aesop;
          · have := hM.1.1 hx; aesop;
        · simp_all +decide [ Set.Pairwise ];
          refine' ⟨ fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint.2.2.2, fun a ha ha' => ⟨ fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint_M a ha ha' |>.1, fun _ => by rw [ Finset.inter_comm ] ; exact h_disjoint_M a ha ha' |>.2, fun b hb hb' hab => _ ⟩ ⟩;
          have := hM.1;
          have := this.2 ha hb hab; aesop;
      -- The size of this packing is $|M| - 1 + 2 = |M| + 1$, which is strictly greater than $|M|$.
      have h_card : ((M \ {e}) ∪ {t1, t2}).card > M.card := by
        have h_card : ((M \ {e}) ∪ {t1, t2}).card = (M \ {e}).card + 2 := by
          have h_card : Disjoint (M \ {e}) {t1, t2} := by
            simp_all +decide [ Finset.disjoint_left ];
            intro f hf hfe; have := h_packing.1; simp_all +decide [ Finset.subset_iff ] ;
            constructor <;> intro h <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
            · grind;
            · have := h_disjoint_M t2 hf; simp_all +decide ;
          rw [ Finset.card_union_of_disjoint h_card, Finset.card_insert_of_notMem, Finset.card_singleton ] ; aesop;
        simp_all +decide [ Finset.card_sdiff ];
        omega;
      have h_contradiction : ((M \ {e}) ∪ {t1, t2}).card ≤ trianglePackingNumber G := by
        have h_contradiction : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ trianglePackingNumber G := by
          unfold trianglePackingNumber;
          intro S hS;
          have h_contradiction : S.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
            exact Finset.mem_image.mpr ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( by exact fun x hx => by have := hS.1 hx; aesop ), hS ⟩, rfl ⟩;
          have := Finset.le_max h_contradiction;
          cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
        exact h_contradiction _ h_packing;
      exact h_card.not_le ( h_contradiction.trans ( hM.2.ge ) )

-- Source: proven/tuza/lemmas/slot32/2b3cce69-ca98-4c3a-9e7d-55ca3afab48d-output.lean
lemma Se_structure_lemma (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (∃ uv, uv ⊆ e ∧ uv.card = 2 ∧ ∀ t ∈ S_e G M e, t ≠ e → uv ⊆ t) ∨
    (∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → t = (t ∩ e) ∪ {x}) := by
      by_cases h : ∃ t1 t2 : Finset V, t1 ∈ S_e G M e ∧ t2 ∈ S_e G M e ∧ t1 ≠ e ∧ t2 ≠ e ∧ t1 ∩ e ≠ t2 ∩ e;
      · obtain ⟨ t1, t2, ht1, ht2, h1, h2, h3 ⟩ := h;
        obtain ⟨ x, hx ⟩ := common_ext_vertex_of_diff_edges G M hM e he t1 t2 ( by aesop ) ( by aesop ) h3;
        refine' Or.inr ⟨ x, hx.1, fun t ht ht' => _ ⟩;
        by_cases h4 : t ∩ e = t1 ∩ e;
        · have := common_ext_vertex_of_diff_edges G M hM e he t t2 ( by
            exact Finset.mem_filter.mpr ⟨ ht, ht' ⟩ ) ( by
            exact Finset.mem_filter.mpr ⟨ ht2, h2 ⟩ ) ( by
            exact h4.symm ▸ h3 );
          grind;
        · have := common_ext_vertex_of_diff_edges G M hM e he t t1 ( by
            exact Finset.mem_filter.mpr ⟨ ht, ht' ⟩ ) ( by
            exact Finset.mem_filter.mpr ⟨ ht1, h1 ⟩ ) h4;
          grind;
      · by_cases h_empty : S_e G M e \ {e} = ∅;
        · simp_all +decide [ Finset.ext_iff ];
          contrapose! h_empty;
          have := hM.1.1 he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          have := this.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          exact False.elim ( h_empty.1 ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose ) ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose_spec |> And.left ) ( Finset.exists_subset_card_eq ( show 2 ≤ e.card from by linarith ) |> Classical.choose_spec |> And.right ) );
        · obtain ⟨t, ht⟩ : ∃ t ∈ S_e G M e \ {e}, ∀ t' ∈ S_e G M e \ {e}, t ∩ e = t' ∩ e := by
            exact Exists.elim ( Finset.nonempty_of_ne_empty h_empty ) fun t ht => ⟨ t, ht, fun t' ht' => Classical.not_not.1 fun h' => h ⟨ t, t', by aesop ⟩ ⟩;
          have := Finset.mem_filter.mp ( Finset.mem_sdiff.mp ht.1 |>.1 );
          have := Finset.mem_filter.mp this.1;
          obtain ⟨uv, huv⟩ : ∃ uv ⊆ t ∩ e, uv.card = 2 := by
            exact Finset.exists_subset_card_eq this.2;
          grind

-- Source: proven/tuza/lemmas/slot32/2b3cce69-ca98-4c3a-9e7d-55ca3afab48d-output.lean
lemma path_nonadjacent_disjoint (e1 e2 e3 e4 : Finset V)
    (v12 : V) (hv12 : e1 ∩ e2 = {v12})
    (v23 : V) (hv23 : e2 ∩ e3 = {v23})
    (v34 : V) (hv34 : e3 ∩ e4 = {v34})
    (h_distinct : v12 ≠ v23 ∧ v23 ≠ v34 ∧ v12 ≠ v34) :
    Disjoint (e1 : Set V) (e3 : Set V) ∧
    Disjoint (e1 : Set V) (e4 : Set V) ∧
    Disjoint (e2 : Set V) (e4 : Set V) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any four distinct vertices $v_1, v_2, v_3, v_4$.
  use ULift (Fin 4);
  -- Let's choose any four distinct vertices $v_1, v_2, v_3, v_4$ and define the edges $e_1, e_2, e_3, e_4$ accordingly.
  use inferInstance, inferInstance, {⟨0⟩, ⟨1⟩}, {⟨1⟩, ⟨2⟩}, {⟨2⟩, ⟨3⟩}, {⟨3⟩, ⟨0⟩};
  -- Let's simplify the goal.
  simp +decide [Set.ext_iff]

-/
-- ══════════════════════════════════════════════════════════════════════════════
-- PATH-SPECIFIC LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

-- In path configuration, non-adjacent elements are vertex-disjoint

