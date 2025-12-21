/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4736da84-a282-4935-ba1b-06d02bc5d92c

The following was proved by Aristotle:

- lemma S_e_pairwise_share_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e) (hne : t1 ≠ t2) :
    shareEdge t1 t2

- lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (S_e G M e) ≤ 2

- lemma Te_eq_Se_when_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 1)
    (e : Finset V) (he : e ∈ M) :
    T_e G e = S_e G M e

- theorem tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G ≤ 3) : coveringNumber G ≤ 2 * packingNumber G
-/

/-
Tuza ν ≤ 3: FIXED coveringNumberOn definition

CRITICAL FIX: coveringNumberOn now restricted to G.edgeFinset
Previous bug: allowed edges not in G
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Triangles represented as 3-element vertex sets
def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3

-- Two triangles share an edge iff they share ≥ 2 vertices
def shareEdge (t1 t2 : Finset V) : Prop :=
  (t1 ∩ t2).card ≥ 2

-- Edge-disjoint = pairwise share at most 1 vertex
def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  Set.Pairwise (T : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (IsTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

-- T_e = triangles sharing an edge with e (share ≥ 2 vertices)
def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

-- S_e = triangles sharing edge with e but NOT with any other f ∈ M
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- FIXED: coveringNumberOn restricts to G.edgeFinset
noncomputable def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E =>
    ∀ t ∈ S, ∃ e ∈ E, e ∈ t.sym2
  ) |>.image Finset.card |>.min |>.getD 0

def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E =>
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2
  ) |>.image Finset.card |>.min |>.getD 0

-- Parker Lemma 2.2: S_e triangles pairwise share edges
noncomputable section AristotleLemmas

/-
If there are two distinct triangles in S_e that do not share an edge, we can replace e with these two triangles to get a larger packing.
-/
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma larger_packing_if_disjoint_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsTrianglePacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e)
    (hne : t1 ≠ t2) (h_disjoint : ¬ shareEdge t1 t2) :
    ∃ M', IsTrianglePacking G M' ∧ M'.card > M.card := by
  -- Let $M' = (M \setminus \{e\}) \cup \{t_1, t_2\}$.
  use (M \ {e}) ∪ {t1, t2};
  constructor;
  · constructor <;> simp_all +decide [ IsTrianglePacking ];
    · simp_all +decide [ Finset.subset_iff, S_e ];
      unfold T_e at *; aesop;
    · simp_all +decide [ IsEdgeDisjoint ];
      simp_all +decide [ Set.Pairwise ];
      unfold S_e at *; simp_all +decide [ Finset.filter_filter ] ;
      simp_all +decide [ Finset.inter_comm, shareEdge ];
      exact ⟨ Nat.le_of_lt_succ h_disjoint, fun _ => Nat.le_of_lt_succ h_disjoint ⟩;
  · rw [ Finset.card_union_of_disjoint ] <;> simp_all +decide [ Finset.disjoint_left ];
    · grind;
    · intro a ha hae; refine' ⟨ _, _ ⟩ <;> intro h <;> simp_all +decide [ S_e ] ;
      · unfold T_e at ht1; simp_all +decide [ Finset.inter_comm ] ;
        exact absurd ( ht1.2 _ ha hae ) ( by rw [ Finset.inter_comm ] ; exact not_le_of_gt ( by rw [ Finset.inter_self ] ; exact ht1.1.1.card_eq.symm ▸ by decide ) );
      · unfold T_e at *; simp_all +decide [ shareEdge ] ;
        have := ht2.2 _ ha hae; simp_all +decide [ Finset.inter_comm ] ;
        exact this.not_lt ( by rw [ ht2.1.1.2 ] ; decide )

end AristotleLemmas

lemma S_e_pairwise_share_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e) (hne : t1 ≠ t2) :
    shareEdge t1 t2 := by
  -- By definition of `IsMaxPacking`, there cannot exist a triangle packing $M'$ with $|M'| > |M|$.
  have h_max_packing : ∀ M' : Finset (Finset V), IsTrianglePacking G M' → M'.card ≤ M.card := by
    unfold IsMaxPacking at hM;
    unfold packingNumber at hM;
    rw [ hM.2 ];
    intro M' hM'
    have hM'_subset : M' ⊆ G.cliqueFinset 3 := by
      exact hM'.1;
    have hM'_card : M'.card ∈ Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset) := by
      exact Finset.mem_image.mpr ⟨ M', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hM'_subset, hM' ⟩, rfl ⟩;
    have := Finset.le_max hM'_card;
    cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( IsTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
  contrapose! h_max_packing with h_max_packing' ; simp_all +decide [ IsMaxPacking ] ; aesop;
  have := larger_packing_if_disjoint_Se G M left e he t1 t2 ht1 ht2 hne h_max_packing' ; aesop;

-- Pairwise sharing implies τ ≤ 2 (star or K4 structure)
noncomputable section AristotleLemmas

/-
If three triangles pairwise share an edge (intersect in size >= 2) and the intersection of the first with the second is different from the intersection of the first with the third, then the union of all three triangles has size 4.
-/
lemma union_of_three_triangles_eq_four {V : Type*} [DecidableEq V]
    (t1 t2 t3 : Finset V)
    (h1 : t1.card = 3) (h2 : t2.card = 3) (h3 : t3.card = 3)
    (h12 : (t1 ∩ t2).card ≥ 2) (h13 : (t1 ∩ t3).card ≥ 2) (h23 : (t2 ∩ t3).card ≥ 2)
    (hne : t1 ∩ t2 ≠ t1 ∩ t3) :
    (t1 ∪ t2 ∪ t3).card = 4 := by
      -- Since each triangle has 3 vertices and they pairwise share at least 2 vertices, the total number of distinct vertices in the union is at most 4.
      have h_card : (t1 ∪ t2 ∪ t3).card ≤ 4 := by
        have := Finset.card_union_add_card_inter t1 ( t2 ∪ t3 ) ; simp_all +decide [ Finset.inter_union_distrib_left ] ;
        have := Finset.card_union_add_card_inter t2 t3; simp_all +decide ;
        have := Finset.card_union_add_card_inter ( t1 ∩ t2 ) ( t1 ∩ t3 ) ; simp_all +decide ;
        contrapose! hne; simp_all +decide [ Finset.inter_comm, Finset.inter_left_comm ] ;
        have := Finset.eq_of_subset_of_card_le ( show t1 ∩ t2 ⊆ t1 ∩ t2 ∪ t1 ∩ t3 from Finset.subset_union_left ) ; have := Finset.eq_of_subset_of_card_le ( show t1 ∩ t3 ⊆ t1 ∩ t2 ∪ t1 ∩ t3 from Finset.subset_union_right ) ; simp_all +decide ;
        exact Finset.Subset.antisymm ( this ( by linarith ) ) ( ‹ ( t1 ∩ t2 ∪ t1 ∩ t3 ).card ≤ ( t1 ∩ t2 ).card → t1 ∩ t3 ⊆ t1 ∩ t2 › ( by linarith ) );
      interval_cases _ : Finset.card ( t1 ∪ t2 ∪ t3 ) <;> simp_all +decide;
      · exact absurd ‹_› ( ne_of_gt ( lt_of_lt_of_le ( by linarith ) ( Finset.card_mono ( Finset.subset_union_left ) ) ) );
      · have := Finset.card_le_card ( show t1 ⊆ t1 ∪ ( t2 ∪ t3 ) by aesop_cat ) ; simp_all +decide ;
      · have h_eq : t1 ⊆ t1 ∪ t2 ∪ t3 ∧ t2 ⊆ t1 ∪ t2 ∪ t3 ∧ t3 ⊆ t1 ∪ t2 ∪ t3 := by
          grind;
        have h_eq : t1 = t1 ∪ t2 ∪ t3 ∧ t2 = t1 ∪ t2 ∪ t3 ∧ t3 = t1 ∪ t2 ∪ t3 := by
          exact ⟨ Finset.eq_of_subset_of_card_le h_eq.1 ( by simp +decide [ * ] ), Finset.eq_of_subset_of_card_le h_eq.2.1 ( by simp +decide [ * ] ), Finset.eq_of_subset_of_card_le h_eq.2.2 ( by simp +decide [ * ] ) ⟩;
        grind

/-
A family of triangles that pairwise share an edge is either a star (all share a common edge) or contained in a K4 (all subsets of a set of size 4).
-/
lemma structure_of_pairwise_edge_sharing_triangles {V : Type*} [DecidableEq V]
    (S : Finset (Finset V))
    (h_tri : ∀ t ∈ S, t.card = 3)
    (h_pair : ∀ t1 ∈ S, ∀ t2 ∈ S, (t1 ∩ t2).card ≥ 2) :
    (∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ S, e ⊆ t) ∨
    (∃ K : Finset V, K.card ≤ 4 ∧ ∀ t ∈ S, t ⊆ K) := by
      by_cases h_cases : ∃ t1 t2 t3, t1 ∈ S ∧ t2 ∈ S ∧ t3 ∈ S ∧ t1 ≠ t2 ∧ t1 ≠ t3 ∧ (t1 ∩ t2) ≠ (t1 ∩ t3);
      · -- Let $K = t1 \cup t2 \cup t3$. By `union_of_three_triangles_eq_four`, $K$ has size 4.
        obtain ⟨t1, t2, t3, ht1, ht2, ht3, hne12, hne13, hne23⟩ := h_cases
        set K : Finset V := t1 ∪ t2 ∪ t3
        have hK_card : K.card = 4 := by
          apply union_of_three_triangles_eq_four t1 t2 t3 (h_tri t1 ht1) (h_tri t2 ht2) (h_tri t3 ht3) (h_pair t1 ht1 t2 ht2) (h_pair t1 ht1 t3 ht3) (h_pair t2 ht2 t3 ht3) hne23;
        -- We claim all $t \in S$ are subsets of $K$.
        have h_subset_K : ∀ t ∈ S, t ⊆ K := by
          intro t ht
          by_contra h_contra
          obtain ⟨v, hv⟩ : ∃ v, v ∈ t ∧ v ∉ K := by
            exact Finset.not_subset.mp h_contra
          have hEdge : ∃ e : Finset V, e.card = 2 ∧ e ⊆ t ∧ e ⊆ t1 := by
            have := h_pair t ht t1 ht1;
            exact Exists.elim ( Finset.exists_subset_card_eq this ) fun e he => ⟨ e, he.2, Finset.Subset.trans he.1 ( Finset.inter_subset_left ), Finset.Subset.trans he.1 ( Finset.inter_subset_right ) ⟩
          obtain ⟨e, he_card, he_t, he_t1⟩ := hEdge
          have hEdge2 : ∃ e' : Finset V, e'.card = 2 ∧ e' ⊆ t ∧ e' ⊆ t2 := by
            have := h_pair t ht t2 ht2;
            obtain ⟨ s, hs ⟩ := Finset.exists_subset_card_eq this;
            exact ⟨ s, hs.2, Finset.Subset.trans hs.1 ( Finset.inter_subset_left ), Finset.Subset.trans hs.1 ( Finset.inter_subset_right ) ⟩
          obtain ⟨e', he'_card, he'_t, he'_t2⟩ := hEdge2
          have hEdge3 : ∃ e'' : Finset V, e''.card = 2 ∧ e'' ⊆ t ∧ e'' ⊆ t3 := by
            have := h_pair t ht t3 ht3;
            exact Exists.elim ( Finset.exists_subset_card_eq this ) fun s hs => ⟨ s, hs.2, Finset.Subset.trans hs.1 ( Finset.inter_subset_left ), Finset.Subset.trans hs.1 ( Finset.inter_subset_right ) ⟩
          obtain ⟨e'', he''_card, he''_t, he''_t3⟩ := hEdge3
          have h_eq_edges : e = e' ∧ e = e'' := by
            have h_eq_edges : e ⊆ t \ {v} ∧ e' ⊆ t \ {v} ∧ e'' ⊆ t \ {v} := by
              simp_all +decide [ Finset.subset_iff ];
              exact ⟨ fun h => hv.2 <| Finset.mem_union_left _ <| Finset.mem_union_left _ <| he_t1 h, fun h => hv.2 <| Finset.mem_union_left _ <| Finset.mem_union_right _ <| he'_t2 h, fun h => hv.2 <| Finset.mem_union_right _ <| he''_t3 h ⟩;
            have h_eq_edges : e = t \ {v} ∧ e' = t \ {v} ∧ e'' = t \ {v} := by
              have h_eq_edges : e.card = (t \ {v}).card ∧ e'.card = (t \ {v}).card ∧ e''.card = (t \ {v}).card := by
                simp_all +decide [ Finset.card_sdiff ];
              exact ⟨ Finset.eq_of_subset_of_card_le ( by tauto ) ( by linarith ), Finset.eq_of_subset_of_card_le ( by tauto ) ( by linarith ), Finset.eq_of_subset_of_card_le ( by tauto ) ( by linarith ) ⟩;
            aesop
          have h_contra_edges : e ⊆ t1 ∩ t2 ∧ e ⊆ t1 ∩ t3 := by
            aesop_cat
          have h_contra_inter : t1 ∩ t2 = t1 ∩ t3 := by
            have h_contra_inter : (t1 ∩ t2).card = 2 ∧ (t1 ∩ t3).card = 2 := by
              have h_contra_inter : (t1 ∩ t2).card ≤ 2 ∧ (t1 ∩ t3).card ≤ 2 := by
                have h_contra_inter : (t1 ∩ t2).card ≤ t1.card - 1 ∧ (t1 ∩ t3).card ≤ t1.card - 1 := by
                  have h_contra_inter : t1 ∩ t2 ⊂ t1 ∧ t1 ∩ t3 ⊂ t1 := by
                    simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
                    exact ⟨ Finset.not_subset.mp fun h => hne12 <| Finset.eq_of_subset_of_card_le h <| by linarith [ h_tri t1 ht1, h_tri t2 ht2 ], Finset.not_subset.mp fun h => hne13 <| Finset.eq_of_subset_of_card_le h <| by linarith [ h_tri t1 ht1, h_tri t3 ht3 ] ⟩;
                  exact ⟨ Nat.le_sub_one_of_lt ( Finset.card_lt_card h_contra_inter.1 ), Nat.le_sub_one_of_lt ( Finset.card_lt_card h_contra_inter.2 ) ⟩;
                aesop;
              exact ⟨ le_antisymm h_contra_inter.1 ( h_pair t1 ht1 t2 ht2 ), le_antisymm h_contra_inter.2 ( h_pair t1 ht1 t3 ht3 ) ⟩;
            have := Finset.eq_of_subset_of_card_le h_contra_edges.1; have := Finset.eq_of_subset_of_card_le h_contra_edges.2; aesop;
          contradiction;
        exact Or.inr ⟨ K, hK_card.le, h_subset_K ⟩;
      · by_cases h_cases : ∃ t1 t2, t1 ∈ S ∧ t2 ∈ S ∧ t1 ≠ t2;
        · obtain ⟨ t1, t2, ht1, ht2, hne ⟩ := h_cases;
          refine' Or.inl ⟨ t1 ∩ t2, _, _ ⟩;
          · have := Finset.card_le_card ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; simp_all +decide ;
            interval_cases _ : Finset.card ( t1 ∩ t2 ) <;> simp_all +decide;
            · exact absurd ( h_pair t1 ht1 t2 ht2 ) ( by simp +decide [ * ] );
            · linarith [ h_pair t1 ht1 t2 ht2 ];
            · have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; aesop;
          · intro t ht; by_cases h : t = t1 <;> by_cases h' : t = t2 <;> simp_all +decide [ Finset.subset_iff ] ;
            intro x hx1 hx2; specialize h_cases t1 ht1 t2 ht2 t ht; simp_all +decide [ Finset.ext_iff ] ;
            grind;
        · rcases S.eq_empty_or_nonempty with ( rfl | ⟨ t, ht ⟩ );
          · exact Or.inr ⟨ ∅, by norm_num ⟩;
          · exact Or.inr ⟨ t, by linarith [ h_tri t ht ], fun u hu => by_contradiction fun h => h_cases ⟨ u, t, hu, ht, by aesop ⟩ ⟩

/-
Any set of triangles contained in a K4 can be covered by at most 2 edges, where each covering edge belongs to one of the triangles.
-/
lemma covering_le_2_of_subset_K4 {V : Type*} [DecidableEq V]
    (S : Finset (Finset V))
    (K : Finset V) (hK : K.card = 4)
    (hS : ∀ t ∈ S, t ⊆ K)
    (h_tri : ∀ t ∈ S, t.card = 3) :
    ∃ E : Finset (Finset V), E.card ≤ 2 ∧
      (∀ e ∈ E, e.card = 2) ∧
      (∀ e ∈ E, ∃ t ∈ S, e ⊆ t) ∧
      (∀ t ∈ S, ∃ e ∈ E, e ⊆ t) := by
        -- Since S is a collection of 3-element subsets of a 4-element set K, there are at most 4 such subsets.
        have h_card_S : S.card ≤ 4 := by
          exact le_trans ( Finset.card_le_card ( show S ⊆ Finset.powersetCard 3 K from fun t ht => Finset.mem_powersetCard.mpr ⟨ hS t ht, h_tri t ht ⟩ ) ) ( by simp +decide [ hK ] );
        interval_cases _ : S.card <;> simp_all +decide;
        · exact ⟨ ∅, by simp +decide ⟩;
        · obtain ⟨ t, ht ⟩ := Finset.card_eq_one.mp ‹_›;
          rcases Finset.card_eq_three.mp ( h_tri t ( ht.symm ▸ Finset.mem_singleton_self _ ) ) with ⟨ a, b, c, hab, hbc, hac ⟩ ; use { { a, b } } ; aesop;
        · obtain ⟨ t1, t2, h ⟩ := Finset.card_eq_two.mp ‹_›;
          -- Since $t1$ and $t2$ are distinct and both have cardinality 3, their intersection must have cardinality at least 2.
          have h_inter : (t1 ∩ t2).card ≥ 2 := by
            have := Finset.card_union_add_card_inter t1 t2; simp_all +decide ;
            linarith [ show Finset.card ( t1 ∪ t2 ) ≤ 4 by exact le_trans ( Finset.card_le_card ( Finset.union_subset hS.1 hS.2 ) ) hK.le ];
          -- Let $e$ be the intersection of $t1$ and $t2$.
          obtain ⟨e, he⟩ : ∃ e : Finset V, e ⊆ t1 ∧ e ⊆ t2 ∧ e.card = 2 := by
            exact Exists.elim ( Finset.exists_subset_card_eq h_inter ) fun e he => ⟨ e, Finset.Subset.trans he.1 ( Finset.inter_subset_left ), Finset.Subset.trans he.1 ( Finset.inter_subset_right ), he.2 ⟩;
          use {e}; aesop;
        · -- Let's denote the three triangles in S as t1, t2, and t3.
          obtain ⟨t1, t2, t3, ht1, ht2, ht3, h_distinct⟩ : ∃ t1 t2 t3 : Finset V, t1 ∈ S ∧ t2 ∈ S ∧ t3 ∈ S ∧ t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 := by
            rcases Finset.card_eq_three.mp ‹_› with ⟨ t1, t2, t3, ht1, ht2, ht3 ⟩ ; use t1, t2, t3 ; aesop;
          -- Let $e_1$ be the edge shared by $t_1$ and $t_2$, and $e_2$ be the edge shared by $t_1$ and $t_3$.
          obtain ⟨e1, he1⟩ : ∃ e1 : Finset V, e1.card = 2 ∧ e1 ⊆ t1 ∧ e1 ⊆ t2 := by
            have h_inter : (t1 ∩ t2).card ≥ 2 := by
              have := Finset.card_union_add_card_inter t1 t2; simp_all +decide ;
              linarith [ show Finset.card ( t1 ∪ t2 ) ≤ 4 by exact le_trans ( Finset.card_mono ( Finset.union_subset ( hS t1 ht1 ) ( hS t2 ht2 ) ) ) hK.le ];
            exact Exists.elim ( Finset.exists_subset_card_eq h_inter ) fun s hs => ⟨ s, hs.2, hs.1.trans ( Finset.inter_subset_left ), hs.1.trans ( Finset.inter_subset_right ) ⟩
          obtain ⟨e2, he2⟩ : ∃ e2 : Finset V, e2.card = 2 ∧ e2 ⊆ t1 ∧ e2 ⊆ t3 := by
            have h_inter : (t1 ∩ t3).card ≥ 2 := by
              have h_inter : (t1 ∩ t3).card = t1.card + t3.card - (t1 ∪ t3).card := by
                rw [ ← Finset.card_union_add_card_inter, add_tsub_cancel_left ];
              exact h_inter.symm ▸ le_tsub_of_add_le_left ( by linarith [ h_tri t1 ht1, h_tri t3 ht3, show ( t1 ∪ t3 ).card ≤ 4 by exact le_trans ( Finset.card_le_card ( Finset.union_subset ( hS t1 ht1 ) ( hS t3 ht3 ) ) ) hK.le ] );
            obtain ⟨ e2, he2 ⟩ := Finset.exists_subset_card_eq h_inter;
            exact ⟨ e2, he2.2, Finset.Subset.trans he2.1 ( Finset.inter_subset_left ), Finset.Subset.trans he2.1 ( Finset.inter_subset_right ) ⟩;
          refine' ⟨ { e1, e2 }, _, _, _, _ ⟩ <;> simp_all +decide;
          · exact Finset.card_insert_le _ _;
          · exact ⟨ ⟨ t1, ht1, he1.2.1 ⟩, ⟨ t1, ht1, he2.2.1 ⟩ ⟩;
          · rw [ Finset.card_eq_three ] at * ; aesop;
        · -- Since S has 4 elements and each element is a 3-element subset of K, S must be the set of all 3-element subsets of K.
          have hS_all : S = Finset.powersetCard 3 K := by
            exact Finset.eq_of_subset_of_card_le ( fun t ht => Finset.mem_powersetCard.mpr ⟨ hS t ht, h_tri t ht ⟩ ) ( by simp +decide [ *, Finset.card_powersetCard ] );
          -- Let's choose the edges {1,2} and {3,4}.
          obtain ⟨v1, v2, v3, v4, hv⟩ : ∃ v1 v2 v3 v4 : V, v1 ≠ v2 ∧ v1 ≠ v3 ∧ v1 ≠ v4 ∧ v2 ≠ v3 ∧ v2 ≠ v4 ∧ v3 ≠ v4 ∧ K = {v1, v2, v3, v4} := by
            simp_rw +decide [ Finset.card_eq_succ ] at hK;
            rcases hK with ⟨ a, t, hat, rfl, b, u, hbu, rfl, c, v, hcv, rfl, d, w, hdw, rfl, hw ⟩ ; use a, b, c, d; aesop;
          refine' ⟨ { { v1, v2 }, { v3, v4 } }, _, _, _, _ ⟩ <;> simp_all +decide;
          · exact Finset.card_insert_le _ _;
          · exact ⟨ ⟨ { v1, v2, v3 }, by aesop_cat ⟩, ⟨ { v1, v3, v4 }, by aesop_cat ⟩ ⟩;
          · intro t ht ht'; rw [ Finset.subset_iff ] at ht; simp_all +decide [ Finset.subset_iff ] ;
            rw [ Finset.card_eq_three ] at ht' ; aesop

/-
If a set of triangles S can be covered by k sets of size 2 (where each set is a subset of some triangle in S), then the covering number of S is at most k.
-/
lemma covering_bound_of_finset_cover {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (k : ℕ)
    (E_fin : Finset (Finset V))
    (h_card : E_fin.card ≤ k)
    (h_edges : ∀ e ∈ E_fin, e.card = 2)
    (h_cover : ∀ t ∈ S, ∃ e ∈ E_fin, e ⊆ t)
    (h_in_G : ∀ e ∈ E_fin, ∃ t ∈ S, e ⊆ t)
    (h_tri : S ⊆ G.cliqueFinset 3) :
    coveringNumberOn G S ≤ k := by
      have h_cover_def : ∃ E : Finset (Finset V), E.card ≤ k ∧ (∀ e ∈ E, e.card = 2) ∧ (∀ e ∈ E, ∃ t ∈ S, e ⊆ t) ∧ (∀ t ∈ S, ∃ e ∈ E, e ⊆ t) := by
        exact ⟨ E_fin, h_card, h_edges, h_in_G, h_cover ⟩;
      obtain ⟨ E, hE₁, hE₂, hE₃, hE₄ ⟩ := h_cover_def;
      -- Construct E_sym as the image of E_fin under the map that takes a set {u, v} to the edge s(u, v) in Sym2 V.
      obtain ⟨ E_sym, hE_sym ⟩ : ∃ E_sym : Finset (Sym2 V), E_sym.card ≤ k ∧ (∀ s ∈ E_sym, s ∈ G.edgeFinset) ∧ (∀ t ∈ S, ∃ s ∈ E_sym, s ∈ t.sym2) := by
        have hE_sym : ∀ e ∈ E, ∃ s ∈ G.edgeFinset, s ∈ e.sym2 := by
          intro e he
          obtain ⟨ t, htS, htE ⟩ := hE₃ e he
          have h_edge : ∃ u v : V, u ≠ v ∧ e = {u, v} := by
            have := Finset.card_eq_two.mp ( hE₂ e he );
            exact this;
          have := h_tri htS; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          rcases h_edge with ⟨ u, v, huv, rfl ⟩ ; have := this.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          exact ⟨ Sym2.mk ( u, v ), by have := this ( htE ( Finset.mem_insert_self _ _ ) ) ( htE ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ) ; aesop ⟩;
        choose! f hf₁ hf₂ using hE_sym;
        refine' ⟨ Finset.image ( fun e => f e.1 e.2 ) ( Finset.attach E ), _, _, _ ⟩ <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
        · exact le_trans ( Finset.card_image_le ) ( by simpa using hE₁ );
        · aesop;
        · exact fun t ht => by obtain ⟨ e, he, he' ⟩ := hE₄ t ht; exact ⟨ _, ⟨ e, he, rfl ⟩, fun x hx => he' ( hf₂ e he x hx ) ⟩ ;
      have h_cover_def : ∀ T ⊆ G.edgeFinset, (∀ t ∈ S, ∃ e ∈ T, e ∈ t.sym2) → coveringNumberOn G S ≤ T.card := by
        unfold coveringNumberOn;
        intro T hT₁ hT₂;
        simp +zetaDelta at *;
        have h_cover_def : (Finset.image Finset.card ({E ∈ G.edgeFinset.powerset | ∀ t ∈ S, ∃ e ∈ E, ∀ a ∈ e, a ∈ t})).min ≤ T.card := by
          exact Finset.min_le ( Finset.mem_image.mpr ⟨ T, by aesop ⟩ );
        cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E => ∀ t ∈ S, ∃ e ∈ E, ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop;
      exact le_trans ( h_cover_def E_sym hE_sym.2.1 hE_sym.2.2 ) hE_sym.1

end AristotleLemmas

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (S_e G M e) ≤ 2 := by
  -- We verify the conditions for `structure_of_pairwise_edge_sharing_triangles`:
  have h_conditions : (∀ t ∈ S_e G M e, t.card = 3) ∧ (∀ t1 ∈ S_e G M e, ∀ t2 ∈ S_e G M e, shareEdge t1 t2) := by
    refine' ⟨ _, _ ⟩;
    · exact fun t ht => G.mem_cliqueFinset_iff.mp ( Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.1 ) |>.2;
    · intro t1 ht1 t2 ht2;
      by_cases h : t1 = t2 <;> simp_all +decide [ shareEdge ];
      · have := Finset.mem_filter.mp ht2;
        have := Finset.mem_filter.mp this.1;
        exact le_trans this.2 ( Finset.card_mono ( Finset.inter_subset_left ) );
      · exact S_e_pairwise_share_edges G M hM e he t1 t2 ht1 ht2 h |> fun h => by simpa [ shareEdge ] using h;
  by_cases h_case1 : ∃ e' : Finset V, e'.card = 2 ∧ ∀ t ∈ S_e G M e, e' ⊆ t;
  · obtain ⟨ e', he', he'' ⟩ := h_case1;
    by_cases h_empty : S_e G M e = ∅;
    · simp [h_empty];
      unfold coveringNumberOn;
      simp +decide [ Finset.min ];
      rw [ Finset.inf_eq_iInf ];
      rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
      rotate_left;
      exact 0;
      · exact fun _ => zero_le _;
      · exact fun w hw => ⟨ ∅, by simp +decide [ hw ] ⟩;
      · decide +revert;
    · refine' le_trans ( covering_bound_of_finset_cover G _ 1 { e' } _ _ _ _ _ ) _;
      all_goals norm_num;
      · exact he';
      · exact he'';
      · exact Exists.elim ( Finset.nonempty_of_ne_empty h_empty ) fun t ht => ⟨ t, ht, he'' t ht ⟩;
      · exact fun t ht => Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.1;
  · -- Therefore, there exists a set K with |K| ≤ 4 such that t ⊆ K for all t ∈ S_e G M e.
    obtain ⟨K, hK⟩ : ∃ K : Finset V, K.card ≤ 4 ∧ ∀ t ∈ S_e G M e, t ⊆ K := by
      exact Or.resolve_left ( structure_of_pairwise_edge_sharing_triangles _ h_conditions.1 h_conditions.2 ) h_case1;
    by_cases hK_card : K.card < 4;
    · have h_case2_sub : S_e G M e ⊆ {K} := by
        intro t ht;
        have := hK.2 t ht;
        have := Finset.eq_of_subset_of_card_le this ( by linarith [ h_conditions.1 t ht ] ) ; aesop;
      by_cases h : S_e G M e = ∅ <;> simp_all +decide;
      · unfold coveringNumberOn;
        simp +decide [ Finset.min ];
        rw [ Finset.inf_eq_iInf ];
        rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
        rotate_left;
        exact 0;
        · exact fun _ => zero_le _;
        · exact fun w hw => ⟨ ∅, by simp +decide ; exact hw ⟩;
        · decide +revert;
      · contrapose! h_case1;
        exact Exists.imp ( by aesop ) ( Finset.exists_subset_card_eq ( show 2 ≤ K.card from by linarith ) );
    · -- Since $K$ has exactly 4 elements, we can apply `covering_le_2_of_subset_K4` to $S_e G M e$ and $K$.
      have h_cover : ∃ E : Finset (Finset V), E.card ≤ 2 ∧ (∀ e' ∈ E, e'.card = 2) ∧ (∀ e' ∈ E, ∃ t ∈ S_e G M e, e' ⊆ t) ∧ (∀ t ∈ S_e G M e, ∃ e' ∈ E, e' ⊆ t) := by
        apply covering_le_2_of_subset_K4;
        exacts [ le_antisymm hK.1 ( not_lt.mp hK_card ), hK.2, h_conditions.1 ];
      obtain ⟨ E, hE₁, hE₂, hE₃, hE₄ ⟩ := h_cover;
      apply covering_bound_of_finset_cover G (S_e G M e) 2 E hE₁ hE₂ hE₄ hE₃;
      exact fun t ht => Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.1

-- When ν = 1, T_e = S_e
lemma Te_eq_Se_when_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 1)
    (e : Finset V) (he : e ∈ M) :
    T_e G e = S_e G M e := by
  ext t; simp [T_e, S_e];
  rw [ Finset.card_eq_one ] at hnu ; aesop

/- Aristotle failed to find a proof. -/
-- Key lemma: τ(T_e) ≤ 2 for e ∈ M when ν ≤ 3
lemma tau_Te_le_2_of_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

-- Main theorem
noncomputable section AristotleLemmas

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma exists_shareEdge_of_isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (t : Finset V) (ht : isTriangle G t) :
    ∃ e ∈ M, shareEdge t e := by
      by_contra! h_contra;
      -- Since $t$ does not share an edge with any $e \in M$, $M \cup \{t\}$ is a triangle packing.
      have h_union : IsTrianglePacking G (M ∪ {t}) := by
        refine' ⟨ _, _ ⟩;
        · simp_all +decide [ Finset.subset_iff, isTriangle ];
          have := hM.1;
          exact fun x hx => by have := this.1 hx; aesop;
        · intro x hx y hy hxy; simp_all +decide [ IsEdgeDisjoint ] ;
          rcases hx with ( rfl | hx ) <;> rcases hy with ( rfl | hy ) <;> simp_all +decide [ shareEdge ];
          · exact Nat.le_of_lt_succ ( h_contra y hy );
          · simpa only [ Finset.inter_comm ] using Nat.le_of_lt_succ ( h_contra x hx );
          · have := hM.1;
            exact this.2 hx hy hxy |> fun h => by linarith;
      have h_card : (M ∪ {t}).card = M.card + 1 := by
        simp_all +decide [ Finset.filter_union_right, Finset.filter_singleton, shareEdge ];
        rw [ Finset.card_insert_of_notMem ];
        intro h;
        specialize h_contra t h;
        simp_all +decide [ isTriangle ];
        exact h_contra.not_le ( by rw [ ht.card_eq ] ; decide );
      have h_card_le : (M ∪ {t}).card ≤ packingNumber G := by
        unfold packingNumber;
        have h_card_le : (M ∪ {t}).card ∈ Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset) := by
          refine' Finset.mem_image.mpr ⟨ M ∪ { t }, _, rfl ⟩;
          simp_all +decide [ IsTrianglePacking ];
        have h_card_le : ∀ x ∈ Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset)).max 0 := by
          intro x hx;
          have := Finset.le_max hx;
          cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( IsTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
        exact h_card_le _ ‹_›;
      linarith [ hM.2 ]

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma exists_min_cover_on (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V))
    (hS : ∀ t ∈ S, isTriangle G t) :
    ∃ E ∈ G.edgeFinset.powerset, (∀ t ∈ S, ∃ e ∈ E, e ∈ t.sym2) ∧ E.card = coveringNumberOn G S := by
      have h_nonempty : Finset.Nonempty (Finset.filter (fun E => ∀ t ∈ S, ∃ e ∈ E, e ∈ t.sym2) (Finset.powerset G.edgeFinset)) := by
        refine' ⟨ G.edgeFinset, _ ⟩;
        simp_all +decide [ isTriangle ];
        intro t ht;
        rcases hS t ht with ⟨ h₁, h₂ ⟩;
        rcases Finset.card_eq_three.mp h₂ with ⟨ a, b, c, hab, hbc, hac ⟩ ; use s(a, b) ; aesop;
      have h_min_card : ∃ E ∈ Finset.filter (fun E => ∀ t ∈ S, ∃ e ∈ E, e ∈ t.sym2) (Finset.powerset G.edgeFinset), ∀ E' ∈ Finset.filter (fun E => ∀ t ∈ S, ∃ e ∈ E, e ∈ t.sym2) (Finset.powerset G.edgeFinset), E.card ≤ E'.card := by
        exact Finset.exists_min_image _ _ h_nonempty;
      obtain ⟨ E, hE₁, hE₂ ⟩ := h_min_card;
      refine' ⟨ E, _, _, _ ⟩;
      · grind;
      · aesop;
      · unfold coveringNumberOn;
        rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E => ∀ t ∈ S, ∃ e ∈ E, e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) ).min = some ( E.card ) from ?_ ];
        · rfl;
        · refine' le_antisymm _ _;
          · exact Finset.min_le ( Finset.mem_image_of_mem _ hE₁ );
          · simp +zetaDelta at *;
            exact fun a x hx₁ hx₂ hx₃ => hx₃ ▸ WithTop.coe_le_coe.mpr ( hE₂ x hx₁ hx₂ )

end AristotleLemmas

theorem tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G ≤ 3) : coveringNumber G ≤ 2 * packingNumber G := by
  have h_max_packing : ∃ M : Finset (Finset V), IsMaxPacking G M := by
    unfold IsMaxPacking packingNumber;
    have h_nonempty : Finset.Nonempty (Finset.filter (IsTrianglePacking G) (G.cliqueFinset 3).powerset) := by
      refine' ⟨ ∅, _ ⟩ ; simp +decide [ IsTrianglePacking ];
      exact fun x hx y hy hxy => by contradiction;
    have := Finset.max_of_nonempty ( show Finset.Nonempty ( Finset.image Finset.card ( Finset.filter ( IsTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) from h_nonempty.image _ );
    obtain ⟨ a, ha ⟩ := this; have := Finset.mem_of_max ha; aesop;
  obtain ⟨M, hM⟩ := h_max_packing
  have h_cover : ∃ E : Finset (Sym2 V), E ⊆ G.edgeFinset ∧ (∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2) ∧ E.card ≤ 2 * M.card := by
    -- For each $e \in M$, let $T_e$ be the set of triangles sharing an edge with $e$.
    have h_te : ∀ e ∈ M, ∃ C_e : Finset (Sym2 V), C_e ⊆ G.edgeFinset ∧ (∀ t ∈ T_e G e, ∃ e' ∈ C_e, e' ∈ t.sym2) ∧ C_e.card ≤ 2 := by
      intro e he
      have h_te_card : coveringNumberOn G (T_e G e) ≤ 2 := by
        apply tau_Te_le_2_of_nu_le_3 G M hM;
        · exact hM.2.symm ▸ h;
        · assumption;
      have := exists_min_cover_on G ( T_e G e );
      unfold isTriangle T_e at *; aesop;
    choose! C hC₁ hC₂ hC₃ using h_te;
    refine' ⟨ Finset.biUnion M C, _, _, _ ⟩;
    · exact Finset.biUnion_subset.mpr hC₁;
    · intro t ht
      obtain ⟨e, heM, he⟩ : ∃ e ∈ M, shareEdge t e := by
        apply exists_shareEdge_of_isMaxPacking G M hM t (by
        exact ht);
      exact Exists.elim ( hC₂ e heM t ( Finset.mem_filter.mpr ⟨ ht, he ⟩ ) ) fun x hx => ⟨ x, Finset.mem_biUnion.mpr ⟨ e, heM, hx.1 ⟩, hx.2 ⟩;
    · exact le_trans ( Finset.card_biUnion_le ) ( by simpa [ mul_comm ] using Finset.sum_le_sum hC₃ );
  obtain ⟨ E, hE₁, hE₂, hE₃ ⟩ := h_cover;
  have h_coveringNumber : coveringNumber G ≤ E.card := by
    unfold coveringNumber;
    have h_coveringNumber : Finset.min (Finset.image Finset.card ({E ∈ G.edgeFinset.powerset | ∀ (t : Finset V), G.IsNClique 3 t → ∃ e ∈ E, ∀ a ∈ e, a ∈ t})) ≤ Finset.card E := by
      exact Finset.min_le ( Finset.mem_image.mpr ⟨ E, by aesop ⟩ );
    cases h : Finset.min ( Finset.image Finset.card ( { E ∈ G.edgeFinset.powerset | ∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ E, ∀ a ∈ e, a ∈ t } ) ) <;> aesop;
  exact h_coveringNumber.trans ( hE₃.trans ( by rw [ hM.2 ] ) )

end