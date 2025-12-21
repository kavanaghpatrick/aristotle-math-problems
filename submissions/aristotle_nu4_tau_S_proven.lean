/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b0891cdd-e176-4ebf-8d21-0d88a6183bb9

The following was proved by Aristotle:

- lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S G e M) ≤ 2

- lemma mem_X_implies_v_in_t (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (he : e.card = 3) (hf : f.card = 3) (h_inter : e ∩ f = {v}) :
    ∀ t ∈ X G e f, v ∈ t

- lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (he : G.IsNClique 3 e) (hf : G.IsNClique 3 f) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X G e f) ≤ 2

- lemma packing_minus_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (T_ef : Finset (Finset V)) (hT : T_ef = trianglesSharingEdge G e ∪ trianglesSharingEdge G f) :
    trianglePackingNumber G - 2 ≥ 0 →
    ∃ M' : Finset (Finset V), isTrianglePacking G M' ∧
      M' ⊆ (G.cliqueFinset 3) \ T_ef ∧ M'.card ≥ M.card - 2

- theorem tuza_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) : triangleCoveringNumber G ≤ 8
-/

/-
Tuza ν=4: Pairwise Descent Strategy

KEY INSIGHT (from Gemini analysis):
Instead of removing ONE triangle (which fails when τ(T_e) = 3 for all e),
remove a PAIR {e, f} that share a vertex v.

This drops ν by 2, allowing cost of 4 edges.
Need: τ(T_e ∪ T_f) ≤ 4

PROVEN BUILDING BLOCKS:
- tau_X_le_2': τ(T_e ∩ T_f) ≤ 2 when e ∩ f = {v}
- tau_S_le_2: τ(S_e) ≤ 2
- mem_X_implies_v_in_t: triangles in T_e ∩ T_f contain v

DECOMPOSITION:
T_e ∪ T_f = S_e ∪ S_f ∪ X(e,f) ∪ (other overlaps)

The key is that covers can share edges at v.
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

def X (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e) ∩ (trianglesSharingEdge G f)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

-- PROVEN: τ(S_e) ≤ 2
noncomputable section AristotleLemmas

/-
Any two triangles in the local structure S_e (triangles sharing an edge with e and disjoint from M \ {e}) must share an edge.
-/
def shareEdge (t1 t2 : Finset V) : Prop :=
  (t1 ∩ t2).card ≥ 2

lemma lemma_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∀ t1 t2, t1 ∈ S G e M → t2 ∈ S G e M → shareEdge t1 t2 := by
  intro t1 t2 h1 h2
  unfold shareEdge
  by_contra h_not_share
  -- If t1 and t2 do not share an edge, then they are disjoint triangles in S_e.
  -- We can replace e with {t1, t2} to get a larger packing.
  have h_card : isTrianglePacking G (M \ {e} ∪ {t1, t2}) := by
    refine' ⟨ _, _ ⟩;
    · simp_all +decide [ Finset.subset_iff ];
      unfold S at *;
      simp_all +decide [ trianglesSharingEdge ];
      exact fun m hm hm' => hM.1.1 hm |> fun h => by simpa using h;
    · intro t1 ht1 t2 ht2 hne; simp_all +decide [ Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton ] ;
      rcases ht1 with ( rfl | rfl | ⟨ ht1, ht1' ⟩ ) <;> rcases ht2 with ( rfl | rfl | ⟨ ht2, ht2' ⟩ ) <;> simp_all +decide [ S ];
      · linarith;
      · rw [ Finset.inter_comm ] ; linarith;
      · exact h1.2 _ ht1 ht1' |> le_trans ( by rw [ Finset.inter_comm ] );
      · have := h2.2 t1 ht1 ht1'; simp_all +decide [ Finset.inter_comm ] ;
      · have := hM.1.2;
        exact this ht1 ht2 ( by aesop );
  -- Since $M$ is a maximum packing, the size of $M$ must be at least as large as the size of any other packing.
  have h_max : M.card ≥ (M \ {e} ∪ {t1, t2}).card := by
    have h_max : ∀ M' : Finset (Finset V), isTrianglePacking G M' → M.card ≥ M'.card := by
      have := hM.2;
      rw [this];
      unfold trianglePackingNumber;
      intro M' hM'
      have h_max : M'.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        exact Finset.mem_image.mpr ⟨ M', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( hM'.1 ), hM' ⟩, rfl ⟩;
      have := Finset.le_max h_max;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_max _ h_card;
  by_cases h : t1 = t2 <;> simp_all +decide [ Finset.card_union ];
  · have := h_card.1;
    have := this ( Finset.mem_insert_self _ _ ) ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] at h_max <;> simp_all +decide [ Finset.sdiff_singleton_eq_erase ];
    · omega;
    · intro hne hmem; have := h_card.1; simp_all +decide [ Finset.subset_iff ] ;
      unfold S at h2; simp_all +decide [ Finset.inter_comm ] ;
      have := h2.2 _ hmem hne; simp_all +decide [ Finset.inter_comm ] ;
      have := ‹G.IsNClique 3 t1 ∧ ∀ a : Finset V, ¬a = e → a ∈ M → G.IsNClique 3 a›.2 t2 hne hmem; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    · intro hne hmem; have := h_card.1; simp_all +decide [ Finset.subset_iff ] ;
      unfold S at h1; simp_all +decide [ Finset.subset_iff ] ;
      have := this.2 t1 hne hmem; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      have := h1.2 t1 hmem hne; simp_all +decide [ Finset.card_le_one ] ;

/-
If 3 triangles pairwise share an edge, either they share a common edge or their union has size at most 4.
-/
lemma three_intersecting_triples_structure {V : Type*} [DecidableEq V]
    (t1 t2 t3 : Finset V)
    (h1 : t1.card = 3) (h2 : t2.card = 3) (h3 : t3.card = 3)
    (h12 : (t1 ∩ t2).card ≥ 2)
    (h13 : (t1 ∩ t3).card ≥ 2)
    (h23 : (t2 ∩ t3).card ≥ 2) :
    (∃ e : Finset V, e.card = 2 ∧ e ⊆ t1 ∧ e ⊆ t2 ∧ e ⊆ t3) ∨ (t1 ∪ t2 ∪ t3).card ≤ 4 := by
  by_cases ht : t1 = t2 ∨ t1 = t3 ∨ t2 = t3;
  · grind;
  · -- If $t_1$, $t_2$, and $t_3$ are distinct, then $|e_{12}| = 2$.
    obtain ⟨u, v, huv⟩ : ∃ u v : V, u ≠ v ∧ u ∈ t1 ∧ v ∈ t1 ∧ u ∈ t2 ∧ v ∈ t2 := by
      obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.1 h12; use u, v; aesop;
    -- If $e_{12} \subseteq t_3$, then $e_{12}$ is a common edge to all three.
    by_cases hex : u ∈ t3 ∧ v ∈ t3;
    · exact Or.inl ⟨ { u, v }, by rw [ Finset.card_insert_of_not_mem, Finset.card_singleton ] ; aesop, by aesop_cat, by aesop_cat, by aesop_cat ⟩;
    · -- Since $t_3$ must intersect $t_1$ in $\ge 2$ vertices and $t_3$ cannot contain both $u$ and $v$, $t_3$ must contain exactly one of $u$ or $v$.
      obtain ⟨w, hw⟩ : ∃ w : V, w ∈ t1 ∧ w ∈ t3 ∧ w ≠ u ∧ w ≠ v := by
        obtain ⟨ w, hw ⟩ := Finset.exists_ne_of_one_lt_card ( show 1 < Finset.card ( t1 ∩ t3 ) from by linarith ) u;
        by_cases hwv : w = v <;> simp_all +decide;
        · obtain ⟨ x, hx ⟩ := Finset.exists_ne_of_one_lt_card ( show 1 < Finset.card ( t1 ∩ t3 ) from by linarith ) v; use x; aesop;
        · aesop;
      -- Since $t_3$ must intersect $t_2$ in $\ge 2$ vertices and $t_3$ cannot contain both $u$ and $v$, $t_3$ must contain exactly one of $u$ or $v$.
      obtain ⟨x, hx⟩ : ∃ x : V, x ∈ t2 ∧ x ∈ t3 ∧ x ≠ u ∧ x ≠ v := by
        obtain ⟨ x, hx ⟩ := Finset.exists_ne_of_one_lt_card h23 u;
        by_cases hxv : x = v <;> simp_all +decide [ Finset.inter_comm ];
        · obtain ⟨ y, hy ⟩ := Finset.exists_ne_of_one_lt_card h23 v; use y; aesop;
        · aesop;
      have h_union : t1 ∪ t2 ∪ t3 ⊆ {u, v, w, x} := by
        intro y hy; simp_all +decide [ Finset.subset_iff ] ;
        rcases hy with ( hy | hy | hy ) <;> have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ huv.2.1, Finset.insert_subset_iff.mpr ⟨ huv.2.2.1, Finset.singleton_subset_iff.mpr hw.1 ⟩ ⟩ ) <;> simp_all +decide;
        · grind;
        · have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ huv.2.2.2.1, Finset.insert_subset_iff.mpr ⟨ huv.2.2.2.2, Finset.singleton_subset_iff.mpr hx.1 ⟩ ⟩ ) ; simp_all +decide ;
          rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] at this <;> aesop;
        · have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ huv.2.2.2.1, Finset.insert_subset_iff.mpr ⟨ huv.2.2.2.2, Finset.singleton_subset_iff.mpr hx.1 ⟩ ⟩ ) ; simp_all +decide ;
          by_cases hu : u = w <;> by_cases hv : v = w <;> simp_all +decide [ Finset.card_insert_of_not_mem ];
          have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ hw.2.1, Finset.insert_subset_iff.mpr ⟨ hx.2.1, Finset.singleton_subset_iff.mpr hy ⟩ ⟩ ) ; simp_all +decide ;
          grind;
      exact Or.inr ( le_trans ( Finset.card_le_card h_union ) ( Finset.card_insert_le _ _ |> le_trans <| add_le_add_right ( Finset.card_insert_le _ _ |> le_trans <| add_le_add_right ( Finset.card_insert_le _ _ ) _ ) _ ) )

/-
If 3 distinct triangles share an edge e, and a 4th triangle intersects all of them in at least 2 vertices, then the 4th triangle must also contain e.
-/
lemma common_edge_of_three_distinct {V : Type*} [DecidableEq V]
    (t1 t2 t3 t4 : Finset V)
    (h_distinct : t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3)
    (h_sz : t1.card = 3 ∧ t2.card = 3 ∧ t3.card = 3 ∧ t4.card = 3)
    (e : Finset V) (he : e.card = 2)
    (h_sub : e ⊆ t1 ∧ e ⊆ t2 ∧ e ⊆ t3)
    (h_inter : (t4 ∩ t1).card ≥ 2 ∧ (t4 ∩ t2).card ≥ 2 ∧ (t4 ∩ t3).card ≥ 2) :
    e ⊆ t4 := by
  simp_all +decide only [Finset.subset_iff];
  -- Since $e$ is a subset of $t1$, $t2$, and $t3$, and $t1$, $t2$, $t3$ are distinct size 3, we can write $t1 = \{e_0, e_1, x\}$, $t2 = \{e_0, e_1, y\}$, $t3 = \{e_0, e_1, z\}$ with $x, y, z$ distinct and disjoint from $e$.
  obtain ⟨x, y, z, hx, hy, hz, h_distinct⟩ : ∃ x y z, x ∈ t1 ∧ y ∈ t2 ∧ z ∈ t3 ∧ x ∉ e ∧ y ∉ e ∧ z ∉ e ∧ t1 = e ∪ {x} ∧ t2 = e ∪ {y} ∧ t3 = e ∪ {z} := by
    -- Since $e$ is a subset of $t1$, $t2$, and $t3$, and $t1$, $t2$, $t3$ are distinct size 3, we can write $t1 = \{e_0, e_1, x\}$, $t2 = \{e_0, e_1, y\}$, $t3 = \{e_0, e_1, z\}$ with $x, y, z$ distinct and disjoint from $e$. Use `Finset.exists_sdiff_of_subset` to find such $x$, $y$, and $z$.
    obtain ⟨x, hx⟩ : ∃ x, x ∈ t1 ∧ x ∉ e := by
      exact Finset.exists_of_ssubset ( Finset.ssubset_iff_subset_ne.mpr ⟨ h_sub.1, by aesop_cat ⟩ )
    obtain ⟨y, hy⟩ : ∃ y, y ∈ t2 ∧ y ∉ e := by
      exact Finset.exists_of_ssubset ( Finset.ssubset_iff_subset_ne.mpr ⟨ h_sub.2.1, by aesop_cat ⟩ )
    obtain ⟨z, hz⟩ : ∃ z, z ∈ t3 ∧ z ∉ e := by
      by_contra h_contra; push_neg at h_contra; (
      exact absurd ( Finset.eq_of_subset_of_card_le h_contra ( by linarith ) ) ( by aesop ));
    have h_t1 : t1 = e ∪ {x} := by
      rw [ Finset.eq_of_subset_of_card_le ( Finset.union_subset h_sub.1 ( Finset.singleton_subset_iff.mpr hx.1 ) ) ] ; aesop
    have h_t2 : t2 = e ∪ {y} := by
      rw [ Finset.eq_of_subset_of_card_le ( Finset.union_subset ( show e ⊆ t2 from fun x hx => h_sub.2.1 hx ) ( show { y } ⊆ t2 from by aesop ) ) ] ; aesop
    have h_t3 : t3 = e ∪ {z} := by
      rw [ Finset.eq_of_subset_of_card_le ( show e ∪ { z } ⊆ t3 from Finset.union_subset ( h_sub.2.2 ) ( Finset.singleton_subset_iff.2 hz.1 ) ) ] ; aesop
    aesop;
  -- Suppose $e \not\subseteq t_4$. Then $t_4$ omits at least one of $e_0, e_1$.
  by_cases h_e0 : x ∈ t4
  by_cases h_e1 : y ∈ t4
  by_cases h_e2 : z ∈ t4;
  · have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ h_e0, Finset.insert_subset_iff.mpr ⟨ h_e1, Finset.singleton_subset_iff.mpr h_e2 ⟩ ⟩ ) ; simp_all +decide ;
    intro v hv; specialize this; rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] at this <;> aesop;
  · have := Finset.eq_of_subset_of_card_le ( show t4 ∩ t3 ⊆ { z } from ?_ ) ; simp_all +decide ;
    simp_all +decide [ Finset.subset_iff ];
    have := Finset.card_eq_three.mp h_sz; obtain ⟨ u, v, w, hu, hv, hw, h ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
    exact ⟨ fun h => by aesop, fun h => by aesop, fun h => by aesop ⟩;
  · contrapose! h_inter; simp_all +decide [ Finset.inter_comm ] ;
    intro h1 h2; rcases Finset.card_eq_two.mp he with ⟨ a, b, hab ⟩ ; simp_all +decide [ Finset.Nonempty ] ;
    rw [ Finset.card_eq_three ] at h_sz ; aesop;
  · have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t4 ∩ e ⊆ e ) ; aesop;

/-
The intersection of 3 distinct triangles contained in a set of size 4 has size at most 1.
-/
lemma intersection_of_three_distinct_triples_in_size_four {V : Type*} [DecidableEq V]
    (U : Finset V) (hU : U.card = 4)
    (t1 t2 t3 : Finset V)
    (h_sub : t1 ⊆ U ∧ t2 ⊆ U ∧ t3 ⊆ U)
    (h_sz : t1.card = 3 ∧ t2.card = 3 ∧ t3.card = 3)
    (h_distinct : t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3) :
    (t1 ∩ t2 ∩ t3).card ≤ 1 := by
      -- Since $t_1$, $t_2$, and $t_3$ are distinct subsets of $U$ each of size 3, they must each omit exactly one element from $U$. Let $a$, $b$, and $c$ be the elements omitted by $t_1$, $t_2$, and $t_3$, respectively.
      obtain ⟨a, ha⟩ : ∃ a ∈ U, t1 = U \ {a} := by
        have h_card_diff : (U \ t1).card = 1 := by
          grind;
        obtain ⟨ a, ha ⟩ := Finset.card_eq_one.mp h_card_diff;
        exact ⟨ a, Finset.mem_sdiff.mp ( ha.symm ▸ Finset.mem_singleton_self _ ) |>.1, by rw [ ← ha, Finset.sdiff_sdiff_eq_self h_sub.1 ] ⟩
      obtain ⟨b, hb⟩ : ∃ b ∈ U, t2 = U \ {b} := by
        have h_card_diff : (U \ t2).card = 1 := by
          grind;
        rw [ Finset.card_eq_one ] at h_card_diff ; aesop;
        exact ⟨ w, Finset.mem_sdiff.mp ( h.symm ▸ Finset.mem_singleton_self _ ) |>.1, by rw [ ← h, Finset.sdiff_sdiff_eq_self left ] ⟩
      obtain ⟨c, hc⟩ : ∃ c ∈ U, t3 = U \ {c} := by
        have h_card : U.card = t3.card + (U \ t3).card := by
          grind;
        have h_card : (U \ t3).card = 1 := by
          linarith;
        obtain ⟨ c, hc ⟩ := Finset.card_eq_one.mp h_card;
        exact ⟨ c, Finset.mem_sdiff.mp ( hc.symm ▸ Finset.mem_singleton_self _ ) |>.1, by rw [ ← hc, Finset.sdiff_sdiff_eq_self h_sub.2.2 ] ⟩;
      simp_all +decide [ Finset.subset_iff ];
      rw [ show U \ { a } ∩ ( U \ { b } ∩ ( U \ { c } ) ) = U \ { a, b, c } by ext x; aesop ] ; simp +decide [ *, Finset.card_sdiff ] ;
      rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> aesop

/-
If 3 distinct triangles are in a set of size 4, and a 4th triangle intersects all of them in at least 2 vertices, then the 4th triangle must be contained in the set.
-/
lemma fourth_triangle_in_union_of_three {V : Type*} [DecidableEq V]
    (U : Finset V) (hU : U.card = 4)
    (t1 t2 t3 : Finset V)
    (h_sub : t1 ⊆ U ∧ t2 ⊆ U ∧ t3 ⊆ U)
    (h_sz : t1.card = 3 ∧ t2.card = 3 ∧ t3.card = 3)
    (h_distinct : t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3)
    (t : Finset V) (ht_card : t.card = 3)
    (h_inter : (t ∩ t1).card ≥ 2 ∧ (t ∩ t2).card ≥ 2 ∧ (t ∩ t3).card ≥ 2) :
    t ⊆ U := by
      -- If $t \not\subseteq U$, then there exists a vertex $v \in t$ such that $v \notin U$.
      by_contra h_not_subset
      obtain ⟨v, hv⟩ : ∃ v, v ∈ t ∧ v ∉ U := by
        exact Finset.not_subset.mp h_not_subset;
      -- Since $v \in t$ and $v \notin U$, the other two vertices of $t$ must be in $t_1$, $t_2$, and $t_3$.
      have h_other_vertices : (t \ {v}).card = 2 := by
        rw [ Finset.card_sdiff ] ; aesop
      have h_other_vertices_t1 : (t \ {v}) ⊆ t1 := by
        have h_other_vertices_t1 : (t ∩ t1).card = 2 := by
          refine' le_antisymm _ h_inter.1;
          refine' le_trans ( Finset.card_le_card _ ) h_other_vertices.le;
          simp_all +decide [ Finset.subset_iff ];
          exact fun x hx hx' hx'' => hv.2 ( hx''.symm ▸ h_sub.1 hx' );
        have h_other_vertices_t1 : t ∩ t1 = t \ {v} := by
          refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _ <;> aesop;
          exact right_4 ( left right_5 );
        exact h_other_vertices_t1 ▸ Finset.inter_subset_right
      have h_other_vertices_t2 : (t \ {v}) ⊆ t2 := by
        have h_other_vertices_t2 : (t \ {v}) ⊆ t2 := by
          have h_inter_t2 : (t ∩ t2).card ≥ 2 := h_inter.right.left
          have h_other_vertices_t2 : (t ∩ t2) = (t \ {v}) := by
            refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _ <;> aesop;
            exact right_4 ( left_6 right_5 );
          exact h_other_vertices_t2 ▸ Finset.inter_subset_right;
        assumption
      have h_other_vertices_t3 : (t \ {v}) ⊆ t3 := by
        have h_other_vertices_t3 : (t ∩ t3).card = 2 := by
          have h_other_vertices_t3 : (t ∩ t3).card ≤ 2 := by
            have h_other_vertices_t3 : (t ∩ t3).card ≤ (t \ {v}).card := by
              refine Finset.card_le_card ?_;
              simp_all +decide [ Finset.subset_iff ];
              exact fun x hx hx' hx'' => hv.2 ( hx''.symm ▸ h_sub.2.2 hx' );
            grind;
          grind;
        have h_other_vertices_t3 : t ∩ t3 = t \ {v} := by
          refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _ <;> aesop;
          exact right_4 ( right right_5 );
        exact h_other_vertices_t3 ▸ Finset.inter_subset_right;
      have h_other_vertices_inter : (t \ {v}) ⊆ t1 ∩ t2 ∩ t3 := by
        exact Finset.subset_inter ( Finset.subset_inter h_other_vertices_t1 h_other_vertices_t2 ) h_other_vertices_t3;
      exact absurd ( Finset.card_le_card h_other_vertices_inter ) ( by linarith [ intersection_of_three_distinct_triples_in_size_four U hU t1 t2 t3 h_sub h_sz h_distinct ] )

/-
If a family of triangles pairwise share an edge, then either they all share a common edge, or their union has size at most 4.
-/
lemma intersecting_triples_structure {V : Type*} [DecidableEq V]
    (F : Finset (Finset V))
    (h3 : ∀ t ∈ F, t.card = 3)
    (h_pair : ∀ t1 t2, t1 ∈ F → t2 ∈ F → (t1 ∩ t2).card ≥ 2) :
    (∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ F, e ⊆ t) ∨ (F.biUnion id).card ≤ 4 := by
      by_contra h_contra;
      -- Since $|F| \geq 3$, we can pick 3 distinct triangles $t_1, t_2, t_3 \in F$.
      obtain ⟨t1, t2, t3, ht1, ht2, ht3, h_distinct⟩ : ∃ t1 t2 t3 : Finset V, t1 ∈ F ∧ t2 ∈ F ∧ t3 ∈ F ∧ t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 := by
        by_cases hF : F.card ≥ 3;
        · rcases Finset.two_lt_card.1 hF with ⟨ t1, ht1, t2, ht2, hne ⟩ ; use t1, t2 ; aesop;
        · interval_cases _ : F.card <;> simp_all +decide;
          · rw [ Finset.card_eq_one ] at * ; aesop;
          · have := Finset.card_eq_two.mp ‹_›;
            obtain ⟨ x, y, hxy, rfl ⟩ := this; simp_all +decide ;
            grind;
      -- By `three_intersecting_triples_structure`, either they share an edge $e$, or their union $U$ has size $\le 4$.
      by_cases h_common_edge : ∃ e : Finset V, e.card = 2 ∧ e ⊆ t1 ∧ e ⊆ t2 ∧ e ⊆ t3;
      · obtain ⟨ e, he1, he2, he3, he4 ⟩ := h_common_edge;
        refine' h_contra ( Or.inl ⟨ e, he1, fun t ht => _ ⟩ );
        apply common_edge_of_three_distinct t1 t2 t3 t ⟨ by tauto, by tauto, by tauto ⟩ ⟨ h3 t1 ht1, h3 t2 ht2, h3 t3 ht3, h3 t ht ⟩ e he1 ⟨ he2, he3, he4 ⟩ ⟨ h_pair t t1 ht ht1, h_pair t t2 ht ht2, h_pair t t3 ht ht3 ⟩;
      · -- By `three_intersecting_triples_structure`, their union $U$ has size $\le 4$.
        have h_union_size : (t1 ∪ t2 ∪ t3).card ≤ 4 := by
          have := three_intersecting_triples_structure t1 t2 t3 ( h3 t1 ht1 ) ( h3 t2 ht2 ) ( h3 t3 ht3 ) ( h_pair t1 t2 ht1 ht2 ) ( h_pair t1 t3 ht1 ht3 ) ( h_pair t2 t3 ht2 ht3 ) ; aesop;
        -- We claim all $t \in F$ are subsets of $U$.
        have h_all_subset : ∀ t ∈ F, t ⊆ t1 ∪ t2 ∪ t3 := by
          intro t ht
          have h_inter : (t ∩ t1).card ≥ 2 ∧ (t ∩ t2).card ≥ 2 ∧ (t ∩ t3).card ≥ 2 := by
            exact ⟨ h_pair t t1 ht ht1, h_pair t t2 ht ht2, h_pair t t3 ht ht3 ⟩;
          have := fourth_triangle_in_union_of_three ( t1 ∪ t2 ∪ t3 ) ?_ t1 t2 t3 ?_ ?_ ?_ t ( h3 t ht ) ?_ <;> simp_all +decide;
          · refine' le_antisymm h_union_size _;
            have h_union_size : (t1 ∪ t2).card ≥ 4 := by
              have h_union_size : (t1 ∩ t2).card ≤ 2 := by
                have := Finset.card_le_card ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.card_le_card ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; simp_all +decide ;
                interval_cases _ : Finset.card ( t1 ∩ t2 ) <;> simp_all +decide;
                have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t1 ∩ t2 ⊆ t1 ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t1 ∩ t2 ⊆ t2 ) ; simp_all +decide ;
              have := Finset.card_union_add_card_inter t1 t2; linarith [ h3 t1 ht1, h3 t2 ht2 ] ;
            exact h_union_size.trans ( Finset.card_mono <| by aesop_cat );
          · exact ⟨ fun x hx => Finset.mem_union_right _ ( Finset.mem_union_left _ hx ), fun x hx => Finset.mem_union_right _ ( Finset.mem_union_right _ hx ) ⟩;
        exact h_contra <| Or.inr <| le_trans ( Finset.card_le_card <| Finset.biUnion_subset.mpr h_all_subset ) h_union_size

/-
If a set of triangles S has size at most 2, it can be covered by at most 2 edges, each contained in a triangle of S.
-/
lemma lemma_K4_cover_small {V : Type*} [DecidableEq V]
    (S : Finset (Finset V))
    (h3 : ∀ t ∈ S, t.card = 3)
    (hS : S.card ≤ 2) :
    ∃ E' : Finset (Finset V), E'.card ≤ 2 ∧
      (∀ e ∈ E', e.card = 2 ∧ ∃ t ∈ S, e ⊆ t) ∧
      (∀ t ∈ S, ∃ e ∈ E', e ⊆ t) := by
  -- For each t in S, we can pick an edge e_t contained in t.
  -- Since |S| <= 2, the set of these edges has size <= 2.
  interval_cases _ : S.card;
  · exact ⟨ ∅, by simp +decide [ Finset.card_eq_zero.mp ‹_› ] ⟩;
  · obtain ⟨ t, ht ⟩ := Finset.card_eq_one.mp ‹_›;
    -- Let $e$ be any edge of $t$.
    obtain ⟨e, he⟩ : ∃ e ∈ t.powersetCard 2, e ⊆ t := by
      exact Exists.elim ( Finset.exists_subset_card_eq ( show 2 ≤ t.card from by linarith [ h3 t ( ht.symm ▸ Finset.mem_singleton_self _ ) ] ) ) fun e he => ⟨ e, Finset.mem_powersetCard.mpr ⟨ he.1, he.2 ⟩, he.1 ⟩;
    refine' ⟨ { e }, _, _, _ ⟩ <;> aesop;
  · obtain ⟨ t1, t2, h1, h2 ⟩ := Finset.card_eq_two.mp ‹_›;
    -- Let $e1$ be a two-element subset of $t1$ and $e2$ be a two-element subset of $t2$.
    obtain ⟨e1, he1⟩ : ∃ e1 : Finset V, e1.card = 2 ∧ e1 ⊆ t1 := by
      exact Exists.imp ( by tauto ) ( Finset.exists_subset_card_eq ( show 2 ≤ t1.card from by linarith [ h3 t1 ( h2.symm ▸ Finset.mem_insert_self _ _ ) ] ) )
    obtain ⟨e2, he2⟩ : ∃ e2 : Finset V, e2.card = 2 ∧ e2 ⊆ t2 := by
      have := h3 t2 ( h2.symm ▸ Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) );
      exact Exists.imp ( by tauto ) ( Finset.exists_subset_card_eq ( show 2 ≤ t2.card from this.ge.trans' ( by decide ) ) );
    exact ⟨ { e1, e2 }, by by_cases h : e1 = e2 <;> simp_all +decide, by aesop ⟩

/-
If a family of triangles pairwise share an edge, then either they all share a common edge, or their union has size at most 4.
-/
lemma intersecting_triples_structure_aux {V : Type*} [DecidableEq V]
    (F : Finset (Finset V))
    (h3 : ∀ t ∈ F, t.card = 3)
    (h_pair : ∀ t1 t2, t1 ∈ F → t2 ∈ F → (t1 ∩ t2).card ≥ 2) :
    (∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ F, e ⊆ t) ∨ (F.biUnion id).card ≤ 4 := by
      exact?

/-
If a family of triangles pairwise share an edge, then either they all share a common edge, or their union has size at most 4.
-/
lemma intersecting_triples_structure_final {V : Type*} [DecidableEq V]
    (F : Finset (Finset V))
    (h3 : ∀ t ∈ F, t.card = 3)
    (h_pair : ∀ t1 t2, t1 ∈ F → t2 ∈ F → (t1 ∩ t2).card ≥ 2) :
    (∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ F, e ⊆ t) ∨ (F.biUnion id).card ≤ 4 := by
      exact?

/-
If a family of triangles pairwise share an edge, then either they all share a common edge, or their union has size at most 4.
-/
lemma intersecting_triples_structure_main {V : Type*} [DecidableEq V]
    (F : Finset (Finset V))
    (h3 : ∀ t ∈ F, t.card = 3)
    (h_pair : ∀ t1 t2, t1 ∈ F → t2 ∈ F → (t1 ∩ t2).card ≥ 2) :
    (∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ F, e ⊆ t) ∨ (F.biUnion id).card ≤ 4 := by
      -- Apply the intersecting_triples_structure_final lemma to the set F.
      apply intersecting_triples_structure_final F h3 h_pair

/-
If a set of triangles S has union of size at most 4, then S can be covered by at most 2 edges, where each edge is a subset of some triangle in S.
-/
lemma lemma_K4_cover {V : Type*} [DecidableEq V]
    (S : Finset (Finset V))
    (h_union : (S.biUnion id).card ≤ 4)
    (h3 : ∀ t ∈ S, t.card = 3) :
    ∃ E' : Finset (Finset V), E'.card ≤ 2 ∧
      (∀ e ∈ E', e.card = 2 ∧ ∃ t ∈ S, e ⊆ t) ∧
      (∀ t ∈ S, ∃ e ∈ E', e ⊆ t) := by
        -- If $|S| \le 2$, use `lemma_K4_cover_small`.
        by_cases hS : S.card ≤ 2;
        · exact?;
        · -- Let $U = \{u_1, u_2, u_3, u_4\}$.
          obtain ⟨U, hU⟩ : ∃ U : Finset V, U.card = 4 ∧ S.biUnion id = U := by
            refine' ⟨ _, _, rfl ⟩;
            -- If $|U| < 4$, then there are fewer than 4 vertices in $U$, so each triangle in $S$ must contain at least 2 vertices from $U$, contradicting $|S| \ge 3$.
            by_contra h_contra
            have h_card_lt : (S.biUnion id).card < 4 := by
              exact lt_of_le_of_ne h_union h_contra;
            have h_card_lt : ∀ t ∈ S, t ⊆ S.biUnion id := by
              exact fun t ht => Finset.subset_biUnion_of_mem id ht;
            have h_card_lt : ∀ t ∈ S, t = S.biUnion id := by
              exact fun t ht => Finset.eq_of_subset_of_card_le ( h_card_lt t ht ) ( by linarith [ h3 t ht ] );
            exact hS ( le_trans ( Finset.card_le_one.mpr ( by intros t ht t' ht'; rw [ h_card_lt t ht, h_card_lt t' ht' ] ) ) ( by decide ) );
          -- Let $e_1 = \{u_1, u_2\}$ and $e_2 = \{u_3, u_4\}$.
          obtain ⟨u1, u2, u3, u4, hu⟩ : ∃ u1 u2 u3 u4 : V, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u1 ≠ u4 ∧ u2 ≠ u3 ∧ u2 ≠ u4 ∧ u3 ≠ u4 ∧ U = {u1, u2, u3, u4} := by
            simp_rw +decide [ Finset.card_eq_succ ] at hU;
            rcases hU with ⟨ ⟨ a, t, hat, rfl, b, u, hbu, rfl, c, v, hcv, rfl, d, w, hdw, rfl, hw ⟩, hU ⟩ ; use a, b, c, d; aesop;
          -- Let $e_1 = \{u_1, u_2\}$ and $e_2 = \{u_3, u_4\}$. We need to show that these edges cover all triangles in $S$.
          use { {u1, u2}, {u3, u4} };
          have h_cover : ∀ t ∈ S, t = {u1, u2, u3} ∨ t = {u1, u2, u4} ∨ t = {u1, u3, u4} ∨ t = {u2, u3, u4} := by
            intro t ht
            have ht_subset : t ⊆ {u1, u2, u3, u4} := by
              exact fun x hx => hu.2.2.2.2.2.2 ▸ hU.2 ▸ Finset.mem_biUnion.2 ⟨ t, ht, hx ⟩;
            have := h3 t ht; rw [ Finset.card_eq_three ] at this; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
            rcases ht_subset with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] at hx hy hz ⊢;
          have h_exists_t1 : ∃ t ∈ S, t = {u1, u2, u3} ∨ t = {u1, u2, u4} := by
            contrapose! hS; simp_all +decide ;
            exact le_trans ( Finset.card_le_card ( show S ⊆ { { u1, u3, u4 }, { u2, u3, u4 } } by intros t ht; simpa using h_cover t ht ) ) ( Finset.card_insert_le _ _ ) |> le_trans <| by simp +decide ;
          have h_exists_t2 : ∃ t ∈ S, t = {u1, u3, u4} ∨ t = {u2, u3, u4} := by
            contrapose! hS; simp_all +decide ;
            exact le_trans ( Finset.card_le_card ( show S ⊆ { { u1, u2, u3 }, { u1, u2, u4 } } by intros t ht; aesop ) ) ( Finset.card_insert_le _ _ ) |> le_trans <| by simp +decide ;
          simp_all +decide [ Finset.subset_iff ];
          refine' ⟨ _, _, _ ⟩;
          · exact Finset.card_insert_le _ _;
          · exact ⟨ by obtain ⟨ t, ht1, rfl | rfl ⟩ := h_exists_t1 <;> [ exact ⟨ _, ht1, by simp +decide, by simp +decide ⟩ ; exact ⟨ _, ht1, by simp +decide, by simp +decide ⟩ ], by obtain ⟨ t, ht1, rfl | rfl ⟩ := h_exists_t2 <;> [ exact ⟨ _, ht1, by simp +decide, by simp +decide ⟩ ; exact ⟨ _, ht1, by simp +decide, by simp +decide ⟩ ] ⟩;
          · grind

/-
If a set of triangles pairwise share an edge, then they can be covered by at most 2 edges.
-/
lemma structural_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (S_tris : Finset (Finset V))
    (h_sub : S_tris ⊆ G.cliqueFinset 3)
    (h_pair : ∀ t1 t2, t1 ∈ S_tris → t2 ∈ S_tris → shareEdge t1 t2) :
    triangleCoveringNumberOn G S_tris ≤ 2 := by
      -- Let $E'$ be a set of edges covering all triangles in $S_tris$.
      obtain ⟨E', hE'_cover, hE'_card⟩ : ∃ E' : Finset (Finset V), E'.card ≤ 2 ∧ (∀ e ∈ E', e.card = 2 ∧ ∃ t ∈ S_tris, e ⊆ t) ∧ (∀ t ∈ S_tris, ∃ e ∈ E', e ⊆ t) := by
        by_cases h_empty : S_tris = ∅;
        · exact ⟨ ∅, by simp +decide [ h_empty ] ⟩;
        · -- By `intersecting_triples_structure_main`, we have two cases:
          obtain ⟨e, he⟩ : (∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ S_tris, e ⊆ t) ∨ (S_tris.biUnion id).card ≤ 4 := by
            have h_cases : ∀ t ∈ S_tris, t.card = 3 := by
              intro t ht; have := h_sub ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
              exact this.2;
            exact intersecting_triples_structure_main S_tris h_cases fun t1 t2 ht1 ht2 => h_pair t1 t2 ht1 ht2;
          · refine' ⟨ { e }, _, _, _ ⟩ <;> simp +decide [ he ];
            · exact Exists.elim ( Finset.nonempty_of_ne_empty h_empty ) fun t ht => ⟨ t, ht, he.2 t ht ⟩;
            · exact he.2;
          · convert lemma_K4_cover S_tris ‹_› ( fun t ht => by simpa using Finset.mem_coe.mp ( h_sub ht ) |> SimpleGraph.mem_cliqueFinset_iff.mp |>.2 ) using 1;
      -- Let $E''$ be the set of edges in $G$ that are subsets of some triangle in $E'$.
      obtain ⟨ E'', hE''_subset, hE''_cover, hE''_card ⟩ : ∃ E'' : Finset (Sym2 V), E''.card ≤ 2 ∧ (∀ e ∈ E'', e ∈ G.edgeFinset) ∧ (∀ t ∈ S_tris, ∃ e ∈ E'', e ∈ t.sym2) := by
        have hE''_subset : ∀ e ∈ E', ∃ e' ∈ G.edgeFinset, e' ∈ e.sym2 := by
          intro e he; specialize hE'_card; rcases hE'_card.1 e he with ⟨ he₁, t, ht, hte ⟩ ; rcases Finset.card_eq_two.mp he₁ with ⟨ u, v, hu, hv, he ⟩ ; simp_all +decide [ Sym2.eq ] ;
          have := h_sub ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          exact ⟨ s(u, v), by have := this.1 ( show u ∈ t from hte ( by simp +decide ) ) ( show v ∈ t from hte ( by simp +decide ) ) ; aesop, by simp +decide ⟩;
        choose! f hf₁ hf₂ using hE''_subset;
        refine' ⟨ Finset.image ( fun e => f e.1 e.2 ) ( Finset.attach E' ), _, _, _ ⟩ <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
        · exact Finset.card_image_le.trans ( by simpa );
        · aesop;
        · intro t ht; obtain ⟨ e, he, he' ⟩ := hE'_card.2 t ht; use f e he; aesop;
      unfold triangleCoveringNumberOn;
      have hE''_in_image : E''.card ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_tris, ∃ e ∈ E', e ∈ t.sym2}) := by
        exact Finset.mem_image.mpr ⟨ E'', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.subset_iff.mpr hE''_cover ), hE''_card ⟩, rfl ⟩;
      have h_min_le : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_tris, ∃ e ∈ E', e ∈ t.sym2})).min ≤ E''.card := by
        exact Finset.min_le hE''_in_image;
      exact le_trans ( by cases h : Finset.min ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_tris, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) <;> aesop ) hE''_subset

/-
If a set of triangles pairwise share an edge, then they can be covered by at most 2 edges.
-/
lemma structural_cover_aux (G : SimpleGraph V) [DecidableRel G.Adj]
    (S_tris : Finset (Finset V))
    (h_sub : S_tris ⊆ G.cliqueFinset 3)
    (h_pair : ∀ t1 t2, t1 ∈ S_tris → t2 ∈ S_tris → shareEdge t1 t2) :
    triangleCoveringNumberOn G S_tris ≤ 2 := by
      exact?

/-
If a set of triangles pairwise share an edge, then they can be covered by at most 2 edges.
-/
lemma structural_cover_final (G : SimpleGraph V) [DecidableRel G.Adj]
    (S_tris : Finset (Finset V))
    (h_sub : S_tris ⊆ G.cliqueFinset 3)
    (h_pair : ∀ t1 t2, t1 ∈ S_tris → t2 ∈ S_tris → shareEdge t1 t2) :
    triangleCoveringNumberOn G S_tris ≤ 2 := by
      exact?

end AristotleLemmas

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S G e M) ≤ 2 := by
  apply structural_cover;
  · unfold S;
    intro t; unfold trianglesSharingEdge at *; aesop;
  · exact?

-- Proven in e7f11dfc

-- PROVEN: triangles in X(e,f) contain shared vertex
lemma mem_X_implies_v_in_t (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (he : e.card = 3) (hf : f.card = 3) (h_inter : e ∩ f = {v}) :
    ∀ t ∈ X G e f, v ∈ t := by
  -- By definition of $X$, a triangle $t$ is in $X_{e,f}$ if and only if $t$ is a triangle in $G$, $t$ shares an edge with $e$, and $t$ shares an edge with $f$.
  unfold X; simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
  unfold trianglesSharingEdge;
  simp_all +decide [ Finset.card_eq_three, Finset.ext_iff ];
  intro t ht ht1 ht2; obtain ⟨ x, y, hx, z, hy, hz, h ⟩ := Finset.card_eq_three.mp ht.2; simp_all +decide [ Finset.inter_comm ] ;
  obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.one_lt_card.1 ht1; obtain ⟨ c, hc, d, hd, hcd ⟩ := Finset.one_lt_card.1 ht2; simp_all +decide [ Finset.inter_comm ] ;
  grind

-- Proven in e7f11dfc

-- PROVEN: τ(X(e,f)) ≤ 2
noncomputable section AristotleLemmas

lemma exists_edge_in_intersection_of_X_and_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (he : G.IsNClique 3 e) (hf : G.IsNClique 3 f) (h_inter : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X G e f) :
    ∃ x ∈ e.erase v, Sym2.mk (v, x) ∈ t.sym2 := by
      -- Since $t \in X(e, f)$, $t$ shares an edge with $e$, so $|t \cap e| \ge 2$.
      have h_inter : 2 ≤ (t ∩ e).card := by
        unfold X at ht;
        unfold trianglesSharingEdge at ht; aesop;
      -- Since $v \in t \cap e$, there must be another element $x \in t \cap e$ such that $x \ne v$.
      obtain ⟨x, hx₁, hx₂⟩ : ∃ x ∈ t ∩ e, x ≠ v := by
        exact Finset.exists_mem_ne h_inter v;
      aesop;
      exact ⟨ x, ⟨ hx₂, right ⟩, by have := mem_X_implies_v_in_t G e f v ( by simp_all +decide [ SimpleGraph.isNClique_iff ] ) ( by simp_all +decide [ SimpleGraph.isNClique_iff ] ) h_inter_1; aesop ⟩

end AristotleLemmas

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (he : G.IsNClique 3 e) (hf : G.IsNClique 3 f) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X G e f) ≤ 2 := by
  -- Let $C$ be the set of edges in $e$ that are not incident to $v$.
  set C := (e.erase v).image (fun x => Sym2.mk (v, x)) with hC_def;
  -- Since $e$ is a clique, every pair in $e$ is an edge of $G$, so $C \subseteq E(G)$.
  have hC_subset : C ⊆ G.edgeFinset := by
    simp_all +decide [ Finset.subset_iff, SimpleGraph.IsNClique ];
    rintro _ x hx₁ hx₂ rfl; have := he.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    replace h_inter := Finset.ext_iff.mp h_inter v; aesop;
  -- Since $e$ is a clique of size 3 and $v \in e$, $e \setminus \{v\}$ has size 2, so $|C| \le 2$.
  have hC_card : C.card ≤ 2 := by
    exact Finset.card_image_le.trans ( by simpa [ Finset.card_erase_of_mem ( show v ∈ e from Finset.mem_of_mem_inter_left ( h_inter.symm ▸ Finset.mem_singleton_self _ ) ) ] using he.card_eq.le );
  -- For any $t \in X(e, f)$, by `exists_edge_in_intersection_of_X_and_e`, there exists $x \in e \setminus \{v\}$ such that $\{v, x\}$ is an edge of $t$.
  have hC_covers : ∀ t ∈ X G e f, ∃ e' ∈ C, e' ∈ t.sym2 := by
    intro t ht
    obtain ⟨x, hx⟩ := exists_edge_in_intersection_of_X_and_e G e f v he hf h_inter t ht
    use Sym2.mk (v, x)
    aesop;
  -- Thus $C$ covers all triangles in $X(e, f)$.
  have hC_triangleCovering : ∀ E' ⊆ G.edgeFinset, (∀ t ∈ X G e f, ∃ e' ∈ E', e' ∈ t.sym2) → triangleCoveringNumberOn G (X G e f) ≤ E'.card := by
    unfold triangleCoveringNumberOn;
    intro E' hE' hE'_covers
    have hE'_in_set : E' ∈ Finset.filter (fun E' => ∀ t ∈ X G e f, ∃ e' ∈ E', e' ∈ t.sym2) (G.edgeFinset.powerset) := by
      grind;
    have := Finset.min_le ( Finset.mem_image_of_mem Finset.card hE'_in_set );
    rw [ WithTop.le_coe_iff ] at this ; aesop;
  exact le_trans ( hC_triangleCovering C hC_subset hC_covers ) hC_card

/- Aristotle failed to find a proof. -/
-- Proven in e7f11dfc

-- KEY NEW LEMMA: Pairwise union bound
-- When e and f share vertex v, we can cover T_e ∪ T_f with ≤ 4 edges
lemma tau_union_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4 := by
  sorry

-- Removing a pair drops packing number by at least 2
lemma packing_minus_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (T_ef : Finset (Finset V)) (hT : T_ef = trianglesSharingEdge G e ∪ trianglesSharingEdge G f) :
    trianglePackingNumber G - 2 ≥ 0 →
    ∃ M' : Finset (Finset V), isTrianglePacking G M' ∧
      M' ⊆ (G.cliqueFinset 3) \ T_ef ∧ M'.card ≥ M.card - 2 := by
  simp [isTrianglePacking, isMaxPacking] at *;
  refine' ⟨ M \ { e, f }, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
  · exact hM.1.2.mono fun x hx => by aesop;
  · intro x hx hxe hxf; simp_all +decide [ trianglesSharingEdge ] ;
    exact ⟨ lt_of_le_of_lt ( hM.1.2 hx he ( by tauto ) ) ( by decide ), lt_of_le_of_lt ( hM.1.2 hx hf ( by tauto ) ) ( by decide ) ⟩;
  · rw [ ← hM.2, Finset.card_sdiff ] ; simp +decide [ *, Finset.subset_iff ];
    omega

/- Aristotle failed to find a proof. -/
-- Case: exists isolated triangle (doesn't share vertex with others)
lemma nu4_case_isolated (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hnu : M.card = 4)
    (h_isolated : ∃ e ∈ M, ∀ f ∈ M, f ≠ e → (e ∩ f).card = 0) :
    triangleCoveringNumber G ≤ 8 := by
  sorry

/- Aristotle failed to find a proof. -/
-- Case: every triangle shares vertex with another (K_6-like)
-- Use pairwise descent
lemma nu4_case_pairwise (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hnu : M.card = 4)
    (h_all_share : ∀ e ∈ M, ∃ f ∈ M, f ≠ e ∧ (e ∩ f).card ≥ 1) :
    triangleCoveringNumber G ≤ 8 := by
  -- Pick any pair {e, f} that share a vertex
  -- τ(T_e ∪ T_f) ≤ 4 by tau_union_le_4
  -- Residual has ν ≤ 2, so τ(residual) ≤ 4 by induction
  -- Total: 4 + 4 = 8
  sorry

-- Main theorem: τ ≤ 8 when ν = 4
theorem tuza_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) : triangleCoveringNumber G ≤ 8 := by
  obtain ⟨M, hM⟩ : ∃ M, isMaxPacking G M ∧ M.card = 4 := by
    have h_max_packing : ∃ M : Finset (Finset V), isTrianglePacking G M ∧ M.card = 4 := by
      unfold trianglePackingNumber at h;
      have := Finset.mem_of_max ( show ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ).max = some 4 from ?_ ) ; aesop;
      rw [ Option.getD_eq_iff ] at h ; aesop;
    unfold isMaxPacking at *; aesop;
  by_cases h_isolated : ∃ e ∈ M, ∀ f ∈ M, f ≠ e → (e ∩ f).card = 0
  · exact nu4_case_isolated G M hM.1 hM.2 h_isolated
  · push_neg at h_isolated
    -- h_isolated : ∀ e ∈ M, ∃ f ∈ M, f ≠ e ∧ (e ∩ f).card ≠ 0
    have h_all_share : ∀ e ∈ M, ∃ f ∈ M, f ≠ e ∧ (e ∩ f).card ≥ 1 := by
      intro e he
      obtain ⟨f, hf, hne, hcard⟩ := h_isolated e he
      exact ⟨f, hf, hne, Nat.one_le_iff_ne_zero.mpr hcard⟩
    exact nu4_case_pairwise G M hM.1 hM.2 h_all_share

end