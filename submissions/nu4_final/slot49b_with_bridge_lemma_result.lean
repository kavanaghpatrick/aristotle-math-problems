/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 82088ab4-b53d-490a-bd41-59fca09373e7

The following was proved by Aristotle:

- theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B

- lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2

- lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2

- lemma path4_A_bridges_only_to_B (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D) :
    bridges G M A ⊆ X_ef G A B

- lemma path4_triangle_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    G.cliqueFinset 3 ⊆
      trianglesSharingEdge G A ∪ trianglesSharingEdge G B ∪
      trianglesSharingEdge G C ∪ trianglesSharingEdge G D

- lemma tau_Te_le_4_for_endpoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumberOn G (trianglesSharingEdge G A) ≤ 4
-/

/-
Tuza ν=4 - Slot 49: PATH_4 Case via tau_S_le_2 Decomposition

PROBLEM: Prove τ(G) ≤ 8 when ν(G) = 4 and packing forms a path A—B—C—D.

STRUCTURE:
- 4 packing elements: A, B, C, D
- 3 shared vertices: v_ab (A∩B), v_bc (B∩C), v_cd (C∐D)
- Non-adjacent pairs (A,C) and (B,D) are vertex-disjoint

CRITICAL ISSUE (from Codex validation):
Bridges are NOT in S_e by definition! S_e excludes triangles that share
≥2 vertices with OTHER packing elements. So bridges need explicit handling.

REVISED STRATEGY:
Use T_pair decomposition instead of per-element:
- T_pair(A,B): all triangles sharing edge with A OR B (includes X_{A,B})
- T_pair(C,D): all triangles sharing edge with C OR D (includes X_{C,D})
- Bound each T_pair using shared_vertex_concentrated_savings

ALTERNATIVE (leaf removal):
- A and D are leaves (share vertex with only one neighbor)
- If τ(T_leaf) ≤ 2, then τ(G) ≤ 2 + τ(ν=3 residual) ≤ 2 + 6 = 8

FOR ARISTOTLE TO EXPLORE:
1. Can we prove τ(T_pair(e,f)) ≤ 4 when e ∩ f = {v}?
2. Or can we prove τ(T_leaf) ≤ 2 for leaves?
3. What's the correct bridge accounting?

SCAFFOLDING: tau_S_le_2 (slot6), tau_X_le_2 (slot24), tau_union_le_sum (slot16)
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def sharesVertex (e f : Finset V) : Prop := (e ∩ f).card ≥ 1

-- Path structure: A—B—C—D where adjacent pairs share exactly one vertex
def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  -- A distinct from B, C, D
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
  -- Adjacent pairs share exactly one vertex
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  -- Non-adjacent pairs are vertex-disjoint
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slots 6, 16, 24)
-- ══════════════════════════════════════════════════════════════════════════════

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

lemma le_triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : isTriangleCover G A E') :
    triangleCoveringNumberOn G A ≤ E'.card := by
  unfold triangleCoveringNumberOn
  have h_mem : E' ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1, h.2⟩
  have := Finset.min_le (Finset.mem_image_of_mem Finset.card h_mem)
  rw [WithTop.le_coe_iff] at this; aesop

lemma isTriangleCover_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  unfold isTriangleCover at *
  constructor
  · exact Finset.union_subset hA.1 hB.1
  · intro t ht
    simp only [Finset.mem_union] at ht
    cases ht with
    | inl htA =>
      obtain ⟨e, heEA, het⟩ := hA.2 t htA
      exact ⟨e, Finset.mem_union_left EB heEA, het⟩
    | inr htB =>
      obtain ⟨e, heEB, het⟩ := hB.2 t htB
      exact ⟨e, Finset.mem_union_right EA heEB, het⟩

-- PROVEN: Te = Se ∪ bridges (from slot 6)
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

-- PROVEN in slot16: τ(A ∪ B) ≤ τ(A) + τ(B)
noncomputable section AristotleLemmas

/-
If a triangle cover exists, then there exists a triangle cover with cardinality equal to the triangle covering number.
-/
lemma exists_min_triangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V))
    (h : ∃ E, isTriangleCover G A E) :
    ∃ E, isTriangleCover G A E ∧ E.card = triangleCoveringNumberOn G A := by
      have h_min : ∃ E ∈ Finset.filter (fun E' => isTriangleCover G A E') (Finset.powerset G.edgeFinset), ∀ E' ∈ Finset.filter (fun E' => isTriangleCover G A E') (Finset.powerset G.edgeFinset), E'.card ≥ E.card := by
        apply_rules [ Finset.exists_min_image ];
        exact ⟨ h.choose, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h.choose_spec.1, h.choose_spec ⟩ ⟩;
      obtain ⟨ E, hE₁, hE₂ ⟩ := h_min;
      refine' ⟨ E, _, _ ⟩ <;> simp_all +decide [ triangleCoveringNumberOn ];
      rw [ show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) = Finset.image Finset.card ( Finset.filter ( fun E' => isTriangleCover G A E' ) ( Finset.powerset G.edgeFinset ) ) from ?_ ];
      · rw [ show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | isTriangleCover G A E' } ) ).min = some ( E.card ) from ?_ ] ; aesop;
        refine' le_antisymm _ _ <;> simp_all +decide [ Finset.min ];
        · refine' Finset.inf_le _ ; aesop;
        · exact fun E' hE'₁ hE'₂ => WithTop.coe_le_coe.mpr ( hE₂ E' hE'₁ hE'₂ );
      · ext; simp [isTriangleCover]

/-
If there is no triangle cover for a set of triangles, the triangle covering number is 0.
-/
lemma triangleCoveringNumberOn_eq_zero_of_not_exists_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (Finset V)) (h : ¬ ∃ E, isTriangleCover G A E) :
    triangleCoveringNumberOn G A = 0 := by
      unfold triangleCoveringNumberOn;
      simp_all +decide [ Finset.ext_iff, isTriangleCover ];
      rw [ show ( Finset.filter ( fun E' ↦ ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( G.edgeFinset.powerset ) ) = ∅ from Finset.filter_eq_empty_iff.mpr fun E' hE' ↦ by specialize h E'; aesop ] ; simp +decide

/-
If a set of edges covers a set of triangles, it also covers any subset of that set of triangles.
-/
lemma isTriangleCover_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset (Finset V)} (hAB : A ⊆ B) {E : Finset (Sym2 V)} (h : isTriangleCover G B E) :
    isTriangleCover G A E := by
      unfold isTriangleCover at *; aesop;

end AristotleLemmas

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases hA : ∃ E, isTriangleCover G A E <;> by_cases hB : ∃ E, isTriangleCover G B E;
  · -- By `exists_min_triangleCover`, we can choose a cover $E_A$ for $A$ with $|E_A| = \tau(A)$ and a cover $E_B$ for $B$ with $|E_B| = \tau(B)$.
    obtain ⟨EA, hEA⟩ := exists_min_triangleCover G A hA
    obtain ⟨EB, hEB⟩ := exists_min_triangleCover G B hB;
    exact le_trans ( le_triangleCoveringNumberOn G ( A ∪ B ) ( EA ∪ EB ) ( isTriangleCover_union G A B EA EB hEA.1 hEB.1 ) ) ( by rw [ Finset.card_union ] ; omega );
  · rw [ triangleCoveringNumberOn_eq_zero_of_not_exists_cover ];
    · exact Nat.zero_le _;
    · simp +zetaDelta at *;
      intro E hE; specialize hB E; unfold isTriangleCover at *; aesop;
  · rw [ triangleCoveringNumberOn_eq_zero_of_not_exists_cover ];
    · exact Nat.zero_le _;
    · rintro ⟨ E, hE ⟩;
      exact hA ⟨ E, by exact ⟨ hE.1, fun t ht => by have := hE.2 t ( Finset.mem_union_left _ ht ) ; aesop ⟩ ⟩;
  · rw [ triangleCoveringNumberOn_eq_zero_of_not_exists_cover G A, triangleCoveringNumberOn_eq_zero_of_not_exists_cover G B ];
    · simp +zetaDelta at *;
      rw [ triangleCoveringNumberOn_eq_zero_of_not_exists_cover ];
      exact fun ⟨ E, hE ⟩ => hB E ( by exact ⟨ hE.1, fun t ht => hE.2 t ( Finset.mem_union_right _ ht ) ⟩ );
    · exact hB;
    · exact hA

-- SCAFFOLDING: Full proof in slot16/slot29

-- PROVEN in slot6: τ(S_e) ≤ 2
noncomputable section AristotleLemmas

lemma S_e_pairwise_intersect (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    ∀ t1 ∈ S_e G M e, ∀ t2 ∈ S_e G M e, (t1 ∩ t2).card ≥ 2 := by
      intro t1 ht1 t2 ht2
      by_contra h_contra;
      -- Consider $M' = (M \setminus \{e\}) \cup \{t1, t2\}$. We claim $M'$ is a triangle packing.
      have h_M'_packing : isTrianglePacking G ((M \ {e}) ∪ {t1, t2}) := by
        constructor;
        · intro x hx;
          simp +zetaDelta at *;
          rcases hx with ( rfl | rfl | ⟨ hx, hx' ⟩ ) <;> simp_all +decide [ S_e ];
          · unfold trianglesSharingEdge at ht1; aesop;
          · unfold trianglesSharingEdge at ht2; aesop;
          · have := hM.1.1 hx; aesop;
        · intro x hx y hy hxy; by_cases hx' : x = t1 <;> by_cases hy' : y = t1 <;> by_cases hx'' : x = t2 <;> by_cases hy'' : y = t2 <;> simp_all +decide ;
          all_goals have := Finset.card_le_card ( Finset.inter_subset_left : t1 ∩ y ⊆ t1 ) ; have := Finset.card_le_card ( Finset.inter_subset_right : t1 ∩ y ⊆ y ) ; simp_all +decide ;
          any_goals linarith;
          all_goals simp_all +decide [ S_e ];
          · rw [ Finset.inter_comm ] ; linarith;
          · exact ht1.2 x hx.1 hx.2 |> le_trans ( by rw [ Finset.inter_comm ] );
          · simpa only [ Finset.inter_comm ] using ht1.2 x hx.1 hx.2;
          · simpa only [ Finset.inter_comm ] using ht2.2 x hx.1 hx.2;
          · have := hM.1.2; aesop;
      -- Since $M$ is a maximum packing, we have $|M'| \le |M|$.
      have h_M'_card : ((M \ {e}) ∪ {t1, t2}).card ≤ M.card := by
        have h_M'_card : ((M \ {e}) ∪ {t1, t2}).card ≤ trianglePackingNumber G := by
          have h_M'_card : ((M \ {e}) ∪ {t1, t2}) ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) := by
            simp_all +decide [ isTrianglePacking ];
          unfold trianglePackingNumber;
          have h_M'_card : (M \ {e} ∪ {t1, t2}).card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
            exact Finset.mem_image_of_mem _ h_M'_card;
          have := Finset.le_max h_M'_card;
          cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 ).powerset ) ) <;> aesop;
        exact h_M'_card.trans ( hM.2.ge );
      by_cases h : t1 = t2 <;> simp_all +decide [ Finset.card_sdiff, Finset.subset_iff ];
      · have := h_M'_packing.1;
        have := this ( Finset.mem_insert_self _ _ ) ; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        exact h_contra.not_le ( this.card_eq.ge.trans' ( by decide ) );
      · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] at h_M'_card <;> simp_all +decide [ Finset.sdiff_singleton_eq_erase ];
        · omega;
        · intro hne hmem; simp_all +decide [ S_e ] ;
          have := ht2.2 _ hmem hne; simp_all +decide [ Finset.inter_comm ] ;
          have := Finset.mem_filter.mp ht2.1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          exact absurd ‹t2.card ≤ 1› ( by rw [ SimpleGraph.isNClique_iff ] at this; aesop );
        · intro h_neq h_mem; simp_all +decide [ S_e ] ;
          unfold trianglesSharingEdge at *; simp_all +decide [ Finset.filter_congr ] ;
          have := ht1.2 t1 h_mem h_neq; simp_all +decide [ Finset.inter_comm ] ;
          exact this.not_lt ( by rw [ ht1.1.1.2 ] ; decide )

lemma three_intersecting_triples (t1 t2 t3 : Finset V)
    (h1 : t1.card = 3) (h2 : t2.card = 3) (h3 : t3.card = 3)
    (h12 : (t1 ∩ t2).card ≥ 2)
    (h13 : (t1 ∩ t3).card ≥ 2)
    (h23 : (t2 ∩ t3).card ≥ 2)
    (h_no_common : ¬∃ u v, u ≠ v ∧ {u, v} ⊆ t1 ∧ {u, v} ⊆ t2 ∧ {u, v} ⊆ t3) :
    (t1 ∪ t2 ∪ t3).card ≤ 4 := by
      have := Finset.card_eq_three.1 h1; obtain ⟨ u, v, w, hu, hv, hw, h ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
      grind

lemma exists_triple_no_common_edge (T : Finset (Finset V))
    (h_card : ∀ t ∈ T, t.card = 3)
    (h_inter : ∀ t1 ∈ T, ∀ t2 ∈ T, (t1 ∩ t2).card ≥ 2)
    (h_no_common : ∀ u v, u ≠ v → ∃ t ∈ T, ¬({u, v} ⊆ t))
    (h_nonempty : T.Nonempty) :
    ∃ t1 ∈ T, ∃ t2 ∈ T, ∃ t3 ∈ T, ¬(∃ u v, u ≠ v ∧ {u, v} ⊆ t1 ∧ {u, v} ⊆ t2 ∧ {u, v} ⊆ t3) := by
      -- Let's choose any $t_1 \in T$ and denote its vertices by $u, v, w$.
      obtain ⟨t1, ht1_T, u, v, w, hu, hv, hw, huv, hvw, hwu⟩ : ∃ t1 ∈ T, ∃ u v w : V, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ t1 = {u, v, w} := by
        obtain ⟨ t, ht ⟩ := h_nonempty; obtain ⟨ u, v, w, h ⟩ := Finset.card_eq_three.mp ( h_card _ ht ) ; exact ⟨ _, ht, u, v, w, by aesop_cat, by aesop_cat, by aesop_cat, by aesop_cat ⟩ ;
      -- By `h_no_common`, there exists $t_2 \in T$ such that $\{u, v\} \not\subseteq t_2$.
      obtain ⟨t2, ht2_T, ht2_not_uv⟩ : ∃ t2 ∈ T, ¬{u, v} ⊆ t2 := h_no_common u v hu;
      -- Since $t_1 \cap t_2$ has at least 2 elements and $\{u, v\} \not\subseteq t_2$, $t_2$ must contain $\{v, w\}$ or $\{u, w\}$.
      have ht2_contains_vw_or_uw : {v, w} ⊆ t2 ∨ {u, w} ⊆ t2 := by
        have ht2_contains_vw_or_uw : (t2 ∩ {u, v, w}).card ≥ 2 := by
          simpa only [ Finset.inter_comm ] using h_inter _ ht1_T _ ht2_T;
        by_cases hu : u ∈ t2 <;> by_cases hv : v ∈ t2 <;> by_cases hw : w ∈ t2 <;> simp_all +decide [ Finset.subset_iff ];
      cases' ht2_contains_vw_or_uw with ht2_contains_vw ht2_contains_uw;
      · -- By `h_no_common`, there exists $t_3 \in T$ such that $\{v, w\} \not\subseteq t_3$.
        obtain ⟨t3, ht3_T, ht3_not_vw⟩ : ∃ t3 ∈ T, ¬({v, w} ⊆ t3) := by
          exact h_no_common v w hw;
        use {u, v, w}, ht1_T, t2, ht2_T, t3, ht3_T;
        simp_all +decide [ Finset.subset_iff ];
        grind;
      · -- By `h_no_common`, there exists $t_3 \in T$ such that $\{u, w\} \not\subseteq t_3$.
        obtain ⟨t3, ht3_T, ht3_not_uw⟩ : ∃ t3 ∈ T, ¬({u, w} ⊆ t3) := by
          exact h_no_common u w hv;
        refine' ⟨ { u, v, w }, ht1_T, t2, ht2_T, t3, ht3_T, _ ⟩;
        simp +decide [ Finset.subset_iff ] at *;
        grind

lemma intersecting_family_structure (T : Finset (Finset V))
    (h_card : ∀ t ∈ T, t.card = 3)
    (h_inter : ∀ t1 ∈ T, ∀ t2 ∈ T, (t1 ∩ t2).card ≥ 2) :
    (∃ u v, u ≠ v ∧ ∀ t ∈ T, {u, v} ⊆ t) ∨ (∃ A : Finset V, A.card ≤ 4 ∧ ∀ t ∈ T, t ⊆ A) := by
      -- Let $t_1, t_2, t_3 \in T$ be three triangles with no common edge.
      by_cases h_empty : T.Nonempty;
      · by_cases h_common : ∃ u v : V, u ≠ v ∧ ∀ t ∈ T, {u, v} ⊆ t;
        · exact Or.inl h_common;
        · -- By `exists_triple_no_common_edge`, there exist $t_1, t_2, t_3 \in T$ with no common edge.
          obtain ⟨t1, ht1, t2, ht2, t3, ht3, h_no_common⟩ : ∃ t1 ∈ T, ∃ t2 ∈ T, ∃ t3 ∈ T, ¬(∃ u v : V, u ≠ v ∧ {u, v} ⊆ t1 ∧ {u, v} ⊆ t2 ∧ {u, v} ⊆ t3) := by
            apply exists_triple_no_common_edge T h_card h_inter;
            · exact fun u v huv => by push_neg at h_common; exact h_common u v huv;
            · exact h_empty;
          -- By `three_intersecting_triples`, $|t_1 \cup t_2 \cup t_3| \le 4$. Let $A = t_1 \cup t_2 \cup t_3$.
          obtain ⟨A, hA⟩ : ∃ A : Finset V, A = t1 ∪ t2 ∪ t3 ∧ A.card ≤ 4 := by
            have h_three_intersecting_triples : (t1 ∪ t2 ∪ t3).card ≤ 4 := by
              apply three_intersecting_triples t1 t2 t3 (h_card t1 ht1) (h_card t2 ht2) (h_card t3 ht3) (h_inter t1 ht1 t2 ht2) (h_inter t1 ht1 t3 ht3) (h_inter t2 ht2 t3 ht3) h_no_common;
            exact ⟨ _, rfl, h_three_intersecting_triples ⟩;
          refine' Or.inr ⟨ A, hA.2, fun t ht => _ ⟩;
          intro x hx; contrapose! h_no_common; simp_all +decide [ Finset.subset_iff ] ;
          -- Since $t \cap t1 \geq 2$, $t \cap t2 \geq 2$, and $t \cap t3 \geq 2$, and $x \notin t1$, $x \notin t2$, $x \notin t3$, it follows that $t1$, $t2$, and $t3$ must each contain at least two elements from $t \setminus \{x\}$.
          have h_inter_t1 : (t1 ∩ (t \ {x})).card ≥ 2 := by
            have := h_inter t1 ht1 t ht; simp_all +decide [ Finset.inter_comm ] ;
            convert h_inter t1 ht1 t ht using 1;
            exact congr_arg Finset.card ( by ext y; by_cases hy : y = x <;> aesop )
          have h_inter_t2 : (t2 ∩ (t \ {x})).card ≥ 2 := by
            have := h_inter t2 ht2 t ht; simp_all +decide [ Finset.inter_comm ] ;
            have := h_inter t2 ht2 t ht; simp_all +decide [ Finset.inter_comm, Finset.sdiff_singleton_eq_erase ] ;
            have := h_inter t2 ht2 t ht; rw [ show t2 ∩ t.erase x = t2 ∩ t from by ext y; by_cases hy : y = x <;> aesop ] ; linarith;
          have h_inter_t3 : (t3 ∩ (t \ {x})).card ≥ 2 := by
            have := h_inter t3 ht3 t ht; simp_all +decide [ Finset.inter_comm ] ;
            have := h_inter t3 ht3 t ht; simp_all +decide [ Finset.inter_comm, Finset.sdiff_singleton_eq_erase ] ;
            have := h_inter t3 ht3 t ht; simp_all +decide [ Finset.inter_erase ] ;
          -- Since $t1$, $t2$, and $t3$ each contain at least two elements from $t \setminus \{x\}$, and $t \setminus \{x\}$ has exactly two elements, it follows that $t1$, $t2$, and $t3$ must each contain both elements of $t \setminus \{x\}$.
          have h_inter_t1_eq : t1 ∩ (t \ {x}) = t \ {x} := by
            refine' Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right ) _;
            rw [ Finset.card_sdiff ] ; aesop
          have h_inter_t2_eq : t2 ∩ (t \ {x}) = t \ {x} := by
            refine' Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right ) _;
            rw [ Finset.card_sdiff ] ; aesop
          have h_inter_t3_eq : t3 ∩ (t \ {x}) = t \ {x} := by
            refine' Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right ) _;
            rw [ Finset.card_sdiff ] ; aesop;
          obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.1 h_inter_t1; use u, v; aesop;
      · exact Or.inr ⟨ ∅, by simp +decide, by aesop ⟩

lemma exists_cover_size_2_of_subset_size_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Finset V))
    (A : Finset V)
    (hA : A.card ≤ 4)
    (h_subset : ∀ t ∈ T, t ⊆ A)
    (h_triangles : T ⊆ G.cliqueFinset 3) :
    ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 2 ∧ ∀ t ∈ T, ∃ e ∈ E', e ∈ t.sym2 := by
      -- If $T$ is nonempty, then $A$ must have size at least 3.
      by_cases hA_card : A.card ≥ 3;
      · interval_cases _ : A.card;
        · -- If $|A| = 3$, then $T \subseteq \{ \{u,v,w\} \}$.
          obtain ⟨u, v, w, hu, hv, hw, hA⟩ : ∃ u v w : V, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ A = {u, v, w} := by
            rw [ Finset.card_eq_three ] at *; tauto;
          by_cases hT : T = ∅ <;> simp_all +decide [ Finset.subset_iff ];
          · exact ⟨ ∅, by simp +decide ⟩;
          · -- If $T \ne \emptyset$, then $T \subseteq \{ \{u,v,w\} \}$.
            have hT_subset : T ⊆ { {u, v, w} } := by
              intro t ht; specialize h_subset t ht; specialize h_triangles ht; rw [ Finset.eq_of_subset_of_card_le ( show t ⊆ { u, v, w } from fun x hx => by aesop ) ] ; aesop;
              rw [ h_triangles.card_eq ] ; aesop;
            refine' ⟨ { Sym2.mk ( u, v ) }, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
        · -- Let $A = \{v_1, v_2, v_3, v_4\}$.
          obtain ⟨v1, v2, v3, v4, hv⟩ : ∃ v1 v2 v3 v4 : V, A = {v1, v2, v3, v4} ∧ v1 ≠ v2 ∧ v1 ≠ v3 ∧ v1 ≠ v4 ∧ v2 ≠ v3 ∧ v2 ≠ v4 ∧ v3 ≠ v4 := by
            rcases Finset.card_eq_succ.mp ‹_› with ⟨ v, hv ⟩;
            rcases hv with ⟨ t, ht, rfl, ht' ⟩ ; rcases Finset.card_eq_three.mp ht' with ⟨ v1, v2, v3, hv1, hv2, hv3 ⟩ ; use v, v1, v2, v3; aesop;
          -- Consider the possible triangles in $T$.
          have h_triangles_cases : ∀ t ∈ T, t = {v1, v2, v3} ∨ t = {v1, v2, v4} ∨ t = {v1, v3, v4} ∨ t = {v2, v3, v4} := by
            intro t ht
            have ht_card : t.card = 3 := by
              have := h_triangles ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
              exact this.2;
            have := Finset.card_eq_three.mp ht_card; obtain ⟨ a, b, c, hab, hbc, hac ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
            rcases h_subset _ ht ( Finset.mem_insert_self _ _ ) with ha | ha | ha | ha <;> rcases h_subset _ ht ( Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ) ) with hb | hb | hb | hb <;> rcases h_subset _ ht ( Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ) with hc | hc | hc | hc <;> simp +decide [ * ] at hab hbc hac ⊢;
            all_goals simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
          -- Consider the edges $e_{12} = \{v_1, v_2\}$ and $e_{34} = \{v_3, v_4\}$.
          by_cases h12 : G.Adj v1 v2
          by_cases h34 : G.Adj v3 v4;
          · refine' ⟨ { Sym2.mk ( v1, v2 ), Sym2.mk ( v3, v4 ) }, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.mem_edgeSet ];
            · simp +decide [ *, Set.insert_subset_iff ];
            · intro t ht; specialize h_triangles_cases t ht; aesop;
          · use {Sym2.mk (v1, v2)};
            simp_all +decide [ SimpleGraph.cliqueFinset ];
            intro t ht; specialize h_triangles_cases t ht; specialize h_triangles ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            rcases h_triangles_cases with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide;
          · by_cases h34 : G.Adj v3 v4;
            · use {Sym2.mk (v3, v4)};
              simp_all +decide [ SimpleGraph.cliqueFinset ];
              intro t ht; specialize h_triangles_cases t ht; specialize h_triangles ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
              rcases h_triangles_cases with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide;
            · use ∅; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
              intro t ht; specialize h_triangles ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
              rcases h_triangles_cases t ht with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ SimpleGraph.isClique_iff ];
      · contrapose! hA_card;
        obtain ⟨ t, htT, ht ⟩ := hA_card ∅ ( Finset.empty_subset _ ) ( by norm_num ) ; have := h_triangles htT ; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        exact le_trans ( by simpa using this.card_eq.ge ) ( Finset.card_le_card ( h_subset t htT ) )

end AristotleLemmas

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  have h_case1 : ∀ t ∈ S_e G M e, t.card = 3 := by
    intro t ht
    have ht_triangle : t ∈ G.cliqueFinset 3 := by
      exact Finset.mem_filter.mp ht |>.1 |> Finset.mem_filter.mp |>.1
    generalize_proofs at *;
    simp_all +decide [ SimpleGraph.mem_cliqueFinset_iff ];
    exact ht_triangle.2
  generalize_proofs at *;
  -- By `intersecting_family_structure`, there exists $A$ with $|A| \le 4$ such that $\forall t \in T, t \subseteq A$ or there exist $u, v$ with $u \ne v$ such that $\forall t \in T, \{u, v\} \subseteq t$.
  obtain ⟨A, hA⟩ | ⟨u, v, huv, h⟩ : (∃ A : Finset V, A.card ≤ 4 ∧ ∀ t ∈ S_e G M e, t ⊆ A) ∨ (∃ u v : V, ¬u = v ∧ ∀ t ∈ S_e G M e, {u, v} ⊆ t) := by
    have := intersecting_family_structure ( S_e G M e ) h_case1 ( S_e_pairwise_intersect G M hM e he ) ; aesop;
  · -- By `exists_cover_size_2_of_subset_size_4`, there exists a cover $E'$ of size $\le 2$.
    obtain ⟨E', hE'_subset, hE'_card, hE'_cover⟩ : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 2 ∧ ∀ t ∈ S_e G M e, ∃ e ∈ E', e ∈ t.sym2 := by
      apply exists_cover_size_2_of_subset_size_4 G (S_e G M e) A hA.left hA.right;
      exact fun t ht => Finset.mem_filter.mp ( Finset.mem_filter.mp ht |>.1 ) |>.1;
    exact le_trans ( le_triangleCoveringNumberOn G _ _ ⟨ hE'_subset, hE'_cover ⟩ ) hE'_card;
  · by_cases h_empty : S_e G M e = ∅;
    · simp +decide [ h_empty ];
      exact le_trans ( le_triangleCoveringNumberOn G ∅ ∅ ⟨ by simp +decide, by simp +decide ⟩ ) ( by simp +decide );
    · -- Let $t \in S_e G M e$. Since $\{u, v\} \subseteq t$ and $t$ is a clique, $\{u, v\}$ is an edge of $G$.
      obtain ⟨t, ht⟩ : ∃ t ∈ S_e G M e, {u, v} ⊆ t := by
        exact Exists.elim ( Finset.nonempty_of_ne_empty h_empty ) fun t ht => ⟨ t, ht, h t ht ⟩
      generalize_proofs at *;
      have h_edge : Sym2.mk (u, v) ∈ G.edgeFinset := by
        have h_edge : t ∈ G.cliqueFinset 3 := by
          exact Finset.mem_filter.mp ht.1 |>.1 |> Finset.mem_filter.mp |>.1 |> fun h => by aesop;
        generalize_proofs at *;
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        have := h_edge.1; simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ] ;
        exact this ht.2.1 ht.2.2 huv
      generalize_proofs at *;
      refine' le_trans ( le_triangleCoveringNumberOn G ( S_e G M e ) { s(u, v) } ⟨ _, _ ⟩ ) _ <;> simp_all +decide [ Finset.subset_iff ]

-- SCAFFOLDING: Full proof in slot6

-- PROVEN in slot24: τ(X_ef) ≤ 2
noncomputable section AristotleLemmas

/-
If a triangle C shares >=2 vertices with A and >=2 with B, and |A ∩ B| <= 1, then A and B share a vertex v which is also in C.
-/
lemma intersect_ge_two_lemma {V : Type*} [Fintype V] [DecidableEq V]
    (A B C : Finset V)
    (hA : A.card = 3) (hB : B.card = 3) (hC : C.card = 3)
    (hAB : (A ∩ B).card ≤ 1)
    (hCA : (C ∩ A).card ≥ 2) (hCB : (C ∩ B).card ≥ 2) :
    ∃ v, v ∈ A ∩ B ∧ v ∈ C := by
      -- Since $|C \cap A| \geq 2$ and $|C \cap B| \geq 2$, and $|A \cap B| \leq 1$, it follows that $C \cap A \cap B$ must contain at least one element.
      have h_inter : (C ∩ A ∩ B).card ≥ 1 := by
        have h_inter : (C ∩ A ∩ B).card ≥ (C ∩ A).card + (C ∩ B).card - 3 := by
          have := Finset.card_union_add_card_inter ( C ∩ A ) ( C ∩ B );
          simp_all +decide [ Finset.inter_left_comm, Finset.inter_comm ];
          linarith [ show Finset.card ( A ∩ C ∪ B ∩ C ) ≤ 3 by exact le_trans ( Finset.card_le_card ( Finset.union_subset ( Finset.inter_subset_right ) ( Finset.inter_subset_right ) ) ) hC.le ];
        exact le_trans ( by omega ) h_inter;
      exact Exists.elim ( Finset.card_pos.mp h_inter ) fun x hx => ⟨ x, by aesop ⟩

lemma lemma_cover_X_ef (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V)
    (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (hef_disj : (e ∩ f).card ≤ 1) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ G.edgeFinset ∧
    ∀ t ∈ X_ef G e f, ∃ edge ∈ E', edge ∈ t.sym2 := by
      -- Since |e ∩ f| ≤ 1, if |e ∩ f| = 1, let v be the unique element in e ∩ f. Otherwise, let v be any element of e.
      by_cases hef : (e ∩ f).card = 1;
      · obtain ⟨ v, hv ⟩ := Finset.card_eq_one.mp hef;
        -- Let's denote the set of edges incident to v by E_v.
        obtain ⟨u, w, huw⟩ : ∃ u w : V, u ≠ v ∧ w ≠ v ∧ e = {u, v, w} ∧ G.Adj u v ∧ G.Adj v w ∧ G.Adj u w := by
          simp_all +decide [ Finset.ext_iff, SimpleGraph.isNClique_iff ];
          -- Since $e$ is a triangle, it must contain exactly three elements. Let's denote them as $u$, $v$, and $w$.
          obtain ⟨u, w, hu, hv, hw⟩ : ∃ u w : V, u ≠ v ∧ w ≠ v ∧ u ≠ w ∧ e = {u, v, w} := by
            obtain ⟨ u, w, hu, hw, h ⟩ := Finset.card_eq_three.mp he.2;
            cases eq_or_ne u v <;> cases eq_or_ne w v <;> cases eq_or_ne hu v <;> simp_all +decide;
            · exact ⟨ w, by tauto, hu, by tauto, by tauto, by aesop ⟩;
            · exact ⟨ u, by tauto, hu, by tauto, by tauto, rfl ⟩;
            · exact ⟨ u, by tauto, w, by tauto, by tauto, by aesop ⟩;
            · specialize hv v; aesop;
          simp_all +decide [ SimpleGraph.isClique_iff ];
          exact ⟨ u, hu, w, hv, by tauto, he.1.2.1, by simpa [ SimpleGraph.adj_comm ] using he.1.1 ( by tauto ), he.1.2.2 ⟩;
        refine' ⟨ { Sym2.mk ( u, v ), Sym2.mk ( v, w ) }, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
        · exact Finset.card_insert_le _ _;
        · intro t ht; simp_all +decide [ Finset.ext_iff, Set.ext_iff ] ;
          have := Finset.mem_filter.mp ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          have := Finset.card_eq_three.mp this.1.2; obtain ⟨ x, y, z, hxyz ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
          grind;
      · refine' ⟨ ∅, _, _, _ ⟩ <;> simp_all +decide [ X_ef ];
        intro t ht ht'; contrapose! hef; interval_cases _ : ( e ∩ f ).card <;> simp_all +decide ;
        have h_inter : (t ∩ e).card + (t ∩ f).card ≤ t.card := by
          rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx hx' => by rw [ Finset.ext_iff ] at *; specialize ‹∀ x, x ∈ e ∩ f ↔ x ∈ ∅› x; aesop ) ] ; exact Finset.card_mono ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ;
        linarith [ ht.2 ]

end AristotleLemmas

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  obtain ⟨E', hE'_card, hE'_sub, hE'_cover⟩ : ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ G.edgeFinset ∧ ∀ t ∈ X_ef G e f, ∃ edge ∈ E', edge ∈ t.sym2 := by
    -- Apply lemma_cover_X_ef to obtain the cover E' for X_ef G e f, using the fact that e and f are triangles in G and |e ∩ f| ≤ 1.
    apply lemma_cover_X_ef;
    · have := hM.1;
      exact this.1 he;
    · exact hM.1.1 hf;
    · have := hM.1.2;
      exact this he hf hef;
  convert le_triangleCoveringNumberOn G _ E' ⟨ hE'_sub, hE'_cover ⟩ |> le_trans <| hE'_card using 1

-- SCAFFOLDING: Full proof in slot24/slot36

-- ══════════════════════════════════════════════════════════════════════════════
-- PATH_4 STRUCTURAL LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/--
In a path A—B—C—D, bridges from A only go to B (the unique neighbor).
-/
lemma path4_A_bridges_only_to_B (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hpath : isPath4 M A B C D) :
    bridges G M A ⊆ X_ef G A B := by
  intro t ht
  simp only [bridges, Finset.mem_filter] at ht
  obtain ⟨h_share_A, f, hfM, hfne, h_share_f⟩ := ht
  -- f must be B since A only shares vertex with B
  simp only [X_ef, Finset.mem_filter]
  constructor
  · -- t is a triangle
    simp only [trianglesSharingEdge, Finset.mem_filter] at h_share_A
    exact h_share_A.1
  constructor
  · -- t shares ≥2 vertices with A
    simp only [trianglesSharingEdge, Finset.mem_filter] at h_share_A
    exact h_share_A.2
  · -- t shares ≥2 vertices with B
    -- Since f ∈ M, f ≠ A, and (t ∩ f).card ≥ 2, we need f = B
    -- Because A is disjoint from C and D in path4
    -- Extract disjointness facts from path structure BEFORE case split
    obtain ⟨hM_eq, hAB, hAC_ne, hAD_ne, hBC_ne, hBD_ne, hCD_ne,
            hAB_share, hBC_share, hCD_share, hAC_disj, hAD_disj, hBD_disj⟩ := hpath
    have hfM' : f ∈ ({A, B, C, D} : Finset (Finset V)) := by rw [← hM_eq]; exact hfM
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfM'
    rcases hfM' with rfl | rfl | rfl | rfl
    · exact absurd rfl hfne
    · exact h_share_f
    · -- f = C: but (A ∩ C).card = 0, so (t ∩ C).card ≥ 2 impossible for t sharing edge with A
      exfalso
      -- t shares ≥2 with A and ≥2 with C, but A ∩ C = ∅
      -- t has only 3 vertices, so this is impossible
      unfold trianglesSharingEdge at h_share_A; simp_all +decide ;
      -- Since $A \cap f = \emptyset$, any element in $t$ that is also in $A$ cannot be in $f$, and vice versa. Therefore, $(t \cap A).card + (t \cap f).card \leq t.card$.
      have h_inter : (t ∩ A).card + (t ∩ f).card ≤ t.card := by
        rw [ ← Finset.card_union_of_disjoint ];
        · exact Finset.card_le_card fun x hx => by aesop;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.notMem_empty x ( hAC_disj ▸ Finset.mem_inter.mpr ⟨ Finset.mem_inter.mp hx₁ |>.2, Finset.mem_inter.mp hx₂ |>.2 ⟩ );
      linarith [ show t.card = 3 by exact h_share_A.1.card_eq ] -- TARGET: derive contradiction from disjointness (use hAC_disj, h_share_f)
    · -- f = D: similar
      exfalso
      -- Since $t$ shares at least two vertices with both $A$ and $f$, and $A$ and $f$ are disjoint, this leads to a contradiction.
      have h_contradiction : (t ∩ A).card ≥ 2 ∧ (t ∩ f).card ≥ 2 := by
        unfold trianglesSharingEdge at h_share_A; aesop;
      have h_contradiction : (t ∩ (A ∪ f)).card ≥ 4 := by
        have h_contradiction : (t ∩ (A ∪ f)).card = (t ∩ A).card + (t ∩ f).card := by
          rw [ ← Finset.card_union_add_card_inter, Finset.inter_union_distrib_left ];
          simp_all +decide [ Finset.ext_iff ];
        linarith;
      have h_contradiction : (t ∩ (A ∪ f)).card ≤ (t).card := by
        exact Finset.card_le_card fun x hx => by aesop;
      have h_contradiction : t.card ≤ 3 := by
        have h_contradiction : t ∈ G.cliqueFinset 3 := by
          exact Finset.mem_filter.mp h_share_A |>.1;
        exact Finset.mem_filter.mp h_contradiction |>.2.2.le;
      linarith

-- TARGET: derive contradiction from disjointness (use hAD_disj, h_share_f)

/--
Bridges X_{A,B} are contained in trianglesSharingEdge A ∪ trianglesSharingEdge B.
This means they're covered when we cover S_A and S_B.
-/
lemma bridges_in_T_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) :
    X_ef G e f ⊆ trianglesSharingEdge G e ∪ trianglesSharingEdge G f := by
  intro t ht
  simp only [X_ef, Finset.mem_filter] at ht
  simp only [Finset.mem_union, trianglesSharingEdge, Finset.mem_filter]
  left
  exact ⟨ht.1, ht.2.1⟩

/--
All triangles in G are covered by T_A ∪ T_B ∪ T_C ∪ T_D.
-/
lemma path4_triangle_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    G.cliqueFinset 3 ⊆
      trianglesSharingEdge G A ∪ trianglesSharingEdge G B ∪
      trianglesSharingEdge G C ∪ trianglesSharingEdge G D := by
  intro t ht
  -- Every triangle must share an edge with some packing element (by maximality)
  by_contra h_none
  simp only [Finset.mem_union, not_or] at h_none
  -- h_none has structure (((¬A) ∧ (¬B)) ∧ (¬C)) ∧ (¬D)
  have h_not_A := h_none.1.1.1
  have h_not_B := h_none.1.1.2
  have h_not_C := h_none.1.2
  have h_not_D := h_none.2
  -- Extract: t doesn't share edge with any element
  have h_disj_A : (t ∩ A).card ≤ 1 := by
    simp only [trianglesSharingEdge, Finset.mem_filter, not_and] at h_not_A
    by_contra h; push_neg at h; exact (h_not_A ht) (Nat.lt_of_succ_le h)
  have h_disj_B : (t ∩ B).card ≤ 1 := by
    simp only [trianglesSharingEdge, Finset.mem_filter, not_and] at h_not_B
    by_contra h; push_neg at h; exact (h_not_B ht) (Nat.lt_of_succ_le h)
  have h_disj_C : (t ∩ C).card ≤ 1 := by
    simp only [trianglesSharingEdge, Finset.mem_filter, not_and] at h_not_C
    by_contra h; push_neg at h; exact (h_not_C ht) (Nat.lt_of_succ_le h)
  have h_disj_D : (t ∩ D).card ≤ 1 := by
    simp only [trianglesSharingEdge, Finset.mem_filter, not_and] at h_not_D
    by_contra h; push_neg at h; exact (h_not_D ht) (Nat.lt_of_succ_le h)
  -- Now show this contradicts maximality: we could add t to M
  have h_not_A : A ∉ trianglesSharingEdge G t := by
    simp_all +decide [ trianglesSharingEdge ];
    exact fun _ => by rw [ Finset.inter_comm ] ; linarith;
  have h_not_B : B ∉ trianglesSharingEdge G t := by
    simp_all +decide [ trianglesSharingEdge ];
    exact fun h => by rw [ Finset.inter_comm ] ; exact h_disj_B.trans_lt ( by decide ) ;
  have h_not_C : C ∉ trianglesSharingEdge G t := by
    unfold trianglesSharingEdge at *; simp_all +decide [ Finset.inter_comm ] ;
  have h_not_D : D ∉ trianglesSharingEdge G t := by
    simp_all +decide [ Finset.inter_comm, trianglesSharingEdge ]
  have h_disj_A : (A ∩ t).card ≤ 1 := by
    rwa [ Finset.inter_comm ]
  have h_disj_B : (B ∩ t).card ≤ 1 := by
    rwa [ Finset.inter_comm ]
  have h_disj_C : (C ∩ t).card ≤ 1 := by
    rwa [ Finset.inter_comm ]
  have h_disj_D : (D ∩ t).card ≤ 1 := by
    rwa [ Finset.inter_comm ]
  simp_all +decide [ Finset.inter_comm ];
  have h_union : M = {A, B, C, D} := by
    exact hpath.1;
  have h_not_max : trianglePackingNumber G ≥ (M ∪ {t}).card := by
    have h_not_max : isTrianglePacking G (M ∪ {t}) := by
      refine' ⟨ _, _ ⟩;
      · simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
        have := hM.1; simp_all +decide [ isTrianglePacking ] ;
        simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
      · simp_all +decide [ Set.Pairwise ];
        simp_all +decide [ Finset.inter_comm ];
        have := hpath.2; aesop;
    unfold trianglePackingNumber;
    have h_not_max : (M ∪ {t}).card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
      simp_all +decide [ isTrianglePacking ];
      exact ⟨ _, ⟨ h_not_max.1, by simpa [ Set.Pairwise ] using h_not_max.2 ⟩, rfl ⟩;
    have h_not_max : ∀ x ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset), x ≤ (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)).max.getD 0 := by
      intros x hx;
      have := Finset.le_max hx;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 ).powerset ) ) <;> aesop;
    exact h_not_max _ ‹_›;
  have h_card_M : M.card = trianglePackingNumber G := by
    exact hM.2;
  by_cases h : t ∈ M <;> simp_all +decide;
  exact absurd h_not_B ( by have := ht.card_eq; aesop )

-- TARGET: maximality argument

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: PATH_4 CASE
-- ══════════════════════════════════════════════════════════════════════════════

/--
τ(T_A) ≤ 2 + τ(bridges from A).
Since bridges from A only go to B, and X_{A,B} ⊆ T_A ∪ T_B, the bridge cost is shared.
-/
lemma tau_Te_le_4_for_endpoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumberOn G (trianglesSharingEdge G A) ≤ 4 := by
  -- T_A = S_A ∪ bridges(A)
  rw [Te_eq_Se_union_bridges G M A]
  -- bridges(A) ⊆ X_{A,B}
  have h_bridges : bridges G M A ⊆ X_ef G A B := path4_A_bridges_only_to_B G M A B C D hpath
  -- τ(S_A ∪ bridges) ≤ τ(S_A) + τ(bridges) ≤ 2 + 2 = 4
  calc triangleCoveringNumberOn G (S_e G M A ∪ bridges G M A)
      ≤ triangleCoveringNumberOn G (S_e G M A) + triangleCoveringNumberOn G (bridges G M A) := by
        apply tau_union_le_sum
    _ ≤ 2 + triangleCoveringNumberOn G (bridges G M A) := by
        have hA : A ∈ M := by rw [hpath.1]; simp
        linarith [tau_S_le_2 G M hM A hA]
    _ ≤ 2 + triangleCoveringNumberOn G (X_ef G A B) := by
        -- If τ(X_ef G A B) < τ(bridges G M A), then there exists an edge cover E' for X_ef G A B such that |E'| < τ(bridges G M A).
        by_contra h_contra
        obtain ⟨E', hE'⟩ : ∃ E' : Finset (Sym2 V), isTriangleCover G (X_ef G A B) E' ∧ E'.card < triangleCoveringNumberOn G (bridges G M A) := by
          have h_exists_E' : ∃ E' ∈ Finset.filter (fun E' => ∀ t ∈ X_ef G A B, ∃ e ∈ E', e ∈ t.sym2) (G.edgeFinset.powerset), E'.card = triangleCoveringNumberOn G (X_ef G A B) := by
            unfold triangleCoveringNumberOn at *;
            have := Finset.min_of_nonempty ( show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ X_ef G A B, ∃ e ∈ E', e ∈ t.sym2 ) ( G.edgeFinset.powerset ) ) ).Nonempty from ?_ );
            · obtain ⟨ a, ha ⟩ := this; rw [ ha ] ; simp +decide [ Option.getD_eq_iff ] ;
              have := Finset.mem_of_min ha; simp +decide at this;
              exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.trans ( by rfl ) ⟩;
            · simp +zetaDelta at *;
              refine' ⟨ G.edgeFinset, _ ⟩;
              simp +decide [ X_ef ];
              intro t ht htA htB; rcases Finset.card_eq_three.mp ht.2 with ⟨ a, b, c, hab, hbc, hac ⟩ ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
              exact ⟨ s(a, b), by aesop ⟩;
          obtain ⟨ E', hE₁, hE₂ ⟩ := h_exists_E'; use E'; unfold isTriangleCover; aesop;
        -- Since E' is a covering for X_ef G A B and bridges G M A is a subset of X_ef G A B, E' must also cover bridges G M A.
        have h_cover_bridges : isTriangleCover G (bridges G M A) E' := by
          unfold isTriangleCover at *; aesop;
        exact hE'.2.not_le ( le_triangleCoveringNumberOn G _ _ h_cover_bridges ) -- TARGET: monotonicity from h_bridges
    _ ≤ 2 + 2 := by
        have hA : A ∈ M := by rw [hpath.1]; simp
        have hB : B ∈ M := by rw [hpath.1]; simp
        linarith [tau_X_le_2 G M hM A B hA hB hpath.2.1]
    _ = 4 := by ring

/- Aristotle failed to find a proof. -/
/--
MAIN THEOREM: For path A—B—C—D, τ(G) ≤ 8.

Proof: Apply tau_S_le_2 to each of A, B, C, D.
Total: 2 + 2 + 2 + 2 = 8 edges.

Alternative view: τ(T_A) + τ(T_B) + τ(T_C) + τ(T_D) with overlaps handled.
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  -- Strategy: Cover all triangles using 2 edges per packing element
  -- Step 1: Get membership facts
  have hA : A ∈ M := by rw [hpath.1]; simp
  have hB : B ∈ M := by rw [hpath.1]; simp
  have hC : C ∈ M := by rw [hpath.1]; simp
  have hD : D ∈ M := by rw [hpath.1]; simp

  -- Step 2: All triangles are in T_A ∪ T_B ∪ T_C ∪ T_D
  have h_cover : G.cliqueFinset 3 ⊆
      trianglesSharingEdge G A ∪ trianglesSharingEdge G B ∪
      trianglesSharingEdge G C ∪ trianglesSharingEdge G D :=
    path4_triangle_partition G M hM A B C D hpath

  -- Step 3: Bound covering number
  -- τ(G) = τ(all triangles) ≤ τ(T_A ∪ T_B ∪ T_C ∪ T_D)
  -- ≤ τ(T_A) + τ(T_B) + τ(T_C) + τ(T_D)
  -- But this gives 4+4+4+4 = 16, too loose!

  -- BETTER: Use S_e decomposition directly
  -- Each S_e needs 2 edges, and bridges are covered by adjacent S_e covers
  sorry

-- MAIN TARGET: Construct 8-edge cover explicitly

end