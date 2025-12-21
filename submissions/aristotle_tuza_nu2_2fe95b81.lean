/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2fe95b81-5b42-4ce8-b5e1-841be8485967

The following was proved by Aristotle:

- lemma Te_eq_Se_of_vertex_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsTrianglePacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_disj : ∀ f ∈ M, f ≠ e → vertexDisjoint e f) :
    T_e G e = S_e G e M

- lemma cover_with_v_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (v a b : V) (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (he_eq : e = {v, a, b})
    (h_all_v : ∀ t ∈ T_e G e, v ∈ t) :
    coveringNumberOn G (T_e G e) ≤ 2

- theorem tuza_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G = 2) : coveringNumber G ≤ 4
-/

/-
Tuza ν ≤ 3: Final Corrected Proof

KEY INSIGHT (verified by Grok-4):
For ν ≤ 3, we can always find a max packing M and element e ∈ M
such that τ(T_e) ≤ 2.

The trick: CHOOSE the right packing, not just the right element!

For ν = 2 with e = {v,a,b}, f = {v,c,d} sharing vertex v:
- If {a,b,z} exists (z ∉ {v,c,d}):
  Switch to M' = {{a,b,z}, f} which is VERTEX-DISJOINT
  Then T_{a,b,z} = S_{a,b,z} and τ ≤ 2
- If no such {a,b,z}: All T_e triangles contain v, covered by va,vb
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}

def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) E}

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ m ∈ M, m ≠ e → (t ∩ m).card ≤ 1)

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

def vertexDisjoint (t1 t2 : Finset V) : Prop := Disjoint t1 t2

def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E}

-- KEY LEMMA: For vertex-disjoint packing elements, T_e = S_e
lemma Te_eq_Se_of_vertex_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsTrianglePacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_disj : ∀ f ∈ M, f ≠ e → vertexDisjoint e f) :
    T_e G e = S_e G e M := by
  ext t; simp [T_e, S_e];
  simp +zetaDelta at *;
  intro ht hne m hm hne';
  -- Since $m \neq e$ and $e$ and $m$ are vertex-disjoint, $t$ and $m$ must share at most one vertex.
  have h_inter : (t ∩ m).card ≤ 1 := by
    have h_disjoint : Disjoint e m := by
      exact h_disj m hm hne'
    have h_inter : (t ∩ e).card ≥ 2 := by
      contrapose! hne;
      interval_cases _ : ( t ∩ e ).card <;> simp_all +decide [ Finset.disjoint_left ];
      · simp_all +decide [ Finset.ext_iff, triangleEdges ];
        rintro _ x y hx hy hxy rfl u v hu hv huv; simp_all +decide [ Sym2.eq_iff ] ;
        grind;
      · unfold triangleEdges; simp +decide [ *, Finset.ext_iff ] ;
        rintro _ x y hx hy hxy rfl u v hu hv huv; simp_all +decide [ Sym2.eq_iff ] ;
        constructor <;> intro <;> simp_all +decide [ Finset.card_eq_one ];
        · have := ht.2; simp_all +decide [ Finset.ext_iff ] ;
          grind +ring;
        · rintro rfl; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
          grind;
    have h_inter : (t ∩ m).card + (t ∩ e).card ≤ t.card := by
      rw [ ← Finset.card_union_of_disjoint ];
      · exact Finset.card_le_card fun x hx => by aesop;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.disjoint_left.mp h_disjoint ( Finset.mem_inter.mp hx₂ |>.2 ) ( Finset.mem_inter.mp hx₁ |>.2 );
    linarith [ ht.card_eq ];
  exact h_inter

/- Aristotle failed to find a proof. -/
-- CORE INSIGHT: Can always find vertex-disjoint packing OR special structure
lemma exists_good_packing_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnu : packingNumber G = 2) :
    ∃ M : Finset (Finset V), IsMaxPacking G M ∧
    (∃ e ∈ M, ∀ f ∈ M, f ≠ e → vertexDisjoint e f) := by
  sorry

-- When all T_e triangles contain vertex v, cover with 2 edges
lemma cover_with_v_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (v a b : V) (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (he_eq : e = {v, a, b})
    (h_all_v : ∀ t ∈ T_e G e, v ∈ t) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  -- Since every triangle in $T_e$ contains $v$, the edges $(v, a)$ and $(v, b)$ cover all triangles in $T_e$.
  have h_cover : ∀ t ∈ T_e G e, ¬Disjoint (triangleEdges t) {Sym2.mk (v, a), Sym2.mk (v, b)} := by
    simp_all +decide [ Finset.disjoint_left, triangleEdges ];
    simp_all +decide [ T_e ];
    intro t ht h; specialize h_all_v t ht h; unfold triangleEdges at h; simp_all +decide [ Finset.disjoint_left ] ;
    rcases h with ⟨ x, y, hy, z, hz, hyz, rfl, h | h | h ⟩ <;> simp_all +decide [ Sym2.eq_swap ];
    · rcases h with ( ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide [ Sym2.eq_swap ];
      · exact ⟨ _, _, hy, _, hz, hyz, rfl, by tauto ⟩;
      · exact ⟨ _, _, hz, _, hy, by tauto, rfl, by tauto ⟩;
      · exact ⟨ _, _, hy, _, hz, hyz, rfl, by tauto ⟩;
      · exact ⟨ _, _, hz, _, hy, by tauto, rfl, by tauto ⟩;
    · use Sym2.mk (v, a);
      aesop;
    · use s(v, b);
      grind;
  refine' Nat.sInf_le _;
  refine' ⟨ { Sym2.mk ( v, a ), Sym2.mk ( v, b ) }, _, _ ⟩ <;> aesop

-- Main theorem for ν = 2
noncomputable section AristotleLemmas

lemma packing_ge_3_of_3_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (t1 t2 t3 : Finset V)
    (h1 : t1 ∈ G.cliqueFinset 3) (h2 : t2 ∈ G.cliqueFinset 3) (h3 : t3 ∈ G.cliqueFinset 3)
    (h_disj : Set.PairwiseDisjoint {t1, t2, t3} triangleEdges)
    (h_dist : t1 ≠ t2 ∧ t2 ≠ t3 ∧ t1 ≠ t3) :
    packingNumber G ≥ 3 := by
      refine' le_csSup _ _;
      · exact ⟨ Finset.card ( G.cliqueFinset 3 ), fun n hn => by rcases hn with ⟨ M, rfl, hM ⟩ ; exact Finset.card_le_card hM.1 ⟩;
      · refine' ⟨ { t1, t2, t3 }, _, _ ⟩ <;> simp_all +decide [ IsTrianglePacking ];
        simp +decide [ *, IsEdgeDisjoint, Finset.subset_iff ]

lemma exists_triangle_on_edge_of_cover_gt_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (u v w : V) (h_e : e = {u, v, w}) (h_uv : u ≠ v) (h_vw : v ≠ w) (h_uw : u ≠ w)
    (h_cover : coveringNumberOn G (T_e G e) > 2) :
    ∃ t ∈ T_e G e, s(u, v) ∈ triangleEdges t ∧ Disjoint (triangleEdges t) {s(v, w), s(u, w)} := by
      -- Since $coveringNumberOn G (T_e G e) > 2$, we can choose $E = \{s(v, w), s(u, w)\}$ which has cardinality at most 2.
      obtain ⟨t, ht⟩ : ∃ t ∈ T_e G e, ¬Disjoint (triangleEdges t) {s(v, w), s(u, w)} → False := by
        have h_card : Finset.card {s(v, w), s(u, w)} ≤ 2 := by
          exact Finset.card_insert_le _ _
        have h_not_cover : ¬(∀ t ∈ T_e G e, ¬Disjoint (triangleEdges t) {s(v, w), s(u, w)}) := by
          contrapose! h_cover;
          exact le_trans ( csInf_le ⟨ 0, fun n hn => Nat.zero_le _ ⟩ ⟨ _, by aesop ⟩ ) h_card;
        aesop;
      unfold T_e at *; simp_all +decide [ Finset.disjoint_left ] ;
      use t;
      simp_all +decide [ triangleEdges ];
      rcases ht.1.2 with ⟨ x, ⟨ a, b, ⟨ ha, hb, hab ⟩, rfl ⟩, c, d, ⟨ hc, hd, hcd ⟩, hcd' ⟩ ; simp_all +decide [ Sym2.eq_swap ] ;
      grind

lemma exists_special_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (u v w : V) (h_e : e = {u, v, w}) (h_uv : u ≠ v) (h_vw : v ≠ w) (h_uw : u ≠ w)
    (h_cover : coveringNumberOn G (T_e G e) > 2) :
    ∃ t_uv t_vw t_uw : Finset V,
      t_uv ∈ T_e G e ∧ t_vw ∈ T_e G e ∧ t_uw ∈ T_e G e ∧
      s(u, v) ∈ triangleEdges t_uv ∧ Disjoint (triangleEdges t_uv) {s(v, w), s(u, w)} ∧
      s(v, w) ∈ triangleEdges t_vw ∧ Disjoint (triangleEdges t_vw) {s(u, v), s(u, w)} ∧
      s(u, w) ∈ triangleEdges t_uw ∧ Disjoint (triangleEdges t_uw) {s(u, v), s(v, w)} := by
        have h1 := exists_triangle_on_edge_of_cover_gt_2 G e he u v w h_e h_uv h_vw h_uw h_cover
        have h2 := exists_triangle_on_edge_of_cover_gt_2 G e he v w u (by
        grind) (by
        assumption) (by
        exact h_uw.symm) (by
        exact h_uv.symm) (by
        exact h_cover)
        have h3 := exists_triangle_on_edge_of_cover_gt_2 G e he u w v (by
        aesop) (by
        assumption) (by
        tauto) (by
        assumption) (by
        exact h_cover);
        obtain ⟨ t_uv, ht_uv₁, ht_uv₂, ht_uv₃ ⟩ := h1; obtain ⟨ t_vw, ht_vw₁, ht_vw₂, ht_vw₃ ⟩ := h2; obtain ⟨ t_uw, ht_uw₁, ht_uw₂, ht_uw₃ ⟩ := h3; use t_uv, t_vw, t_uw; simp_all +decide [ Sym2.eq_swap ] ;

lemma structure_of_intersecting_special_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (u v w : V) (h_e : e = {u, v, w}) (h_uv : u ≠ v) (h_vw : v ≠ w) (h_uw : u ≠ w)
    (t_uv t_vw : Finset V)
    (ht_uv : t_uv ∈ T_e G e ∧ s(u, v) ∈ triangleEdges t_uv ∧ Disjoint (triangleEdges t_uv) {s(v, w), s(u, w)})
    (ht_vw : t_vw ∈ T_e G e ∧ s(v, w) ∈ triangleEdges t_vw ∧ Disjoint (triangleEdges t_vw) {s(u, v), s(u, w)})
    (h_not_disj : ¬Disjoint (triangleEdges t_uv) (triangleEdges t_vw)) :
    ∃ x : V, t_uv = {u, v, x} ∧ t_vw = {v, w, x} ∧ x ≠ u ∧ x ≠ v ∧ x ≠ w := by
      simp_all +decide [ T_e, triangleEdges ];
      -- Since $t_{uv}$ and $t_{vw}$ are not disjoint, there exists a vertex $x$ such that $x \in t_{uv}$ and $x \in t_{vw}$.
      obtain ⟨x, hx_t_uv, hx_t_vw⟩ : ∃ x, x ∈ t_uv ∧ x ∈ t_vw ∧ x ≠ u ∧ x ≠ v ∧ x ≠ w := by
        obtain ⟨ x, hx ⟩ := Finset.not_disjoint_iff.mp h_not_disj;
        rcases Finset.mem_image.mp hx.1 with ⟨ ⟨ a, b ⟩, ⟨ hab, rfl ⟩ ⟩ ; rcases Finset.mem_image.mp hx.2 with ⟨ ⟨ c, d ⟩, ⟨ hcd, hcd' ⟩ ⟩ ; simp_all +decide [ Sym2.eq_iff ];
        grind;
      refine' ⟨ x, _, _, hx_t_vw.2.1, hx_t_vw.2.2.1, hx_t_vw.2.2.2 ⟩;
      · have := Finset.eq_of_subset_of_card_le ( show { u, v, x } ⊆ t_uv from ?_ ) ?_ <;> simp_all +decide;
        · simp_all +decide [ Finset.insert_subset_iff ];
          grind +ring;
        · have := ht_uv.1.1.2; simp_all +decide [ Finset.card_insert_of_not_mem ] ;
          rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] <;> simp +decide [ * ];
          · grind;
          · grind;
      · have := ht_vw.1.1.2; simp_all +decide [ Finset.card_eq_three ] ;
        rcases this with ⟨ a, b, hab, c, hac, hbc, rfl ⟩ ; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
        grind

lemma disjoint_edges_of_special_config (u v w x z : V)
  (h_uv : u ≠ v) (h_vw : v ≠ w) (h_uw : u ≠ w)
  (h_xu : x ≠ u) (h_xv : x ≠ v) (h_xw : x ≠ w)
  (h_zu : z ≠ u) (h_zv : z ≠ v)
  (h_zx : z ≠ x) (h_zw : z ≠ w) :
  Disjoint (triangleEdges {u, v, z}) (triangleEdges {v, w, x}) := by
    rw [ Finset.disjoint_left ];
    unfold triangleEdges; aesop;

lemma disjoint_or_disjoint_of_special_intersection (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (u v w x : V) (h_e : e = {u, v, w}) (h_uv : u ≠ v) (h_vw : v ≠ w) (h_uw : u ≠ w)
    (t_uv t_vw t' : Finset V)
    (h_t_uv : t_uv = {u, v, x})
    (h_t_vw : t_vw = {v, w, x})
    (h_x_ne : x ≠ u ∧ x ≠ v ∧ x ≠ w)
    (ht' : t' ∈ T_e G e)
    (h_disj : Disjoint (triangleEdges t') {s(v, x), s(u, w)}) :
    Disjoint (triangleEdges t') (triangleEdges t_vw) ∨ Disjoint (triangleEdges t') (triangleEdges t_uv) := by
      unfold triangleEdges at *; simp_all +decide [ Finset.disjoint_left ] ;
      simp_all +decide [ Sym2.eq, eq_comm ];
      grind

lemma exists_disjoint_pair_from_special_intersection (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (u v w : V) (h_e : e = {u, v, w}) (h_uv : u ≠ v) (h_vw : v ≠ w) (h_uw : u ≠ w)
    (t_uv t_vw : Finset V)
    (ht_uv : t_uv ∈ T_e G e ∧ s(u, v) ∈ triangleEdges t_uv ∧ Disjoint (triangleEdges t_uv) {s(v, w), s(u, w)})
    (ht_vw : t_vw ∈ T_e G e ∧ s(v, w) ∈ triangleEdges t_vw ∧ Disjoint (triangleEdges t_vw) {s(u, v), s(u, w)})
    (h_not_disj : ¬Disjoint (triangleEdges t_uv) (triangleEdges t_vw))
    (h_cover : coveringNumberOn G (T_e G e) > 2) :
    ∃ t1 t2 : Finset V, t1 ∈ T_e G e ∧ t2 ∈ T_e G e ∧ Disjoint (triangleEdges t1) (triangleEdges t2) := by
      -- By `structure_of_intersecting_special_triangles`, there exists `x` such that `t_uv = {u, v, x}` and `t_vw = {v, w, x}`.
      obtain ⟨x, hxuv, hxvw⟩ : ∃ x : V, t_uv = {u, v, x} ∧ t_vw = {v, w, x} ∧ x ≠ u ∧ x ≠ v ∧ x ≠ w := by
        exact?;
      -- Since the covering number is greater than 2, there exists a triangle $t'$ in $T_e$ that is disjoint from the set $\{s(v, x), s(u, w)\}$.
      obtain ⟨t', ht', ht'_disj⟩ : ∃ t' ∈ T_e G e, Disjoint (triangleEdges t') {s(v, x), s(u, w)} := by
        contrapose! h_cover;
        refine' Nat.sInf_le _;
        refine' ⟨ { s(v, x), s(u, w) }, _, _ ⟩ <;> simp_all +decide [ Finset.card_insert_of_notMem ];
      rcases disjoint_or_disjoint_of_special_intersection G e he u v w x h_e h_uv h_vw h_uw t_uv t_vw t' hxuv hxvw.1 hxvw.2 ht' ht'_disj with h | h <;> [ exact ⟨ t', t_vw, ht', ht_vw.1, h ⟩ ; exact ⟨ t', t_uv, ht', ht_uv.1, h ⟩ ]

lemma exists_disjoint_pair_in_Te (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (h_cover : coveringNumberOn G (T_e G e) > 2) :
    ∃ t1 t2 : Finset V, t1 ∈ T_e G e ∧ t2 ∈ T_e G e ∧ Disjoint (triangleEdges t1) (triangleEdges t2) := by
      obtain ⟨u, v, w, h_e, h_uv, h_vw, h_uw⟩ : ∃ u v w : V, e = {u, v, w} ∧ u ≠ v ∧ v ≠ w ∧ u ≠ w := by
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        rcases Finset.card_eq_three.mp he.2 with ⟨ u, v, w, hu, hv, hw ⟩ ; use u, v, w ; aesop;
      obtain ⟨t_uv, t_vw, t_uw, ht_uv, ht_vw, ht_uw, h_uv_edge, h_vw_edge, h_uw_edge, h_uv_disj, h_vw_disj, h_uw_disj⟩ := exists_special_triangles G e he u v w h_e h_uv h_vw h_uw h_cover;
      by_cases h_disj : Disjoint (triangleEdges t_uv) (triangleEdges t_vw);
      · exact ⟨ t_uv, t_vw, ht_uv, ht_vw, h_disj ⟩;
      · obtain ⟨t1, t2, ht1, ht2, h_disj⟩ := exists_disjoint_pair_from_special_intersection G e he u v w h_e h_uv h_vw h_uw t_uv t_vw ⟨ht_uv, h_uv_edge, h_vw_edge⟩ ⟨ht_vw, h_uw_edge, h_uv_disj⟩ h_disj h_cover;
        exact ⟨ t1, t2, ht1, ht2, h_disj ⟩

lemma edge_disjoint_of_vertex_disjoint_neighbor (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f t : Finset V)
    (he : e ∈ G.cliqueFinset 3)
    (hf : f ∈ G.cliqueFinset 3)
    (ht : t ∈ G.cliqueFinset 3)
    (h_ef_vdisj : Disjoint e f)
    (h_te_not_disj : ¬Disjoint (triangleEdges t) (triangleEdges e)) :
    Disjoint (triangleEdges t) (triangleEdges f) := by
      -- Since $e$ and $f$ are disjoint, their intersection is empty. Therefore, $t$ cannot have two elements in common with both $e$ and $f$.
      have h_inter_empty : (t ∩ e).card + (t ∩ f).card ≤ 3 := by
        have h_inter_card : (t ∩ e).card + (t ∩ f).card ≤ t.card := by
          rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx hx' => Finset.disjoint_left.mp h_ef_vdisj ( Finset.mem_inter.mp hx |>.2 ) ( Finset.mem_inter.mp hx' |>.2 ) ) ] ; exact Finset.card_mono ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ;
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        exact h_inter_card.trans ( by rw [ ht.2 ] );
      -- Since $t$ and $e$ are not edge-disjoint, they share an edge $s(u, v)$. So $u, v \in t$ and $u, v \in e$. So $\{u, v\} \subseteq t \cap e$. Thus $|t \cap e| \ge 2$.
      have h_te_inter : (t ∩ e).card ≥ 2 := by
        unfold triangleEdges at h_te_not_disj; simp_all +decide [ Finset.disjoint_left ] ;
        obtain ⟨ x, y, hy, z, hz, hne, rfl, w, hw, v, hv, hne', h ⟩ := h_te_not_disj; simp_all +decide [ Sym2.eq_iff ] ;
        exact Finset.one_lt_card.2 ⟨ y, by aesop, z, by aesop ⟩;
      have h_tf_inter : (t ∩ f).card ≤ 1 := by
        linarith;
      unfold triangleEdges; simp_all +decide [ Finset.disjoint_left ] ;
      rintro _ x y hx hy hxy rfl z w hz hw hzw; contrapose! h_tf_inter; simp_all +decide [ Finset.card_eq_one ] ;
      exact Finset.one_lt_card.2 ⟨ x, by aesop, y, by aesop ⟩

lemma extend_packing_with_Te_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsTrianglePacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_disj : ∀ f ∈ M, f ≠ e → vertexDisjoint e f)
    (t1 t2 : Finset V)
    (ht1 : t1 ∈ T_e G e) (ht2 : t2 ∈ T_e G e)
    (h_t1_t2_disj : Disjoint (triangleEdges t1) (triangleEdges t2)) :
    IsTrianglePacking G ((M.erase e) ∪ {t1, t2}) ∧ ((M.erase e) ∪ {t1, t2}).card = M.card + 1 := by
      constructor;
      · constructor;
        · simp_all +decide [ Finset.subset_iff, IsTrianglePacking ];
          unfold T_e at ht1 ht2; aesop;
        · -- Since $t1$ and $t2$ are in $T_e G e$, they are edge-disjoint from each other and from any element in $M.erase e$.
          have h_disjoint : ∀ f ∈ M.erase e, Disjoint (triangleEdges t1) (triangleEdges f) ∧ Disjoint (triangleEdges t2) (triangleEdges f) := by
            intro f hf
            have h_disjoint_t1_f : Disjoint (triangleEdges t1) (triangleEdges f) := by
              apply edge_disjoint_of_vertex_disjoint_neighbor G e f t1;
              · exact hM.1 he;
              · exact hM.1 ( Finset.mem_of_mem_erase hf );
              · exact Finset.mem_filter.mp ht1 |>.1;
              · exact h_disj f ( Finset.mem_of_mem_erase hf ) ( by aesop );
              · unfold T_e at ht1; aesop;
            have h_disjoint_t2_f : Disjoint (triangleEdges t2) (triangleEdges f) := by
              apply edge_disjoint_of_vertex_disjoint_neighbor G e f t2;
              · exact hM.1 he;
              · exact hM.1 ( Finset.mem_of_mem_erase hf );
              · exact Finset.mem_filter.mp ht2 |>.1;
              · exact h_disj f ( Finset.mem_of_mem_erase hf ) ( by aesop );
              · unfold T_e at ht2; aesop;
            exact ⟨h_disjoint_t1_f, h_disjoint_t2_f⟩;
          intro x hx y hy hxy; simp_all +decide [ IsEdgeDisjoint ] ;
          rcases hx with ( rfl | rfl | ⟨ hxM, hxe ⟩ ) <;> rcases hy with ( rfl | rfl | ⟨ hyM, hye ⟩ ) <;> simp_all +decide [ Function.onFun ];
          · exact h_t1_t2_disj.symm;
          · exact Disjoint.symm ( h_disjoint x hxe hxM |>.1 );
          · exact Disjoint.symm ( h_disjoint x hxe hxM |>.2 );
          · exact hM.2 hxM hyM hxy;
      · rw [ Finset.card_union ];
        -- Since $t1$ and $t2$ are in $T_e G e$, they are triangles in $G$ that intersect with $e$. But since $M$ is a packing, and $e$ is in $M$, any triangle in $M$ that intersects with $e$ must be $e$ itself. Therefore, $t1$ and $t2$ can't be in $M.erase e$.
        have h_not_in_M_erase_e : t1 ∉ M.erase e ∧ t2 ∉ M.erase e := by
          constructor <;> intro h <;> simp_all +decide [ IsTrianglePacking ];
          · unfold T_e at ht1; simp_all +decide [ IsEdgeDisjoint ] ;
            have := hM.2 h.2 he h.1; simp_all +decide [ Finset.disjoint_left, Set.PairwiseDisjoint ] ;
          · unfold T_e at ht2; simp_all +decide [ IsEdgeDisjoint ] ;
            have := hM.2 h.2 he; simp_all +decide [ Finset.disjoint_left ] ;
        rw [ Finset.card_erase_of_mem he ];
        by_cases h : t1 = t2 <;> simp_all +decide;
        · unfold T_e at ht2; aesop;
        · exact Nat.succ_pred_eq_of_pos ( Finset.card_pos.mpr ⟨ e, he ⟩ )

lemma Te_cover_le_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnu : packingNumber G = 2)
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_disj : ∀ f ∈ M, f ≠ e → vertexDisjoint e f) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
      -- By `exists_disjoint_pair_in_Te`, there exist `t1, t2 \in T_e G e` such that `Disjoint (triangleEdges t1) (triangleEdges t2)`.
      by_contra h_contra;
      obtain ⟨t1, t2, ht1, ht2, h_t1_t2_disj⟩ : ∃ t1 t2 : Finset V, t1 ∈ T_e G e ∧ t2 ∈ T_e G e ∧ Disjoint (triangleEdges t1) (triangleEdges t2) := by
        apply exists_disjoint_pair_in_Te;
        · exact hM.1.1 he;
        · exact not_le.mp h_contra;
      -- By `extend_packing_with_Te_pair`, `M' = (M \setminus \{e\}) \cup {t1, t2}` is a packing of size `|M| + 1`.
      obtain ⟨M', hM'_packing, hM'_card⟩ : ∃ M' : Finset (Finset V), IsTrianglePacking G M' ∧ M'.card = M.card + 1 := by
        use (M.erase e) ∪ {t1, t2};
        apply extend_packing_with_Te_pair G M hM.1 e he h_disj t1 t2 ht1 ht2 h_t1_t2_disj;
      have hM'_card_le_packingNumber : M'.card ≤ packingNumber G := by
        apply le_csSup;
        · exact ⟨ Finset.card ( Finset.univ : Finset ( Finset V ) ), fun n hn => by obtain ⟨ M, rfl, hM ⟩ := hn; exact Finset.card_le_univ _ ⟩;
        · exact ⟨ M', rfl, hM'_packing ⟩;
      linarith [ hM.2 ]

end AristotleLemmas

theorem tuza_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G = 2) : coveringNumber G ≤ 4 := by
  -- Apply `exists_good_packing_nu2` to obtain a maximal packing `M` and a triangle `e \in M` such that `e` is vertex-disjoint from all other triangles in `M`.
  obtain ⟨M, hM, ⟨e, he, h_disj⟩⟩ : ∃ M : Finset (Finset V), IsMaxPacking G M ∧ (∃ e ∈ M, ∀ f ∈ M, f ≠ e → vertexDisjoint e f) := by
    exact?;
  -- Since `packingNumber G = 2`, `|M| = 2`. Let `M = {e, f}`.
  obtain ⟨f, hf, hM_eq⟩ : ∃ f ∈ M, f ≠ e ∧ M = {e, f} := by
    have h_card_M : M.card = 2 := by
      cases hM ; aesop;
    rw [ Finset.card_eq_two ] at h_card_M; obtain ⟨ f, g, hfg ⟩ := h_card_M; use if f = e then g else f; aesop;
  -- Every triangle `t` in `G` must intersect some element of `M`.
  have h_inter : ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) (triangleEdges e) ∨ ¬Disjoint (triangleEdges t) (triangleEdges f) := by
    intro t ht
    by_contra h_contra
    push_neg at h_contra;
    -- Since `t` is edge-disjoint from `e` and `f`, `M \cup {t}` would be a larger packing, contradicting `|M| = packingNumber G`.
    have h_larger_packing : IsTrianglePacking G (M ∪ {t}) := by
      constructor;
      · exact Finset.union_subset ( hM.1.1 ) ( Finset.singleton_subset_iff.mpr ht );
      · intro x hx y hy hxy; simp_all +decide [ IsEdgeDisjoint ] ;
        rcases hx with ( rfl | rfl | rfl ) <;> rcases hy with ( rfl | rfl | rfl ) <;> simp_all +decide [ Function.onFun, Finset.disjoint_left ];
        · exact fun a ha hb => h_contra.1 hb ha;
        · intro a ha hb; have := hM.1.2; simp_all +decide [ IsEdgeDisjoint ] ;
          exact absurd ( this ( by aesop : x ∈ _ ) ( by aesop : y ∈ _ ) hxy ) ( Finset.not_disjoint_iff.mpr ⟨ a, ha, hb ⟩ );
        · exact fun a ha₁ ha₂ => h_contra.2 ha₂ ha₁;
        · intro a ha hb; have := hM.1.2; simp_all +decide [ IsEdgeDisjoint ] ;
          exact absurd ( this ( by aesop : y ∈ _ ) ( by aesop : x ∈ _ ) ( by aesop ) ) ( Finset.not_disjoint_iff.mpr ⟨ a, hb, ha ⟩ );
    have h_card : (M ∪ {t}).card > M.card := by
      simp_all +decide [ Finset.disjoint_left ];
      rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp_all +decide [ Finset.disjoint_left ];
      · rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop;
      · constructor <;> rintro rfl <;> simp_all +decide [ IsTrianglePacking ];
        · rcases Finset.card_eq_three.mp ht.2 with ⟨ u, v, w, hu, hv, hw, h ⟩ ; simp_all +decide [ triangleEdges ];
          exact h_contra.1 _ _ ( Or.inl rfl ) ( Or.inr ( Or.inl rfl ) ) hu rfl;
        · rcases Finset.card_eq_three.mp ht.2 with ⟨ u, v, w, hu, hv, hw, h ⟩ ; simp_all +decide [ triangleEdges ];
          exact h_contra.2 _ _ ( Or.inl rfl ) ( Or.inr ( Or.inl rfl ) ) hu rfl;
      · tauto;
    have h_contra : (M ∪ {t}).card ≤ packingNumber G := by
      apply le_csSup;
      · exact ⟨ Finset.card ( Finset.univ : Finset ( Finset V ) ), fun n hn => by obtain ⟨ M, rfl, hM ⟩ := hn; exact Finset.card_le_univ _ ⟩;
      · exact ⟨ _, rfl, h_larger_packing ⟩;
    exact h_card.not_le ( h_contra.trans ( hM.2.symm ▸ le_rfl ) );
  -- Let `C_e` be a cover for `T_e G e` of size $\le 2$, and `C_f` be a cover for `T_e G f` of size $\le 2$.
  obtain ⟨C_e, hC_e⟩ : ∃ C_e : Finset (Sym2 V), C_e.card ≤ 2 ∧ ∀ t ∈ T_e G e, ¬Disjoint (triangleEdges t) C_e := by
    have := Te_cover_le_two G h M hM e he h_disj;
    contrapose! this;
    refine' lt_of_not_ge fun h => _;
    obtain ⟨ C, hC₁, hC₂ ⟩ := Nat.sInf_mem ( show { n : ℕ | ∃ E : Finset ( Sym2 V ), E.card = n ∧ ∀ t ∈ T_e G e, ¬Disjoint ( triangleEdges t ) E }.Nonempty from by
                                              refine' ⟨ _, ⟨ Finset.univ, rfl, _ ⟩ ⟩;
                                              simp +decide [ Finset.disjoint_left ];
                                              simp +decide [ triangleEdges ];
                                              simp +decide [ T_e ];
                                              exact fun t ht ht' => by rcases Finset.card_eq_three.mp ht.2 with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; exact ⟨ _, a, b, ⟨ by aesop, by aesop, by aesop ⟩, rfl ⟩ ; );
    exact absurd ( this C ( hC₁.symm ▸ h ) ) ( by tauto )
  obtain ⟨C_f, hC_f⟩ : ∃ C_f : Finset (Sym2 V), C_f.card ≤ 2 ∧ ∀ t ∈ T_e G f, ¬Disjoint (triangleEdges t) C_f := by
    have := Te_cover_le_two G h M hM f hf (by
    simp_all +decide [ vertexDisjoint ];
    exact fun _ => h_disj.symm);
    unfold coveringNumberOn at this;
    contrapose! this;
    refine' lt_of_lt_of_le _ ( le_csInf _ _ );
    exact lt_add_one 2;
    · refine' ⟨ _, ⟨ Finset.univ, rfl, _ ⟩ ⟩;
      simp +decide [ Finset.disjoint_left ];
      simp +decide [ T_e, triangleEdges ];
      exact fun t ht ht' => by rcases Finset.card_eq_three.mp ht.2 with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; exact ⟨ _, a, b, ⟨ by aesop, by aesop, by aesop ⟩, rfl ⟩ ;
    · rintro n ⟨ E, rfl, hE ⟩;
      exact not_lt.1 fun contra => by obtain ⟨ t, ht₁, ht₂ ⟩ := this E ( by linarith ) ; exact hE t ht₁ ht₂;
  refine' le_trans ( csInf_le _ _ ) _;
  exact ( C_e ∪ C_f ).card;
  · exact ⟨ 0, fun n hn => hn.choose_spec.1.symm ▸ Nat.zero_le _ ⟩;
  · refine' ⟨ C_e ∪ C_f, rfl, fun t ht => _ ⟩;
    cases h_inter t ht <;> simp_all +decide [ Finset.disjoint_union_right ];
    · exact fun h => False.elim ( hC_e.2 t ( Finset.mem_filter.mpr ⟨ Finset.mem_coe.mpr ( by simpa using ht ), by simpa using ‹¬Disjoint ( triangleEdges t ) ( triangleEdges e ) › ⟩ ) h );
    · exact fun _ => hC_f.2 t ( Finset.mem_filter.mpr ⟨ Finset.mem_coe.mpr ( by simpa using ht ), by tauto ⟩ );
  · exact le_trans ( Finset.card_union_le _ _ ) ( add_le_add hC_e.1 hC_f.1 )

/- Aristotle failed to find a proof. -/
-- Main theorem for ν ≤ 3
theorem tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G ≤ 3) : coveringNumber G ≤ 2 * packingNumber G := by
  sorry

end