/-
Slot52: Hyper-Focused tau_pair_le_4 Attack

CONTEXT:
- slot44 and slot51 proved 20+ helper lemmas
- The gap: tau(containing) ≤ 4, tau(avoiding) ≤ 2, but 4+2=6, not 4
- This file provides MAXIMUM scaffolding to help Aristotle focus

KEY INSIGHT FROM SLOT51:
- tau_avoiding_share_le_1: For SINGLE e, avoiding needs only 1 edge!
- So avoiding(T_pair) ≤ 1 + 1 = 2 ✓

THE REAL QUESTION:
Can we cover containing triangles with < 4 spokes?
OR can spokes ALSO cover some avoiding triangles? (No - avoiding don't contain v!)
OR is the avoiding set actually EMPTY for maximal packing?

STEPPING STONES:
1. If avoiding is empty → only 4 spokes needed → τ ≤ 4 ✓
2. If containing needs only 2 spokes → 2 + 2 = 4 ✓
3. Find 4-edge construction that covers both

All proven code from slot44, slot51 included.
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

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def trianglesContaining (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∈ t)

def trianglesAvoiding (triangles : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  triangles.filter (fun t => v ∉ t)

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

def isTriangleCover (G : SimpleGraph V) (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_union_le_sum (from slot44)
-- ══════════════════════════════════════════════════════════════════════════════

lemma isTriangleCover_union (G : SimpleGraph V) (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) :=
  ⟨ Finset.union_subset hA.1 hB.1, fun t ht => by cases' Finset.mem_union.mp ht with ht ht <;> [ exact hA.2 _ ht |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Finset.mem_union_left _ he₁, he₂ ⟩ ; exact hB.2 _ ht |> fun ⟨ e, he₁, he₂ ⟩ => ⟨ e, Finset.mem_union_right _ he₁, he₂ ⟩ ] ⟩

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

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- PROVEN in slot44

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: V-decomposition (from slot51)
-- ══════════════════════════════════════════════════════════════════════════════

lemma v_decomposition_union (triangles : Finset (Finset V)) (v : V) :
    triangles = trianglesContaining triangles v ∪ trianglesAvoiding triangles v := by
  ext t; by_cases h : v ∈ t <;> simp +decide [ h, trianglesContaining, trianglesAvoiding ]

theorem tau_v_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (v : V) :
    triangleCoveringNumberOn G triangles ≤
    triangleCoveringNumberOn G (trianglesContaining triangles v) +
    triangleCoveringNumberOn G (trianglesAvoiding triangles v) := by
  calc triangleCoveringNumberOn G triangles
      = triangleCoveringNumberOn G (trianglesContaining triangles v ∪ trianglesAvoiding triangles v) := by
        rw [← v_decomposition_union]
    _ ≤ triangleCoveringNumberOn G (trianglesContaining triangles v) +
        triangleCoveringNumberOn G (trianglesAvoiding triangles v) := tau_union_le_sum _ _ _

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_containing_v_in_pair_le_4 (from slot51)
-- 4 spoke edges cover all triangles containing v
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_containing_v_in_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (v : V) (hv_e : v ∈ e) (hv_f : v ∈ f) :
    triangleCoveringNumberOn G (trianglesContaining (T_pair G e f) v) ≤ 4 := by
  unfold triangleCoveringNumberOn trianglesContaining;
  simp +decide [ T_pair ];
  unfold trianglesSharingEdge;
  have h_four_edges : ∃ E' ∈ Finset.powerset G.edgeFinset, E'.card ≤ 4 ∧ ∀ t ∈ (G.cliqueFinset 3).filter (fun x => (x ∩ e).card ≥ 2) ∪ (G.cliqueFinset 3).filter (fun x => (x ∩ f).card ≥ 2), v ∈ t → ∃ e' ∈ E', ∀ a ∈ e', a ∈ t := by
    refine' ⟨ _, _, _, _ ⟩;
    exact Finset.image ( fun u => s(u, v) ) ( e ∪ f |> Finset.erase <| v );
    · simp_all +decide [ Finset.subset_iff, SimpleGraph.mem_edgeSet ];
      rintro _ x hx₁ hx₂ rfl; cases hx₂ <;> simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      · exact he.1 ‹_› hv_e ( by aesop );
      · exact hf.1 ( by aesop ) ( by aesop ) ( by aesop );
    · refine' le_trans ( Finset.card_image_le ) _;
      have := Finset.card_union_add_card_inter e f; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      linarith [ he.card_eq, hf.card_eq, show Finset.card ( e ∩ f ) ≥ 1 from Finset.card_pos.mpr ⟨ v, Finset.mem_inter.mpr ⟨ hv_e, hv_f ⟩ ⟩ ];
    · simp +zetaDelta at *;
      rintro t ( ⟨ ht₁, ht₂ ⟩ | ⟨ ht₁, ht₂ ⟩ ) hv_t <;> obtain ⟨ a, ha₁, ha₂ ⟩ := Finset.exists_mem_ne ht₂ v <;> use a <;> aesop;
  obtain ⟨ E', hE₁, hE₂, hE₃ ⟩ := h_four_edges;
  have h_min_le_four : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ (t : Finset V), t ∈ {x ∈ G.cliqueFinset 3 | (x ∩ e).card ≥ 2} ∪ {x ∈ G.cliqueFinset 3 | (x ∩ f).card ≥ 2} → v ∈ t → ∃ e ∈ E', ∀ a ∈ e, a ∈ t})).min ≤ E'.card := by
    exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', by aesop ⟩ );
  simp +zetaDelta at *;
  exact le_trans ( by cases h : Finset.min ( Finset.image Finset.card _ ) <;> aesop ) ( Nat.cast_le.mpr hE₂ )

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_avoiding_share_le_1 (from slot51)
-- KEY: For SINGLE triangle e, avoiding triangles need only 1 base edge!
-- ══════════════════════════════════════════════════════════════════════════════

lemma share_edge_avoid_vertex
    (e t : Finset V) (v : V)
    (he_card : e.card = 3)
    (h_share : (e ∩ t).card ≥ 2)
    (hv_in_e : v ∈ e)
    (hv_notin_t : v ∉ t) :
    e \ {v} ⊆ t := by
  intro x hx; simp_all +decide [ Finset.subset_iff ] ;
  contrapose! h_share;
  exact lt_of_le_of_lt ( Finset.card_le_card fun y hy => by aesop ) ( show Finset.card ( e.erase v \ { x } ) < 2 from by rw [ Finset.card_sdiff ] ; aesop )

lemma tau_avoiding_share_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3) (v : V) (hv : v ∈ e) :
    triangleCoveringNumberOn G (trianglesAvoiding (trianglesSharingEdge G e) v) ≤ 1 := by
  obtain ⟨u, w, hu, hw, hvu, hvw, huv⟩ : ∃ u w : V, u ∈ e ∧ w ∈ e ∧ v ≠ u ∧ v ≠ w ∧ u ≠ w ∧ e = {v, u, w} := by
    simp_all +decide [ SimpleGraph.isNClique_iff ];
    rcases Finset.card_eq_three.mp he.2 with ⟨ u, w, x, hu, hw, hx, h ⟩ ; aesop;
  have h_edge : ∀ t ∈ trianglesAvoiding (trianglesSharingEdge G e) v, {u, w} ⊆ t := by
    intro t ht
    obtain ⟨ht_containing, ht_not_containing⟩ : t ∈ trianglesSharingEdge G e ∧ v ∉ t := by
      unfold trianglesAvoiding at ht; aesop;
    unfold trianglesSharingEdge at ht_containing;
    have := Finset.eq_of_subset_of_card_le ( show t ∩ { u, w } ⊆ { u, w } from Finset.inter_subset_right ) ; aesop;
  unfold triangleCoveringNumberOn;
  by_cases h : Sym2.mk ( u, w ) ∈ G.edgeFinset <;> simp_all +decide;
  · have h_cover : {Sym2.mk (u, w)} ∈ Finset.filter (fun E' => ∀ t ∈ trianglesAvoiding (trianglesSharingEdge G {v, u, w}) v, ∃ e ∈ E', ∀ a ∈ e, a ∈ t) (Finset.powerset G.edgeFinset) := by
      simp_all +decide [ Finset.subset_iff ];
    have h_min : Finset.min (Finset.image Finset.card (Finset.filter (fun E' => ∀ t ∈ trianglesAvoiding (trianglesSharingEdge G {v, u, w}) v, ∃ e ∈ E', ∀ a ∈ e, a ∈ t) (Finset.powerset G.edgeFinset))) ≤ Finset.card {Sym2.mk (u, w)} := by
      exact Finset.min_le ( Finset.mem_image_of_mem _ h_cover );
    cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ trianglesAvoiding ( trianglesSharingEdge G { v, u, w } ) v, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> aesop;
  · simp_all +decide [ SimpleGraph.isNClique_iff ]

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_avoiding_v_in_pair_le_2 (from slot51)
-- 2 base edges cover all avoiding triangles
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_avoiding_v_in_pair_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) ≤ 2 := by
  rw [ show trianglesAvoiding ( T_pair G e f ) v = trianglesAvoiding ( trianglesSharingEdge G e ) v ∪ trianglesAvoiding ( trianglesSharingEdge G f ) v from ?_ ];
  · refine' le_trans ( tau_union_le_sum _ _ _ ) _;
    have h_e : e ∈ G.cliqueFinset 3 := hM.1.1 he;
    have h_f : f ∈ G.cliqueFinset 3 := hM.1.1 hf;
    refine' le_trans ( add_le_add ( tau_avoiding_share_le_1 G e h_e v _ ) ( tau_avoiding_share_le_1 G f h_f v _ ) ) _ <;> simp_all +decide [ Finset.ext_iff ];
    · specialize hv v; aesop;
    · specialize hv v; aesop;
  · unfold trianglesAvoiding T_pair trianglesSharingEdge; ext; aesop;

-- ══════════════════════════════════════════════════════════════════════════════
-- STEPPING STONE 1: Naive bound τ ≤ 6
-- This SHOULD be easy - just apply v-decomposition
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_pair_le_6 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 6 := by
  have h_e : e ∈ G.cliqueFinset 3 := hM.1.1 he
  have h_f : f ∈ G.cliqueFinset 3 := hM.1.1 hf
  have hv_e : v ∈ e := by simp_all +decide [Finset.ext_iff]
  have hv_f : v ∈ f := by simp_all +decide [Finset.ext_iff]
  calc triangleCoveringNumberOn G (T_pair G e f)
      ≤ triangleCoveringNumberOn G (trianglesContaining (T_pair G e f) v) +
        triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) := by
          rw [v_decomposition_union (T_pair G e f) v]
          exact tau_union_le_sum _ _ _
    _ ≤ 4 + 2 := Nat.add_le_add (tau_containing_v_in_pair_le_4 G e f h_e h_f v hv_e hv_f)
                                (tau_avoiding_v_in_pair_le_2 G M hM e f he hf hef v hv)
    _ = 6 := rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- STEPPING STONE 2: If avoiding is empty, τ ≤ 4
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_pair_le_4_of_avoiding_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (v : V) (hv_e : v ∈ e) (hv_f : v ∈ f)
    (h_empty : trianglesAvoiding (T_pair G e f) v = ∅) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  rw [v_decomposition_union (T_pair G e f) v, h_empty, Finset.union_empty]
  exact tau_containing_v_in_pair_le_4 G e f he hf v hv_e hv_f

-- ══════════════════════════════════════════════════════════════════════════════
-- STEPPING STONE 3: If containing needs only 2 edges, τ ≤ 4
-- This could happen if all containing triangles share a common edge through v
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_pair_le_4_of_containing_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (h_small : triangleCoveringNumberOn G (trianglesContaining (T_pair G e f) v) ≤ 2) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  calc triangleCoveringNumberOn G (T_pair G e f)
      ≤ triangleCoveringNumberOn G (trianglesContaining (T_pair G e f) v) +
        triangleCoveringNumberOn G (trianglesAvoiding (T_pair G e f) v) := by
          rw [v_decomposition_union (T_pair G e f) v]
          exact tau_union_le_sum _ _ _
    _ ≤ 2 + 2 := Nat.add_le_add h_small (tau_avoiding_v_in_pair_le_2 G M hM e f he hf hef v hv)
    _ = 4 := rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- STEPPING STONE 4: Direct 4-edge construction
-- Try: 2 spoke edges + 2 base edges
-- ══════════════════════════════════════════════════════════════════════════════

/--
Attempt: Use {v,a}, {v,c}, {a,b}, {c,d} where e = {v,a,b}, f = {v,c,d}
- {a,b} covers e and all avoiding triangles sharing {a,b} with e
- {c,d} covers f and all avoiding triangles sharing {c,d} with f
- {v,a} covers some containing triangles
- {v,c} covers some containing triangles

QUESTION: Does this cover ALL containing triangles?
A containing triangle must contain v and share edge with e or f.
- If it shares {v,a} or {v,b} with e: {v,a} might not cover {v,b,x}!
- If it shares {v,c} or {v,d} with f: {v,c} might not cover {v,d,x}!

So this doesn't work in general. Need different approach.
-/

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY QUESTION: When is avoiding empty?
-- ══════════════════════════════════════════════════════════════════════════════

/--
An avoiding triangle t must:
1. Share edge with e or f (so (t ∩ e).card ≥ 2 or (t ∩ f).card ≥ 2)
2. Not contain v (so v ∉ t)

For e = {v,a,b}: if t shares edge with e but v ∉ t, then t shares {a,b}
So t = {a,b,x} for some x ≠ v.

For such t to exist as a triangle, we need G.Adj a b (yes, in e) and
G.Adj a x, G.Adj b x for some x.

MAXIMALITY ARGUMENT:
If t = {a,b,x} exists and is edge-disjoint from M \ {e}, could we swap e for t?
- M' = (M \ {e}) ∪ {t} is still a packing (t shares edge with e, so same size)
- But t shares edge {a,b} with e, so (t ∩ e).card = 2

Actually swapping e for t gives same size packing, not contradiction.

The key might be that t must share edge with ANOTHER packing element,
which constrains x significantly.
-/

-- MAIN TARGET: Try to prove avoiding is empty via maximality
theorem avoiding_empty_of_maximal (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    trianglesAvoiding (T_pair G e f) v = ∅ := by
  sorry
  -- HINT: If t ∈ Avoiding(T_pair, v), then t shares base edge with e or f
  -- Consider what happens when we try to add t to M or swap
  -- The maximality of M should constrain this

-- ══════════════════════════════════════════════════════════════════════════════
-- ALTERNATIVE: Maybe avoiding is NOT empty, but we can cover with 0 extra edges
-- ══════════════════════════════════════════════════════════════════════════════

/--
Alternative approach: The base edges {a,b} and {c,d} are ALSO part of e and f.
Maybe some of the 4 spoke edges from tau_containing_v_in_pair_le_4 are redundant
because {a,b} or {c,d} already cover those triangles?

Actually no - containing triangles CONTAIN v, so they must have a spoke edge.
Base edges {a,b}, {c,d} don't contain v, so can't be in containing triangles.
-/

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  have h_e : e ∈ G.cliqueFinset 3 := hM.1.1 he
  have h_f : f ∈ G.cliqueFinset 3 := hM.1.1 hf
  have hv_e : v ∈ e := by simp_all +decide [Finset.ext_iff]
  have hv_f : v ∈ f := by simp_all +decide [Finset.ext_iff]
  -- Use avoiding_empty_of_maximal
  have h_empty := avoiding_empty_of_maximal G M hM e f he hf hef v hv
  exact tau_pair_le_4_of_avoiding_empty G e f h_e h_f v hv_e hv_f h_empty

end
