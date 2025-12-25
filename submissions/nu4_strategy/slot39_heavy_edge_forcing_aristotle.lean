/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f71e7003-3204-4746-8e88-8b5735c628af

The following was proved by Aristotle:

- theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B

- lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2

- lemma no_edge_sharing_implies_single_vertex_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_no_edge : noEdgeSharing M e) :
    ∀ t ∈ X_ef G e f, (t ∩ e).card = 2 ∧ (t ∩ f).card = 2 ∧ (e ∩ f).card = 1

- lemma single_vertex_bridge_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_single : (e ∩ f).card = 1) :
    ∃ v, v ∈ e ∧ v ∈ f ∧ ∀ t ∈ X_ef G e f, v ∈ t

- lemma tau_Te_le_2_no_edge_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_no_edge : noEdgeSharing M e) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2

- theorem heavy_implies_edge_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_heavy : triangleCoveringNumberOn G (trianglesSharingEdge G e) ≥ 3) :
    ∃ f ∈ M, f ≠ e ∧ sharesEdge e f

- theorem no_edge_sharing_implies_light (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_no_edge : noEdgeSharing M e) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2

- theorem tuza_nu4_no_edge_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_no_edges : ∀ e ∈ M, noEdgeSharing M e) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8
-/

/-
Tuza ν=4 Strategy - Slot 39: Heavy Edge Forcing Lemma

NOVEL INSIGHT (from Gemini consultation):
If τ(T_e) ≥ 3 for some packing element e, what structure does this FORCE?

HYPOTHESIS:
If τ(T_e) ≥ 3, then e must share an EDGE (not just a vertex) with another element.

CONTRAPOSITIVE:
If e shares only vertices (no edges) with all other elements, then τ(T_e) ≤ 2.

WHY THIS IS USEFUL:
- If proven, elements with τ(T_e) ≥ 3 form edge-sharing pairs
- Edge-sharing pairs have very constrained bridge structure
- This reduces to the τ(T_pair) ≤ 4 case

PROOF STRATEGY:
1. If e shares no edges with M, then all bridges X(e,f) must share only 1 vertex
2. Bridges through single vertex v can be covered efficiently
3. Combined with τ(S_e) ≤ 2, get τ(T_e) ≤ 2

SCAFFOLDING: Full proofs from slots 6, 16, 29
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

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∃ f ∈ M, f ≠ e ∧ (t ∩ f).card ≥ 2)

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- Key definitions for this slot
def sharesEdge (e f : Finset V) : Prop := (e ∩ f).card ≥ 2

def sharesOnlyVertex (e f : Finset V) : Prop := (e ∩ f).card = 1

def noEdgeSharing (M : Finset (Finset V)) (e : Finset V) : Prop :=
  ∀ f ∈ M, f ≠ e → ¬sharesEdge e f

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slots 6, 16, 29)
-- ══════════════════════════════════════════════════════════════════════════════

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

lemma isTriangleCover_iff_mem_filter (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V)) (E' : Finset (Sym2 V)) :
    isTriangleCover G A E' ↔ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)) := by
  unfold isTriangleCover; aesop

lemma le_triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : isTriangleCover G A E') :
    triangleCoveringNumberOn G A ≤ E'.card := by
  unfold triangleCoveringNumberOn
  have h_mem : E' ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) := by
    exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h.1, h.2 ⟩
  have := Finset.min_le ( Finset.mem_image_of_mem Finset.card h_mem )
  rw [ WithTop.le_coe_iff ] at this; aesop

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

lemma isTriangleCover_union (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  unfold isTriangleCover at *
  grind

lemma isTriangleCover_subset (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : A ⊆ B) (hCover : isTriangleCover G B E') :
    isTriangleCover G A E' := by
  exact ⟨ hCover.1, fun t ht => hCover.2 t ( h ht ) ⟩

-- PROVEN: tau_union_le_sum (from slot 16/29)
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
lemma bridges_absorbed_by_Se_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_no_edge : noEdgeSharing M e) :
    ∃ E' : Finset (Sym2 V), isTriangleCover G (S_e G M e ∪ bridges G M e) E' ∧ E'.card ≤ 2 := by
  sorry

-- TARGET: Single cover handles both S_e and bridges

/--
COROLLARY: τ(T_e) ≤ 2 when no edge sharing

Since T_e = S_e ∪ bridges and the same 2-edge cover works for both,
we get τ(T_e) ≤ 2 without adding bridge cost.
-/
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
  -- Apply the lemma that the covering number of a union is at most the sum of the covering numbers.
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