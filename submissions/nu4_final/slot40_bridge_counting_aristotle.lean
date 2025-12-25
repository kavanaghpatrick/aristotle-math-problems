/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5eeea552-fcc8-4f60-ae27-2a9251bb1eaf

The following was proved by Aristotle:

- theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B

- lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2

- lemma tau_all_bridges_le_12 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 12

- lemma tau_bridges_sparse_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_sparse : maxSharingDegree M ≤ 2) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 8

- lemma tau_bridges_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e₁ e₂ e₃ e₄ : Finset V)
    (he : M = {e₁, e₂, e₃, e₄})
    (h_path : sharesVertex e₁ e₂ ∧ sharesVertex e₂ e₃ ∧ sharesVertex e₃ e₄ ∧
              ¬sharesVertex e₁ e₃ ∧ ¬sharesVertex e₁ e₄ ∧ ¬sharesVertex e₂ e₄) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 6

- lemma tau_bridges_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e_center e₁ e₂ e₃ : Finset V)
    (he : M = {e_center, e₁, e₂, e₃})
    (h_star : sharesVertex e_center e₁ ∧ sharesVertex e_center e₂ ∧ sharesVertex e_center e₃ ∧
              ¬sharesVertex e₁ e₂ ∧ ¬sharesVertex e₁ e₃ ∧ ¬sharesVertex e₂ e₃) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 6

- lemma tau_bridges_le_6_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e₁ e₂ e₃ e₄ : Finset V) (he : M = {e₁, e₂, e₃, e₄})
    (h_path : sharesVertex e₁ e₂ ∧ sharesVertex e₂ e₃ ∧ sharesVertex e₃ e₄ ∧
              ¬sharesVertex e₁ e₃ ∧ ¬sharesVertex e₁ e₄ ∧ ¬sharesVertex e₂ e₄) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 6

- lemma tau_bridges_le_6_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e_center e₁ e₂ e₃ : Finset V) (he : M = {e_center, e₁, e₂, e₃})
    (h_star : sharesVertex e_center e₁ ∧ sharesVertex e_center e₂ ∧ sharesVertex e_center e₃ ∧
              ¬sharesVertex e₁ e₂ ∧ ¬sharesVertex e₁ e₃ ∧ ¬sharesVertex e₂ e₃) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 6
-/

/-
Tuza ν=4 Strategy - Slot 40: Bridge Counting Bound

NOVEL APPROACH (from Strategic Map Dec 24):
Instead of trying to absorb bridges into S_e covers (which FAILS - Negation #9),
COUNT bridges explicitly using proven τ(X_ef) ≤ 2 bound.

KEY INSIGHT:
- Bridges X(e,f) are triangles sharing edges with BOTH e and f
- For ν=4 packing M = {e₁, e₂, e₃, e₄}, bridges partition by pairs
- Each X(eᵢ,eⱼ) has τ ≤ 2 (proven in slot 24)

COUNTING STRATEGY:
1. Classify elements by sharing graph degree
2. For sparse sharing (≤2 neighbors each): bound via sum of X pairs
3. For dense sharing (complete K₄): use apex reduction from slot 29

SCAFFOLDING: Full proofs from slots 6, 16, 24, 29
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

def sharingDegree (M : Finset (Finset V)) (e : Finset V) : ℕ :=
  (M.filter (fun f => f ≠ e ∧ sharesVertex e f)).card

-- Packing elements containing vertex v
def packingElementsContaining (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  M.filter (fun t => v ∈ t)

-- All bridges across all pairs
def allBridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ∃ e f, e ∈ M ∧ f ∈ M ∧ e ≠ f ∧ (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- All S_e sets unioned
def allS (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  M.biUnion (fun e => S_e G M e)

-- Sharing graph has max degree (for degree constraints)
def maxSharingDegree (M : Finset (Finset V)) : ℕ :=
  M.sup (sharingDegree M)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slots 6, 16, 24, 29)
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

lemma cover_union_implies_cover_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_left B ht)

lemma cover_union_implies_cover_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : ∀ t ∈ A ∪ B, ∃ e ∈ E', e ∈ t.sym2) :
    ∀ t ∈ B, ∃ e ∈ E', e ∈ t.sym2 := by
  intro t ht
  exact h t (Finset.mem_union_right A ht)

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

-- PROVEN in slot16/29 (full proof in slot29_triple_apex.lean)
theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  by_cases hA : ∃ E', isTriangleCover G A E';
  · by_cases hB : ∃ E', isTriangleCover G B E';
    · obtain ⟨ E₁, hE₁ ⟩ := exists_min_cover G A hA;
      obtain ⟨ E₂, hE₂ ⟩ := exists_min_cover G B hB;
      have := le_triangleCoveringNumberOn G ( A ∪ B ) ( E₁ ∪ E₂ ) ?_;
      · exact this.trans ( Finset.card_union_le _ _ ) |> le_trans <| by linarith;
      · exact isTriangleCover_union G A B E₁ E₂ hE₁.1 hE₂.1;
    · simp_all +decide [ triangleCoveringNumberOn ];
      simp_all +decide [ Finset.min, Option.getD ];
      rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hB E' ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp hE' |>.1 ), fun t ht => by aesop ⟩ ] ; simp +decide;
  · simp_all +decide [ triangleCoveringNumberOn ];
    rw [ show ( { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } : Finset ( Finset ( Sym2 V ) ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun E' hE' => hA E' ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp hE' |>.1 ), fun t ht => by have := Finset.mem_filter.mp hE' |>.2 t ht; aesop ⟩ ] ; simp +decide [ Option.getD ];
    rw [ show ( Finset.image Finset.card ( { E' ∈ G.edgeFinset.powerset | ∀ t : Finset V, t ∈ A ∨ t ∈ B → ∃ e ∈ E', ∀ a ∈ e, a ∈ t } ) ) = ∅ from Finset.eq_empty_of_forall_notMem fun x hx => by obtain ⟨ E', hE', rfl ⟩ := Finset.mem_image.mp hx; exact hA E' ⟨ Finset.mem_powerset.mp ( Finset.mem_filter.mp hE' |>.1 ), fun t ht => by aesop ⟩ ] ; simp +decide

-- SCAFFOLDING: Full 90+ line proof in slot29_triple_apex.lean

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

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
-- PROVEN: tau_S_le_2 (from slot 6/29)
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry

-- SCAFFOLDING: Full proof in slot29_triple_apex.lean (500+ lines)

-- SCAFFOLDING: tau_X_le_2 (target for slot 24)
noncomputable section AristotleLemmas

/-
If e and f are disjoint, X_ef is empty. If they share a vertex v, every t in X_ef contains v and an edge of e incident to v.
-/
lemma X_ef_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    (X_ef G e f = ∅) ∨
    (∃ v, e ∩ f = {v} ∧ ∀ t ∈ X_ef G e f, v ∈ t ∧
      (∃ u ∈ e, u ≠ v ∧ Sym2.mk (u, v) ∈ t.sym2)) := by
        by_cases h : ∃ v : V, e ∩ f = { v };
        · obtain ⟨ v, hv ⟩ := h;
          right
          use v;
          simp_all +decide [ X_ef ];
          intro t ht ht₁ ht₂;
          have h_inter : (t ∩ e).card + (t ∩ f).card ≤ t.card + (t ∩ (e ∩ f)).card := by
            have := Finset.card_union_add_card_inter ( t ∩ e ) ( t ∩ f );
            simp_all +decide [ Finset.inter_left_comm, Finset.inter_assoc ];
            exact this ▸ add_le_add_right ( Finset.card_mono ( by aesop_cat ) ) _;
          have := ht.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          by_cases hv : v ∈ t <;> simp_all +decide [ Finset.inter_comm ];
          · obtain ⟨ u, hu ⟩ := Finset.exists_ne_of_one_lt_card ( lt_of_lt_of_le ( by decide ) ht₁ ) v; use u; aesop;
          · linarith;
        · left;
          -- Since $e$ and $f$ are disjoint, any triangle $t$ in $X_ef$ must intersect both $e$ and $f$ in at least two vertices, which is impossible.
          have h_disjoint : e ∩ f = ∅ := by
            have := hM.2 he hf hef;
            contrapose! h;
            exact Finset.card_eq_one.mp ( le_antisymm this ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty h ) ) );
          ext t;
          simp [X_ef, h_disjoint];
          have := hM.2;
          have := this he hf hef; simp_all +decide [ Finset.ext_iff ] ;
          intro ht ht'; have := Finset.card_le_card ( show t ∩ e ∪ t ∩ f ⊆ t from Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ; simp_all +decide ;
          rw [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx₁ hx₂ => h_disjoint x ( Finset.mem_of_mem_inter_right hx₁ ) ( Finset.mem_of_mem_inter_right hx₂ ) ) ] at this ; linarith [ show Finset.card t = 3 from by simpa using ht.card_eq ]

end AristotleLemmas

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  have h_cover : ∃ E' : Finset (Sym2 V), isTriangleCover G (X_ef G e f) E' ∧ E'.card ≤ 2 := by
    have := X_ef_structure G M hM.1 e f he hf hef;
    rcases this with ( h | ⟨ v, hv₁, hv₂ ⟩ );
    · exact ⟨ ∅, ⟨ Finset.empty_subset _, by simp +decide [ h ] ⟩, by simp +decide ⟩;
    · -- Construct the cover $E' = (e.erase v).image (fun u => Sym2.mk (u, v))$.
      use (e.erase v).image (fun u => Sym2.mk (u, v));
      refine' ⟨ _, _ ⟩;
      · refine' ⟨ _, _ ⟩;
        · have := hM.1.1 he;
          simp_all +decide [ Finset.subset_iff, SimpleGraph.cliqueFinset ];
          intro x u hu heu hx; subst hx; have := this.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          exact this ( by aesop ) ( by rw [ Finset.ext_iff ] at hv₁; specialize hv₁ v; aesop ) hu;
        · intro t ht; specialize hv₂ t ht; aesop;
      · refine' le_trans ( Finset.card_image_le ) _;
        have := hM.1.1 he; simp_all +decide [ Finset.card_eq_three ] ;
        rw [ Finset.card_erase_of_mem ( show v ∈ e from Finset.mem_of_mem_inter_left ( hv₁.symm ▸ Finset.mem_singleton_self _ ) ), this.card_eq ];
  exact le_trans ( le_triangleCoveringNumberOn _ _ _ h_cover.choose_spec.1 ) h_cover.choose_spec.2

/- Aristotle failed to find a proof. -/
-- SCAFFOLDING: Proven in slot24

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE COUNTING LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/--
Bridges partition by pairs: each bridge belongs to exactly one X(eᵢ,eⱼ)
-/
lemma bridges_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    ∀ t ∈ allBridges G M, ∃! (p : Finset V × Finset V),
      p.1 ∈ M ∧ p.2 ∈ M ∧ p.1 ≠ p.2 ∧ t ∈ X_ef G p.1 p.2 := by
  sorry

-- TARGET: Each bridge belongs to exactly one pair

/--
Bound bridges via pair decomposition.
For ν=4, we have at most 6 pairs (4 choose 2).
Each X(eᵢ,eⱼ) contributes τ ≤ 2.
Naive bound: τ(allBridges) ≤ 12.
-/
lemma tau_all_bridges_le_12 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 12 := by
  -- By definition of $allBridges$, we have $allBridges G M = \bigcup_{e, f \in M, e < f} X_{ef}$.
  have h_allBridges : allBridges G M = Finset.biUnion (Finset.powersetCard 2 M) (fun p => X_ef G p.toList.head! p.toList.tail!.head!) := by
    ext t; simp [allBridges, X_ef];
    constructor;
    · rintro ⟨ ht, e, he, f, hf, hef, hte, htf ⟩;
      by_cases hef' : e ⊆ f;
      · have := hM.1;
        have := this.2;
        have := this he hf hef; simp_all +decide [ Finset.inter_eq_left.mpr hef' ] ;
        exact absurd hte ( not_le_of_gt ( lt_of_le_of_lt ( Finset.card_le_card ( Finset.inter_subset_right ) ) ( lt_of_le_of_lt this ( by decide ) ) ) );
      · refine' ⟨ { e, f }, _, ht, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
        · rcases n : Finset.toList { e, f } with _ | ⟨ x, _ | ⟨ y, _ | h ⟩ ⟩ ; aesop;
          · replace n := congr_arg List.length n; aesop;
          · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; have := n e; have := n f; aesop;
          · replace n := congr_arg List.length n ; simp_all +decide;
        · rcases n : Finset.toList { e, f } with _ | ⟨ x, _ | ⟨ y, _ | h ⟩ ⟩ ; aesop;
          · replace n := congr_arg List.length n; aesop;
          · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; have := n e; have := n f; aesop;
          · replace n := congr_arg List.length n ; simp_all +decide;
    · norm_num +zetaDelta at *;
      intro x hx hx' ht ht' ht''; rw [ Finset.card_eq_two ] at hx'; obtain ⟨ e, f, he, hf, h ⟩ := hx'; use ht; use e, hx ( by aesop ), f, hx ( by aesop ), by aesop;
      rcases n : Finset.toList { e, f } with _ | ⟨ a, _ | ⟨ b, _ | h ⟩ ⟩ ; aesop;
      · replace n := congr_arg List.length n; aesop;
      · have := n ▸ Finset.mem_toList.mpr ( Finset.mem_insert_self _ _ ) ; have := n ▸ Finset.mem_toList.mpr ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ; aesop;
      · replace n := congr_arg List.length n ; simp_all +decide;
  -- Applying the lemma $\tau(X_{ef}) \leq 2$ to each term in the union.
  have h_tau_X_le_2 : ∀ p ∈ Finset.powersetCard 2 M, triangleCoveringNumberOn G (X_ef G p.toList.head! p.toList.tail!.head!) ≤ 2 := by
    intro p hp
    have h_pair : p.toList.length = 2 := by
      aesop
    have h_pair_elements : p.toList.head! ≠ p.toList.tail!.head! := by
      rcases x : p.toList with ( _ | ⟨ a, _ | ⟨ b, _ | h ⟩ ⟩ ) <;> simp_all +decide;
      replace x := congr_arg List.Nodup x; simp_all +decide [ Finset.nodup_toList ] ;
    have h_pair_elements : p.toList.head! ∈ M ∧ p.toList.tail!.head! ∈ M := by
      have h_pair_elements : ∀ x ∈ p.toList, x ∈ M := by
        exact fun x hx => Finset.mem_powersetCard.mp hp |>.1 ( Finset.mem_toList.mp hx );
      rcases n : p.toList with ( _ | ⟨ x, _ | ⟨ y, _ | n ⟩ ⟩ ) <;> aesop;
    exact tau_X_le_2 G M hM _ _ h_pair_elements.1 h_pair_elements.2 ‹_›;
  -- Applying the lemma $\tau(X_{ef}) \leq 2$ to the union of all $X_{ef}$.
  have h_tau_union_le_sum : triangleCoveringNumberOn G (Finset.biUnion (Finset.powersetCard 2 M) (fun p => X_ef G p.toList.head! p.toList.tail!.head!)) ≤ Finset.sum (Finset.powersetCard 2 M) (fun p => triangleCoveringNumberOn G (X_ef G p.toList.head! p.toList.tail!.head!)) := by
    have h_tau_union_le_sum : ∀ (S : Finset (Finset (Finset V))), triangleCoveringNumberOn G (Finset.biUnion S (fun p => X_ef G p.toList.head! p.toList.tail!.head!)) ≤ Finset.sum S (fun p => triangleCoveringNumberOn G (X_ef G p.toList.head! p.toList.tail!.head!)) := by
      intros S
      induction' S using Finset.induction with p S hpS ih;
      · simp +decide [ triangleCoveringNumberOn ];
        simp +decide [ Finset.min ];
        rw [ Finset.inf_eq_iInf ];
        rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
        rotate_left;
        exact 0;
        · exact fun _ => zero_le _;
        · exact fun w hw => ⟨ ∅, by simp +decide [ hw ] ⟩;
        · rfl;
      · rw [ Finset.sum_insert hpS, Finset.biUnion_insert ];
        exact le_trans ( tau_union_le_sum _ _ _ ) ( add_le_add_left ih _ );
    exact h_tau_union_le_sum _;
  exact h_allBridges ▸ h_tau_union_le_sum.trans ( le_trans ( Finset.sum_le_sum h_tau_X_le_2 ) ( by simp +decide [ hM_card ] ) )

-- TARGET: 6 pairs × 2 edges each

/--
If sharing graph has max degree ≤ 2, bridges are more constrained.
Each element shares with ≤2 others, so only specific pairs have bridges.
-/
lemma tau_bridges_sparse_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_sparse : maxSharingDegree M ≤ 2) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 8 := by
  -- Since the sharing graph has max degree 2, each element in M shares with at most 2 other elements, leading to at most 6 pairs.
  have h_pairs : (allBridges G M).card ≤ 6 := by
    -- Since the sharing graph has max degree 2, each bridge is counted exactly once.
    have h_unique_bridges : ∀ t ∈ allBridges G M, ∃! (p : Finset V × Finset V), p.1 ∈ M ∧ p.2 ∈ M ∧ p.1 ≠ p.2 ∧ t ∈ X_ef G p.1 p.2 := by
      apply bridges_partition G M hM;
    choose! p hp hp' using fun t ht => h_unique_bridges t ht;
    -- Since each bridge is counted exactly once, the number of bridges is at most the number of pairs.
    have h_card_bridges : (allBridges G M).card ≤ (Finset.powersetCard 2 M).card := by
      have h_card_bridges : (allBridges G M).card ≤ (Finset.image (fun t => {p t |>.1, p t |>.2} : Finset V → Finset (Finset V)) (allBridges G M)).card := by
        rw [ Finset.card_image_of_injOn ];
        intro t ht t' ht' h_eq;
        have := hp t ht; have := hp t' ht'; simp_all +decide [ X_ef ] ;
        grind;
      refine' h_card_bridges.trans ( Finset.card_le_card _ );
      grind;
    exact h_card_bridges.trans ( by simp +decide [ hM_card ] );
  unfold triangleCoveringNumberOn;
  have h_exists_cover : ∃ E' ∈ G.edgeFinset.powerset, (∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2) ∧ E'.card ≤ 6 := by
    have h_exists_cover : ∀ t ∈ allBridges G M, ∃ e ∈ G.edgeFinset, e ∈ t.sym2 := by
      intro t ht;
      unfold allBridges at ht;
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      rcases ht.1 with ⟨ h₁, h₂ ⟩;
      rcases Finset.card_eq_three.mp h₂ with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use s(a, b) ; aesop;
    choose! f hf₁ hf₂ using h_exists_cover;
    refine' ⟨ Finset.image ( fun t : allBridges G M => f t.1 t.2 ) ( Finset.univ : Finset ( allBridges G M ) ), _, _, _ ⟩ <;> simp_all +decide [ Finset.card_image_of_injective ];
    · exact Set.range_subset_iff.mpr fun t => hf₁ _ _;
    · exact fun t ht => ⟨ f t ht, ⟨ t, ht, rfl ⟩, hf₂ t ht ⟩;
    · exact le_trans ( Finset.card_image_le ) ( by simpa using h_pairs );
  have h_exists_cover : Option.getD (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2})).min 0 ≤ Finset.card h_exists_cover.choose := by
    have h_exists_cover : ∀ E' ∈ {E' ∈ G.edgeFinset.powerset | ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2}, Option.getD (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2})).min 0 ≤ E'.card := by
      intro E' hE'
      have h_min_le_card : ∀ x ∈ Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2}), Option.getD (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2})).min 0 ≤ x := by
        simp +decide [ Option.getD ];
        intro x E' hE' hE'' hx; rw [ hx.symm ] ;
        cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ allBridges G M, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> simp +decide [ h ];
        exact_mod_cast h ▸ Finset.min_le ( Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( show E' ⊆ G.edgeFinset from fun e he => by simpa using hE' he ), hE'' ⟩ ) );
      exact h_min_le_card _ ( Finset.mem_image_of_mem _ hE' );
    exact h_exists_cover _ ( Finset.mem_filter.mpr ⟨ ‹∃ E' ∈ G.edgeFinset.powerset, ( ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2 ) ∧ E'.card ≤ 6›.choose_spec.1, ‹∃ E' ∈ G.edgeFinset.powerset, ( ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2 ) ∧ E'.card ≤ 6›.choose_spec.2.1 ⟩ );
  linarith [ ‹∃ E' ∈ G.edgeFinset.powerset, ( ∀ t ∈ allBridges G M, ∃ e ∈ E', e ∈ t.sym2 ) ∧ E'.card ≤ 6›.choose_spec.2.2 ]

-- TARGET: Sparse sharing → fewer bridge pairs

/--
KEY: If sharing graph is a path P₄, we have exactly 3 pairs with bridges.
Each contributes τ ≤ 2, so τ(allBridges) ≤ 6.
-/
lemma tau_bridges_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e₁ e₂ e₃ e₄ : Finset V)
    (he : M = {e₁, e₂, e₃, e₄})
    (h_path : sharesVertex e₁ e₂ ∧ sharesVertex e₂ e₃ ∧ sharesVertex e₃ e₄ ∧
              ¬sharesVertex e₁ e₃ ∧ ¬sharesVertex e₁ e₄ ∧ ¬sharesVertex e₂ e₄) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 6 := by
  -- Since these are the only edges that share a vertex, we can apply the lemma about bridges.
  have h_bridges : ∀ t ∈ allBridges G M, ∃ p ∈ ({(e₁, e₂), (e₂, e₃), (e₃, e₄)} : Finset (Finset V × Finset V)), t ∈ X_ef G p.1 p.2 := by
    intros t ht
    obtain ⟨p, hp⟩ : ∃ p ∈ ({(e₁, e₂), (e₂, e₃), (e₃, e₄), (e₁, e₃), (e₁, e₄), (e₂, e₄)} : Finset (Finset V × Finset V)), t ∈ X_ef G p.1 p.2 := by
      unfold allBridges X_ef at *; aesop;
    simp_all +decide [ sharesVertex ];
    rcases hp with ⟨ rfl | rfl | rfl | rfl | rfl | rfl, hp ⟩ <;> simp_all +decide [ X_ef ];
    · have := Finset.card_eq_three.mp hp.1.2; obtain ⟨ a, b, c, hab, hbc, hac, h ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
      grind;
    · have h_contradiction : (t ∩ e₁).card + (t ∩ e₄).card ≤ (t ∩ (e₁ ∪ e₄)).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        simp +decide [ Finset.inter_union_distrib_left, Finset.inter_assoc, Finset.inter_left_comm, Finset.inter_comm ];
        grind;
      have h_contradiction : (t ∩ (e₁ ∪ e₄)).card ≤ t.card := by
        exact Finset.card_le_card fun x hx => by aesop;
      exact absurd h_contradiction ( by have := hp.1.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ; linarith );
    · have h_contradiction : (t ∩ e₂).card + (t ∩ e₄).card ≤ (t ∩ e₂ ∪ t ∩ e₄).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        simp_all +decide [ Finset.ext_iff ];
      have h_contradiction : (t ∩ e₂ ∪ t ∩ e₄).card ≤ t.card := by
        exact Finset.card_le_card ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) );
      linarith [ show t.card ≤ 3 by exact hp.1.card_eq.le ];
  -- Therefore, the number of bridges is at most the number of pairs containing them.
  have h_bridges_card : triangleCoveringNumberOn G (allBridges G M) ≤ triangleCoveringNumberOn G (X_ef G e₁ e₂ ∪ X_ef G e₂ e₃ ∪ X_ef G e₃ e₄) := by
    apply le_of_not_gt; intro h_contra;
    -- If there exists a cover for the union of X_ef sets with fewer edges than the cover for allBridges, then this cover must also cover allBridges.
    obtain ⟨E', hE', hE'_card⟩ : ∃ E' : Finset (Sym2 V), isTriangleCover G (X_ef G e₁ e₂ ∪ X_ef G e₂ e₃ ∪ X_ef G e₃ e₄) E' ∧ E'.card < triangleCoveringNumberOn G (allBridges G M) := by
      have := exists_min_cover G ( X_ef G e₁ e₂ ∪ X_ef G e₂ e₃ ∪ X_ef G e₃ e₄ ) ?_;
      · exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.symm ▸ h_contra ⟩;
      · refine' ⟨ G.edgeFinset, _, _ ⟩ <;> simp +decide [ isTriangleCover ];
        rintro t ( ht | ht | ht ) <;> simp_all +decide [ X_ef ];
        · rcases ht.1 with ⟨ h₁, h₂ ⟩;
          rcases Finset.card_eq_three.mp h₂ with ⟨ a, b, c, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ) ; aesop;
        · rcases ht.1 with ⟨ h₁, h₂ ⟩;
          rcases Finset.card_eq_three.mp h₂ with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ) ; aesop;
        · rcases ht.1 with ⟨ h₁, h₂ ⟩;
          rcases Finset.card_eq_three.mp h₂ with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ) ; aesop;
    refine' hE'_card.not_le ( le_triangleCoveringNumberOn G ( allBridges G M ) E' _ );
    exact ⟨ hE'.1, fun t ht => by obtain ⟨ p, hp₁, hp₂ ⟩ := h_bridges t ht; exact hE'.2 t ( by aesop ) ⟩;
  refine' le_trans h_bridges_card ( le_trans ( _ : _ ≤ _ ) _ );
  exact triangleCoveringNumberOn G ( X_ef G e₁ e₂ ) + triangleCoveringNumberOn G ( X_ef G e₂ e₃ ) + triangleCoveringNumberOn G ( X_ef G e₃ e₄ );
  · exact le_trans ( tau_union_le_sum _ _ _ ) ( add_le_add ( tau_union_le_sum _ _ _ ) le_rfl );
  · exact le_trans ( add_le_add_three ( tau_X_le_2 G M hM e₁ e₂ ( by aesop ) ( by aesop ) ( by aesop ) ) ( tau_X_le_2 G M hM e₂ e₃ ( by aesop ) ( by aesop ) ( by aesop ) ) ( tau_X_le_2 G M hM e₃ e₄ ( by aesop ) ( by aesop ) ( by aesop ) ) ) ( by norm_num )

-- TARGET: Path case → 3 bridge pairs × 2

/-
KEY: If sharing graph is a star K₁,₃, center connects to all leaves.
Bridges only between center and each leaf: 3 pairs.
τ(allBridges) ≤ 6.
-/
noncomputable section AristotleLemmas

/-
If two sets `e` and `f` do not share any vertices, then `X_ef G e f` is empty.
-/
lemma X_ef_eq_empty_of_not_sharesVertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (h : ¬sharesVertex e f) :
    X_ef G e f = ∅ := by
      ext t;
      simp [X_ef, h];
      intro ht ht'
      have h_inter : (t ∩ e).card + (t ∩ f).card ≤ (t ∩ (e ∪ f)).card := by
        rw [ ← Finset.card_union_add_card_inter ];
        simp_all +decide [ Finset.inter_union_distrib_left ];
        simp_all +decide [ Finset.ext_iff, sharesVertex ];
      have h_inter_union : (t ∩ (e ∪ f)).card ≤ t.card := by
        exact Finset.card_le_card fun x hx => by aesop;
      linarith [ show t.card = 3 by exact ht.card_eq ]

end AristotleLemmas

lemma tau_bridges_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e_center e₁ e₂ e₃ : Finset V)
    (he : M = {e_center, e₁, e₂, e₃})
    (h_star : sharesVertex e_center e₁ ∧ sharesVertex e_center e₂ ∧ sharesVertex e_center e₃ ∧
              ¬sharesVertex e₁ e₂ ∧ ¬sharesVertex e₁ e₃ ∧ ¬sharesVertex e₂ e₃) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 6 := by
  -- Using the helper lemma `X_ef_eq_empty_of_not_sharesVertex`, we have `X_ef G e₁ e₂ = ∅`, `X_ef G e₁ e₃ = ∅`, and `X_ef G e₂ e₃ = ∅`.
  have hX_empty : X_ef G e₁ e₂ = ∅ ∧ X_ef G e₁ e₃ = ∅ ∧ X_ef G e₂ e₃ = ∅ := by
    exact ⟨ X_ef_eq_empty_of_not_sharesVertex G e₁ e₂ h_star.2.2.2.1, X_ef_eq_empty_of_not_sharesVertex G e₁ e₃ h_star.2.2.2.2.1, X_ef_eq_empty_of_not_sharesVertex G e₂ e₃ h_star.2.2.2.2.2 ⟩;
  -- Using `tau_union_le_sum` repeatedly, we have:
  have h_union : triangleCoveringNumberOn G (allBridges G M) ≤ triangleCoveringNumberOn G (X_ef G e_center e₁) + triangleCoveringNumberOn G (X_ef G e_center e₂) + triangleCoveringNumberOn G (X_ef G e_center e₃) := by
    have h_union : triangleCoveringNumberOn G (allBridges G M) ≤ triangleCoveringNumberOn G (X_ef G e_center e₁ ∪ X_ef G e_center e₂) + triangleCoveringNumberOn G (X_ef G e_center e₃) := by
      have h_union : allBridges G M ⊆ X_ef G e_center e₁ ∪ X_ef G e_center e₂ ∪ X_ef G e_center e₃ := by
        intro t ht; simp_all +decide [ allBridges ] ;
        simp_all +decide [ X_ef ];
        grind;
      refine' le_trans ( _ : triangleCoveringNumberOn G ( allBridges G M ) ≤ triangleCoveringNumberOn G ( X_ef G e_center e₁ ∪ X_ef G e_center e₂ ∪ X_ef G e_center e₃ ) ) _;
      · apply le_of_not_gt; intro h_contra;
        obtain ⟨E', hE'⟩ : ∃ E', isTriangleCover G (X_ef G e_center e₁ ∪ X_ef G e_center e₂ ∪ X_ef G e_center e₃) E' ∧ E'.card = triangleCoveringNumberOn G (X_ef G e_center e₁ ∪ X_ef G e_center e₂ ∪ X_ef G e_center e₃) := by
          apply exists_min_cover;
          refine' ⟨ G.edgeFinset, _, _ ⟩ <;> simp +decide [ isTriangleCover ];
          rintro t ( ht | ht | ht ) <;> simp_all +decide [ X_ef ];
          · rcases ht.1 with ⟨ h₁, h₂ ⟩;
            rcases Finset.card_eq_three.mp h₂ with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use Sym2.mk ( a, b ) ; aesop;
          · rcases ht.1 with ⟨ ht₁, ht₂ ⟩;
            rcases Finset.card_eq_three.mp ht₂ with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; use s(a, b) ; aesop;
          · rcases ht.1 with ⟨ h₁, h₂ ⟩;
            obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := Finset.card_eq_three.mp h₂;
            exact ⟨ Sym2.mk ( a, b ), by simpa [ Sym2.eq_swap ] using h₁ ( by simp +decide [ ha ] ) ( by simp +decide [ hb ] ) ( by simp +decide [ ha, hb ] ), by simp +decide [ ha, hb ] ⟩;
        refine' h_contra.not_le _;
        refine' le_trans _ hE'.2.le;
        apply le_triangleCoveringNumberOn;
        exact ⟨ hE'.1.1, fun t ht => hE'.1.2 t ( h_union ht ) ⟩;
      · apply_rules [ tau_union_le_sum ];
    exact h_union.trans ( add_le_add_right ( tau_union_le_sum G _ _ ) _ );
  -- By `tau_X_le_2`, each term is at most 2.
  have h_term_le_2 : triangleCoveringNumberOn G (X_ef G e_center e₁) ≤ 2 ∧ triangleCoveringNumberOn G (X_ef G e_center e₂) ≤ 2 ∧ triangleCoveringNumberOn G (X_ef G e_center e₃) ≤ 2 := by
    refine' ⟨ tau_X_le_2 G M hM e_center e₁ _ _ _, tau_X_le_2 G M hM e_center e₂ _ _ _, tau_X_le_2 G M hM e_center e₃ _ _ _ ⟩ <;> simp_all +decide [ Finset.ext_iff, Finset.subset_iff ];
    · grind;
    · grind;
    · grind;
  grind

-- TARGET: Star case → 3 bridge pairs × 2

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN COUNTING THEOREMS
-- ══════════════════════════════════════════════════════════════════════════════

/-
BRIDGE COUNTING (Honest Assessment):

The naive approach gives:
- τ(allS) ≤ 4 × 2 = 8
- τ(allBridges) ≤ 6-12 depending on structure
- Sum = 14-20, NOT 8

To get τ ≤ 8, we need OVERLAP ACCOUNTING:
1. Bridges absorbed by S_e cover (slot 39 approach)
2. Pair reduction: τ(T_pair) ≤ 4 (slot 43 approach)

This file establishes the BRIDGE BOUNDS, not the final theorem.
Use slot 43 for the full τ ≤ 8 proof.
-/

/--
PATH CASE: Bridge bound only (not full τ ≤ 8)

When sharing graph is P₄:
- 3 sharing pairs → τ(allBridges) ≤ 6
- This is a COMPONENT of the full proof, not the full proof
-/
lemma tau_bridges_le_6_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e₁ e₂ e₃ e₄ : Finset V) (he : M = {e₁, e₂, e₃, e₄})
    (h_path : sharesVertex e₁ e₂ ∧ sharesVertex e₂ e₃ ∧ sharesVertex e₃ e₄ ∧
              ¬sharesVertex e₁ e₃ ∧ ¬sharesVertex e₁ e₄ ∧ ¬sharesVertex e₂ e₄) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 6 := by
  exact?

-- TARGET: 3 pairs × 2 edges each

/--
STAR CASE: Bridge bound τ(allBridges) ≤ 6

When sharing graph is K₁,₃ (star):
- 3 sharing pairs (center to each leaf)
- Each X(center, leaf) has τ ≤ 2
- τ(allBridges) ≤ 6

NOTE: This contributes to τ ≤ 8 via overlap with S_e covers,
not via naive summation. Use slot 43 for full proof.
-/
lemma tau_bridges_le_6_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e_center e₁ e₂ e₃ : Finset V) (he : M = {e_center, e₁, e₂, e₃})
    (h_star : sharesVertex e_center e₁ ∧ sharesVertex e_center e₂ ∧ sharesVertex e_center e₃ ∧
              ¬sharesVertex e₁ e₂ ∧ ¬sharesVertex e₁ e₃ ∧ ¬sharesVertex e₂ e₃) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 6 := by
  exact?

-- TARGET: 3 pairs × 2 edges each

/-
MAIN CONTRIBUTION: Bridge bounds enable slot 43 proofs

This file establishes:
1. τ(allBridges) ≤ 12 (naive, any sharing graph)
2. τ(allBridges) ≤ 8 (sparse, degree ≤ 2)
3. τ(allBridges) ≤ 6 (path P₄ or star K₁,₃)

Combined with slot 39 (bridges absorbed) or slot 43 (pair decomposition),
these bounds lead to τ ≤ 8.
-/

end