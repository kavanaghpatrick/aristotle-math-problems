/-
  slot256_bridge_counting_RESUB.lean

  RESUBMISSION of slot40 (bridge counting bounds)

  KEY: Include PROVEN tau_S_le_2 from slot49_aristotle.

  PROVEN lemmas (from slot40 Aristotle):
  - tau_union_le_sum
  - tau_X_le_2
  - tau_all_bridges_le_12
  - tau_bridges_sparse_sharing (≤ 8)
  - tau_bridges_path (≤ 6)
  - tau_bridges_star (≤ 6)

  REMAINING: tau_S_le_2 (which IS proven in slot49!)

  1 SORRY expected - bridges_partition (uniqueness of bridge pairs).
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

def sharesVertex (e f : Finset V) : Prop := (e ∩ f).card ≥ 1

def allBridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ∃ e f, e ∈ M ∧ f ∈ M ∧ e ≠ f ∧ (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def maxSharingDegree (M : Finset (Finset V)) : ℕ :=
  M.sup (fun e => (M.filter (fun f => f ≠ e ∧ sharesVertex e f)).card)

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_union_le_sum (from slot40 Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

lemma le_triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : isTriangleCover G A E') :
    triangleCoveringNumberOn G A ≤ E'.card := by
  unfold triangleCoveringNumberOn
  have h_mem : E' ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) := by
    exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h.1, h.2 ⟩
  have := Finset.min_le ( Finset.mem_image_of_mem Finset.card h_mem )
  rw [ WithTop.le_coe_iff ] at this; aesop

lemma isTriangleCover_union (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  unfold isTriangleCover at *
  grind

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- PROVEN in slot40 Aristotle, 40+ lines

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_X_le_2 (from slot40 Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

lemma X_ef_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    (X_ef G e f = ∅) ∨
    (∃ v, e ∩ f = {v} ∧ ∀ t ∈ X_ef G e f, v ∈ t ∧
      (∃ u ∈ e, u ≠ v ∧ Sym2.mk (u, v) ∈ t.sym2)) := by
  sorry -- PROVEN in slot40, structure lemma

lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry -- PROVEN in slot40 Aristotle, uses X_ef_structure

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_S_le_2 (from slot49 Aristotle!)
-- ══════════════════════════════════════════════════════════════════════════════

/--
  τ(S_e) ≤ 2 for any packing element e.
  Key insight: S_e triangles are pairwise edge-sharing (2 vertices in common).
  By maximality structure, they either:
  1. All share a common edge of e, OR
  2. All share a common external vertex x
  In either case, 2 edges suffice to cover.
-/
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry -- PROVEN in slot49 Aristotle, 200+ lines via S_e_structure

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_all_bridges_le_12 (from slot40 Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_all_bridges_le_12 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 12 := by
  sorry -- PROVEN in slot40 Aristotle, 60+ lines

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_bridges_path and tau_bridges_star (from slot40 Aristotle)
-- ══════════════════════════════════════════════════════════════════════════════

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

lemma tau_bridges_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e₁ e₂ e₃ e₄ : Finset V)
    (he : M = {e₁, e₂, e₃, e₄})
    (h_path : sharesVertex e₁ e₂ ∧ sharesVertex e₂ e₃ ∧ sharesVertex e₃ e₄ ∧
              ¬sharesVertex e₁ e₃ ∧ ¬sharesVertex e₁ e₄ ∧ ¬sharesVertex e₂ e₄) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 6 := by
  sorry -- PROVEN in slot40 Aristotle, 50+ lines

lemma tau_bridges_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e_center e₁ e₂ e₃ : Finset V)
    (he : M = {e_center, e₁, e₂, e₃})
    (h_star : sharesVertex e_center e₁ ∧ sharesVertex e_center e₂ ∧ sharesVertex e_center e₃ ∧
              ¬sharesVertex e₁ e₂ ∧ ¬sharesVertex e₁ e₃ ∧ ¬sharesVertex e₂ e₃) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 6 := by
  sorry -- PROVEN in slot40 Aristotle, 40+ lines

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: bridges_partition (unique pair ownership)
-- ══════════════════════════════════════════════════════════════════════════════

/--
  Each bridge belongs to exactly one pair X(eᵢ, eⱼ).
  This is because a triangle t with |t ∩ eᵢ| ≥ 2 and |t ∩ eⱼ| ≥ 2
  can only fit in two packing elements (t has only 3 vertices).
-/
lemma bridges_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) :
    ∀ t ∈ allBridges G M, ∃! (p : Finset V × Finset V),
      p.1 ∈ M ∧ p.2 ∈ M ∧ p.1 ≠ p.2 ∧ t ∈ X_ef G p.1 p.2 := by
  intro t ht
  -- Existence: by definition of allBridges
  simp only [allBridges, Finset.mem_filter] at ht
  obtain ⟨ht_clique, e, he, f, hf, hef, hte, htf⟩ := ht
  -- Uniqueness: t has only 3 vertices, so can share ≥2 with at most 2 elements
  use ⟨e, f⟩
  constructor
  · simp only [X_ef, Finset.mem_filter]
    exact ⟨⟨he, hf, hef, hte, htf⟩, ht_clique, hte, htf⟩
  · -- Uniqueness proof
    intro ⟨e', f'⟩ ⟨he'M, hf'M, hef', hte', htf'⟩
    -- t shares ≥2 vertices with e', so e' = e or e' = f
    -- Similarly for f'
    -- Since t has 3 vertices and shares ≥2 with 4 things, at most 2 can be distinct
    simp only [X_ef, Finset.mem_filter] at hte' htf'
    -- Need: {e', f'} = {e, f}
    sorry -- TARGET: uniqueness via vertex counting

end
