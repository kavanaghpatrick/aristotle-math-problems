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
  sorry -- SCAFFOLDING: Full 90+ line proof in slot29_triple_apex.lean

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
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry -- SCAFFOLDING: Full proof in slot29_triple_apex.lean (500+ lines)

-- SCAFFOLDING: tau_X_le_2 (target for slot 24)
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry -- SCAFFOLDING: Proven in slot24

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
  sorry -- TARGET: Each bridge belongs to exactly one pair

/--
Bound bridges via pair decomposition.
For ν=4, we have at most 6 pairs (4 choose 2).
Each X(eᵢ,eⱼ) contributes τ ≤ 2.
Naive bound: τ(allBridges) ≤ 12.
-/
lemma tau_all_bridges_le_12 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 12 := by
  sorry -- TARGET: 6 pairs × 2 edges each

/--
If sharing graph has max degree ≤ 2, bridges are more constrained.
Each element shares with ≤2 others, so only specific pairs have bridges.
-/
lemma tau_bridges_sparse_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_sparse : maxSharingDegree M ≤ 2) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 8 := by
  sorry -- TARGET: Sparse sharing → fewer bridge pairs

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
  sorry -- TARGET: Path case → 3 bridge pairs × 2

/--
KEY: If sharing graph is a star K₁,₃, center connects to all leaves.
Bridges only between center and each leaf: 3 pairs.
τ(allBridges) ≤ 6.
-/
lemma tau_bridges_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e_center e₁ e₂ e₃ : Finset V)
    (he : M = {e_center, e₁, e₂, e₃})
    (h_star : sharesVertex e_center e₁ ∧ sharesVertex e_center e₂ ∧ sharesVertex e_center e₃ ∧
              ¬sharesVertex e₁ e₂ ∧ ¬sharesVertex e₁ e₃ ∧ ¬sharesVertex e₂ e₃) :
    triangleCoveringNumberOn G (allBridges G M) ≤ 6 := by
  sorry -- TARGET: Star case → 3 bridge pairs × 2

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
  sorry -- TARGET: 3 pairs × 2 edges each

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
  sorry -- TARGET: 3 pairs × 2 edges each

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
