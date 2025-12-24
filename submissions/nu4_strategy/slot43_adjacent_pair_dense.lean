/-
Tuza ν=4 Strategy - Slot 43: Adjacent Pair Bound for Dense Sharing Graphs

NOVEL APPROACH (from AI Review Round 2):
For dense sharing graphs (C₄, K₄-e, K₄) without leaves, find a pair
with τ(T_pair) ≤ 4, enabling pair reduction: τ ≤ 4 + 4 = 8.

KEY INSIGHT (from Gemini):
The "Holy Grail" is proving τ(T_e ∪ T_f) ≤ 4 for some adjacent pair.
- τ(S_e) ≤ 2, τ(S_f) ≤ 2, τ(X_ef) ≤ 2 gives sum ≤ 6
- Need to find 2 edges of overlap!

OVERLAP SOURCES:
1. Shared vertex v between e and f: edges through v can hit multiple sets
2. S_e ∩ S_f may be non-empty (triangles in both)
3. Some S_e triangles may be covered by X_ef edges

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

def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  trianglesSharingEdge G e ∪ trianglesSharingEdge G f

def sharesVertex (e f : Finset V) : Prop := (e ∩ f).card ≥ 1

def sharesEdge (e f : Finset V) : Prop := (e ∩ f).card ≥ 2

def sharingDegree (M : Finset (Finset V)) (e : Finset V) : ℕ :=
  (M.filter (fun f => f ≠ e ∧ sharesVertex e f)).card

-- Packing elements containing vertex v
def packingElementsContaining (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  M.filter (fun t => v ∈ t)

-- Dense sharing: no isolated vertices and no leaves (all degrees ≥ 2)
def isDenseSharingGraph (M : Finset (Finset V)) : Prop :=
  ∀ e ∈ M, sharingDegree M e ≥ 2

-- C₄ sharing structure
def isC4Sharing (M : Finset (Finset V)) (e₁ e₂ e₃ e₄ : Finset V) : Prop :=
  M = {e₁, e₂, e₃, e₄} ∧
  sharesVertex e₁ e₂ ∧ sharesVertex e₂ e₃ ∧ sharesVertex e₃ e₄ ∧ sharesVertex e₄ e₁ ∧
  ¬sharesVertex e₁ e₃ ∧ ¬sharesVertex e₂ e₄

-- K₄-e sharing structure (missing one edge)
def isK4MinusEdgeSharing (M : Finset (Finset V)) (e₁ e₂ e₃ e₄ : Finset V) : Prop :=
  M = {e₁, e₂, e₃, e₄} ∧
  sharesVertex e₁ e₂ ∧ sharesVertex e₁ e₃ ∧ sharesVertex e₁ e₄ ∧
  sharesVertex e₂ e₃ ∧ sharesVertex e₂ e₄ ∧
  ¬sharesVertex e₃ e₄

-- K₄ sharing structure (complete)
def isK4Sharing (M : Finset (Finset V)) : Prop :=
  ∀ e f, e ∈ M → f ∈ M → e ≠ f → sharesVertex e f

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

lemma isTriangleCover_union (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  unfold isTriangleCover at *
  grind

-- PROVEN in slot16 (full proof in slot29_triple_apex.lean)
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
-- PAIR DECOMPOSITION LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/--
T_pair decomposes into S_e, S_f, and X_ef (bridges between e and f).
Key: T_pair = S_e ∪ S_f ∪ X_ef (with some overlap).
-/
lemma T_pair_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    T_pair G e f ⊆ S_e G M e ∪ S_e G M f ∪ X_ef G e f := by
  sorry -- TARGET: T_pair covered by these three sets

/--
Naive bound: τ(T_pair) ≤ τ(S_e) + τ(S_f) + τ(X_ef) ≤ 2 + 2 + 2 = 6.
-/
lemma tau_T_pair_le_6 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 6 := by
  sorry -- TARGET: Naive bound via sum

/--
KEY INSIGHT: When e and f share a vertex v, many triangles pass through v.
Edges incident to v can cover multiple triangles efficiently.
-/
lemma shared_vertex_savings (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hve : v ∈ e) (hvf : v ∈ f) :
    ∃ E' : Finset (Sym2 V), isTriangleCover G (T_pair G e f) E' ∧ E'.card ≤ 5 := by
  sorry -- TARGET: Shared vertex saves 1 edge

/--
STRONGER: When e and f share exactly one vertex v, and this vertex has
many triangles passing through it, we can save 2 edges.
-/
lemma shared_vertex_concentrated_savings (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_share_one : (e ∩ f).card = 1) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  sorry -- TARGET: Single shared vertex → τ ≤ 4

-- ══════════════════════════════════════════════════════════════════════════════
-- C₄ CYCLE CASE
-- ══════════════════════════════════════════════════════════════════════════════

/--
In C₄ sharing graph, adjacent pairs share exactly one vertex.
Choose any adjacent pair (e₁, e₂): τ(T_pair) ≤ 4.
-/
lemma c4_adjacent_pair_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e₁ e₂ e₃ e₄ : Finset V)
    (hC4 : isC4Sharing M e₁ e₂ e₃ e₄) :
    triangleCoveringNumberOn G (T_pair G e₁ e₂) ≤ 4 := by
  sorry -- TARGET: C₄ adjacent pair bound

/--
C₄ MAIN THEOREM: τ ≤ 8 via pair reduction.
Take adjacent pair (e₁, e₂): τ(T_pair) ≤ 4.
Remaining pair (e₃, e₄) forms ν=2 subproblem: τ ≤ 4 by Parker.
-/
theorem tuza_nu4_c4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e₁ e₂ e₃ e₄ : Finset V)
    (hC4 : isC4Sharing M e₁ e₂ e₃ e₄) :
    triangleCoveringNumber G ≤ 8 := by
  sorry -- MAIN TARGET: C₄ case

-- ══════════════════════════════════════════════════════════════════════════════
-- K₄-e CASE (ALMOST COMPLETE)
-- ══════════════════════════════════════════════════════════════════════════════

/--
In K₄-e, the non-adjacent pair (e₃, e₄) has no bridges between them.
Adjacent pairs (e₁, e₃) or (e₁, e₄) may have τ ≤ 4.
-/
lemma k4_minus_edge_adjacent_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e₁ e₂ e₃ e₄ : Finset V)
    (hK4e : isK4MinusEdgeSharing M e₁ e₂ e₃ e₄) :
    triangleCoveringNumberOn G (T_pair G e₁ e₃) ≤ 4 ∨
    triangleCoveringNumberOn G (T_pair G e₁ e₄) ≤ 4 := by
  sorry -- TARGET: At least one adjacent pair works

/--
K₄-e MAIN THEOREM: τ ≤ 8.
Strategy: Use the pair that works from above lemma.
-/
theorem tuza_nu4_k4_minus_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (e₁ e₂ e₃ e₄ : Finset V)
    (hK4e : isK4MinusEdgeSharing M e₁ e₂ e₃ e₄) :
    triangleCoveringNumber G ≤ 8 := by
  sorry -- MAIN TARGET: K₄-e case

-- ══════════════════════════════════════════════════════════════════════════════
-- K₄ COMPLETE CASE
-- ══════════════════════════════════════════════════════════════════════════════

/--
In complete K₄ sharing, all 6 pairs share vertices.
KEY QUESTION: Does some pair have τ(T_pair) ≤ 4?

APPROACH 1: If all 4 share a common vertex v, use apex theorem (slot 29).
APPROACH 2: Otherwise, find a pair with concentrated sharing.
-/
lemma k4_some_pair_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hK4 : isK4Sharing M) :
    ∃ e f, e ∈ M ∧ f ∈ M ∧ e ≠ f ∧ triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  sorry -- TARGET: Some pair achieves ≤ 4

/--
K₄ MAIN THEOREM: τ ≤ 8.

Case split:
1. If all 4 share a common vertex v: Use tau_le_8_star from slot 29
2. Otherwise: Find pair with τ ≤ 4, remaining pair has τ ≤ 4
-/
theorem tuza_nu4_k4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hK4 : isK4Sharing M) :
    triangleCoveringNumber G ≤ 8 := by
  sorry -- MAIN TARGET: K₄ case

-- ══════════════════════════════════════════════════════════════════════════════
-- UNIFIED DENSE CASE THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/--
MAIN THEOREM: Dense sharing graph → τ ≤ 8.

When sharing graph has no isolated vertices and no leaves (all degrees ≥ 2),
it must be C₄, K₄-e, or K₄. All three cases give τ ≤ 8.
-/
theorem tuza_nu4_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_dense : isDenseSharingGraph M) :
    triangleCoveringNumber G ≤ 8 := by
  sorry -- MAIN TARGET: All dense cases

/--
COROLLARY: Existence of good pair in dense case.
This is the "ammunition" for the local reduction strategy (slot 42).
-/
theorem dense_good_pair_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_dense : isDenseSharingGraph M) :
    ∃ e f, e ∈ M ∧ f ∈ M ∧ e ≠ f ∧ triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  sorry -- COROLLARY: Pair reduction always possible in dense case

end
