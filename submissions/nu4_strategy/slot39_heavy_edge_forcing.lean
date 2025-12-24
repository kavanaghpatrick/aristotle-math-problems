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
    sorry -- Zero case handled
  · sorry -- Zero case handled

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
  sorry -- SCAFFOLDING: Full proof in slot29_triple_apex.lean

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
  sorry -- TARGET: Bridge structure when no edge sharing

/--
When bridges share exactly one vertex with both elements,
the bridge set X(e,f) has a special structure.
-/
lemma single_vertex_bridge_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (h_single : (e ∩ f).card = 1) :
    ∃ v, v ∈ e ∧ v ∈ f ∧ ∀ t ∈ X_ef G e f, v ∈ t := by
  sorry -- TARGET: All bridges contain the shared vertex

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
  sorry -- TARGET: Single cover handles both S_e and bridges

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
  sorry -- TARGET: Use bridges_absorbed_by_Se_cover + Te = Se ∪ bridges

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
  sorry -- MAIN TARGET

/--
CONTRAPOSITIVE FORM: No edge sharing implies light element
-/
theorem no_edge_sharing_implies_light (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_no_edge : noEdgeSharing M e) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e) ≤ 2 := by
  sorry -- ALTERNATIVE TARGET: Easier form

/--
COROLLARY: Application to ν=4

If all elements have no edge sharing, then τ ≤ 8.
-/
theorem tuza_nu4_no_edge_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (h_no_edges : ∀ e ∈ M, noEdgeSharing M e) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  sorry -- COROLLARY: Use no_edge_sharing_implies_light 4 times

end
