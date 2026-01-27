/-
  slot388_direct_8cover_construction.lean

  Tuza ν=4 PATH_4: Direct 8-edge cover construction

  BLOCKER ANALYSIS (from slot387):
  - tau_S_union_X_le_2 is FALSE (pattern #28 in false_lemmas)
  - Counterexample: S_e uses base edge {a₁,a₂}, X_{e,f} uses spokes {v,a₁}, {v,a₂}
  - Total: 3 edges, not 2

  NEW APPROACH: Direct global construction
  Instead of proving τ(S_e ∪ X_{e,f}) ≤ 2 for each pair, we:
  1. Choose 2 edges per M-element globally
  2. Show the 8-edge union covers all triangles
  3. Key: edges can be chosen to cover overlapping bridge sets

  PATH_4 STRUCTURE: A —v₁— B —v₂— C —v₃— D
  - A = {v₁, a₁, a₂}
  - B = {v₁, v₂, b₃}
  - C = {v₂, v₃, c₃}
  - D = {v₃, d₁, d₂}

  8-EDGE COVER CONSTRUCTION:
  From A: e₁ = {v₁, a₁}, e₂ = {v₁, a₂}  (2 spokes through v₁)
  From B: e₃ = {v₁, v₂}, e₄ = {v₂, b₃}  (spine + spoke)
  From C: e₅ = {v₂, v₃}, e₆ = {v₃, c₃}  (spine + spoke)
  From D: e₇ = {v₃, d₁}, e₈ = {v₃, d₂}  (2 spokes through v₃)

  COVERAGE ANALYSIS:
  - S_A: Triangles sharing edge with A only
    * A itself: covered by e₁ or e₂ ✓
    * {v₁,a₁,x}: covered by e₁ ✓
    * {v₁,a₂,x}: covered by e₂ ✓
    * {a₁,a₂,x}: NOT covered by e₁,e₂!!! This is the gap.

  THE GAP: Base triangles {a₁,a₂,x} in S_A are not covered.

  RESOLUTION: Such triangles must be covered by OTHER M-elements' edges!
  - If {a₁,a₂,x} shares edge with B, it would be in X_{A,B}, not S_A
  - So {a₁,a₂,x} shares no edge with B,C,D
  - For it to share no edge with B = {v₁,v₂,b₃}, we need x ∉ B and {a₁,a₂} ∩ B = ∅
  - But v₁ ∈ A ∩ B, so v₁ ∈ {v₁,a₁,a₂}... so a₁ ≠ v₁ and a₂ ≠ v₁
  - Since (A ∩ B).card = 1 and A ∩ B = {v₁}, we have a₁,a₂ ∉ B
  - So {a₁,a₂} ∩ B = ∅ ✓

  So base triangles {a₁,a₂,x} in S_A CANNOT be covered by our 8-edge construction!
  This means 8 edges are NOT always sufficient with this strategy.

  ALTERNATIVE: Use S_e_structure more carefully.
  - Either all S_A triangles share a common edge (could be {a₁,a₂})
  - Or S_A has star structure with external vertex x

  If S_A has star structure with external vertex x:
  - All S_A triangles (except A) contain x
  - We can cover S_A with edges through x: {x,v₁} and one other
  - But x might not be adjacent to v₁!

  FALLBACK: Prove case-by-case based on S_e_structure.

  TIER: 2 (Complex case analysis)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from slot257)
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

def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

-- PATH_4 structure
def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING (from slot257/slot387)
-- ══════════════════════════════════════════════════════════════════════════════

-- From slot257: tau_S_le_2
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry -- PROVEN in slot257 (200+ lines)

-- From slot257: tau_X_le_2
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry -- PROVEN in slot257 (100+ lines)

-- From slot387: path4_triangle_decomposition
lemma path4_triangle_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    G.cliqueFinset 3 = S_e G M A ∪ S_e G M B ∪ S_e G M C ∪ S_e G M D ∪
                        X_ef G A B ∪ X_ef G B C ∪ X_ef G C D := by
  sorry -- PROVEN in slot387

-- From slot257: subadditivity
lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
    triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- PROVEN in slot257

lemma le_triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : isTriangleCover G A E') :
    triangleCoveringNumberOn G A ≤ E'.card := by
  unfold triangleCoveringNumberOn
  have h_mem : E' ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1, h.2⟩
  have := Finset.min_le (Finset.mem_image_of_mem Finset.card h_mem)
  rw [WithTop.le_coe_iff] at this; aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY INSIGHT: Bridge edges can cover S_e triangles!
-- ══════════════════════════════════════════════════════════════════════════════

/-
CRITICAL OBSERVATION:
X_{A,B} triangles all contain v₁ (the shared vertex of A and B).
X_{A,B} is covered by edges from A through v₁: {v₁,a₁}, {v₁,a₂}.

If S_A is covered by edges through v₁, then S_A ∪ X_{A,B} is covered by 2 edges!
The only problematic case is when S_A uses the "base edge" {a₁,a₂}.

KEY LEMMA (to prove): If S_A uses base edge {a₁,a₂}, then X_{A,B} is empty
OR X_{A,B} can still be covered by the base edge.

Actually, this is FALSE as shown by the counterexample in slot387.

NEW APPROACH: Count edges more carefully.
- S_A, S_B, S_C, S_D: at most 2 edges each → 8 edges
- X_{A,B}, X_{B,C}, X_{C,D}: at most 2 edges each → 6 edges
- BUT X edges can OVERLAP with S edges!

Specifically:
- X_{A,B} is covered by 2 edges from A through v₁
- These same edges might also cover part of S_A (triangles through v₁)

The question is: can we always find a cover where:
- S_A ∪ S_B ∪ S_C ∪ S_D uses ≤ 8 edges total
- These 8 edges ALSO cover X_{A,B} ∪ X_{B,C} ∪ X_{C,D}

This requires proving that bridge sets are "absorbed" by S covers.
-/

-- ══════════════════════════════════════════════════════════════════════════════
-- CASE ANALYSIS: When is bridge absorption possible?
-- ══════════════════════════════════════════════════════════════════════════════

/-- X_{A,B} triangles all contain the shared vertex v₁ -/
lemma X_ef_contains_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  -- From slot257 X_ef_mem_inter
  by_contra hv_not_in_t
  have h_disj : Disjoint (t ∩ e) (t ∩ f) := by
    rw [Finset.disjoint_left]
    intro x hxe hxf
    have hx_in_ef : x ∈ e ∩ f := mem_inter.mpr ⟨mem_of_mem_inter_right hxe, mem_of_mem_inter_right hxf⟩
    rw [hv] at hx_in_ef
    simp only [mem_singleton] at hx_in_ef
    rw [hx_in_ef] at hxe
    exact hv_not_in_t (mem_of_mem_inter_left hxe)
  have ht_card : t.card = 3 := by
    have ht_tri : t ∈ G.cliqueFinset 3 := by
      simp only [X_ef, mem_filter] at ht
      exact ht.1
    exact (G.mem_cliqueFinset_iff.mp ht_tri).2
  have h_ge : (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2 := by
    simp only [X_ef, mem_filter] at ht
    exact ht.2
  have h_union : (t ∩ e ∪ t ∩ f).card ≤ t.card := card_le_card (union_subset inter_subset_left inter_subset_left)
  rw [card_union_of_disjoint h_disj] at h_union
  omega

/-- X_{A,B} is covered by 2 edges from A through the shared vertex -/
lemma X_ef_covered_by_spokes (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v})
    (he_card : e.card = 3) :
    ∃ a b : V, a ≠ b ∧ a ∈ e ∧ b ∈ e ∧ a ≠ v ∧ b ≠ v ∧
    (∀ t ∈ X_ef G e f, s(v, a) ∈ t.sym2 ∨ s(v, b) ∈ t.sym2) := by
  -- Extract vertices of e
  have hv_in_e : v ∈ e := by
    have : v ∈ e ∩ f := by rw [hv]; exact mem_singleton_self v
    exact mem_of_mem_inter_left this
  obtain ⟨x, y, z, hxy, hxz, hyz, he_eq⟩ := card_eq_three.mp he_card
  rw [he_eq] at hv_in_e
  simp only [mem_insert, mem_singleton] at hv_in_e
  -- v is one of x, y, z; the other two are a, b
  rcases hv_in_e with rfl | rfl | rfl
  · use y, z
    constructor; exact hyz
    constructor; rw [he_eq]; simp
    constructor; rw [he_eq]; simp
    constructor; exact hxy.symm
    constructor; exact hxz.symm
    intro t ht
    have hx_in_t : x ∈ t := X_ef_contains_shared_vertex G M hM e f he hf hef x hv t ht
    -- t shares ≥2 vertices with e = {x,y,z}, and x ∈ t
    -- So t contains x and at least one of y, z
    have ht_inter : (t ∩ e).card ≥ 2 := by
      simp only [X_ef, mem_filter] at ht
      exact ht.2.1
    have hx_in_inter : x ∈ t ∩ e := by
      rw [he_eq]
      exact mem_inter.mpr ⟨hx_in_t, mem_insert_self x _⟩
    -- Since |t ∩ e| ≥ 2 and x ∈ t ∩ e, there exists another vertex in t ∩ e
    have ht_card : t.card = 3 := by
      have := (X_ef G e f).mem_filter.mp ht
      exact (G.mem_cliqueFinset_iff.mp this.1).2
    rw [he_eq] at ht_inter
    -- Need to show y ∈ t or z ∈ t
    by_cases hy : y ∈ t
    · left
      simp only [Finset.sym2, Finset.mem_image, Finset.mem_filter, Finset.mem_powersetCard]
      use {x, y}
      constructor
      · constructor
        · intro w hw
          simp only [mem_insert, mem_singleton] at hw
          rcases hw with rfl | rfl <;> assumption
        · simp
      · simp [Sym2.eq_iff]
    · have hz : z ∈ t := by
        -- If y ∉ t, then since |t ∩ e| ≥ 2 and x ∈ t ∩ e, we need z ∈ t
        have : t ∩ e ⊆ {x, z} := by
          intro w hw
          simp only [mem_inter, mem_insert, mem_singleton] at hw ⊢
          rcases hw.2 with rfl | rfl | rfl
          · left; rfl
          · exact absurd hw.1 hy
          · right; rfl
        have hcard : ({x, z} : Finset V).card ≥ 2 := by
          have := card_le_card this
          omega
        have hxz_card : ({x, z} : Finset V).card = 2 := by
          rw [card_insert_of_not_mem (by simp [hxz]), card_singleton]
        -- Since t ∩ e ⊆ {x,z} and |t ∩ e| ≥ 2 and |{x,z}| = 2, we have t ∩ e = {x,z}
        have : t ∩ e = {x, z} := by
          apply eq_of_subset_of_card_le this
          omega
        -- So z ∈ t ∩ e, hence z ∈ t
        have : z ∈ t ∩ e := by rw [this]; simp
        exact mem_of_mem_inter_left this
      right
      simp only [Finset.sym2, Finset.mem_image, Finset.mem_filter, Finset.mem_powersetCard]
      use {x, z}
      constructor
      · constructor
        · intro w hw
          simp only [mem_insert, mem_singleton] at hw
          rcases hw with rfl | rfl <;> assumption
        · simp
      · simp [Sym2.eq_iff]
  · -- Similar case analysis for v = y
    use x, z
    sorry
  · -- Similar case analysis for v = z
    use x, y
    sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4 via spoke cover strategy
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF STRATEGY:
1. For each M-element, construct a 2-edge cover using spokes through shared vertices
2. Show that S_e triangles NOT covered by spokes are covered by OTHER M-element covers
3. Show that X_{e,f} bridges are covered by spoke edges

The key insight: If S_A has a "base triangle" {a₁,a₂,x} not covered by A's spoke edges,
then x must be a vertex that allows coverage by other M-elements.

Actually, this is where the proof gets hard. The base triangle {a₁,a₂,x} might not
share any edge with B, C, or D (that's why it's in S_A, not in X_{A,B} etc.).

We need to either:
(a) Prove such triangles can't exist in PATH_4 configurations, OR
(b) Prove they're covered by some global structure, OR
(c) Accept τ ≤ 10 or τ ≤ 12 as the best achievable bound

Let's try approach (a): analyze when base triangles in S_A can exist.
-/

/-- Base triangles avoiding shared vertex might not exist in PATH_4 -/
lemma base_triangle_constraint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (h_adj : (A ∩ B).card = 1)
    (v : V) (hv : A ∩ B = {v})
    (a₁ a₂ : V) (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (ha₁v : a₁ ≠ v) (ha₂v : a₂ ≠ v) (ha₁a₂ : a₁ ≠ a₂)
    (x : V) (hx_not_A : x ∉ A)
    (ht_clique : {a₁, a₂, x} ∈ G.cliqueFinset 3)
    (ht_in_Se : {a₁, a₂, x} ∈ S_e G M A) :
    -- The base triangle {a₁, a₂, x} must have some special structure
    -- that allows it to be covered by the 8-edge cover
    ∃ e ∈ ({s(v, a₁), s(v, a₂)} : Finset (Sym2 V)), e ∈ ({a₁, a₂, x} : Finset V).sym2 := by
  -- This is FALSE in general! The base triangle {a₁,a₂,x} doesn't contain v.
  -- So it can't be covered by edges through v.
  -- This is exactly the gap that blocks τ ≤ 8.
  sorry

/-- Alternative: Count base triangles and show they're few -/
lemma base_triangles_bounded (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M) (hA_card : A.card = 3)
    (v : V) (hv : v ∈ A) :
    -- Triangles in S_A that avoid v
    let base_triangles := (S_e G M A).filter (fun t => v ∉ t)
    -- All such triangles share the same base edge {a₁, a₂}
    ∀ t₁ t₂ ∈ base_triangles, (t₁ ∩ A) = (t₂ ∩ A) := by
  -- This follows from S_e_structure: either all triangles share an edge,
  -- or they have star structure with external vertex x.
  -- In star structure, x ∉ A, so base triangles form {a,b,x} for fixed {a,b} ⊆ A.
  sorry

-- The actual bound we can prove with current scaffolding
theorem tau_le_8_path4_conditional (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D)
    -- CONDITION: No base triangles exist (all S_e triangles go through shared vertices)
    (h_no_base_A : ∀ t ∈ S_e G M A, ∃ v ∈ A ∩ B, v ∈ t)
    (h_no_base_D : ∀ t ∈ S_e G M D, ∃ v ∈ C ∩ D, v ∈ t) :
    triangleCoveringNumber G ≤ 8 := by
  -- Under this condition, the 8-edge spoke cover works
  sorry

-- Without the condition, we fall back to τ ≤ 12
theorem tau_le_12_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (hpath : isPath4 M A B C D) :
    triangleCoveringNumber G ≤ 12 := by
  -- This is proven in slot139
  sorry

end
