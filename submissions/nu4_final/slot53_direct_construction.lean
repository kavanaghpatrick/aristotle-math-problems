/-
Slot53: Direct 4-Edge Construction for tau_pair_le_4

DIFFERENT APPROACH: Instead of proving avoiding is empty,
find 4 specific edges that cover ALL of T_pair.

KEY INSIGHT: We don't need to use the v-decomposition!
Instead, find 4 edges E' ⊆ G.edgeFinset such that:
∀ t ∈ T_pair(e,f), ∃ edge ∈ E', edge ∈ t.sym2

CANDIDATE CONSTRUCTION:
Let e = {v, a, b} and f = {v, c, d}.

Option 1: {v,a}, {v,c}, {a,b}, {c,d}
- Covers e (has {v,a}, {a,b})
- Covers f (has {v,c}, {c,d})
- Covers avoiding triangles (they must share {a,b} or {c,d})
- Covers containing triangles... MAYBE NOT ALL!
  - Triangle {v,b,x} contains v, shares edge {v,b} with e
  - Not covered by {v,a}, {v,c}, {a,b}, {c,d}!

Option 2: {a,b}, {c,d}, {v,x}, {v,y} for carefully chosen x,y
- If all external containing triangles share a common vertex x...
- This relates to the Se_structure_lemma!

Option 3: Use Se_structure_lemma on both e and f
- Se_structure says: either common edge OR common external vertex
- If common edge through v → 1 edge covers S_e (excluding e itself)
- If common external x → edges {v,x} covers all externals at e

STRATEGY: Case split using Se_structure on e and f,
then construct appropriate 4 edges for each case.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (same as slot52)
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

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def isTriangleCover (G : SimpleGraph V) (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN INFRASTRUCTURE (from slot44)
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  sorry -- PROVEN in slot44

lemma triangleCoveringNumberOn_le_of_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (E' : Finset (Sym2 V))
    (hE : E' ⊆ G.edgeFinset)
    (h_cover : ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) :
    triangleCoveringNumberOn G triangles ≤ E'.card := by
  sorry -- Standard lemma, proven in slot44

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Se_structure_lemma (from slot44)
-- KEY: S_e has either common edge OR common external vertex
-- ══════════════════════════════════════════════════════════════════════════════

lemma Se_structure_lemma (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    (∃ uv, uv ⊆ e ∧ uv.card = 2 ∧ ∀ t ∈ S_e G M e, t ≠ e → uv ⊆ t) ∨
    (∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → t = (t ∩ e) ∪ {x}) := by
  sorry -- PROVEN in slot44

-- ══════════════════════════════════════════════════════════════════════════════
-- NEW LEMMAS FOR DIRECT CONSTRUCTION
-- ══════════════════════════════════════════════════════════════════════════════

/-- When all non-e triangles in S_e share a common edge uv ⊆ e,
    that single edge covers all of S_e except possibly e itself -/
lemma cover_Se_common_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (uv : Finset V) (huv_sub : uv ⊆ e) (huv_card : uv.card = 2)
    (h_common : ∀ t ∈ S_e G M e, t ≠ e → uv ⊆ t) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ isTriangleCover G (S_e G M e) E' := by
  sorry
  -- HINT: Use uv for the external triangles, plus one edge from e for e itself
  -- Actually just {uv} covers all non-e, and uv ⊆ e so uv covers e too!
  -- So E' = {sym2_of uv} has card 1 ≤ 2

/-- When all non-e triangles in S_e share a common external vertex x,
    the edge {v, x} covers all containing triangles (where v is the shared vertex) -/
lemma cover_Se_common_external (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (v : V) (hv : v ∈ e)
    (x : V) (hx : x ∉ e)
    (h_common : ∀ t ∈ S_e G M e, t ≠ e → t = (t ∩ e) ∪ {x}) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧
      isTriangleCover G (trianglesContaining (S_e G M e) v) E' := by
  sorry
  -- HINT: Use {v, x} to cover all external triangles containing v
  -- Each such triangle is (t ∩ e) ∪ {x}, and if v ∈ t then v ∈ t ∩ e
  -- So t contains both v and x, hence {v,x} ∈ t.sym2

-- ══════════════════════════════════════════════════════════════════════════════
-- DECOMPOSITION OF T_pair
-- ══════════════════════════════════════════════════════════════════════════════

/-- T_pair = S_e ∪ S_f ∪ X_ef where X_ef = bridges sharing edge with both -/
def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

lemma T_pair_eq_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) :
    T_pair G e f = S_e G M e ∪ S_e G M f ∪ X_ef G e f := by
  sorry
  -- This is a set-theoretic decomposition

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGES THROUGH SHARED VERTEX
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridges_contain_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  simp_all +decide [ Finset.ext_iff, X_ef ];
  by_contra hv_not_in_t
  have h_disjoint : Disjoint (t ∩ e) (t ∩ f) := by
    exact Finset.disjoint_left.mpr fun x hx hx' => hv_not_in_t <| by have := hv x; aesop;
  have h_card : (t ∩ e) ∪ (t ∩ f) ⊆ t := by aesop_cat;
  have := Finset.card_le_card h_card; simp_all +decide [ Finset.card_union_add_card_inter ] ;
  linarith [ ht.1.card_eq ]

/-- Bridges can be covered by 2 edges through v -/
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 2 := by
  sorry -- PROVEN in slot44

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Case Analysis via Se_structure
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_pair_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (hv : e ∩ f = {v}) :
    triangleCoveringNumberOn G (T_pair G e f) ≤ 4 := by
  -- Get structure of S_e and S_f
  obtain ⟨uv_e, huv_e_sub, huv_e_card, huv_e_common⟩ | ⟨x_e, hx_e, hx_e_common⟩ := Se_structure_lemma G M hM e he
  · -- Case: S_e has common edge uv_e
    obtain ⟨uv_f, huv_f_sub, huv_f_card, huv_f_common⟩ | ⟨x_f, hx_f, hx_f_common⟩ := Se_structure_lemma G M hM f hf
    · -- Subcase: Both have common edges
      -- Use uv_e for S_e, uv_f for S_f, plus 2 edges for bridges
      sorry
    · -- Subcase: S_e has common edge, S_f has common external
      sorry
  · -- Case: S_e has common external vertex x_e
    obtain ⟨uv_f, huv_f_sub, huv_f_card, huv_f_common⟩ | ⟨x_f, hx_f, hx_f_common⟩ := Se_structure_lemma G M hM f hf
    · -- Subcase: S_e has common external, S_f has common edge
      sorry
    · -- Subcase: Both have common external vertices
      -- If x_e = x_f, then {v, x_e} covers lots of triangles!
      sorry

end
