/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b96583cc-e65e-420e-8cfe-dd8627b90ebe

The following was proved by Aristotle:

- lemma bridges_contain_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t

- lemma triangle_decomposition_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (v₁ v₂ v₃ : V)
    (hPath : isPath4Packing M A B C D v₁ v₂ v₃) :
    G.cliqueFinset 3 = S_e G M A ∪ S_e G M B ∪ S_e G M C ∪ S_e G M D ∪
                       X_ef G A B ∪ X_ef G B C ∪ X_ef G C D

- lemma Se_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    Disjoint (S_e G M e) (S_e G M f)

The following was negated by Aristotle:

- lemma Se_disjoint_Xef (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f g : Finset V) (he : e ∈ M) :
    Disjoint (S_e G M e) (X_ef G f g)

- lemma bridges_covered_by_one_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v w : V) (hv : e ∩ f = {v}) (hvw : G.Adj v w) :
    ∀ t ∈ X_ef G e f, s(v, w) ∈ t.sym2

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```


-/

/-
Tuza ν=4 Strategy - Slot 54: S_e Decomposition with Bridge Absorption

ALTERNATIVE APPROACH: Instead of τ(T_pair) ≤ 4, use individual S_e bounds.

KEY INSIGHT:
- τ(S_e) ≤ 2 for each e (PROVEN in slot44)
- Bridges X_{e,f} all contain the shared vertex (PROVEN)
- Total triangles = ⋃ S_e ∪ ⋃ X_{e,f} (disjoint!)

STRATEGY FOR PATH_4 (A-B-C-D):
All triangles = S_A ∪ S_B ∪ S_C ∪ S_D ∪ X_{A,B} ∪ X_{B,C} ∪ X_{C,D}

NAIVE BOUND: 4×2 + 3×2 = 14 (way too loose!)

CLEVER BOUND via shared covers:
- X_{A,B} ⊆ triangles containing v₁
- X_{B,C} ⊆ triangles containing v₂
- X_{C,D} ⊆ triangles containing v₃

If we use spokes at v₁, v₂, v₃, bridges are FREE!

COVER CONSTRUCTION:
- Edge {v₁, a₁}: covers v₁-containing in S_A, part of X_{A,B}
- Edge {a₁, a₂}: covers v₁-avoiding in S_A (base edge)
- Edge {v₁, v₂}: covers part of X_{A,B}, part of S_B, part of X_{B,C}
- Edge {v₂, b}: covers part of S_B, bridges
- Edge {v₂, v₃}: covers part of X_{B,C}, part of S_C, part of X_{C,D}
- Edge {v₃, c}: covers part of S_C, bridges
- Edge {v₃, d₁}: covers part of S_D
- Edge {d₁, d₂}: covers v₃-avoiding in S_D

Total: 8 edges!

The key is that shared vertices create OVERLAP in coverage.
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (same as slot44)
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

-- S_e: triangles sharing edge with e but NOT bridging to other packing elements
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- X_{e,f}: bridges between e and f (triangles sharing edge with both)
def X_ef (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

-- PATH_4 structure
def isPath4Packing (M : Finset (Finset V)) (A B C D : Finset V)
    (v₁ v₂ v₃ : V) : Prop :=
  M = {A, B, C, D} ∧
  A ∩ B = {v₁} ∧ B ∩ C = {v₂} ∧ C ∩ D = {v₃} ∧
  A ∩ C = ∅ ∧ A ∩ D = ∅ ∧ B ∩ D = ∅ ∧
  v₁ ≠ v₂ ∧ v₂ ≠ v₃ ∧ v₁ ≠ v₃

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMAS (from slot44)
-- ══════════════════════════════════════════════════════════════════════════════

/-- τ(S_e) ≤ 2 for any packing element e. PROVEN in slot44. -/
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  sorry

-- Full proof in slot44

/-- Bridges X_{e,f} all contain the shared vertex. PROVEN in slot44. -/
lemma bridges_contain_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v})
    (t : Finset V) (ht : t ∈ X_ef G e f) :
    v ∈ t := by
  -- Since t intersects e in at least two elements and e ∩ f = {v}, t must contain v.
  have h_inter_e : (t ∩ e).card ≥ 2 := by
    unfold X_ef at ht; aesop;
  have h_inter_f : (t ∩ f).card ≥ 2 := by
    unfold X_ef at ht; aesop;
  contrapose! h_inter_e;
  -- Since $t \cap e$ and $t \cap f$ are subsets of $e$ and $f$ respectively, and $e \cap f = \{v\}$, we have $(t \cap e) \cap (t \cap f) = \emptyset$.
  have h_inter_empty : (t ∩ e) ∩ (t ∩ f) = ∅ := by
    simp_all +decide [ Finset.ext_iff ];
  have h_inter_card : (t ∩ e).card + (t ∩ f).card ≤ t.card := by
    rw [ ← Finset.card_union_add_card_inter ];
    exact le_trans ( add_le_add_right ( Finset.card_mono ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ) _ ) ( by simp +decide [ h_inter_empty ] );
  have h_inter_card_le : t.card ≤ 3 := by
    have h_inter_card_le : t ∈ G.cliqueFinset 3 := by
      unfold X_ef at ht; aesop;
    exact Finset.mem_filter.mp h_inter_card_le |>.2 |> fun h => by simpa using h.card_eq.le;
  linarith

-- Full proof in slot44

-- ══════════════════════════════════════════════════════════════════════════════
-- DECOMPOSITION LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/- All triangles decompose into S_e sets and bridge sets. -/
noncomputable section AristotleLemmas

/-
Every triangle in the graph must share at least one edge (intersection size >= 2) with some triangle in a maximum packing M. If not, we could add the triangle to M, contradicting maximality.
-/
lemma max_packing_intersects_every_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ T ∈ M, (t ∩ T).card ≥ 2 := by
      unfold isMaxPacking at hM;
      unfold isTrianglePacking at hM;
      unfold trianglePackingNumber at hM;
      -- If there's no such T, then M ∪ {t} would form a larger packing, contradicting the maximality of M.
      by_contra h_no_T
      have h_larger_packing : isTrianglePacking G (M ∪ {t}) := by
        constructor <;> simp_all +decide [ Finset.subset_iff ];
        intro x hx y hy hxy; cases hx <;> cases hy <;> simp_all +decide [ Finset.inter_comm ] ;
        · exact Nat.le_of_lt_succ ( h_no_T _ ‹_› );
        · linarith [ h_no_T x ‹_› ];
        · exact hM.1.2 ‹x ∈ M› ‹y ∈ M› hxy;
      -- Since $M$ is a maximum packing, $M \cup \{t\}$ cannot be a larger packing.
      have h_max_packing : M.card ≥ (M ∪ {t}).card := by
        have h_max_packing : ∀ S ∈ (G.cliqueFinset 3).powerset.filter (isTrianglePacking G), S.card ≤ M.card := by
          intro S hS; rw [ hM.2 ] ; exact (by
          have := Finset.le_max ( Finset.mem_image_of_mem Finset.card hS );
          cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop);
        grind;
      by_cases h : t ∈ M <;> simp_all +decide;
      specialize h_no_T t h ; simp_all +decide [ Finset.inter_comm ];
      exact h_no_T.not_le ( by rw [ ht.card_eq ] ; decide )

/-
If two sets A and B are disjoint, there are no triangles that share an edge (>= 2 vertices) with both A and B. This is because a triangle has size 3, and sharing >= 2 vertices with disjoint sets would require size >= 4.
-/
lemma no_bridge_between_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hdisj : A ∩ B = ∅) :
    X_ef G A B = ∅ := by
      ext t;
      -- If $t \in X_{ef}$, then $t$ must share an edge with both $A$ and $B$.
      simp [X_ef, hdisj];
      intro ht htA
      have h_card : (t ∩ A).card + (t ∩ B).card ≤ t.card := by
        rw [ ← Finset.card_union_of_disjoint ];
        · exact Finset.card_le_card fun x hx => by aesop;
        · exact Finset.disjoint_left.mpr fun x hx hx' => Finset.notMem_empty x ( hdisj ▸ Finset.mem_inter.mpr ⟨ Finset.mem_inter.mp hx |>.2, Finset.mem_inter.mp hx' |>.2 ⟩ );
      linarith [ Finset.card_eq_sum_ones t, ht.card_eq ]

/-
In a Path4 packing (A-B-C-D), the non-adjacent pairs (A,C), (A,D), and (B,D) are disjoint by definition. Therefore, by `no_bridge_between_disjoint`, the bridge sets X_ef between them are empty.
-/
lemma path4_empty_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V) (v₁ v₂ v₃ : V)
    (hPath : isPath4Packing M A B C D v₁ v₂ v₃) :
    X_ef G A C = ∅ ∧ X_ef G A D = ∅ ∧ X_ef G B D = ∅ := by
      have := hPath.2.2.2;
      exact ⟨ no_bridge_between_disjoint G A C this.2.1, no_bridge_between_disjoint G A D this.2.2.1, no_bridge_between_disjoint G B D this.2.2.2.1 ⟩

/-
Every triangle `t` in `G` is either in `S_e` for some `T` in `M` (meaning it shares an edge with `T` and no other packing triangle), or it is in `X_ef` for some pair `T1, T2` in `M` (meaning it shares an edge with both `T1` and `T2`). This follows from `max_packing_intersects_every_triangle`: `t` must share an edge with at least one `T`. If it shares with exactly one, it's in `S_e`. If it shares with more than one, it's in `X_ef`.
-/
lemma triangle_in_S_or_X (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    (∃ T ∈ M, t ∈ S_e G M T) ∨ (∃ T1 ∈ M, ∃ T2 ∈ M, T1 ≠ T2 ∧ t ∈ X_ef G T1 T2) := by
      obtain ⟨T, hT⟩ : ∃ T ∈ M, (t ∩ T).card ≥ 2 := max_packing_intersects_every_triangle G M hM t ht;
      by_cases hT_unique : ∀ T' ∈ M, T' ≠ T → (t ∩ T').card ≤ 1;
      · unfold S_e;
        unfold trianglesSharingEdge; aesop;
      · simp_all +decide [ S_e, X_ef ];
        exact Or.inr ⟨ _, hT_unique.choose_spec.1, _, hT.1, hT_unique.choose_spec.2.1, hT_unique.choose_spec.2.2, hT.2 ⟩

end AristotleLemmas

lemma triangle_decomposition_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (v₁ v₂ v₃ : V)
    (hPath : isPath4Packing M A B C D v₁ v₂ v₃) :
    G.cliqueFinset 3 = S_e G M A ∪ S_e G M B ∪ S_e G M C ∪ S_e G M D ∪
                       X_ef G A B ∪ X_ef G B C ∪ X_ef G C D := by
  apply Finset.ext
  intro t
  simp [triangle_in_S_or_X];
  constructor;
  · intro ht;
    -- By `triangle_in_S_or_X`, $t$ is either in $S_e$ for some $e \in M$ or in $X_{ef}$ for some distinct $e, f \in M$.
    have h_triangle_in_S_or_X : t ∈ S_e G M A ∪ S_e G M B ∪ S_e G M C ∪ S_e G M D ∪ X_ef G A B ∪ X_ef G A C ∪ X_ef G A D ∪ X_ef G B C ∪ X_ef G B D ∪ X_ef G C D := by
      rcases hPath with ⟨ rfl, hA, hB, hC, hD ⟩ ; simp_all +decide [ isPath4Packing ] ;
      have := triangle_in_S_or_X G { A, B, C, D } hM t ( by simpa [ SimpleGraph.isNClique_iff ] using ht ) ; simp_all +decide [ S_e, X_ef ] ;
      grind +ring;
    -- Since `X_{AC} = X_{AD} = X_{BD} = ∅`, we can simplify the union.
    have h_empty_bridges : X_ef G A C = ∅ ∧ X_ef G A D = ∅ ∧ X_ef G B D = ∅ := by
      exact?;
    aesop;
  · unfold S_e X_ef;
    unfold trianglesSharingEdge; aesop;

/-- The decomposition has disjoint components (except bridges overlap with nothing). -/
lemma Se_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    Disjoint (S_e G M e) (S_e G M f) := by
  unfold S_e;
  unfold trianglesSharingEdge; rw [ Finset.disjoint_left ] ; aesop;

/- Aristotle found this block to be false. Here is a proof of the negation:



lemma Se_disjoint_Xef (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f g : Finset V) (he : e ∈ M) :
    Disjoint (S_e G M e) (X_ef G f g) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  fconstructor;
  exact ULift ( Fin 3 );
  refine' ⟨ inferInstance, inferInstance, _, _, _ ⟩;
  exact ⊤;
  infer_instance;
  native_decide +revert

-/
lemma Se_disjoint_Xef (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f g : Finset V) (he : e ∈ M) :
    Disjoint (S_e G M e) (X_ef G f g) := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
══════════════════════════════════════════════════════════════════════════════
KEY INSIGHT: Bridges are covered by spokes
══════════════════════════════════════════════════════════════════════════════

All bridges at vertex v are covered by any edge incident to v.
Since bridges_contain_shared_vertex, one spoke covers all bridges at that vertex.
-/
lemma bridges_covered_by_one_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v w : V) (hv : e ∩ f = {v}) (hvw : G.Adj v w) :
    ∀ t ∈ X_ef G e f, s(v, w) ∈ t.sym2 := by
  intro t ht
  have hv_in_t : v ∈ t := bridges_contain_shared_vertex G e f v hv t ht
  -- t is a triangle containing v, so it has edges {v, x} and {v, y} for some x, y
  -- If w ∈ t, then s(v,w) ∈ t.sym2
  -- Need to show w ∈ t... this is NOT always true!
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose the specific graph $G$ and sets $e$, $f$, $v$, and $w$ as described.
  use ULift (Fin 4);
  -- Let's choose the specific graph $G$ and sets $e$, $f$, $v$, and $w$ as described in the provided solution.
  use inferInstance, inferInstance, SimpleGraph.mk (fun v w => v ≠ w), inferInstance;
  -- Let's choose the specific triangle $t$ as described.
  simp +decide [X_ef]

-/
-- ══════════════════════════════════════════════════════════════════════════════
-- KEY INSIGHT: Bridges are covered by spokes
-- ══════════════════════════════════════════════════════════════════════════════

/--
All bridges at vertex v are covered by any edge incident to v.
Since bridges_contain_shared_vertex, one spoke covers all bridges at that vertex.
-/
lemma bridges_covered_by_one_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v w : V) (hv : e ∩ f = {v}) (hvw : G.Adj v w) :
    ∀ t ∈ X_ef G e f, s(v, w) ∈ t.sym2 := by
  intro t ht
  have hv_in_t : v ∈ t := bridges_contain_shared_vertex G e f v hv t ht
  -- t is a triangle containing v, so it has edges {v, x} and {v, y} for some x, y
  -- If w ∈ t, then s(v,w) ∈ t.sym2
  -- Need to show w ∈ t... this is NOT always true!
  sorry

/- Aristotle took a wrong turn (reason code: 13). Please try again. -/
/--
Actually: τ(X_{e,f}) ≤ 1 since all bridges contain v.
Any single edge through v covers all bridges.
-/
lemma tau_bridges_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (hv : e ∩ f = {v}) (he : e ∈ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (X_ef G e f) ≤ 1 := by
  -- All bridges contain v, so any edge {v, x} where x is adjacent to all bridges works
  -- Actually, we just need one edge from each bridge triangle
  -- Since all contain v, use any spoke from v
  sorry

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 8-edge cover for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/--
For PATH_4, construct explicit 8-edge cover:

Let A = {v₁, a₁, a₂}, B = {v₁, v₂, b}, C = {v₂, v₃, c}, D = {v₃, d₁, d₂}

Cover edges:
1. {a₁, a₂}: covers S_A avoiding v₁
2. {v₁, a₁}: covers S_A containing v₁, part of X_{A,B}
3. {v₁, v₂}: covers part of X_{A,B}, part of S_B, part of X_{B,C}
4. {v₂, b}: covers S_B, X_{A,B}, X_{B,C}
5. {v₂, v₃}: covers part of X_{B,C}, part of S_C, part of X_{C,D}
6. {v₃, c}: covers S_C, X_{B,C}, X_{C,D}
7. {v₃, d₁}: covers S_D containing v₃, part of X_{C,D}
8. {d₁, d₂}: covers S_D avoiding v₃

This works because:
- S_A, S_D need base edges for avoiding triangles (2 edges)
- S_B, S_C are "middle" elements, covered by shared vertex spokes
- All bridges are absorbed by spokes at shared vertices
-/
theorem tau_le_8_path4_via_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (v₁ v₂ v₃ : V)
    (a₁ a₂ b c d₁ d₂ : V)
    (hA : A = {v₁, a₁, a₂}) (hB : B = {v₁, v₂, b})
    (hC : C = {v₂, v₃, c}) (hD : D = {v₃, d₁, d₂})
    (hPath : isPath4Packing M A B C D v₁ v₂ v₃)
    -- Distinctness conditions
    (h_distinct_A : v₁ ≠ a₁ ∧ v₁ ≠ a₂ ∧ a₁ ≠ a₂)
    (h_distinct_B : v₁ ≠ v₂ ∧ v₁ ≠ b ∧ v₂ ≠ b)
    (h_distinct_C : v₂ ≠ v₃ ∧ v₂ ≠ c ∧ v₃ ≠ c)
    (h_distinct_D : v₃ ≠ d₁ ∧ v₃ ≠ d₂ ∧ d₁ ≠ d₂)
    -- Triangles are in G
    (hA_tri : A ∈ G.cliqueFinset 3) (hB_tri : B ∈ G.cliqueFinset 3)
    (hC_tri : C ∈ G.cliqueFinset 3) (hD_tri : D ∈ G.cliqueFinset 3) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- Construct the 8-edge cover
  let cover : Finset (Sym2 V) := {s(a₁, a₂), s(v₁, a₁), s(v₁, v₂), s(v₂, b),
                                   s(v₂, v₃), s(v₃, c), s(v₃, d₁), s(d₁, d₂)}
  -- Show cover has size 8
  have h_size : cover.card ≤ 8 := by
    sorry
  -- Show cover ⊆ G.edgeFinset
  have h_edges : cover ⊆ G.edgeFinset := by
    sorry
  -- Show cover covers all triangles
  have h_covers : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ cover, e ∈ t.sym2 := by
    intro t ht
    -- Use decomposition: t is in some S_e or X_{e,f}
    sorry
  -- Conclude
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- BONUS: Same approach works for CYCLE_4
-- ══════════════════════════════════════════════════════════════════════════════

def isCycle4Packing (M : Finset (Finset V)) (A B C D : Finset V)
    (v₁ v₂ v₃ v₄ : V) : Prop :=
  M = {A, B, C, D} ∧
  A ∩ B = {v₁} ∧ B ∩ C = {v₂} ∧ C ∩ D = {v₃} ∧ D ∩ A = {v₄} ∧
  A ∩ C = ∅ ∧ B ∩ D = ∅ ∧  -- diagonal pairs are disjoint
  v₁ ≠ v₂ ∧ v₂ ≠ v₃ ∧ v₃ ≠ v₄ ∧ v₄ ≠ v₁

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
theorem tau_le_8_cycle4_via_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (v₁ v₂ v₃ v₄ : V)
    (hCycle : isCycle4Packing M A B C D v₁ v₂ v₃ v₄) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- Similar construction with 8 edges, using spokes at all 4 shared vertices
  sorry

end