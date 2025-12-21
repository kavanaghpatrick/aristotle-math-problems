/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6a718c09-4c2b-4b83-93e0-3dfdf7c4e55e

The following was proved by Aristotle:

- lemma restricted_nu_le_1_implies_cover_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V))
    (h_S : S ⊆ G.cliqueFinset 3)
    (h_pair : (S : Set (Finset V)).Pairwise (fun t₁ t₂ => 2 ≤ (t₁ ∩ t₂).card)) :
    ∃ F : Finset (Sym2 V), F ⊆ G.edgeFinset ∧ F.card ≤ 2 ∧
      ∀ t ∈ S, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F

- lemma vertex_disjoint_share_exclusive (e f t : Finset V)
    (he : e.card = 3) (hf : f.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint e f) :
    ¬((t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

- lemma S_e_pairwise_share_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    (S_e G e M : Set (Finset V)).Pairwise (fun t₁ t₂ => 2 ≤ (t₁ ∩ t₂).card)

- lemma tau_S_e_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∃ F : Finset (Sym2 V), F.card ≤ 2 ∧ ∀ t ∈ S_e G e M, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F

- lemma all_triangles_share_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hM_ne : M.Nonempty) :
    ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2

- lemma Te_Tf_intersection_through_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (v : V) (hve : v ∈ e) (hvf : v ∈ f)
    (h_only_v : e ∩ f = {v}) :
    ∀ t ∈ T_e G e, t ∈ T_e G f → v ∈ t

The following was negated by Aristotle:

- lemma nu3_exists_clean_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3) :
    ∃ e ∈ M, T_e G e = S_e G e M

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
Tuza ν=3 using proven lemmas from ν=1 and ν=2

KEY INSIGHT: The ν=1 proof contains `restricted_nu_le_1_implies_cover_le_2`:
  If triangles pairwise share edges → can be covered by ≤2 edges

Combined with Parker's lemma_2_2 (S_e triangles pairwise share edges),
this gives τ(S_e) ≤ 2 directly!
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Core definitions (matching ν=1 proof style)
def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧ (S : Set (Finset V)).Pairwise fun t₁ t₂ => (t₁ ∩ t₂).card ≤ 1

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (IsTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def IsTriangleCovering (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset (Sym2 V)) : Prop :=
  F ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (IsTriangleCovering G) |>.image Finset.card |>.min |>.getD 0

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (T_e G e).filter (fun t => ∀ m ∈ M, m ≠ e → (t ∩ m).card ≤ 1)

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = trianglePackingNumber G

-- PROVEN in ν=1 (2b21c426): Pairwise edge-sharing → cover with ≤2 edges
-- This is THE KEY LEMMA for τ(S_e) ≤ 2
noncomputable section AristotleLemmas

/-
A nonempty family of triangles where every pair shares at least 2 vertices either all share a common edge, or are all contained in a set of 4 vertices.
-/
lemma intersecting_triangles_structure {V : Type*} [DecidableEq V] (S : Finset (Finset V))
    (h_nonempty : S.Nonempty)
    (h_card : ∀ t ∈ S, t.card = 3)
    (h_pair : (S : Set (Finset V)).Pairwise (fun t₁ t₂ => 2 ≤ (t₁ ∩ t₂).card)) :
    (∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ S, e ⊆ t) ∨
    (∃ A : Finset V, A.card = 4 ∧ ∀ t ∈ S, t ⊆ A) := by
      by_cases h_two_elements : ∃ t₁ t₂, t₁ ∈ S ∧ t₂ ∈ S ∧ t₁ ≠ t₂;
      · -- Let t₁ and t₂ be two distinct elements of S. Let e = t₁ ∩ t₂. Since |t₁| = |t₂| = 3 and they are distinct and |t₁ ∩ t₂| ≥ 2, we must have |e| = 2.
        obtain ⟨t₁, t₂, ht₁, ht₂, h_ne⟩ : ∃ t₁ t₂, t₁ ∈ S ∧ t₂ ∈ S ∧ t₁ ≠ t₂ := h_two_elements
        set e := t₁ ∩ t₂ with he
        have h_e_card : e.card = 2 := by
          have h_e_card : e.card ≥ 2 := by
            exact h_pair ht₁ ht₂ h_ne
          have h_e_card_le : e.card ≤ 2 := by
            have := Finset.card_le_card ( Finset.inter_subset_left : t₁ ∩ t₂ ⊆ t₁ ) ; ( have := Finset.card_le_card ( Finset.inter_subset_right : t₁ ∩ t₂ ⊆ t₂ ) ; simp_all +decide ; );
            interval_cases _ : Finset.card ( t₁ ∩ t₂ ) ; simp_all +decide;
            have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t₁ ∩ t₂ ⊆ t₁ ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : t₁ ∩ t₂ ⊆ t₂ ) ; aesop;
          exact le_antisymm h_e_card_le h_e_card;
        by_cases h_all_contain_e : ∀ t ∈ S, e ⊆ t;
        · exact Or.inl ⟨ e, h_e_card, h_all_contain_e ⟩;
        · -- If there is some t₃ in S that does not contain e, let A = t₁ ∪ t₂. Since t₁ and t₂ share exactly 2 vertices, |A| = 4.
          obtain ⟨t₃, ht₃, h_not_contain_e⟩ : ∃ t₃ ∈ S, ¬e ⊆ t₃ := by
            exact by push_neg at h_all_contain_e; exact h_all_contain_e;
          set A := t₁ ∪ t₂ with hA
          have hA_card : A.card = 4 := by
            have := Finset.card_union_add_card_inter t₁ t₂; aesop;
          -- We claim every t in S is a subset of A.
          have h_all_subset_A : ∀ t ∈ S, t ⊆ A := by
            -- If e ⊆ t, then t = {u, v, z}. If z ∉ {x, y}, then t ∩ t₃ would be too small (check against {v, x, y} and {u, x, y}).
            intros t ht
            by_cases h_e_subset_t : e ⊆ t;
            · have h_t_subset_A : t ⊆ t₁ ∪ t₂ := by
                have h_t_inter_t₃ : (t ∩ t₃).card ≥ 2 := by
                  exact h_pair ht ht₃ ( by aesop )
                have h_t₃_subset_A : t₃ ⊆ t₁ ∪ t₂ := by
                  have h_t₃_inter_t₁ : (t₃ ∩ t₁).card ≥ 2 := by
                    exact h_pair ht₃ ht₁ ( by aesop ) |> fun h => by simpa only [ Finset.inter_comm ] using h;
                  have h_t₃_inter_t₂ : (t₃ ∩ t₂).card ≥ 2 := by
                    exact h_pair ht₃ ht₂ ( by aesop );
                  have h_t₃_subset_A : (t₃ ∩ t₁ ∪ t₃ ∩ t₂).card = 3 := by
                    have h_t₃_subset_A : (t₃ ∩ t₁ ∪ t₃ ∩ t₂).card ≤ t₃.card := by
                      exact Finset.card_le_card fun x hx => by aesop;
                    have h_t₃_subset_A : (t₃ ∩ t₁ ∪ t₃ ∩ t₂).card ≥ (t₃ ∩ t₁).card + (t₃ ∩ t₂).card - (t₃ ∩ t₁ ∩ t₂).card := by
                      rw [ ← Finset.card_union_add_card_inter ];
                      simp +decide [ Finset.inter_left_comm, Finset.inter_comm ];
                    have h_t₃_subset_A : (t₃ ∩ t₁ ∩ t₂).card ≤ 1 := by
                      contrapose! h_not_contain_e;
                      have := Finset.eq_of_subset_of_card_le ( show t₃ ∩ t₁ ∩ t₂ ⊆ t₁ ∩ t₂ from fun x hx => by aesop ) ; aesop;
                    grind;
                  have h_t₃_subset_A : t₃ ∩ t₁ ∪ t₃ ∩ t₂ = t₃ := by
                    exact Finset.eq_of_subset_of_card_le ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ( by aesop );
                  exact h_t₃_subset_A ▸ Finset.union_subset ( Finset.inter_subset_right.trans ( Finset.subset_union_left ) ) ( Finset.inter_subset_right.trans ( Finset.subset_union_right ) )
                have h_t_subset_A : (t ∩ (t₁ ∪ t₂)).card ≥ 3 := by
                  have h_t_subset_A : (t ∩ (t₁ ∪ t₂)).card ≥ (t ∩ t₃).card + (e \ t₃).card := by
                    have h_t_subset_A : (t ∩ (t₁ ∪ t₂)) ⊇ (t ∩ t₃) ∪ (e \ t₃) := by
                      grind;
                    exact le_trans ( by rw [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx₁ hx₂ => by aesop ) ] ) ( Finset.card_mono h_t_subset_A );
                  exact le_trans ( by linarith [ show Finset.card ( e \ t₃ ) ≥ 1 from Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty ( by aesop ) ) ] ) h_t_subset_A;
                have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t ∩ ( t₁ ∪ t₂ ) ⊆ t ) ; aesop;
              exact h_t_subset_A;
            · -- If e ⊈ t, then by the same logic as t₃, t ⊆ A.
              have h_t_subset_A : t ⊆ A := by
                have h_inter_t1 : (t ∩ t₁).card ≥ 2 := by
                  by_cases h : t = t₁ <;> aesop
                have h_inter_t2 : (t ∩ t₂).card ≥ 2 := by
                  exact h_pair ht ht₂ ( by aesop )
                -- Since $t$ intersects $t₁$ and $t₂$ in at least two vertices each, and $t₁$ and $t₂$ share exactly two vertices, $t$ must contain at least three vertices from $t₁ ∪ t₂$.
                have h_three_vertices : (t ∩ (t₁ ∪ t₂)).card ≥ 3 := by
                  have h_three_vertices : (t ∩ t₁).card + (t ∩ t₂).card - (t ∩ t₁ ∩ t₂).card ≥ 3 := by
                    have h_three_vertices : (t ∩ t₁ ∩ t₂).card ≤ 1 := by
                      contrapose! h_e_subset_t;
                      have := Finset.eq_of_subset_of_card_le ( show t ∩ t₁ ∩ t₂ ⊆ t₁ ∩ t₂ from by aesop_cat ) ; aesop;
                    exact le_tsub_of_add_le_left ( by linarith );
                  refine' le_trans h_three_vertices _;
                  rw [ show t ∩ ( t₁ ∪ t₂ ) = ( t ∩ t₁ ) ∪ ( t ∩ t₂ ) by ext; aesop ] ; rw [ ← Finset.card_union_add_card_inter ] ; simp +decide [ *, Finset.inter_left_comm, Finset.inter_comm ] ;
                have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : t ∩ ( t₁ ∪ t₂ ) ⊆ t ) ; aesop;
              exact h_t_subset_A;
          exact Or.inr ⟨ A, hA_card, h_all_subset_A ⟩;
      · -- Since there's only one element in S, let's denote it as t.
        obtain ⟨t, ht⟩ : ∃ t, S = {t} := by
          exact ⟨ h_nonempty.choose, Finset.eq_singleton_iff_unique_mem.mpr ⟨ h_nonempty.choose_spec, fun t ht => Classical.not_not.1 fun h => h_two_elements ⟨ t, h_nonempty.choose, ht, h_nonempty.choose_spec, h ⟩ ⟩ ⟩;
        obtain ⟨ u, v, w, h ⟩ := Finset.card_eq_three.mp ( h_card t ( ht ▸ Finset.mem_singleton_self t ) );
        exact Or.inl ⟨ { u, v }, by aesop ⟩

end AristotleLemmas

lemma restricted_nu_le_1_implies_cover_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V))
    (h_S : S ⊆ G.cliqueFinset 3)
    (h_pair : (S : Set (Finset V)).Pairwise (fun t₁ t₂ => 2 ≤ (t₁ ∩ t₂).card)) :
    ∃ F : Finset (Sym2 V), F ⊆ G.edgeFinset ∧ F.card ≤ 2 ∧
      ∀ t ∈ S, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F := by
  by_cases h : S.Nonempty <;> simp_all +decide [ Finset.subset_iff ];
  · -- Apply `intersecting_triangles_structure` to obtain either an edge or a set of four vertices.
    obtain ⟨e, he⟩ | ⟨A, hA⟩ := intersecting_triangles_structure S h (fun t ht => by
      exact h_S ht |>.2) h_pair;
    · obtain ⟨ u, v, huv ⟩ := Finset.card_eq_two.mp he.1;
      refine' ⟨ { s(u, v) }, _, _, _ ⟩ <;> simp_all +decide [ Sym2.eq_swap ];
      · obtain ⟨ t, ht ⟩ := h; specialize h_S ht; have := h_S.1; aesop;
      · exact fun t ht => ⟨ u, he t ht ( Finset.mem_insert_self _ _ ), v, he t ht ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ), huv.1, Or.inl ⟨ rfl, rfl ⟩ ⟩;
    · -- Let $A = \{a, b, c, d\}$.
      obtain ⟨a, b, c, d, hA_def⟩ : ∃ a b c d : V, A = {a, b, c, d} ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
        simp_rw +decide [ Finset.card_eq_succ ] at hA ; aesop;
      -- Let $F$ be the subset of $\{e_1, e_2\}$ consisting of edges actually present in $G$.
      obtain ⟨F, hF⟩ : ∃ F : Finset (Sym2 V), F ⊆ {s(a, b), s(c, d)} ∧ (∀ t ∈ S, ∃ u ∈ t, ∃ x ∈ t, ¬u = x ∧ s(u, x) ∈ F) := by
        refine' ⟨ { s(a, b), s(c, d) }, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
        intro t ht; specialize h_S ht; rcases h_S with ⟨ ht₁, ht₂ ⟩ ; rcases Finset.card_eq_three.mp ht₂ with ⟨ u, v, w, hu, hv, hw, h ⟩ ; simp_all +decide ;
        rcases hA _ ht ( Finset.mem_insert_self _ _ ) with ( rfl | rfl | rfl | rfl ) <;> rcases hA _ ht ( Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ) ) with ( rfl | rfl | rfl | rfl ) <;> rcases hA _ ht ( Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ) with ( rfl | rfl | rfl | rfl ) <;> simp +decide at hu hv hw ⊢;
      refine' ⟨ F ∩ G.edgeFinset, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      · exact le_trans ( Finset.card_le_card fun x hx => show x ∈ { s(a, b), s(c, d) } from by aesop ) ( Finset.card_insert_le _ _ ) |> le_trans <| by simp +decide ;
      · intro t ht; obtain ⟨ u, hu, v, hv, huv, hF ⟩ := hF.2 t ht; exact ⟨ u, hu, v, hv, huv, hF, by have := h_S ht; exact this.1 hu hv huv ⟩ ;
  · exact ⟨ ∅, by simp +decide ⟩

-- PROVEN in aristotle_tuza_nu1_PROVEN.lean

-- PROVEN in ν=2 (0764be78): Disjoint triangles can't share edge with same t
lemma vertex_disjoint_share_exclusive (e f t : Finset V)
    (he : e.card = 3) (hf : f.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint e f) :
    ¬((t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2) := by
  intro h_inter
  have h_inter_card : (t ∩ e).card + (t ∩ f).card ≤ 3 := by
    rw [ ← Finset.card_union_of_disjoint ];
    · exact le_trans ( Finset.card_le_card ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ) ht.le;
    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.disjoint_left.mp h_disj ( Finset.mem_inter.mp hx₁ |>.2 ) ( Finset.mem_inter.mp hx₂ |>.2 );
  linarith

-- PROVEN in aristotle_tuza_nu2_PROVEN.lean

-- Parker's lemma 2.2: S_e triangles pairwise share edges
noncomputable section AristotleLemmas

lemma packing_augmentation_contradiction {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t₁ t₂ : Finset V)
    (ht₁ : t₁ ∈ S_e G e M) (ht₂ : t₂ ∈ S_e G e M)
    (hne₁ : t₁ ≠ e) (hne₂ : t₂ ≠ e)
    (h_disj : (t₁ ∩ t₂).card ≤ 1)
    (h_diff : t₁ ≠ t₂) : False := by
      -- We claim that $|M'| = |M| + 1$.
      have h_card_M' : ((M \ {e}) ∪ {t₁, t₂}).card = M.card + 1 := by
        have h_card_M'_eq : ((M \ {e}) ∪ {t₁, t₂}).card = (M \ {e}).card + 2 := by
          rw [ Finset.card_union ] ; simp +decide [ * ];
          rw [ show M \ { e } ∩ { t₁, t₂ } = ∅ from Finset.eq_empty_of_forall_notMem fun x hx => ?_ ] ; simp +decide [ * ];
          simp_all +decide [ S_e ];
          rcases hx.2 with ( rfl | rfl ) <;> simp_all +decide [ T_e ];
          · have := ht₁.2 x hx.1 hx.2; simp_all +decide [ Finset.inter_comm ] ;
            exact this.not_lt ( by have := ht₁.1.1.2; aesop );
          · exact absurd ( ht₂.2 x hx.1 hx.2 ) ( by have := ht₂.1.2; have := ht₂.1.1; have := ht₁.1.2; have := ht₁.1.1; simp_all +decide [ SimpleGraph.isNClique_iff ] );
        grind;
      -- We claim that $M'$ is a triangle packing.
      have h_M'_packing : IsTrianglePacking G ((M \ {e}) ∪ {t₁, t₂}) := by
        constructor;
        · unfold S_e at ht₁ ht₂;
          unfold T_e at *; simp_all +decide [ Finset.subset_iff ] ;
          exact fun m hm hm' => hM.1.1 hm |> fun h => by simpa using h;
        · simp_all +decide [ Set.Pairwise, Finset.subset_iff ];
          simp_all +decide [ Finset.inter_comm, S_e ];
          exact fun a ha ha' b hb hb' hab => hM.1.2 ha hb hab;
      have h_max_packing : ∀ S : Finset (Finset V), IsTrianglePacking G S → S.card ≤ M.card := by
        have := hM.2;
        rw [this];
        intro S hS; exact (by
        have h_max_packing : S ∈ Finset.filter (IsTrianglePacking G) (Finset.powerset (G.cliqueFinset 3)) := by
          exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hS.1, hS ⟩;
        have h_max_packing : ∀ x ∈ Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (Finset.powerset (G.cliqueFinset 3))), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (Finset.powerset (G.cliqueFinset 3)))).max 0 := by
          intro x hx;
          have := Finset.le_max hx;
          cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( IsTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
        exact h_max_packing _ ( Finset.mem_image_of_mem _ ‹_› ));
      linarith [ h_max_packing _ h_M'_packing ]

end AristotleLemmas

lemma S_e_pairwise_share_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    (S_e G e M : Set (Finset V)).Pairwise (fun t₁ t₂ => 2 ≤ (t₁ ∩ t₂).card) := by
  intro t₁ ht₁ t₂ ht₂ hne;
  by_contra h_contra;
  have := packing_augmentation_contradiction G M hM e he t₁ t₂ ht₁ ht₂;
  simp_all +decide [ Finset.mem_coe, S_e ];
  by_cases h₁ : t₁ = e <;> by_cases h₂ : t₂ = e <;> simp_all +decide;
  · unfold T_e at *; simp_all +decide ;
    exact h_contra.not_le ( by simpa only [ Finset.inter_comm ] using ht₂.1.2 );
  · exact h_contra.not_le ( by simpa using Finset.mem_filter.mp ht₁.1 |>.2 );
  · linarith

-- PROVEN in aristotle_parker_full.lean (lemma_2_2)

-- DIRECT CONSEQUENCE: τ(S_e) ≤ 2
lemma tau_S_e_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∃ F : Finset (Sym2 V), F.card ≤ 2 ∧ ∀ t ∈ S_e G e M, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F := by
  have := S_e_pairwise_share_edges G M hM e he;
  -- Since $\nu(S_e) \leq 1$, by Parker's lemma 2.2, we can cover $S_e$ with at most 2 edges.
  obtain ⟨F, hF⟩ : ∃ F : Finset (Sym2 V), F ⊆ G.edgeFinset ∧ F.card ≤ 2 ∧ ∀ t ∈ S_e G e M, ∃ u v, u ∈ t ∧ v ∈ t ∧ u ≠ v ∧ s(u, v) ∈ F := by
    convert restricted_nu_le_1_implies_cover_le_2 _ _ _ this;
    exact fun x hx => Finset.mem_filter.mp hx |>.1 |> Finset.mem_filter.mp |>.1;
  exact ⟨ F, hF.2.1, hF.2.2 ⟩

-- Every triangle shares edge with some packing element (by maximality)
lemma all_triangles_share_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hM_ne : M.Nonempty) :
    ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2 := by
  intro t ht;
  -- If $t$ does not share an edge with any packing triangle, then $M \cup \{t\}$ would be a packing larger than $M$, contradicting $M$'s maximality.
  by_contra h_contra
  have h_contra' : IsTrianglePacking G (M ∪ {t}) := by
    refine' ⟨ _, _ ⟩;
    · simp_all +decide [ Finset.subset_iff ];
      have := hM.1;
      exact fun x hx => by have := this.1 hx; aesop;
    · intro x hx y hy hxy; by_cases hx' : x = t <;> by_cases hy' : y = t <;> simp_all +decide ;
      · exact Nat.le_of_lt_succ ( h_contra y hy );
      · simpa only [ Finset.inter_comm ] using Nat.le_of_lt_succ ( h_contra x hx );
      · have := hM.1.2 hx hy hxy;
        exact this;
  have h_contra'' : (M ∪ {t}).card > M.card := by
    norm_num +zetaDelta at *;
    rw [ Finset.card_insert_of_notMem ] ; aesop;
    intro h; specialize h_contra t h; have := ht.card_eq; simp_all +decide ;
  have h_contra''' : (trianglePackingNumber G) ≥ (M ∪ {t}).card := by
    unfold trianglePackingNumber;
    have h_contra''' : (M ∪ {t}) ∈ Finset.filter (IsTrianglePacking G) (Finset.powerset (G.cliqueFinset 3)) := by
      simp_all +decide [ IsTrianglePacking ];
    have h_contra''' : (Finset.image Finset.card (Finset.filter (IsTrianglePacking G) (Finset.powerset (G.cliqueFinset 3)))).max ≥ (M ∪ {t}).card := by
      exact Finset.le_max ( Finset.mem_image_of_mem _ h_contra''' );
    exact WithBot.coe_le_coe.mp ( h_contra'''.trans ( by cases h : ( Finset.image Finset.card ( Finset.filter ( IsTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) |> Finset.max ) <;> aesop ) );
  linarith [ hM.2 ]

-- Key for ν=3: T_e \ S_e structure when packing elements share vertices
-- If e = {v,a,b} and f = {v,c,d} share vertex v, then T_e ∩ T_f triangles contain v
lemma Te_Tf_intersection_through_shared_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (v : V) (hve : v ∈ e) (hvf : v ∈ f)
    (h_only_v : e ∩ f = {v}) :
    ∀ t ∈ T_e G e, t ∈ T_e G f → v ∈ t := by
  simp +decide [ T_e ] at *;
  intro t ht ht' ht'' ht''' ; have := Finset.card_le_card ( Finset.inter_subset_left : t ∩ e ⊆ t ) ; simp_all +decide ;
  by_contra h_contra;
  -- Since $t$ is a triangle and $v$ is not in $t$, $t$ must be disjoint from $e$ and $f$.
  have h_disjoint : Disjoint (t ∩ e) (t ∩ f) := by
    exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => h_contra <| by rw [ Finset.ext_iff ] at h_only_v; specialize h_only_v x; aesop;
  have := Finset.card_le_card ( Finset.union_subset ( Finset.inter_subset_left : t ∩ e ⊆ t ) ( Finset.inter_subset_left : t ∩ f ⊆ t ) ) ; simp_all +decide ;
  linarith [ ht''.card_eq ]

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Defining the counterexample graph and packing.
-/
def CounterexampleEdges : Finset (Sym2 (Fin 7)) :=
  {s(0, 3), s(3, 4), s(4, 0),
   s(0, 1), s(1, 2), s(2, 0),
   s(1, 5), s(5, 6), s(6, 1),
   s(4, 2), s(2, 5)}

def CounterexampleGraph : SimpleGraph (Fin 7) := SimpleGraph.fromEdgeSet CounterexampleEdges

def A_ex : Finset (Fin 7) := {0, 3, 4}
def B_ex : Finset (Fin 7) := {0, 1, 2}
def C_ex : Finset (Fin 7) := {1, 5, 6}
def M_ex : Finset (Finset (Fin 7)) := {A_ex, B_ex, C_ex}

instance : DecidableRel CounterexampleGraph.Adj := by
  unfold CounterexampleGraph
  infer_instance

/-
M_ex is a valid triangle packing.
-/
lemma M_ex_is_packing : IsTrianglePacking CounterexampleGraph M_ex := by
  constructor;
  · unfold M_ex CounterexampleGraph; simp +decide [ SimpleGraph.cliqueFinset ] ;
  · decide +kernel

/-
M_ex is a maximum triangle packing (size 3).
-/
lemma M_ex_is_max : IsMaxPacking CounterexampleGraph M_ex := by
  -- To prove that M_ex is a maximum packing, we need to show that its cardinality is equal to the trianglePackingNumber.
  have h_max : trianglePackingNumber CounterexampleGraph = 3 := by
    rw [ eq_comm, trianglePackingNumber ];
    unfold CounterexampleGraph IsTrianglePacking; simp +decide [ SimpleGraph.cliqueFinset ] ;
    simp +decide [ SimpleGraph.isNClique_iff ] at *;
  constructor;
  · exact?;
  · aesop

/-
Every element of M_ex is "dirty" (T_e != S_e).
-/
lemma M_ex_all_dirty : ∀ e ∈ M_ex, T_e CounterexampleGraph e ≠ S_e CounterexampleGraph e M_ex := by
  decide +kernel

/-
The conjecture that every max packing of size 3 has a clean element is false.
-/
lemma nu3_conjecture_false : ¬ (∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)), IsMaxPacking G M → M.card = 3 → ∃ e ∈ M, T_e G e = S_e G e M) := by
  intro h_contra;
  contrapose! h_contra;
  refine' ⟨ _, _, _, _, _, _, _ ⟩;
  exact ULift ( Fin 7 );
  all_goals try infer_instance;
  exact SimpleGraph.fromEdgeSet { s(ULift.up 0, ULift.up 3), s(ULift.up 3, ULift.up 4), s(ULift.up 4, ULift.up 0), s(ULift.up 0, ULift.up 1), s(ULift.up 1, ULift.up 2), s(ULift.up 2, ULift.up 0), s(ULift.up 1, ULift.up 5), s(ULift.up 5, ULift.up 6), s(ULift.up 6, ULift.up 1), s(ULift.up 4, ULift.up 2), s(ULift.up 2, ULift.up 5) };
  infer_instance;
  exact { { ULift.up 0, ULift.up 3, ULift.up 4 }, { ULift.up 0, ULift.up 1, ULift.up 2 }, { ULift.up 1, ULift.up 5, ULift.up 6 } };
  refine' ⟨ _, _, _ ⟩;
  · refine' ⟨ _, _ ⟩;
    · constructor;
      · native_decide +revert;
      · simp +decide [ Set.Pairwise ];
    · unfold trianglePackingNumber;
      unfold IsTrianglePacking; simp +decide [ SimpleGraph.cliqueFinset ] ;
      simp +decide [ SimpleGraph.isNClique_iff ];
  · decide +revert;
  · native_decide +revert

end AristotleLemmas

/-
For ν=3, at least one packing element has T_e = S_e
(No triangle shares edge with both that element AND another)
-/
lemma nu3_exists_clean_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3) :
    ∃ e ∈ M, T_e G e = S_e G e M := by
  revert hM hnu;
  intro hM hnu
  by_contra h_contra;
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  use ULift ( Fin 7 );
  refine' ⟨ inferInstance, inferInstance, _, _, _, _, _ ⟩;
  exact SimpleGraph.fromEdgeSet { s(ULift.up 0, ULift.up 3), s(ULift.up 3, ULift.up 4), s(ULift.up 4, ULift.up 0), s(ULift.up 0, ULift.up 1), s(ULift.up 1, ULift.up 2), s(ULift.up 2, ULift.up 0), s(ULift.up 1, ULift.up 5), s(ULift.up 5, ULift.up 6), s(ULift.up 6, ULift.up 1), s(ULift.up 4, ULift.up 2), s(ULift.up 2, ULift.up 5) };
  infer_instance;
  exact { { ULift.up 0, ULift.up 3, ULift.up 4 }, { ULift.up 0, ULift.up 1, ULift.up 2 }, { ULift.up 1, ULift.up 5, ULift.up 6 } };
  · constructor;
    · constructor;
      · simp +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
      · simp +decide [ Set.Pairwise ];
    · rw [ eq_comm, trianglePackingNumber ];
      unfold IsTrianglePacking; simp +decide [ SimpleGraph.cliqueFinset ] ;
      simp +decide [ SimpleGraph.isNClique_iff ];
  · native_decide +revert

-/
-- For ν=3, at least one packing element has T_e = S_e
-- (No triangle shares edge with both that element AND another)
lemma nu3_exists_clean_element (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3) :
    ∃ e ∈ M, T_e G e = S_e G e M := by
  sorry

/- Aristotle failed to find a proof. -/
-- Main theorem: τ ≤ 6 when ν = 3
theorem tuza_nu3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 3) : triangleCoveringNumber G ≤ 6 := by
  sorry

end