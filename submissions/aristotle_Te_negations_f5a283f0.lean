/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f5a283f0-4913-4b51-a98c-d9df7c0f99cf

The following was negated by Aristotle:

- theorem no_counterexample_6_vertices :
    ∀ (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 6))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2

- theorem no_counterexample_7_vertices :
    ∀ (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 7))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2

- theorem no_counterexample_8_vertices :
    ∀ (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 8))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2

- theorem no_counterexample_9_vertices :
    ∀ (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 9))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2

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
Tuza ν ≤ 3: Finite counterexample search

Search for counterexamples on small vertex sets (≤ 9 vertices).
If τ(T_e) ≤ 2 fails for ANY e ∈ M with |M| ≤ 3, this will find it.
-/

import Mathlib


set_option maxHeartbeats 800000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))

def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E}

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Definitions of the specific graph and triangle packing for the counterexample.
-/
def e_ex : Finset (Fin 6) := {0, 1, 2}
def t1 : Finset (Fin 6) := {0, 1, 3}
def t2 : Finset (Fin 6) := {1, 2, 4}
def t3 : Finset (Fin 6) := {0, 2, 5}
def t5 : Finset (Fin 6) := {1, 3, 4}
def t6 : Finset (Fin 6) := {2, 4, 5}

def edges_ex : Finset (Sym2 (Fin 6)) :=
  {Sym2.mk (0, 1), Sym2.mk (1, 2), Sym2.mk (0, 2),
   Sym2.mk (0, 3), Sym2.mk (1, 3),
   Sym2.mk (1, 4), Sym2.mk (2, 4),
   Sym2.mk (0, 5), Sym2.mk (2, 5),
   Sym2.mk (3, 4),
   Sym2.mk (4, 5)}

def G_ex : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet edges_ex

def M_ex : Finset (Finset (Fin 6)) := {e_ex, t5, t6}

/-
t1, t2, t3 are edge disjoint, and T_e is {e, t1, t2, t3}.
-/
lemma t1_t2_t3_edge_disjoint :
  Disjoint (triangleEdges t1) (triangleEdges t2) ∧
  Disjoint (triangleEdges t1) (triangleEdges t3) ∧
  Disjoint (triangleEdges t2) (triangleEdges t3) := by
    unfold triangleEdges; simp +decide ;

lemma T_e_ex_eq : T_e G_ex e_ex = {e_ex, t1, t2, t3} := by
  simp +decide [ T_e, SimpleGraph.fromEdgeSet ];
  -- By definition of $T_e$, we need to show that the set of triangles in $G_ex$ that intersect with $e_ex$ is exactly $\{e_ex, t1, t2, t3\}$.
  apply Finset.ext
  intro t
  simp [triangleEdges, e_ex, t1, t2, t3];
  revert t ; simp +decide [ G_ex ] ;

/-
The covering number of T_e is at least 3.
-/
lemma covering_number_ge_3 : coveringNumberOn G_ex (T_e G_ex e_ex) ≥ 3 := by
  apply le_csInf;
  · -- Let's choose the set $E$ to consist of all edges of the graph $G_ex$.
    use 11;
    use edges_ex;
    simp +decide [ T_e ];
    unfold G_ex; simp +decide [ SimpleGraph.isNClique_iff ] ;
  · rintro n ⟨ E, rfl, hE ⟩;
    contrapose! hE;
    -- Since $E$ has fewer than 3 edges, it cannot cover all the triangles in $T_e$.
    have h_not_cover : ∃ t ∈ ({e_ex, t1, t2, t3} : Finset (Finset (Fin 6))), Disjoint (triangleEdges t) E := by
      native_decide +revert;
    convert h_not_cover using 1;
    ext; simp [T_e_ex_eq]

/-
For any triangle packing M in G, 3 * |M| <= |E(G)|.
-/
lemma packing_size_le_edges_div_3 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (hM : IsTrianglePacking G M) :
    3 * M.card ≤ G.edgeFinset.card := by
  have h_sum_edges : (Finset.biUnion M (fun t => triangleEdges t)).card = 3 * M.card := by
    have h_sum_edges : ∀ t ∈ M, (triangleEdges t).card = 3 := by
      intro t ht
      have h_card : t.card = 3 := by
        have := hM.1 ht;
        simp_all +decide [ SimpleGraph.cliqueFinset ];
        exact this.card_eq;
      unfold triangleEdges;
      have := Finset.card_eq_three.mp h_card; obtain ⟨ x, y, z, hxyz ⟩ := this; simp_all +decide [ Finset.offDiag ] ;
      simp +decide [ Finset.filter, Finset.image, * ];
      simp +decide [ Multiset.filter_cons, Multiset.filter_singleton, hxyz ];
      aesop;
    rw [ Finset.card_biUnion, Finset.sum_congr rfl h_sum_edges, Finset.sum_const, smul_eq_mul, mul_comm ];
    exact hM.2;
  refine' h_sum_edges ▸ Finset.card_mono _;
  simp_all +decide [ IsTrianglePacking, Finset.subset_iff ];
  simp_all +decide [ SimpleGraph.isNClique_iff, triangleEdges ];
  rintro _ t ht x y hx hy hxy rfl; have := hM.1 ht; have := this.1 hx hy hxy; aesop;

/-
M_ex is a triangle packing, G_ex has 11 edges, and |M_ex| = 3.
-/
lemma M_ex_is_packing : IsTrianglePacking G_ex M_ex := by
  constructor;
  · simp +decide [ M_ex, G_ex ];
    simp +decide [ Finset.insert_subset_iff, SimpleGraph.cliqueFinset ];
  · unfold IsEdgeDisjoint;
    simp +decide [ Set.PairwiseDisjoint ]

lemma G_ex_edge_card : G_ex.edgeFinset.card = 11 := by
  unfold G_ex; simp +decide ;

lemma M_ex_card : M_ex.card = 3 := by
  native_decide +revert

/-
The packing number of G_ex is 3.
-/
lemma packingNumber_eq_3 : packingNumber G_ex = 3 := by
  refine' le_antisymm _ _;
  · exact csSup_le' fun x hx => by obtain ⟨ M, rfl, hM ⟩ := hx; linarith [ packing_size_le_edges_div_3 G_ex M hM, G_ex_edge_card ] ;
  · refine' le_csSup _ _ <;> norm_num +zetaDelta at *;
    · exact ⟨ _, fun n hn => hn.choose_spec.1 ▸ Finset.card_le_univ _ ⟩;
    · exact ⟨ M_ex, M_ex_card, M_ex_is_packing ⟩

end AristotleLemmas

theorem no_counterexample_6_vertices :
    ∀ (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 6))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  use G_ex, ?_, M_ex, ?_, ?_, e_ex, ?_, ?_ <;> norm_cast;
  infer_instance;
  · constructor;
    · exact M_ex_is_packing;
    · rw [ packingNumber_eq_3, M_ex_card ];
  · -- Apply the lemma that states the covering number is at least 3.
    apply lt_of_lt_of_le (by norm_num) (covering_number_ge_3)

-/
theorem no_counterexample_6_vertices :
    ∀ (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 6))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def G_counter : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => i.val < 5 ∧ j.val < 5 ∧ i ≠ j)

def M_counter : Finset (Finset (Fin 7)) :=
  { {0, 1, 2}, {0, 3, 4} }

lemma G_counter_adj (i j : Fin 7) : G_counter.Adj i j ↔ i.val < 5 ∧ j.val < 5 ∧ i ≠ j := by
  -- By definition of $G_counter$, we know that $G_counter.Adj i j$ holds if and only if $i$ and $j$ are both in the first 5 vertices and $i \ne j$. This follows directly from the construction of $G_counter$ as a $K_5$ on the first 5 vertices.
  simp [G_counter, SimpleGraph.fromRel];
  native_decide +revert

instance : DecidableRel G_counter.Adj := by
  intro i j
  rw [G_counter_adj]
  infer_instance

lemma M_counter_is_packing : IsTrianglePacking G_counter M_counter := by
  unfold M_counter;
  constructor;
  · simp +decide [ Finset.subset_iff ];
    simp +decide [ G_counter, SimpleGraph.isNClique_iff ];
  · unfold IsEdgeDisjoint;
    simp +decide [ Set.PairwiseDisjoint ]

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma triangleEdges_card (t : Finset V) (ht : t.card = 3) : (triangleEdges t).card = 3 := by
  unfold triangleEdges;
  rw [ Finset.card_eq_three ] at *;
  rcases ht with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; use Sym2.mk ( x, y ), Sym2.mk ( x, z ), Sym2.mk ( y, z ) ; simp +decide [ *, Finset.ext_iff ] ;
  intro a;
  constructor <;> intro h;
  · rcases h with ⟨ a, b, ⟨ rfl | rfl | rfl, rfl | rfl | rfl, hab ⟩, rfl ⟩ <;> aesop;
  · rcases h with ( rfl | rfl | rfl ) <;> [ exact ⟨ x, y, by aesop ⟩ ; exact ⟨ x, z, by aesop ⟩ ; exact ⟨ y, z, by aesop ⟩ ]

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma packing_edges_card (M : Finset (Finset V)) (hM : IsEdgeDisjoint M)
    (h_card : M.card = 3)
    (h_triangles : ∀ t ∈ M, t.card = 3) :
    (M.biUnion triangleEdges).card = 9 := by
  -- Apply the lemma that states the cardinality of the union of disjoint sets is the sum of their cardinalities.
  have h_union_card : (M.biUnion triangleEdges).card = Finset.sum M (fun t => (triangleEdges t).card) := by
    rw [ Finset.card_biUnion ];
    exact hM;
  exact h_union_card.trans ( by rw [ Finset.sum_congr rfl fun t ht => triangleEdges_card t ( h_triangles t ht ) ] ; simp +decide [ h_card ] )

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma packing_le_2_of_K5_structure (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (hG : ∀ i j, G.Adj i j ↔ i.val < 5 ∧ j.val < 5 ∧ i ≠ j) :
    packingNumber G ≤ 2 := by
  refine' csSup_le _ _;
  · use 0
    simp;
    constructor <;> norm_num;
    tauto;
  · rintro n ⟨ M, rfl, hM ⟩;
    -- Since $M$ is a triangle packing, each triangle in $M$ must be a subset of $\{0, 1, 2, 3, 4\}$.
    have h_subsets : ∀ t ∈ M, t ⊆ {0, 1, 2, 3, 4} := by
      intro t ht; have := hM.1 ht; simp_all +decide [ Finset.subset_iff ] ;
      intro x hx; have := this.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      fin_cases x <;> simp_all +decide [ SimpleGraph.isClique_iff ];
      · have := Finset.card_eq_three.mp ‹_›; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := this; simp_all +decide [ Set.Pairwise ] ;
        fin_cases a <;> fin_cases b <;> fin_cases c <;> trivial;
      · have := Finset.card_eq_three.mp ‹_›; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := this; simp_all +decide [ Set.Pairwise ] ;
        fin_cases a <;> fin_cases b <;> fin_cases c <;> trivial;
    -- Since $M$ is a triangle packing, each triangle in $M$ must be one of the triangles $\{0, 1, 2\}$, $\{0, 1, 3\}$, $\{0, 1, 4\}$, $\{0, 2, 3\}$, $\{0, 2, 4\}$, $\{0, 3, 4\}$, $\{1, 2, 3\}$, $\{1, 2, 4\}$, $\{1, 3, 4\}$, or $\{2, 3, 4\}$.
    have h_triangles : ∀ t ∈ M, t = {0, 1, 2} ∨ t = {0, 1, 3} ∨ t = {0, 1, 4} ∨ t = {0, 2, 3} ∨ t = {0, 2, 4} ∨ t = {0, 3, 4} ∨ t = {1, 2, 3} ∨ t = {1, 2, 4} ∨ t = {1, 3, 4} ∨ t = {2, 3, 4} := by
      intro t ht; specialize h_subsets t ht; specialize hM; have := hM.1 ht; simp_all +decide [ Finset.subset_iff ] ;
      have := Finset.card_eq_three.mp this.2; obtain ⟨ a, b, c, hab, hbc, hca ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
      rcases h_subsets with ⟨ rfl | rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl | rfl ⟩ <;> simp +decide at hab hbc hca ⊢;
    -- Since $M$ is a triangle packing, it cannot contain two triangles that share an edge.
    have h_no_shared_edges : ∀ t1 t2 : Finset (Fin 7), t1 ∈ M → t2 ∈ M → t1 ≠ t2 → Disjoint (triangleEdges t1) (triangleEdges t2) := by
      intro t1 t2 ht1 ht2 hne; have := hM.2; simp_all +decide [ Set.PairwiseDisjoint ] ;
      exact this ht1 ht2 hne;
    have h_max_triangles : ∀ S : Finset (Finset (Fin 7)), S ⊆ ({ {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 4}, {0, 3, 4}, {1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4} } : Finset (Finset (Fin 7))) → (∀ t1 t2 : Finset (Fin 7), t1 ∈ S → t2 ∈ S → t1 ≠ t2 → Disjoint (triangleEdges t1) (triangleEdges t2)) → S.card ≤ 2 := by
      native_decide +revert;
    exact h_max_triangles M ( fun t ht => by simpa using h_triangles t ht ) h_no_shared_edges

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma covering_check :
  ∀ E ∈ ((Finset.univ : Finset (Sym2 (Fin 7))).powersetCard 0) ∪
        ((Finset.univ : Finset (Sym2 (Fin 7))).powersetCard 1) ∪
        ((Finset.univ : Finset (Sym2 (Fin 7))).powersetCard 2),
  ¬ (∀ t ∈ T_e G_counter {0, 1, 2}, ¬Disjoint (triangleEdges t) E) := by
    -- Let's consider each possible size of E.
    intro E hE
    by_cases hE0 : E.card = 0;
    · native_decide +revert;
    · by_cases hE1 : E.card = 1;
      · obtain ⟨ e, he ⟩ := Finset.card_eq_one.mp hE1;
        fin_cases e <;> simp +decide [ he ];
        all_goals native_decide;
      · have hE2 : E.card = 2 := by
          aesop;
        rw [ Finset.card_eq_two ] at hE2; aesop;
        native_decide +revert

lemma exists_cover_3 :
  ∃ E : Finset (Sym2 (Fin 7)), E.card = 3 ∧ ∀ t ∈ T_e G_counter {0, 1, 2}, ¬Disjoint (triangleEdges t) E := by
    -- Let's choose the edges (0, 1), (0, 2), and (1, 2) as our set E.
    use {Sym2.mk (0, 1), Sym2.mk (0, 2), Sym2.mk (1, 2)};
    native_decide +revert

lemma covering_gt_2 : coveringNumberOn G_counter (T_e G_counter {0, 1, 2}) > 2 := by
  refine' lt_of_lt_of_le _ ( le_csInf _ _ ) <;> norm_num;
  exact lt_add_one _;
  · refine' ⟨ _, ⟨ Finset.univ, rfl, _ ⟩ ⟩ ; simp +decide [ T_e ];
    simp +decide [ Finset.disjoint_left ];
    grind;
  · intros b x hx h_disjoint;
    -- By contradiction, assume $b < 3$.
    by_contra hb_lt_3;
    interval_cases b <;> simp_all +decide;
    · exact h_disjoint { 0, 1, 2 } ( Finset.mem_filter.mpr ⟨ by native_decide, by native_decide ⟩ );
    · obtain ⟨ e, rfl ⟩ := Finset.card_eq_one.mp hx; simp_all +decide [ Finset.disjoint_left ] ;
      revert e; native_decide;
    · rw [ Finset.card_eq_two ] at hx;
      rcases hx with ⟨ a, b, hab, rfl ⟩ ; simp_all +decide [ Finset.disjoint_left ] ;
      revert a b; native_decide;

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma disproof_of_no_counterexample :
    ¬ (∀ (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj],
       ∀ (M : Finset (Finset (Fin 7))), IsMaxPacking G M → M.card ≤ 3 →
       ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2) := by
         push_neg;
         use G_counter;
         refine' ⟨ _, M_counter, _, _, _ ⟩;
         infer_instance;
         · constructor;
           · exact?;
           · refine' le_antisymm _ _;
             · refine' le_csSup _ _;
               · exact ⟨ _, fun n hn => hn.choose_spec.1 ▸ Finset.card_le_univ _ ⟩;
               · exact ⟨ _, rfl, M_counter_is_packing ⟩;
             · exact packing_le_2_of_K5_structure G_counter G_counter_adj |> le_trans <| by simp +decide [ M_counter ] ;
         · native_decide +revert;
         · use { 0, 1, 2 };
           exact ⟨ by decide, covering_gt_2 ⟩

end AristotleLemmas

theorem no_counterexample_7_vertices :
    ∀ (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 7))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose the specific graph and triangle packing from the provided solution.
  use G_counter, by infer_instance, M_counter;
  refine' ⟨ _, _, _ ⟩;
  · refine' ⟨ _, _ ⟩;
    · exact?;
    · rw [ show packingNumber G_counter = 2 from _ ];
      · native_decide;
      · apply le_antisymm;
        · -- Apply the lemma that states the packing number of G_counter is at most 2.
          apply packing_le_2_of_K5_structure;
          native_decide +revert;
        · refine' le_csSup _ _ <;> norm_num +zetaDelta at *;
          · exact ⟨ _, fun n hn => hn.choose_spec.1 ▸ Finset.card_le_univ _ ⟩;
          · use M_counter; simp +decide [ M_counter_is_packing ] ;
  · native_decide +revert;
  · use {0, 1, 2};
    exact ⟨ by decide, covering_gt_2 ⟩

-/
theorem no_counterexample_7_vertices :
    ∀ (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 7))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Disproof of the conjecture for 8 vertices.
-/
theorem disproof_8_vertices : ¬ (∀ (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 8))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2) := by
  intro h
  let edges : Finset (Sym2 (Fin 8)) := {
    Sym2.mk (0, 1), Sym2.mk (1, 2), Sym2.mk (2, 0), -- e
    Sym2.mk (0, 3), Sym2.mk (3, 5), Sym2.mk (5, 0), -- f
    Sym2.mk (1, 4), Sym2.mk (4, 6), Sym2.mk (6, 1), -- g
    Sym2.mk (1, 3), -- for t1
    Sym2.mk (2, 4), -- for t2
    Sym2.mk (5, 2)  -- for t3
  }
  let G := SimpleGraph.fromEdgeSet (edges : Set (Sym2 (Fin 8)))
  haveI : DecidableRel G.Adj := by
    simp only [G, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe]; infer_instance
  let e : Finset (Fin 8) := {0, 1, 2}
  let f : Finset (Fin 8) := {0, 3, 5}
  let g : Finset (Fin 8) := {1, 4, 6}
  let M : Finset (Finset (Fin 8)) := {e, f, g}
  have hM_packing : IsTrianglePacking G M := by
    constructor;
    · simp +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
      native_decide +revert;
    · -- Show that the edges of $e$, $f$, and $g$ are pairwise disjoint.
      simp [IsEdgeDisjoint, triangleEdges];
      simp +decide [ Set.PairwiseDisjoint ];
      native_decide +revert
  have hM_card : M.card = 3 := by
    decide
  have h_packing_num : packingNumber G = 3 := by
    -- To prove the equality, it suffices to show that no triangle packing larger than 3 exists.
    have h_no_larger_packing : ∀ M : Finset (Finset (Fin 8)), IsTrianglePacking G M → M.card ≤ 3 := by
      intro M hM_packing
      have h_max_packing : ∀ t ∈ M, t ∈ G.cliqueFinset 3 := by
        exact fun t ht => hM_packing.1 ht;
      have h_max_packing : ∀ t ∈ M, t ∈ ({ {0, 1, 2}, {0, 3, 5}, {1, 4, 6}, {0, 1, 3}, {1, 2, 4}, {2, 0, 5} } : Finset (Finset (Fin 8))) := by
        intro t ht; specialize h_max_packing t ht; simp +decide [ SimpleGraph.isNClique_iff ] at h_max_packing ⊢;
        have h_max_packing : ∀ t ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 8)), G.IsClique (↑t : Set (Fin 8)) → t ∈ ({ {0, 1, 2}, {0, 3, 5}, {1, 4, 6}, {0, 1, 3}, {1, 2, 4}, {2, 0, 5} } : Finset (Finset (Fin 8))) := by
          simp +decide [ SimpleGraph.isClique_iff, edges ];
          simp +decide [ G, edges ];
          decide +kernel;
        grind;
      have h_max_packing : ∀ t ∈ M, ∀ u ∈ M, t ≠ u → Disjoint (triangleEdges t) (triangleEdges u) := by
        exact fun t ht u hu htu => hM_packing.2 ht hu htu;
      have h_max_packing : ∀ S ⊆ ({ {0, 1, 2}, {0, 3, 5}, {1, 4, 6}, {0, 1, 3}, {1, 2, 4}, {2, 0, 5} } : Finset (Finset (Fin 8))), (∀ t ∈ S, ∀ u ∈ S, t ≠ u → Disjoint (triangleEdges t) (triangleEdges u)) → S.card ≤ 3 := by
        native_decide +revert;
      exact h_max_packing M ‹_› ‹_›;
    exact le_antisymm ( csSup_le ⟨ M.card, ⟨ M, hM_card, hM_packing ⟩ ⟩ fun n hn => by obtain ⟨ M, rfl, hM ⟩ := hn; exact h_no_larger_packing M hM ) ( le_csSup ⟨ 3, fun n hn => by obtain ⟨ M, rfl, hM ⟩ := hn; exact h_no_larger_packing M hM ⟩ ⟨ M, hM_card, hM_packing ⟩ )
  have hM_max : IsMaxPacking G M := by
    -- Since M is a triangle packing and its cardinality is 3, and the packing number of G is also 3, M must be a maximum packing.
    apply And.intro hM_packing (by rw [hM_card, h_packing_num])
  have he : e ∈ M := by
    -- Since $e$ is one of the elements in $M$, we can conclude that $e \in M$.
    simp [M]
  specialize h G M hM_max (by rw [hM_card]) e he
  have h_cov : coveringNumberOn G (T_e G e) = 3 := by
    -- By definition of $T_e$, we know that $T_e(G, e) = \{e, t1, t2, t3\}$.
    have h_T_e : T_e G e = {e, {0, 1, 3}, {1, 2, 4}, {2, 0, 5}} := by
      simp +decide [ T_e ];
      -- By definition of $T_e$, we know that $T_e(G, e)$ is the set of triangles in $G$ that share an edge with $e$.
      ext t
      simp [triangleEdges, e];
      simp +decide [ SimpleGraph.isNClique_iff ];
      simp +decide [ G, SimpleGraph.isClique_iff ];
      native_decide +revert;
    refine' le_antisymm _ _ <;> norm_num [ h_T_e ];
    · grind;
    · refine' le_csInf _ _ <;> norm_num;
      · exact ⟨ _, ⟨ Finset.univ, rfl, by decide, by decide, by decide, by decide ⟩ ⟩;
      · intro b x hx h₁ h₂ h₃ h₄; contrapose! h₁; interval_cases b <;> simp_all +decide ;
        · -- Since $x$ has only one element, let's denote it as $e$. So, $x = \{e\}$.
          obtain ⟨e, he⟩ : ∃ e, x = {e} := by
            exact Finset.card_eq_one.mp hx;
          simp_all +decide [ Finset.disjoint_singleton_right ];
          fin_cases e <;> trivial;
        · rw [ Finset.card_eq_two ] at hx;
          rcases hx with ⟨ a, b, hab, rfl ⟩ ; simp_all +decide [ Finset.disjoint_left ] ;
          -- By examining the possible values of a and b, we can see that they cannot cover all elements in the triangleEdges of {0,1,3}, {1,2,4}, and {2,0,5} without overlap.
          have h_contradiction : ∀ a b : Sym2 (Fin 8), a ≠ b → (∃ x ∈ triangleEdges {0, 1, 3}, ¬x = a → x = b) → (∃ x ∈ triangleEdges {1, 2, 4}, ¬x = a → x = b) → (∃ x ∈ triangleEdges {2, 0, 5}, ¬x = a → x = b) → False := by
            native_decide +revert;
          exact False.elim <| h_contradiction a b hab h₂ h₃ h₄
  linarith

end AristotleLemmas

theorem no_counterexample_8_vertices :
    ∀ (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 8))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose the graph $G$ to be the disjoint union of two complete graphs on 4 vertices each, and let $M$ be the set containing the two triangles from each complete graph.
  obtain ⟨G, inst, M, hM⟩ : ∃ G : SimpleGraph (Fin 8), ∃ inst : DecidableRel G.Adj, ∃ M : Finset (Finset (Fin 8)), IsMaxPacking G M ∧ M.card ≤ 3 ∧ ∃ e ∈ M, coveringNumberOn G (T_e G e) > 2 := by
    -- By contradiction, assume the conjecture holds.
    by_contra h_contra;
    -- Apply the disproof_8_vertices theorem to obtain the contradiction.
    apply disproof_8_vertices;
    aesop;
  exact ⟨ G, inst, M, hM ⟩

-/
theorem no_counterexample_8_vertices :
    ∀ (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 8))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Define the counterexample graph and its triangles. Prove that the identified sets are indeed cliques.
-/
def edges_counter : Finset (Sym2 (Fin 9)) :=
  {Sym2.mk (0, 1), Sym2.mk (1, 2), Sym2.mk (0, 2), -- e
   Sym2.mk (0, 3), Sym2.mk (1, 3), -- t1 \ e
   Sym2.mk (1, 4), Sym2.mk (2, 4), -- t2 \ e
   Sym2.mk (0, 5), Sym2.mk (2, 5), -- t3 \ e
   Sym2.mk (1, 6), Sym2.mk (3, 6), -- e' \ t1
   Sym2.mk (2, 7), Sym2.mk (4, 7)} -- e'' \ t2

def G_counter : SimpleGraph (Fin 9) := SimpleGraph.fromEdgeSet edges_counter

def e_c : Finset (Fin 9) := {0, 1, 2}
def t1_c : Finset (Fin 9) := {0, 1, 3}
def t2_c : Finset (Fin 9) := {1, 2, 4}
def t3_c : Finset (Fin 9) := {0, 2, 5}
def e_prime_c : Finset (Fin 9) := {1, 3, 6}
def e_double_prime_c : Finset (Fin 9) := {2, 4, 7}

def cliques_c : Finset (Finset (Fin 9)) := {e_c, t1_c, t2_c, t3_c, e_prime_c, e_double_prime_c}

lemma cliques_are_cliques : ∀ t ∈ cliques_c, G_counter.IsClique t := by
  -- Let's choose any clique $t$ in $cliques_c$.
  intro t ht
  simp [G_counter];
  native_decide +revert

/-
Prove that the set of triangles in G_counter is exactly cliques_c using native_decide.
-/
lemma cliques_eq : G_counter.cliqueFinset 3 = cliques_c := by
  unfold G_counter cliques_c;
  rw [ eq_comm, Finset.ext_iff ];
  simp +zetaDelta at *;
  native_decide +revert

/-
Define M_c and prove it is a triangle packing using native_decide.
-/
def M_c : Finset (Finset (Fin 9)) := {e_c, e_prime_c, e_double_prime_c}

lemma M_c_is_packing : IsTrianglePacking G_counter M_c := by
  constructor;
  · -- Since M_c is defined as {e_c, t1_c, t3_c, e_double_prime_c}, we can check each element individually.
    simp [M_c, cliques_eq];
    native_decide +revert;
  · intro t ht t' ht' h;
    native_decide +revert

/-
Define a boolean check for edge disjointness and prove it is equivalent to the Prop definition.
-/
def isEdgeDisjoint_bool (M : Finset (Finset (Fin 9))) : Bool :=
  let bad_pairs := M.offDiag.filter (fun x => (triangleEdges x.1 ∩ triangleEdges x.2).card ≠ 0)
  bad_pairs.card == 0

lemma isEdgeDisjoint_bool_spec (M : Finset (Finset (Fin 9))) :
    isEdgeDisjoint_bool M = true ↔ IsEdgeDisjoint M := by
      constructor;
      · intro h;
        intro t1 ht1 t2 ht2 hne;
        unfold isEdgeDisjoint_bool at h;
        simp +zetaDelta at *;
        exact Finset.disjoint_iff_inter_eq_empty.mpr ( h t1 t2 ht1 ht2 hne );
      · unfold IsEdgeDisjoint isEdgeDisjoint_bool; aesop;
        exact Finset.disjoint_iff_inter_eq_empty.mp ( a a_2 a_3 a_4 )

/-
Define a boolean check that verifies no subset of cliques_c is both edge-disjoint and has size > 3. Prove it returns true by computation.
-/
def check_packing_le_3_bool : Bool :=
  let bad_packings := cliques_c.powerset.filter (fun M => isEdgeDisjoint_bool M && 3 < M.card)
  bad_packings.card == 0

lemma check_packing_le_3_bool_true : check_packing_le_3_bool = true := by
  native_decide

/-
Prove that any triangle packing in G_counter has size at most 3, using the boolean check.
-/
lemma packing_le_3 : ∀ M : Finset (Finset (Fin 9)), IsTrianglePacking G_counter M → M.card ≤ 3 := by
  intros M hM
  have h_subset : M ⊆ cliques_c := by
    have := hM.1;
    exact this.trans ( by rw [ cliques_eq ] );
  have h_card : ∀ M' ⊆ cliques_c, IsEdgeDisjoint M' → M'.card ≤ 3 := by
    intros M' hM' h_disjoint;
    have h_card : M'.card ≤ 3 := by
      have h_check : ∀ M' ⊆ cliques_c, isEdgeDisjoint_bool M' = true → M'.card ≤ 3 := by
        native_decide
      exact h_check M' hM' ( by simpa using isEdgeDisjoint_bool_spec M' |>.2 h_disjoint );
    exact h_card;
  exact h_card M h_subset hM.2

/-
Prove that the packing number of G_counter is exactly 3.
-/
lemma packing_eq_3 : packingNumber G_counter = 3 := by
  refine' le_antisymm _ _;
  · exact csSup_le' fun n hn => by rcases hn with ⟨ M, rfl, hM ⟩ ; exact packing_le_3 M hM;
  · -- Since $M_c$ is a triangle packing of size 3, we have $3 \leq \text{packingNumber } G_counter$.
    have h_packing_M_c : IsTrianglePacking G_counter M_c := by
      exact?;
    refine' le_csSup _ _;
    · exact ⟨ _, fun n hn => hn.choose_spec.1 ▸ Finset.card_le_univ _ ⟩;
    · exact ⟨ M_c, by decide, h_packing_M_c ⟩

/-
Compute T_e explicitly and prove it equals the expected set.
-/
def T_e_computed : Finset (Finset (Fin 9)) :=
  cliques_c.filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e_c))

lemma T_e_computed_eq : T_e_computed = {e_c, t1_c, t2_c, t3_c} := by
  native_decide

lemma T_e_eq : T_e G_counter e_c = {e_c, t1_c, t2_c, t3_c} := by
  rw [T_e, cliques_eq]
  exact T_e_computed_eq

/-
If a set of edges E covers a set of triangles S in G, then the subset of E consisting of edges in G also covers S.
-/
lemma cover_subset_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3)
    (E : Finset (Sym2 V))
    (h_cover : ∀ t ∈ S, ¬Disjoint (triangleEdges t) E) :
    ∀ t ∈ S, ¬Disjoint (triangleEdges t) (E.filter (fun e => e ∈ G.edgeSet)) := by
      intro t ht; specialize h_cover t ht; simp_all +decide [ disjoint_iff ] ;
      simp_all +decide [ Finset.ext_iff ];
      obtain ⟨ x, hx₁, hx₂ ⟩ := h_cover; use x; simp_all +decide [ triangleEdges ] ;
      obtain ⟨ a, b, ⟨ ha, hb, hab ⟩, rfl ⟩ := hx₁; specialize hS ht; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
      exact hS.1 ha hb hab

/-
Define a boolean check that verifies no subset of edges of size <= 2 covers T_e_computed. Prove it returns true.
-/
def is_cover_bool (E : Finset (Sym2 (Fin 9))) (S : Finset (Finset (Fin 9))) : Bool :=
  let uncovered := S.filter (fun t => (triangleEdges t ∩ E).card == 0)
  uncovered.card == 0

def check_no_cover_le_2 : Bool :=
  let candidates := edges_counter.powerset.filter (fun s => s.card ≤ 2)
  let covers := candidates.filter (fun E => is_cover_bool E T_e_computed)
  covers.card == 0

lemma check_no_cover_le_2_true : check_no_cover_le_2 = true := by
  native_decide

/-
Prove that the covering number of T_e(G_counter, e_c) is greater than 2. This is done by showing that any cover of size <= 2 can be reduced to a cover using only graph edges, which we have computationally verified does not exist.
-/
lemma covering_gt_2 : coveringNumberOn G_counter (T_e G_counter e_c) > 2 := by
  have h_covering_number : ∀ E : Finset (Sym2 (Fin 9)), E.card ≤ 2 → ¬(∀ t ∈ T_e G_counter e_c, ¬Disjoint (triangleEdges t) E) := by
    intros E hE h_cover
    have h_cover_subset : ∀ t ∈ T_e G_counter e_c, ¬Disjoint (triangleEdges t) (E.filter (fun e => e ∈ G_counter.edgeSet)) := by
      apply cover_subset_edges;
      · unfold T_e; aesop;
      · assumption;
    -- Apply the computational check to find that no subset of edges of size <= 2 covers T_e_computed.
    have h_computation : ∀ E ⊆ edges_counter, E.card ≤ 2 → ¬(∀ t ∈ T_e_computed, ¬Disjoint (triangleEdges t) E) := by
      native_decide +revert;
    apply h_computation (E.filter (fun e => e ∈ G_counter.edgeSet));
    · intro e he; unfold G_counter at he; aesop;
    · exact le_trans ( Finset.card_filter_le _ _ ) hE;
    · convert h_cover_subset using 1;
      rw [ show T_e G_counter e_c = T_e_computed from T_e_eq ];
  refine' lt_of_lt_of_le _ ( le_csInf _ _ );
  exact Nat.lt_succ_self _;
  · refine' ⟨ _, ⟨ Finset.univ, rfl, _ ⟩ ⟩;
    simp +decide [ Finset.disjoint_left ];
    simp +decide [ T_e ];
    exact fun t ht ht' => Finset.nonempty_of_ne_empty ( by aesop );
  · grind

/-
Prove the existence of the counterexample using the constructed graph and lemmas.
-/
theorem counterexample_exists : ∃ (G : SimpleGraph (Fin 9)) (M : Finset (Finset (Fin 9))) (e : Finset (Fin 9)),
    IsMaxPacking G M ∧ M.card ≤ 3 ∧ e ∈ M ∧ coveringNumberOn G (T_e G e) > 2 := by
      use G_counter, M_c, e_c;
      constructor;
      · refine' ⟨ M_c_is_packing, _ ⟩;
        exact Eq.symm ( by rw [ show packingNumber G_counter = 3 from packing_eq_3 ] ; rfl );
      · exact ⟨ by native_decide, by native_decide, covering_gt_2 ⟩

end AristotleLemmas

theorem no_counterexample_9_vertices :
    ∀ (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 9))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Apply the `counterexample_exists` lemma to obtain the required graph.
  obtain ⟨G, M, e, hM, hG⟩ := counterexample_exists;
  -- Use the obtained graph G, maximum packing M, and edge e to construct the existence statement.
  use G, inferInstance, M, hM, hG.left, e, hG.right.left, hG.right.right

-/
theorem no_counterexample_9_vertices :
    ∀ (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj],
    ∀ (M : Finset (Finset (Fin 9))), IsMaxPacking G M → M.card ≤ 3 →
    ∀ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

end