/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1a6abfa8-531a-4726-9d91-04a588b0f8a7

The following was negated by Aristotle:

- theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2

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
slot274: PATH_4 τ ≤ 8 via T_pair Decomposition (Gemini recommended)

STRATEGY: Decompose into two "bowtie" subproblems.
- T_pair(A,B) = triangles sharing edge with A OR B
- T_pair(C,D) = triangles sharing edge with C OR D
- By maximality: All triangles ∈ T_pair(A,B) ∪ T_pair(C,D)
- Prove: τ(T_pair(A,B)) ≤ 4 (bowtie with shared vertex v1)
- Prove: τ(T_pair(C,D)) ≤ 4 (bowtie with shared vertex v3)
- By subadditivity: τ ≤ 4 + 4 = 8

KEY INSIGHT: A bowtie (two triangles sharing exactly one vertex) has τ ≤ 4.
The 4-edge cover for bowtie at v: pick 2 edges incident to v from each triangle.
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

structure Path4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  v1 : V
  v2 : V
  v3 : V
  hAB : A ∩ B = {v1}
  hBC : B ∩ C = {v2}
  hCD : C ∩ D = {v3}
  hAC : A ∩ C = ∅
  hAD : A ∩ D = ∅
  hBD : B ∩ D = ∅

/-- T_pair(e,f) = triangles sharing edge with e OR f -/
def T_pair (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∨ (t ∩ f).card ≥ 2)

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Definitions for the counterexample graph G_c and packing M_c.
-/
abbrev V_c := Fin 18

def mk_edge (i j : V_c) : Sym2 V_c :=
  Sym2.mk (i, j)

def edges_A : List (Sym2 V_c) := [mk_edge 0 1, mk_edge 1 2, mk_edge 0 2]
def flowers_A : List (Sym2 V_c) := [mk_edge 0 3, mk_edge 1 3, mk_edge 1 4, mk_edge 2 4, mk_edge 0 5, mk_edge 2 5]
def edges_B : List (Sym2 V_c) := [mk_edge 2 6, mk_edge 6 7, mk_edge 2 7]
def flowers_B : List (Sym2 V_c) := [mk_edge 2 8, mk_edge 6 8, mk_edge 6 9, mk_edge 7 9, mk_edge 2 10, mk_edge 7 10]
def edges_C : List (Sym2 V_c) := [mk_edge 7 11, mk_edge 11 12, mk_edge 7 12]
def flowers_C : List (Sym2 V_c) := [mk_edge 7 13, mk_edge 11 13, mk_edge 11 14, mk_edge 12 14, mk_edge 7 15, mk_edge 12 15]
def edges_D : List (Sym2 V_c) := [mk_edge 12 16, mk_edge 16 17, mk_edge 12 17]

def all_edges : List (Sym2 V_c) := edges_A ++ flowers_A ++ edges_B ++ flowers_B ++ edges_C ++ flowers_C ++ edges_D

def G_c : SimpleGraph V_c := SimpleGraph.fromEdgeSet all_edges.toFinset

def A_c : Finset V_c := {0, 1, 2}
def B_c : Finset V_c := {2, 6, 7}
def C_c : Finset V_c := {7, 11, 12}
def D_c : Finset V_c := {12, 16, 17}
def M_c : Finset (Finset V_c) := {A_c, B_c, C_c, D_c}

/-
Definitions of the specific triangles in the counterexample graph.
-/
def F_A1 : Finset V_c := {0, 1, 3}
def F_A2 : Finset V_c := {1, 2, 4}
def F_A3 : Finset V_c := {0, 2, 5}
def triangles_A : Finset (Finset V_c) := {A_c, F_A1, F_A2, F_A3}

def F_B1 : Finset V_c := {2, 6, 8}
def F_B2 : Finset V_c := {6, 7, 9}
def F_B3 : Finset V_c := {2, 7, 10}
def triangles_B : Finset (Finset V_c) := {B_c, F_B1, F_B2, F_B3}

def F_C1 : Finset V_c := {7, 11, 13}
def F_C2 : Finset V_c := {11, 12, 14}
def F_C3 : Finset V_c := {7, 12, 15}
def triangles_C : Finset (Finset V_c) := {C_c, F_C1, F_C2, F_C3}

def triangles_D : Finset (Finset V_c) := {D_c}

def all_triangles : Finset (Finset V_c) := triangles_A ∪ triangles_B ∪ triangles_C ∪ triangles_D

/-
All defined triangles are cliques of size 3 in G_c.
-/
lemma triangles_subset_clique : all_triangles ⊆ G_c.cliqueFinset 3 := by
  simp +decide [ all_triangles, Finset.subset_iff ];
  rintro t ( ht | ht | ht | ht ) <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
  · fin_cases ht <;> simp +decide [ G_c ];
  · fin_cases ht <;> simp +decide [ *, SimpleGraph.isClique_iff ] at *;
    · simp +decide [ B_c, G_c ];
    · simp +decide [ F_B1, G_c ];
    · simp +decide [ SimpleGraph.Adj, G_c ];
    · unfold F_B3; simp +decide [ G_c ] ;
  · revert ht; simp +decide [ triangles_C ] ;
    rintro ( rfl | rfl | rfl | rfl ) <;> simp +decide [ G_c ];
  · simp_all +decide [ triangles_D ];
    simp +decide [ G_c, SimpleGraph.IsClique ]

/-
The edge sets of the four clusters are pairwise disjoint.
-/
def cluster_edges_A : Finset (Sym2 V_c) := (edges_A ++ flowers_A).toFinset
def cluster_edges_B : Finset (Sym2 V_c) := (edges_B ++ flowers_B).toFinset
def cluster_edges_C : Finset (Sym2 V_c) := (edges_C ++ flowers_C).toFinset
def cluster_edges_D : Finset (Sym2 V_c) := edges_D.toFinset

lemma clusters_edge_disjoint :
  Disjoint cluster_edges_A cluster_edges_B ∧
  Disjoint cluster_edges_A cluster_edges_C ∧
  Disjoint cluster_edges_A cluster_edges_D ∧
  Disjoint cluster_edges_B cluster_edges_C ∧
  Disjoint cluster_edges_B cluster_edges_D ∧
  Disjoint cluster_edges_C cluster_edges_D := by
  simp +decide [cluster_edges_A, cluster_edges_B, cluster_edges_C, cluster_edges_D,
                edges_A, flowers_A, edges_B, flowers_B, edges_C, flowers_C, edges_D,
                mk_edge, Finset.disjoint_iff_ne]

/-
The set of 3-cliques in G_c is exactly the set of triangles we defined.
-/
lemma cliques_eq_all_triangles : G_c.cliqueFinset 3 = all_triangles := by
  refine' Finset.Subset.antisymm _ _;
  · intro t ht;
    rw [ SimpleGraph.mem_cliqueFinset_iff ] at ht;
    unfold G_c at ht;
    simp_all +decide [ SimpleGraph.fromEdgeSet, SimpleGraph.isNClique_iff ];
    rcases Finset.card_eq_three.mp ht.2 with ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ ; simp_all +decide [ Set.Pairwise ];
    native_decide +revert;
  · exact triangles_subset_clique

/-
Covering the triangles in cluster A requires at least 3 edges.
-/
lemma min_cover_A (E : Finset (Sym2 V_c)) (hE : E ⊆ cluster_edges_A)
  (h_cover : ∀ t ∈ triangles_A, ∃ e ∈ E, e ∈ t.sym2) :
  E.card ≥ 3 := by
    -- Let's consider all possible subsets of `cluster_edges_A` with fewer than 3 edges.
    have h_subsets : ∀ E ⊆ cluster_edges_A, E.card < 3 → ¬∀ t ∈ triangles_A, ∃ e ∈ E, e ∈ t.sym2 := by
      native_decide;
    exact not_lt.1 fun contra => h_subsets E hE contra h_cover

/-
Covering the triangles in cluster B requires at least 3 edges.
-/
lemma min_cover_B (E : Finset (Sym2 V_c)) (hE : E ⊆ cluster_edges_B)
  (h_cover : ∀ t ∈ triangles_B, ∃ e ∈ E, e ∈ t.sym2) :
  E.card ≥ 3 := by
    have h_subsets : ∀ E ⊆ cluster_edges_B, E.card < 3 → ¬∀ t ∈ triangles_B, ∃ e ∈ E, e ∈ t.sym2 := by
      native_decide
    exact not_lt.1 fun contra => h_subsets E hE contra h_cover

/-
Covering the triangles in cluster C requires at least 3 edges.
-/
lemma min_cover_C (E : Finset (Sym2 V_c)) (hE : E ⊆ cluster_edges_C)
  (h_cover : ∀ t ∈ triangles_C, ∃ e ∈ E, e ∈ t.sym2) :
  E.card ≥ 3 := by
    have h_subsets : ∀ E ⊆ cluster_edges_C, E.card < 3 → ¬∀ t ∈ triangles_C, ∃ e ∈ E, e ∈ t.sym2 := by
      native_decide
    exact not_lt.1 fun contra => h_subsets E hE contra h_cover

/-
Covering the triangles in cluster D requires at least 1 edge.
-/
lemma min_cover_D (E : Finset (Sym2 V_c)) (hE : E ⊆ cluster_edges_D)
  (h_cover : ∀ t ∈ triangles_D, ∃ e ∈ E, e ∈ t.sym2) :
  E.card ≥ 1 := by
    have h_subsets : ∀ E ⊆ cluster_edges_D, E.card < 1 → ¬∀ t ∈ triangles_D, ∃ e ∈ E, e ∈ t.sym2 := by
      native_decide
    exact not_lt.1 fun contra => h_subsets E hE contra h_cover

/-
Construction of the Path4 structure for the counterexample.
-/
def path4_c : Path4 G_c M_c := {
  A := A_c
  B := B_c
  C := C_c
  D := D_c
  hA := by
    native_decide +revert
  hB := by
    -- By definition of $M_c$, we know that $B_c \in M_c$.
    simp [M_c]
  hC := by
    decide +revert
  hD := by
    native_decide +revert
  hM_eq := by
    rfl
  v1 := 2
  v2 := 7
  v3 := 12
  hAB := by
    native_decide +revert
  hBC := by
    native_decide +revert
  hCD := by
    native_decide +revert
  hAC := by
    native_decide +revert
  hAD := by
    native_decide +revert
  hBD := by
    native_decide +revert
}

/-
M_c is a maximal triangle packing in G_c.
-/
lemma isMaxPacking_c : isMaxPacking G_c M_c := by
  constructor;
  · constructor;
    · rw [ cliques_eq_all_triangles ];
      native_decide +revert;
    · simp +decide [ Set.Pairwise ];
  · -- By examining the structure of the graph and the packing, we can see that any triangle not in M_c must share an edge with one of the clusters, thus satisfying the condition.
    intros t ht htm
    have h_cluster : ∃ m ∈ M_c, (t ∩ m).card ≥ 2 := by
      -- By examining each triangle in `all_triangles`, we can verify that they all intersect with some element of `M_c` in at least two elements.
      have h_intersect : ∀ t ∈ all_triangles, t ∉ M_c → ∃ m ∈ M_c, (t ∩ m).card ≥ 2 := by
        native_decide;
      exact h_intersect t ( by rw [ cliques_eq_all_triangles ] at ht; exact ht ) htm;
    exact h_cluster

/-
Edges of triangles in each cluster are contained in the cluster's edge set (restricted to graph edges).
-/
lemma triangles_A_edges_subset : ∀ t ∈ triangles_A, ∀ e ∈ t.sym2, e ∈ G_c.edgeFinset → e ∈ cluster_edges_A := by
  simp +decide [ cluster_edges_A ];
  intro t ht e he h; unfold G_c at h; simp_all +decide [ Sym2.forall ] ;
  native_decide +revert

lemma triangles_B_edges_subset : ∀ t ∈ triangles_B, ∀ e ∈ t.sym2, e ∈ G_c.edgeFinset → e ∈ cluster_edges_B := by
  simp +zetaDelta at *;
  -- We can verify each triangle in cluster B and see which edges are in the graph and part of the cluster.
  have h_cluster_B : ∀ t ∈ ({B_c, F_B1, F_B2, F_B3} : Finset (Finset V_c)), t.sym2.filter (fun e => e ∈ G_c.edgeFinset) ⊆ cluster_edges_B := by
    simp +zetaDelta at *;
    unfold G_c; simp +decide [ Set.subset_def ] ;
  intro t ht e he hG; specialize h_cluster_B t; simp_all +decide [ Finset.subset_iff ] ;
  unfold triangles_B at ht; aesop;

lemma triangles_C_edges_subset : ∀ t ∈ triangles_C, ∀ e ∈ t.sym2, e ∈ G_c.edgeFinset → e ∈ cluster_edges_C := by
  unfold cluster_edges_C;
  simp +zetaDelta at *;
  intro t ht e he heG;
  rcases e with ⟨ a, b ⟩;
  unfold G_c at heG; simp_all +decide [ SimpleGraph.fromEdgeSet ] ;
  native_decide +revert

lemma triangles_D_edges_subset : ∀ t ∈ triangles_D, ∀ e ∈ t.sym2, e ∈ G_c.edgeFinset → e ∈ cluster_edges_D := by
  norm_num +zetaDelta at *;
  -- Since triangles_D contains only one triangle, D_c, we can focus on this triangle.
  simp [triangles_D];
  rintro e h₁ h₂; rcases e with ⟨ a, b ⟩ ; simp_all +decide ;
  fin_cases a <;> fin_cases b <;> simp +decide at h₁ h₂ ⊢

/-
The graph G_c with packing M_c is a valid counterexample to the conjecture, having tau > 8.
-/
lemma counterexample_tau_gt_8 :
    isMaxPacking G_c M_c ∧
    Nonempty (Path4 G_c M_c) ∧
    ¬ (∃ E : Finset (Sym2 V_c), E.card ≤ 8 ∧ E ⊆ G_c.edgeFinset ∧ ∀ t ∈ G_c.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2) := by
      refine' ⟨ _, _, _ ⟩;
      · exact?;
      · exact ⟨ path4_c ⟩;
      · -- Assume there exists a cover E of size at most 8.
        by_contra h_contra
        obtain ⟨E, hE_card, hE_sub, hE_cover⟩ := h_contra;
        -- Partition E into parts covering A, B, C, D clusters.
        have h_partition : E.card ≥ (E ∩ cluster_edges_A).card + (E ∩ cluster_edges_B).card + (E ∩ cluster_edges_C).card + (E ∩ cluster_edges_D).card := by
          rw [ ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint ];
          · exact Finset.card_le_card fun x hx => by aesop;
          · simp_all +decide [ Finset.disjoint_left ];
            unfold cluster_edges_A cluster_edges_B cluster_edges_C cluster_edges_D at *; simp_all +decide [ Finset.disjoint_left ] ;
            rintro a ( ⟨ ha₁, ha₂ ⟩ | ⟨ ha₁, ha₂ ⟩ | ⟨ ha₁, ha₂ ⟩ ) ha₃ <;> simp_all +decide [ edges_A, edges_B, edges_C, edges_D, flowers_A, flowers_B, flowers_C ];
            · rcases ha₂ with ( ( rfl | rfl | rfl ) | rfl | rfl | rfl | rfl | rfl | rfl ) <;> decide;
            · rcases ha₂ with ( ( rfl | rfl | rfl ) | rfl | rfl | rfl | rfl | rfl | rfl ) <;> decide;
            · rcases ha₂ with ( ( rfl | rfl | rfl ) | rfl | rfl | rfl | rfl | rfl | rfl ) <;> decide;
          · simp_all +decide [ Finset.disjoint_left ];
            rintro e ( ⟨ he₁, he₂ ⟩ | ⟨ he₁, he₂ ⟩ ) he₃ <;> simp_all +decide [ cluster_edges_A, cluster_edges_B, cluster_edges_C ];
            · rcases he₂ with ( he₂ | he₂ ) <;> fin_cases he₂ <;> trivial;
            · exact ⟨ by rcases he₂ with ( he₂ | he₂ ) <;> fin_cases he₂ <;> trivial, by rcases he₂ with ( he₂ | he₂ ) <;> fin_cases he₂ <;> trivial ⟩;
          · exact Finset.disjoint_left.mpr ( by intros e he₁ he₂; exact Finset.disjoint_left.mp ( clusters_edge_disjoint.1 ) ( Finset.mem_inter.mp he₁ |>.2 ) ( Finset.mem_inter.mp he₂ |>.2 ) );
        -- Using `min_cover_*` lemmas, we show these parts must have sizes at least 3, 3, 3, 1.
        have h_min_cover_A : (E ∩ cluster_edges_A).card ≥ 3 := by
          apply min_cover_A;
          · exact Finset.inter_subset_right;
          · intro t ht;
            obtain ⟨ e, he₁, he₂ ⟩ := hE_cover t ( cliques_eq_all_triangles ▸ Finset.mem_union_left _ ( Finset.mem_union_left _ ( Finset.mem_union_left _ ht ) ) );
            use e;
            exact ⟨ Finset.mem_inter.mpr ⟨ he₁, triangles_A_edges_subset t ht e he₂ ( hE_sub he₁ ) ⟩, he₂ ⟩
        have h_min_cover_B : (E ∩ cluster_edges_B).card ≥ 3 := by
          apply min_cover_B;
          · exact Finset.inter_subset_right;
          · intro t ht;
            obtain ⟨ e, he₁, he₂ ⟩ := hE_cover t ( cliques_eq_all_triangles ▸ Finset.mem_union_left _ ( Finset.mem_union_left _ ( Finset.mem_union_right _ ht ) ) );
            have := triangles_B_edges_subset t ht e; aesop;
        have h_min_cover_C : (E ∩ cluster_edges_C).card ≥ 3 := by
          apply min_cover_C;
          · exact Finset.inter_subset_right;
          · intro t ht
            obtain ⟨e, heE, heT⟩ := hE_cover t (by
            rw [ cliques_eq_all_triangles ];
            native_decide +revert);
            have he_cluster : e ∈ cluster_edges_C := by
              apply triangles_C_edges_subset t ht e heT (hE_sub heE);
            aesop
        have h_min_cover_D : (E ∩ cluster_edges_D).card ≥ 1 := by
          grind;
        linarith

/-
The graph G_c with packing M_c is a valid counterexample to the conjecture, having tau > 8.
-/
lemma counterexample_tau_gt_8_final :
    isMaxPacking G_c M_c ∧
    Nonempty (Path4 G_c M_c) ∧
    ¬ (∃ E : Finset (Sym2 V_c), E.card ≤ 8 ∧ E ⊆ G_c.edgeFinset ∧ ∀ t ∈ G_c.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2) := by
      exact?

/-
The conjecture `tau_le_8_path4` is false.
-/
theorem tau_le_8_path4_false : ¬ (∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M),
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2) := by
      intro h_contra
      obtain ⟨E, hE⟩ : ∃ E : Finset (Sym2 V_c), E.card ≤ 8 ∧ E ⊆ G_c.edgeFinset ∧ ∀ t ∈ G_c.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
        specialize @h_contra ( ULift V_c );
        specialize h_contra ( G_c.comap ULift.down ) ( Finset.image ( fun t : Finset V_c => Finset.image ULift.up t ) M_c ) ?_ ?_;
        · constructor;
          · constructor;
            · intro t ht;
              simp +zetaDelta at *;
              rcases ht with ⟨ a, ha, rfl ⟩ ; fin_cases ha <;> simp +decide [ SimpleGraph.isNClique_iff ] ;
              · simp +decide [ Set.Pairwise, SimpleGraph.comap ];
                simp +decide [ A_c, G_c ];
              · simp +decide [ Set.Pairwise, G_c ];
              · simp +decide [ SimpleGraph.isClique_iff, Set.Pairwise ];
                simp +decide [ C_c, G_c ];
              · simp +decide [ SimpleGraph.IsClique, Set.Pairwise ];
                simp +decide [ D_c, G_c ];
            · simp +decide [ Set.Pairwise ];
          · intro t ht ht';
            -- Let's unfold the definition of `isMaxPacking` to use the properties of `M_c`.
            obtain ⟨m, hm⟩ : ∃ m ∈ M_c, (t.image ULift.down ∩ m).card ≥ 2 := by
              have h_max_packing : ∀ t ∈ G_c.cliqueFinset 3, t ∉ M_c → ∃ m ∈ M_c, (t ∩ m).card ≥ 2 := by
                exact fun t ht ht' => ( isMaxPacking_c.2 t ht ht' );
              apply h_max_packing;
              · convert ht using 1;
                simp +decide [ SimpleGraph.isNClique_iff, Finset.card_image_of_injective, Function.Injective ];
                simp +decide [ SimpleGraph.IsClique, Set.Pairwise ];
              · contrapose! ht';
                rw [ Finset.mem_image ] at *;
                use Finset.image ULift.down t;
                exact ⟨ ht', by rw [ Finset.image_image ] ; aesop ⟩;
            refine' ⟨ Finset.image ULift.up m, _, _ ⟩ <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
            · exact ⟨ m, hm.1, rfl ⟩;
            · convert hm.2 using 1;
              rw [ ← Finset.card_image_of_injective _ ULift.down_injective ] ; congr ; ext ; aesop;
        · constructor;
          all_goals norm_num [ M_c ];
          all_goals norm_cast;
          · exact Or.inl rfl;
          · exact Or.inr <| Or.inl rfl;
          · exact Or.inr <| Or.inr <| Or.inl rfl;
          · exact Or.inr <| Or.inr <| Or.inr rfl;
        · obtain ⟨ E, hE₁, hE₂, hE₃ ⟩ := h_contra;
          refine' ⟨ E.image ( fun e => Sym2.map ULift.down e ), _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
          · exact le_trans ( Finset.card_image_le ) hE₁;
          · intro e he; specialize hE₂ he; rcases e with ⟨ ⟨ x, y ⟩ ⟩ ; aesop;
          · intro t ht; specialize hE₃ ( Finset.image ULift.up t ) ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            convert hE₃ _ _;
            · intro x hx y hy; aesop;
            · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy, ht.2 ];
      exact counterexample_tau_gt_8_final.2.2 ⟨ E, hE ⟩

/-
The graph G_c has no edge cover of size 8 or less.
-/
lemma counterexample_disproof :
    ¬ (∃ E : Finset (Sym2 V_c), E.card ≤ 8 ∧ E ⊆ G_c.edgeFinset ∧ ∀ t ∈ G_c.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2) := by
      convert counterexample_tau_gt_8_final.2.2 using 1

/-
The conjecture `tau_le_8_path4` is false, as demonstrated by the counterexample G_c.
-/
theorem tau_le_8_path4_disproof : ¬ (∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M),
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2) := by
      push_neg;
      convert tau_le_8_path4_false;
      constructor <;> intro h;
      convert tau_le_8_path4_false;
      push_neg at h;
      convert h

end AristotleLemmas

/-
PROOF SKETCH:
1. Every triangle shares edge with some M-element (maximality)
2. M = {A, B, C, D}, so every triangle shares edge with A, B, C, or D
3. If shares with A or B: t ∈ T_pair(A,B)
4. If shares with C or D: t ∈ T_pair(C,D)
5. Hence G.cliqueFinset 3 ⊆ T_pair(A,B) ∪ T_pair(C,D)

For τ(T_pair(A,B)) ≤ 4:
- A and B share exactly vertex v1
- 4-edge cover: {v1,a1}, {v1,a2} from A, {v1,v2}, {v1,b'} from B
- Every triangle in T_pair(A,B) contains v1 OR shares base {a1,a2} or {v2,b'}
- If contains v1: covered by star edges
- If shares {a1,a2}: covered by... hmm, {a1,a2} not in cover!

ISSUE: Bowtie cover works for triangles CONTAINING the shared vertex,
but not for triangles sharing the BASE edges opposite the shared vertex.

REVISED APPROACH: Use 2 edges per original M-triangle, selected to cover bases.
For A: use {v1,a1} and {a1,a2} (covers leg and base)
For B: use {v1,b'} and {v2,b'} (covers both legs from b')
Total from A∪B: 4 edges

Hmm, but {v1,a2,x} is missed if we use {v1,a1} and {a1,a2}!

Let Aristotle figure out the right selection.
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  by_contra! h_contra;
  have := @tau_le_8_path4_disproof;
  apply this;
  convert h_contra using 1

-/
/-
PROOF SKETCH:
1. Every triangle shares edge with some M-element (maximality)
2. M = {A, B, C, D}, so every triangle shares edge with A, B, C, or D
3. If shares with A or B: t ∈ T_pair(A,B)
4. If shares with C or D: t ∈ T_pair(C,D)
5. Hence G.cliqueFinset 3 ⊆ T_pair(A,B) ∪ T_pair(C,D)

For τ(T_pair(A,B)) ≤ 4:
- A and B share exactly vertex v1
- 4-edge cover: {v1,a1}, {v1,a2} from A, {v1,v2}, {v1,b'} from B
- Every triangle in T_pair(A,B) contains v1 OR shares base {a1,a2} or {v2,b'}
- If contains v1: covered by star edges
- If shares {a1,a2}: covered by... hmm, {a1,a2} not in cover!

ISSUE: Bowtie cover works for triangles CONTAINING the shared vertex,
but not for triangles sharing the BASE edges opposite the shared vertex.

REVISED APPROACH: Use 2 edges per original M-triangle, selected to cover bases.
For A: use {v1,a1} and {a1,a2} (covers leg and base)
For B: use {v1,b'} and {v2,b'} (covers both legs from b')
Total from A∪B: 4 edges

Hmm, but {v1,a2,x} is missed if we use {v1,a1} and {a1,a2}!

Let Aristotle figure out the right selection.
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  sorry

end