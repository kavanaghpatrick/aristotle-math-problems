/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: dc919546-e79f-4e64-89fe-f752acb4a853

The following was proved by Aristotle:

- theorem triangle_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    cfg.v1 ∈ t ∨ cfg.v2 ∈ t ∨ cfg.v3 ∈ t ∨
    ((t ∩ cfg.A).card ≥ 2 ∧ cfg.v1 ∉ t) ∨
    ((t ∩ cfg.D).card ≥ 2 ∧ cfg.v3 ∉ t)

- lemma path4_cover_card_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (cfg : Path4 G M) :
    (path4_cover G cfg).card ≤ 8
-/

/-
slot269: PATH_4 τ ≤ 8 via Structural Decomposition

KEY INSIGHT (from AI consultation):
Every triangle in PATH_4 either:
1. Contains a spine vertex (v1, v2, or v3), OR
2. Is "endpoint-private" (shares edge with A avoiding v1, or D avoiding v3)

8-EDGE COVER:
- edges(A) = 3 edges (covers A, endpoint-private A, triangles with v1)
- {v1,v2}, {v2,v3} = 2 edges (covers triangles with v2)
- edges(D) = 3 edges (covers D, endpoint-private D, triangles with v3)
Total: 8 edges
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

-- Basic membership lemmas
lemma v1_in_A (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v1 ∈ cfg.A := by
  have h := cfg.hAB
  rw [Finset.ext_iff] at h
  have := (h cfg.v1).mpr (by simp)
  exact Finset.mem_inter.mp this |>.1

lemma v1_in_B (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v1 ∈ cfg.B := by
  have h := cfg.hAB
  rw [Finset.ext_iff] at h
  have := (h cfg.v1).mpr (by simp)
  exact Finset.mem_inter.mp this |>.2

lemma v2_in_B (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v2 ∈ cfg.B := by
  have h := cfg.hBC
  rw [Finset.ext_iff] at h
  have := (h cfg.v2).mpr (by simp)
  exact Finset.mem_inter.mp this |>.1

lemma v2_in_C (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v2 ∈ cfg.C := by
  have h := cfg.hBC
  rw [Finset.ext_iff] at h
  have := (h cfg.v2).mpr (by simp)
  exact Finset.mem_inter.mp this |>.2

lemma v3_in_C (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v3 ∈ cfg.C := by
  have h := cfg.hCD
  rw [Finset.ext_iff] at h
  have := (h cfg.v3).mpr (by simp)
  exact Finset.mem_inter.mp this |>.1

lemma v3_in_D (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (cfg : Path4 G M) : cfg.v3 ∈ cfg.D := by
  have h := cfg.hCD
  rw [Finset.ext_iff] at h
  have := (h cfg.v3).mpr (by simp)
  exact Finset.mem_inter.mp this |>.2

-- Key structural lemma
/-
PROOF SKETCH:
For any triangle t, by maximality of M, t shares edge with some m ∈ {A,B,C,D}.
- If m = A and v1 ∉ t: then t ∩ A has ≥2 elements from A\{v1}, endpoint-private
- If m = B and v1 ∉ t and v2 ∉ t: t ∩ B ⊆ {b}, so |t ∩ B| ≤ 1, contradiction
- If m = C and v2 ∉ t and v3 ∉ t: t ∩ C ⊆ {c}, so |t ∩ C| ≤ 1, contradiction
- If m = D and v3 ∉ t: then t ∩ D has ≥2 elements from D\{v3}, endpoint-private
-/
theorem triangle_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    cfg.v1 ∈ t ∨ cfg.v2 ∈ t ∨ cfg.v3 ∈ t ∨
    ((t ∩ cfg.A).card ≥ 2 ∧ cfg.v1 ∉ t) ∨
    ((t ∩ cfg.D).card ≥ 2 ∧ cfg.v3 ∉ t) := by
  -- Let's choose any triangle t in G.
  by_contra h_contra;
  -- By maximality of M, there exists m ∈ {A,B,C,D} such that t ∩ m has ≥ 2 elements.
  obtain ⟨m, hm⟩ : ∃ m ∈ ({cfg.A, cfg.B, cfg.C, cfg.D} : Finset (Finset V)), (t ∩ m).card ≥ 2 := by
    have := hM.2 t ht;
    by_cases h : t ∈ M <;> simp_all +decide [ cfg.hM_eq ];
    have := ht.card_eq; aesop;
  -- Let's consider the cases where m is A, B, C, or D.
  by_cases hmA : m = cfg.A;
  · simp_all +decide [ Finset.inter_comm ];
  · by_cases hmB : m = cfg.B;
    · have h_card_B : (t ∩ cfg.B).card ≤ 1 := by
        have h_card_B : (t ∩ cfg.B) ⊆ {cfg.v1, cfg.v2}ᶜ := by
          simp_all +decide [ Finset.subset_iff ];
          grind;
        have h_card_B : (t ∩ cfg.B) ⊆ cfg.B \ {cfg.v1, cfg.v2} := by
          simp_all +decide [ Finset.subset_iff ];
        have h_card_B : (cfg.B \ {cfg.v1, cfg.v2}).card ≤ 1 := by
          have h_card_B : cfg.B.card = 3 := by
            have := hM.1;
            have := this.1 cfg.hB; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
            exact this.card_eq;
          have h_card_B : (cfg.B \ {cfg.v1, cfg.v2}).card = cfg.B.card - ({cfg.v1, cfg.v2} : Finset V).card := by
            have := cfg.hAB; have := cfg.hBC; simp_all +decide [ Finset.ext_iff ] ;
            grind;
          by_cases h : cfg.v1 = cfg.v2 <;> simp_all +decide;
          have := cfg.hAB; have := cfg.hBC; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
          have := cfg.hAC; simp_all +decide [ Finset.ext_iff ] ;
        exact le_trans ( Finset.card_le_card ‹_› ) h_card_B;
      grind;
    · by_cases hmC : m = cfg.C;
      · have h_inter_C : t ∩ cfg.C ⊆ {cfg.v2, cfg.v3}ᶜ := by
          intro x hx; aesop;
        have h_inter_C_card : (t ∩ cfg.C).card ≤ (cfg.C \ {cfg.v2, cfg.v3}).card := by
          exact Finset.card_le_card fun x hx => by have := h_inter_C hx; aesop;
        have h_inter_C_card : cfg.C.card = 3 := by
          have := hM.1;
          have := this.1; simp_all +decide [ isTrianglePacking ] ;
          have := this cfg.hC; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        have := cfg.hBC; have := cfg.hCD; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
        have := cfg.hBD; simp_all +decide [ Finset.ext_iff ] ;
        grind;
      · simp_all +decide [ Finset.inter_comm ];
        exact h_contra.2.2.1 ( h_contra.2.2.2.2 ( by simpa only [ hm.1, Finset.inter_comm ] using hm.2 ) )

-- 8-edge cover
def path4_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (cfg : Path4 G M) : Finset (Sym2 V) :=
  cfg.A.sym2.filter (· ∈ G.edgeFinset) ∪
  ({s(cfg.v1, cfg.v2), s(cfg.v2, cfg.v3)} : Finset (Sym2 V)).filter (· ∈ G.edgeFinset) ∪
  cfg.D.sym2.filter (· ∈ G.edgeFinset)

lemma path4_cover_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Path4 G M) :
    path4_cover G cfg ⊆ G.edgeFinset := by
  -- Each component is filtered to G.edgeFinset, so union is subset
  unfold path4_cover
  intro e he
  simp only [Finset.mem_union, Finset.mem_filter] at he
  aesop

/-
PROOF SKETCH:
A.sym2 has ≤ 3 edges (A is a 3-clique)
Spine set has ≤ 2 edges
D.sym2 has ≤ 3 edges
Total ≤ 8
-/
lemma path4_cover_card_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (cfg : Path4 G M) :
    (path4_cover G cfg).card ≤ 8 := by
  refine' le_trans ( Finset.card_union_le _ _ ) _;
  refine' le_trans ( add_le_add ( Finset.card_union_le _ _ ) le_rfl ) _;
  -- Each triangle contributes at most 3 edges, so the total number of edges in the path4_cover is at most $3 + 2 + 3 = 8$.
  have h_triangle_edges : ∀ t ∈ M, t.card = 3 → Finset.card (Finset.filter (fun e => e ∈ G.edgeFinset) (t.sym2)) ≤ 3 := by
    intro t ht ht'; have := Finset.card_eq_three.mp ht'; obtain ⟨ a, b, c, hab, hbc, hac ⟩ := this; simp +decide [ *, SimpleGraph.edgeFinset ] ;
    refine' le_trans ( Finset.card_le_card _ ) _;
    exact { Sym2.mk ( a, b ), Sym2.mk ( a, c ), Sym2.mk ( b, c ) };
    · simp +decide [ Finset.subset_iff, Sym2.forall ];
      aesop;
    · exact Finset.card_insert_le _ _ |> le_trans <| add_le_add_right ( Finset.card_insert_le _ _ ) _;
  refine' le_trans ( add_le_add_three ( h_triangle_edges _ _ _ ) ( Finset.card_filter_le _ _ ) ( h_triangle_edges _ _ _ ) ) _;
  · exact cfg.hA;
  · have := hM.1;
    have := this cfg.hA; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
    exact this.card_eq;
  · exact cfg.hD;
  · have := cfg.hM_eq ▸ hM.1;
    simp_all +decide [ Finset.subset_iff ];
    exact this.2.2.2.2;
  · grind

/- Aristotle failed to find a proof. -/
/-
PROOF SKETCH (coverage):
By triangle_structure, every triangle t either:
1. Contains v1: t has edge in A.sym2 (since v1 ∈ A and t is a clique)
2. Contains v2 (not v1): t has edge {v1,v2} or {v2,v3}
3. Contains v3 (not v1,v2): t has edge in D.sym2 or {v2,v3}
4. Endpoint-private A: t shares {a,a'} with A, edge in A.sym2
5. Endpoint-private D: t shares edge with D, in D.sym2
-/
lemma path4_cover_covers (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ path4_cover G cfg, e ∈ t.sym2 := by
  sorry

-- Main theorem
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (cfg : Path4 G M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  use path4_cover G cfg
  refine ⟨path4_cover_card_le_8 G M hM.1 cfg, path4_cover_subset G M cfg, ?_⟩
  intro t ht
  exact path4_cover_covers G M hM cfg t ht

end