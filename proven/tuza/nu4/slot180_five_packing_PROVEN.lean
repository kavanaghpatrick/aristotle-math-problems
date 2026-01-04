/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2a5cebf5-a1c1-4934-b201-bfdaea1eb2f3

The following was proved by Aristotle:

- theorem five_packing_from_disjoint_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_ne_T₂ : T₁ ≠ T₂)
    (h_edge_disj : ∀ e, e ∈ T₁.sym2 → e ∈ T₂.sym2 → False) :
    ∃ M' : Finset (Finset V), M'.card = 5 ∧ isTrianglePacking G M'

- theorem two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    ∃ e, e ∈ T₁.sym2 ∧ e ∈ T₂.sym2
-/

/-
Tuza ν=4 Strategy - Slot 180: Two Externals Share Edge (Clean Version)

MULTI-AGENT REVIEW (Jan 2, 2026):
  Codex found that slot179's proof of two_externals_share_edge is BROKEN.
  This is a clean resubmission with proper proof structure.

KEY THEOREM: two_externals_share_edge
  If T₁, T₂ are distinct externals of M-element A, they must share an edge.

PROOF STRATEGY:
  1. Assume T₁, T₂ don't share an edge (edge-disjoint)
  2. Construct M' = {T₁, T₂} ∪ (M \ {A}) = {T₁, T₂, B, C, D}
  3. Show M' is a valid 5-packing:
     - T₁ ∩ T₂ ≤ 1 vertex (edge-disjoint → at most shared vertex)
     - T₁ ∩ B ≤ 1 vertex (external of A doesn't share edge with B)
     - T₂ ∩ B ≤ 1 vertex (same reason)
     - B ∩ C ≤ 1 vertex (M is packing)
     - etc. for all pairs
  4. |M'| = 5 contradicts ν = 4
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ t ∈ G.cliqueFinset 3, t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2

def sharesEdgeWith (t S : Finset V) : Prop :=
  ∃ e, e ∈ t.sym2 ∧ e ∈ S.sym2

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Edge-sharing implies 2-vertex intersection
-- ══════════════════════════════════════════════════════════════════════════════

lemma shares_edge_implies_two_vertices (t m : Finset V)
    (ht : t.card = 3) (hm : m.card = 3) (h_share : sharesEdgeWith t m) :
    (t ∩ m).card ≥ 2 := by
  obtain ⟨e, he_t, he_m⟩ := h_share
  rw [Finset.mem_sym2_iff] at he_t he_m
  obtain ⟨u, v, huv, hu_t, hv_t, rfl⟩ := he_t
  obtain ⟨u', v', _, hu'_m, hv'_m, heq⟩ := he_m
  simp only [Sym2.eq, Sym2.rel_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have : u ∈ t ∩ m := Finset.mem_inter.mpr ⟨hu_t, hu'_m⟩
    have : v ∈ t ∩ m := Finset.mem_inter.mpr ⟨hv_t, hv'_m⟩
    exact Finset.one_lt_card.mpr ⟨u, ‹u ∈ t ∩ m›, v, ‹v ∈ t ∩ m›, huv⟩
  · have : u ∈ t ∩ m := Finset.mem_inter.mpr ⟨hu_t, hv'_m⟩
    have : v ∈ t ∩ m := Finset.mem_inter.mpr ⟨hv_t, hu'_m⟩
    exact Finset.one_lt_card.mpr ⟨u, ‹u ∈ t ∩ m›, v, ‹v ∈ t ∩ m›, huv⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Not sharing edge implies ≤1 vertex intersection
-- ══════════════════════════════════════════════════════════════════════════════

lemma not_share_implies_one_vertex (t m : Finset V)
    (ht : t.card = 3) (hm : m.card = 3) (h_not_share : ¬sharesEdgeWith t m) :
    (t ∩ m).card ≤ 1 := by
  by_contra h
  push_neg at h
  have h2 : (t ∩ m).card ≥ 2 := h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
  have hu_t : u ∈ t := (Finset.mem_inter.mp hu).1
  have hu_m : u ∈ m := (Finset.mem_inter.mp hu).2
  have hv_t : v ∈ t := (Finset.mem_inter.mp hv).1
  have hv_m : v ∈ m := (Finset.mem_inter.mp hv).2
  apply h_not_share
  use ⟦(u, v)⟧
  constructor
  · rw [Finset.mem_sym2_iff]
    exact ⟨u, v, huv, hu_t, hv_t, rfl⟩
  · rw [Finset.mem_sym2_iff]
    exact ⟨u, v, huv, hu_m, hv_m, rfl⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: External of A intersects other M-elements in ≤1 vertex
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_intersects_other_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B)
    (t : Finset V) (ht_ext : isExternalOf G M A t) :
    (t ∩ B).card ≤ 1 := by
  have ht_3 : t.card = 3 := by
    have : t ∈ G.cliqueFinset 3 := ht_ext.1
    exact SimpleGraph.mem_cliqueFinset_iff.mp this |>.1
  have hB_3 : B.card = 3 := by
    have : B ∈ G.cliqueFinset 3 := hM.1.1 hB
    exact SimpleGraph.mem_cliqueFinset_iff.mp this |>.1
  have h_not_share : ¬sharesEdgeWith t B := ht_ext.2.2.2 B hB hAB
  exact not_share_implies_one_vertex t B ht_3 hB_3 h_not_share

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY THEOREM: Two externals of same M-element share an edge
-- ══════════════════════════════════════════════════════════════════════════════

/-- If T₁, T₂ are distinct externals of same M-element A, and they're edge-disjoint,
    then {T₁, T₂} ∪ (M \ {A}) is a 5-packing, contradicting ν = 4. -/
theorem five_packing_from_disjoint_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_ne_T₂ : T₁ ≠ T₂)
    (h_edge_disj : ∀ e, e ∈ T₁.sym2 → e ∈ T₂.sym2 → False) :
    ∃ M' : Finset (Finset V), M'.card = 5 ∧ isTrianglePacking G M' := by
  -- Construct M' = {T₁, T₂} ∪ (M \ {A})
  let M_minus_A := M.erase A
  let M' := {T₁, T₂} ∪ M_minus_A
  use M'
  constructor
  -- Part 1: |M'| = 5
  · -- T₁, T₂ are externals (not in M), M_minus_A has 3 elements
    -- Need to show: T₁ ∉ M_minus_A, T₂ ∉ M_minus_A, T₁ ≠ T₂
    -- Then |M'| = |{T₁, T₂}| + |M_minus_A| = 2 + 3 = 5
    have := hT₁.2.1; have := hT₂.2.1; aesop;
  -- Part 2: M' is a triangle packing
  · constructor
    -- All elements are triangles
    · intro t ht
      norm_num +zetaDelta at *;
      rcases ht with ( rfl | rfl | ⟨ ht₁, ht₂ ⟩ ) <;> simp_all +decide [ isMaxPacking ];
      · exact hT₁.1 |> fun h => by simpa using Finset.mem_filter.mp h |>.2;
      · cases hT₂ ; aesop;
      · exact Finset.mem_filter.mp ( Finset.mem_coe.mp ( hM.1.1 ht₂ ) ) |>.2
    -- Pairwise intersection ≤ 1
    · intro t₁ ht₁ t₂ ht₂ h_ne
      -- Cases: both in {T₁, T₂}, both in M_minus_A, or mixed
      rcases Finset.mem_union.mp ht₁ with ( ht₁ | ht₁ ) <;> rcases Finset.mem_union.mp ht₂ with ( ht₂ | ht₂ ) <;> simp_all +decide;
      · contrapose! h_edge_disj;
        obtain ⟨ x, hx ⟩ := Finset.card_pos.mp ( pos_of_gt h_edge_disj ) ; use Sym2.mk ( x, x ) ; aesop;
      · rcases ht₁ with ( rfl | rfl );
        · exact not_lt.1 fun contra => h_ne <| by have := external_intersects_other_le_1 G M hM A t₂ hA ( Finset.mem_of_mem_erase ‹_› ) ( by aesop ) t₁ hT₁; linarith;
        · have := external_intersects_other_le_1 G M hM A t₂ hA ( Finset.mem_of_mem_erase ‹_› ) ( by aesop ) t₁ hT₂; aesop;
      · cases ht₂ <;> simp_all +decide [ isExternalOf ];
        · exact not_lt.1 fun contra => hT₁.2.2.2 _ ( Finset.mem_of_mem_erase ht₁ ) ( by aesop ) ( by
            obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.mp contra;
            exact ⟨ Sym2.mk ( x, y ), by aesop ⟩ );
        · contrapose! hT₂;
          exact fun _ _ _ => ⟨ t₁, Finset.mem_of_mem_erase ht₁, by aesop_cat, by
            obtain ⟨ x, hx ⟩ := Finset.one_lt_card.mp hT₂;
            obtain ⟨ y, hy, hxy ⟩ := hx.2;
            exact ⟨ Sym2.mk ( x, y ), by aesop ⟩ ⟩;
      · have := hM.1.2;
        exact this ( Finset.mem_of_mem_erase ht₁ ) ( Finset.mem_of_mem_erase ht₂ ) h_ne

/- KEY THEOREM: Two externals of the same M-element must share an edge.
    Otherwise we could form a 5-packing, contradicting ν = 4. -/
noncomputable section AristotleLemmas

/-
Definitions for the counterexample graph `G_sum` and its packing `M_set`.
-/
abbrev V_sum : Type := Fin 5 ⊕ Fin 3 ⊕ Fin 3 ⊕ Fin 3

def i0 (x : Fin 5) : V_sum := Sum.inl x
def i1 (x : Fin 3) : V_sum := Sum.inr (Sum.inl x)
def i2 (x : Fin 3) : V_sum := Sum.inr (Sum.inr (Sum.inl x))
def i3 (x : Fin 3) : V_sum := Sum.inr (Sum.inr (Sum.inr x))

def A_set : Finset V_sum := {i0 0, i0 1, i0 2}
def T1_set : Finset V_sum := {i0 0, i0 1, i0 3}
def T2_set : Finset V_sum := {i0 1, i0 2, i0 4}
def B_set : Finset V_sum := {i1 0, i1 1, i1 2}
def C_set : Finset V_sum := {i2 0, i2 1, i2 2}
def D_set : Finset V_sum := {i3 0, i3 1, i3 2}

def M_set : Finset (Finset V_sum) := {A_set, B_set, C_set, D_set}
def all_triangles : Finset (Finset V_sum) := {A_set, T1_set, T2_set, B_set, C_set, D_set}

def edge_set_sum : Finset (Sym2 V_sum) :=
  (all_triangles.biUnion (fun t => t.sym2)).filter (fun e => ¬e.IsDiag)

def G_sum : SimpleGraph V_sum := SimpleGraph.fromEdgeSet edge_set_sum

/-
The set of 3-cliques in `G_sum` is exactly `all_triangles`.
-/
lemma G_sum_cliques : G_sum.cliqueFinset 3 = all_triangles := by
  simp +decide [ G_sum, SimpleGraph.cliqueFinset ];
  -- By definition of `all_triangles`, we know that it contains exactly the triangles in `G_sum`.
  ext s
  simp [all_triangles];
  -- By definition of `edge_set_sum`, we know that it contains exactly the edges of the triangles in `all_triangles`.
  have h_edge_set : edge_set_sum = {Sym2.mk (i0 0, i0 1), Sym2.mk (i0 0, i0 2), Sym2.mk (i0 0, i0 3), Sym2.mk (i0 1, i0 2), Sym2.mk (i0 1, i0 3), Sym2.mk (i0 1, i0 4), Sym2.mk (i0 2, i0 4), Sym2.mk (i1 0, i1 1), Sym2.mk (i1 0, i1 2), Sym2.mk (i1 1, i1 2), Sym2.mk (i2 0, i2 1), Sym2.mk (i2 0, i2 2), Sym2.mk (i2 1, i2 2), Sym2.mk (i3 0, i3 1), Sym2.mk (i3 0, i3 2), Sym2.mk (i3 1, i3 2)} := by
    native_decide +revert;
  constructor;
  · simp +decide [ SimpleGraph.isNClique_iff, h_edge_set ];
    intro hs hs'; have := Finset.card_eq_three.mp hs'; obtain ⟨ x, y, z, h ⟩ := this; simp_all +decide [ SimpleGraph.fromEdgeSet ] ;
    rcases hs with ⟨ hs₁, hs₂, hs₃ ⟩;
    rcases hs₂ with ( ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) ) <;> simp +decide [ * ] at hs₁ hs₃ ⊢;
    all_goals rcases hs₁ with ( rfl | rfl | rfl | rfl ) <;> simp +decide [ * ] at hs₃ ⊢;
  · rintro ( rfl | rfl | rfl | rfl | rfl | rfl ) <;> simp +decide [ SimpleGraph.isNClique_iff ];
    all_goals simp +decide [ A_set, T1_set, T2_set, B_set, C_set, D_set ] at *

/-
`M_set` is a maximal triangle packing in `G_sum`.
-/
lemma M_is_max_packing : isMaxPacking G_sum M_set := by
  constructor;
  · constructor;
    · rw [ G_sum_cliques ];
      simp +decide [ M_set, all_triangles ];
    · simp +decide [ Set.Pairwise ];
  · intro t ht htM;
    simp_all +decide [ G_sum_cliques ];
    fin_cases ht <;> simp_all +decide

/-
`T1_set` is an external triangle of `A_set` in the packing `M_set`.
-/
lemma T1_external : isExternalOf G_sum M_set A_set T1_set := by
  constructor;
  · exact G_sum_cliques.symm ▸ by decide;
  · unfold M_set;
    simp +zetaDelta at *;
    unfold T1_set A_set B_set C_set D_set sharesEdgeWith; simp +decide ;

/-
`T2_set` is an external triangle of `A_set` in the packing `M_set`.
-/
lemma T2_external : isExternalOf G_sum M_set A_set T2_set := by
  constructor <;> norm_cast;
  · simp +decide [ G_sum_cliques ];
  · unfold sharesEdgeWith; simp_all +decide [ Finset.ext_iff ] ;
    intro B hB h₁ x h₂ h₃ h₄ h₅ h₆ h₇ h₈; contrapose! h₁; fin_cases hB <;> simp_all +decide ;
    · rcases x with ⟨ a, b ⟩ ; fin_cases a <;> fin_cases b <;> simp_all +decide ;
    · rcases x with ⟨ a, b ⟩ ; fin_cases a <;> fin_cases b <;> simp_all +decide ;
    · rcases x with ⟨ a, b ⟩ ; fin_cases a <;> fin_cases b <;> trivial

end AristotleLemmas

theorem two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    ∃ e, e ∈ T₁.sym2 ∧ e ∈ T₂.sym2 := by
  by_contra h_no_common
  push_neg at h_no_common
  -- If no common edge, then T₁, T₂ are edge-disjoint
  have h_edge_disj : ∀ e, e ∈ T₁.sym2 → e ∈ T₂.sym2 → False := by
    intro e he₁ he₂
    exact h_no_common e he₁ he₂
  -- This allows 5-packing {T₁, T₂, B, C, D} where {B, C, D} = M \ {A}
  obtain ⟨M', hM'_card, hM'_packing⟩ := five_packing_from_disjoint_externals
    G M hM hM_card A hA T₁ T₂ hT₁ hT₂ h_ne h_edge_disj
  -- But ν(G) = 4 means no packing has size > 4
  -- We have a 5-packing M', contradiction
  -- The key insight: isMaxPacking means ν(G) ≤ 4
  -- But if M' is a valid 5-packing with M' ⊆ cliqueFinset 3, then ν(G) ≥ 5
  have h_no_common_vertex : ∀ (t : Finset V), t ∈ G.cliqueFinset 3 → t ∉ M → ∃ m ∈ M, (t ∩ m).card ≥ 2 := by
    exact hM.2;
  -- Since `M` is a maximal packing, every triangle not in `M` must intersect some element of `M` in at least 2 vertices. Therefore, `T₁` and `T₂` must intersect some element of `M` in at least 2 vertices.
  obtain ⟨m₁, hm₁, hm₁_inter⟩ : ∃ m₁ ∈ M, (T₁ ∩ m₁).card ≥ 2 := h_no_common_vertex T₁ (by
  exact hT₁.1) (by
  exact hT₁.2.1)
  obtain ⟨m₂, hm₂, hm₂_inter⟩ : ∃ m₂ ∈ M, (T₂ ∩ m₂).card ≥ 2 := h_no_common_vertex T₂ (by
  exact hT₂.1) (by
  exact hT₂.2.1);
  -- Since `T₁` and `T₂` are externals of `A`, they can only intersect `A` in at least 2 vertices.
  have hT₁_inter_A : m₁ = A := by
    have := hT₁.2.2.2 m₁ hm₁; simp_all +decide [ Finset.disjoint_left ] ;
    exact Classical.not_not.1 fun h => this h <| by rcases Finset.one_lt_card.1 hm₁_inter with ⟨ x, hx, y, hy, hxy ⟩ ; exact ⟨ Sym2.mk ( x, y ), by aesop ⟩ ;
  have hT₂_inter_A : m₂ = A := by
    have := hT₂.2.2.2 m₂ hm₂;
    contrapose! this;
    exact ⟨ this, by obtain ⟨ x, hx ⟩ := Finset.card_pos.mp ( by linarith ) ; exact ⟨ Sym2.mk ( x, x ), by aesop ⟩ ⟩;
  have hT₁_inter_T₂ : (T₁ ∩ T₂).card ≥ 1 := by
    have hT₁_inter_T₂ : (T₁ ∩ A).card + (T₂ ∩ A).card ≤ A.card + (T₁ ∩ T₂).card := by
      rw [ ← Finset.card_union_add_card_inter ];
      exact add_le_add ( Finset.card_mono <| by aesop_cat ) ( Finset.card_mono <| by aesop_cat );
    have := hM.1.1 hA; simp_all +decide ;
    exact Finset.card_pos.mp ( by linarith [ this.2 ] );
  obtain ⟨ x, hx ⟩ := Finset.card_pos.mp hT₁_inter_T₂; specialize h_no_common ( Sym2.mk ( x, x ) ) ; simp_all +decide ;

end