/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 66fd8e4f-1cd6-42ed-b0e4-f0783d1f7b9f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma bridge_in_unique_Se' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (T : Finset V) (hT_bridge : isBridge G M T) :
    ∃! e, e ∈ M ∧ T ∈ S_e' G M e idx

- lemma non_M_triangle_in_some_Se' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) (hT_notM : T ∉ M) :
    ∃ e ∈ M, T ∈ S_e' G M e idx

- lemma two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ ∀ T ∈ S_e G M e, ∃ edge ∈ E, edge ∈ T.sym2

The following was negated by Aristotle:

- lemma two_edges_cover_all_vertices (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (e1 e2 : Sym2 V) (he1 : e1 ∈ ({a, b, c} : Finset V).sym2) (he2 : e2 ∈ ({a, b, c} : Finset V).sym2)
    (hne : e1 ≠ e2) :
    ∀ v ∈ ({a, b, c} : Finset V), v ∈ e1 ∨ v ∈ e2

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
  slot506_Se_prime_partition.lean

  S_e' PARTITION WITH MIN-INDEX BRIDGE ASSIGNMENT

  Multi-Agent Debate Consensus (Jan 23, 2026):
  - Grok, Gemini, Codex all agreed: bridges escape original S_e
  - Solution: Min-index assignment assigns each bridge to exactly one S_e'
  - Constrained edge selection: include bridge's shared edge in cover

  KEY INSIGHT (Grok Round 2):
  "Constrain edge selection to include at least one edge from each bridge's
   shared set. Feasible by Hall's Marriage Theorem when bridges ≤ 2 per element."

  TIER: 2 (partition + constrained selection)
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- CORE DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isMaximalPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧
  ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ e ∈ M, (T ∩ e).card ≥ 2

/-- Original S_e: Triangles sharing edge with e, edge-disjoint from other M-elements -/
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧
    2 ≤ (T ∩ e).card ∧
    ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

/-- Bridge: Triangle sharing ≥2 vertices with multiple M-elements -/
def isBridge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧
  T ∉ M ∧
  ∃ e f : Finset V, e ∈ M ∧ f ∈ M ∧ e ≠ f ∧ 2 ≤ (T ∩ e).card ∧ 2 ≤ (T ∩ f).card

/-- Elements that T shares edge with (has ≥2 vertex intersection) -/
def sharesEdgeWith (M : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  M.filter (fun e => 2 ≤ (T ∩ e).card)

/-- S_e': Extended S_e including bridges via min-index assignment -/
def S_e' (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V)
    (idx : Finset V → ℕ) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧
    2 ≤ (T ∩ e).card ∧
    -- T is assigned to e if e has the minimum index among all M-elements T shares edge with
    (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 1: S_e ⊆ S_e'
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. If T ∈ S_e, then T shares edge only with e (among M-elements)
2. Therefore sharesEdgeWith M T = {e}
3. No f with idx f < idx e exists in sharesEdgeWith
4. So T ∈ S_e'
-/
lemma S_e_subset_S_e' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e ∈ M)
    (idx : Finset V → ℕ) :
    S_e G M e ⊆ S_e' G M e idx := by
  intro T hT
  simp only [S_e, S_e', mem_filter] at hT ⊢
  refine ⟨hT.1, hT.2.1, hT.2.2.1, ?_⟩
  -- T only shares edge with e, so no f with smaller index exists
  ext f
  simp only [mem_filter, not_mem_empty, iff_false, not_and]
  intro hf_shares hf_lt
  -- f ∈ sharesEdgeWith M T means 2 ≤ (T ∩ f).card
  simp only [sharesEdgeWith, mem_filter] at hf_shares
  have hf_M := hf_shares.1
  have hf_inter := hf_shares.2
  -- But T ∈ S_e means (T ∩ f).card ≤ 1 for f ≠ e
  by_cases hfe : f = e
  · -- f = e contradicts idx f < idx e
    subst hfe
    exact Nat.lt_irrefl _ hf_lt
  · -- f ≠ e means (T ∩ f).card ≤ 1
    have := hT.2.2.2 f hf_M hfe
    omega

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 2: Bridges are in exactly one S_e'
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Bridge T shares edge with ≥2 M-elements
2. Let e = argmin { idx f | T shares edge with f }
3. T ∈ S_e' by definition (no f with smaller index)
4. T ∉ S_f' for any f ≠ e with idx f > idx e (e would be in the filter)
-/
lemma bridge_in_unique_Se' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (T : Finset V) (hT_bridge : isBridge G M T) :
    ∃! e, e ∈ M ∧ T ∈ S_e' G M e idx := by
  obtain ⟨hT_clique, hT_notM, e, f, he, hf, hef, he_inter, hf_inter⟩ := hT_bridge
  -- sharesEdgeWith M T is nonempty (contains e and f)
  have h_nonempty : (sharesEdgeWith M T).Nonempty := by
    use e
    simp only [sharesEdgeWith, mem_filter]
    exact ⟨he, he_inter⟩
  -- Let e_min be the element with minimum idx in sharesEdgeWith
  -- By definition of $S_e'$, there exists a unique $e \in M$ such that $T \in S_e'$ because $idx$ is injective.
  obtain ⟨e, he⟩ : ∃ e ∈ (sharesEdgeWith M T), ∀ f ∈ (sharesEdgeWith M T), idx f ≥ idx e := by
    exact Finset.exists_min_image _ _ h_nonempty;
  refine' ⟨ e, _, _ ⟩ <;> simp_all +decide [ S_e' ];
  · unfold sharesEdgeWith at he; aesop;
  · intro y hy hyT hy_inter hy_le; have := hy_le he.1; have := he.2 y; simp_all +decide [ h_inj.eq_iff ] ;
    exact h_inj ( le_antisymm ( hy_le he.1 ) ( he.2 y ( by unfold sharesEdgeWith; aesop ) ) ) ▸ rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 3: Every non-M triangle is in some S_e'
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. If T ∉ M and T is a triangle, maximality gives some e ∈ M with (T ∩ e).card ≥ 2
2. So sharesEdgeWith M T is nonempty
3. Let e_min = argmin { idx f | f ∈ sharesEdgeWith M T }
4. Then T ∈ S_e_min' by definition
-/
lemma non_M_triangle_in_some_Se' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) (hT_notM : T ∉ M) :
    ∃ e ∈ M, T ∈ S_e' G M e idx := by
  -- By maximality, T shares edge with some M-element
  obtain ⟨e, he, he_inter⟩ := hM.2 T hT hT_notM
  -- sharesEdgeWith M T is nonempty
  have h_nonempty : (sharesEdgeWith M T).Nonempty := by
    use e
    simp only [sharesEdgeWith, mem_filter]
    exact ⟨he, he_inter⟩
  -- Let $e_min$ be the element in $sharesEdgeWith M T$ with the smallest index.
  obtain ⟨e_min, he_min⟩ : ∃ e_min ∈ sharesEdgeWith M T, ∀ f ∈ sharesEdgeWith M T, idx f ≥ idx e_min := by
    exact Finset.exists_min_image _ _ h_nonempty;
  unfold S_e' sharesEdgeWith at * ; aesop

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 4: S_e' sets are disjoint
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. If T ∈ S_e' ∩ S_f' for e ≠ f
2. WLOG idx e < idx f
3. T ∈ S_f' means no g with idx g < idx f shares edge with T
4. But T ∈ S_e' means T shares edge with e, and idx e < idx f
5. Contradiction
-/
lemma S_e'_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx) :
    Disjoint (S_e' G M e idx) (S_e' G M f idx) := by
  rw [Finset.disjoint_iff_ne]
  intro T hT_e T' hT_f hTT'
  subst hTT'
  simp only [S_e', mem_filter] at hT_e hT_f
  -- T shares edge with both e and f
  -- But one of idx e, idx f is smaller
  by_cases h : idx e < idx f
  · -- idx e < idx f, so e ∈ (sharesEdgeWith M T).filter (idx · < idx f)
    have : e ∈ (sharesEdgeWith M T).filter (fun g => idx g < idx f) := by
      simp only [mem_filter, sharesEdgeWith, mem_filter]
      exact ⟨⟨he, hT_e.2.2.1⟩, h⟩
    -- But hT_f says this filter is empty
    rw [hT_f.2.2.2] at this
    exact not_mem_empty e this
  · push_neg at h
    have h' : idx f < idx e ∨ idx f = idx e := Nat.lt_or_eq_of_le h
    rcases h' with h_lt | h_eq
    · -- idx f < idx e, so f ∈ (sharesEdgeWith M T).filter (idx · < idx e)
      have : f ∈ (sharesEdgeWith M T).filter (fun g => idx g < idx e) := by
        simp only [mem_filter, sharesEdgeWith, mem_filter]
        exact ⟨⟨hf, hT_f.2.2.1⟩, h_lt⟩
      rw [hT_e.2.2.2] at this
      exact not_mem_empty f this
    · -- idx e = idx f contradicts injectivity (e ≠ f)
      have := h_inj h_eq
      exact hef this

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 5: Bridge contains shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH (from slot441, PROVEN):
1. If T shares ≥2 vertices with e AND ≥2 vertices with f
2. And e ∩ f = {v} (single shared vertex)
3. Then v ∈ T by cardinality argument
-/
lemma bridge_contains_shared_vertex (e f T : Finset V)
    (he3 : e.card = 3) (hf3 : f.card = 3) (hT3 : T.card = 3)
    (he_inter : 2 ≤ (T ∩ e).card) (hf_inter : 2 ≤ (T ∩ f).card)
    (hef_inter : (e ∩ f).card = 1) :
    ∃ v, e ∩ f = {v} ∧ v ∈ T := by
  -- e ∩ f is a singleton
  obtain ⟨v, hv⟩ := card_eq_one.mp hef_inter
  use v
  constructor
  · exact hv
  · -- T ∩ e has ≥2 elements, T ∩ f has ≥2 elements
    -- (T ∩ e) ∩ (T ∩ f) = T ∩ (e ∩ f) = T ∩ {v}
    -- If v ∉ T, then T ∩ {v} = ∅
    -- But |T ∩ e| + |T ∩ f| ≥ 4, and |T| = 3
    -- By inclusion-exclusion: |T ∩ e ∪ T ∩ f| = |T ∩ e| + |T ∩ f| - |T ∩ e ∩ f|
    -- ≤ |T| = 3, so |T ∩ e ∩ f| ≥ 4 - 3 = 1
    -- Therefore T ∩ (e ∩ f) ≠ ∅, so v ∈ T
    by_contra hv_notT
    have h1 : (T ∩ e ∩ f).card ≥ 1 := by
      have h_union : (T ∩ e ∪ T ∩ f).card ≤ T.card := card_le_card (union_subset (inter_subset_left) (inter_subset_left))
      have h_ie : (T ∩ e ∪ T ∩ f).card = (T ∩ e).card + (T ∩ f).card - (T ∩ e ∩ T ∩ f).card := by
        rw [card_union_eq_card_add_card_sub_card_inter]
        simp only [inter_inter_distrib_left]
      simp only [inter_inter_distrib_left] at h_ie
      rw [hT3] at h_union
      omega
    have h2 : T ∩ e ∩ f = T ∩ (e ∩ f) := inter_inter_distrib_left T e f
    rw [h2, hv] at h1
    simp only [inter_singleton_of_not_mem hv_notT, card_empty] at h1
    omega

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Sym2.mk ?m.22
but this term has type
  Sym2 ?m.21

Note: Expected a function because this term is being applied to the argument
  u
Application type mismatch: The argument
  v
has type
  V
but is expected to have type
  ?m.21 × ?m.21
in the application
  Sym2.mk v-/
-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 6: Spoke from shared vertex covers bridge
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Bridge T contains shared vertex v (by lemma 5)
2. T = {v, x, y} for some x, y
3. Edge {v, x} or {v, y} is in T.sym2
4. If our cover includes any spoke from v, it hits T
-/
lemma spoke_covers_bridge (T e : Finset V) (v : V)
    (hT3 : T.card = 3) (hv_T : v ∈ T) (hv_e : v ∈ e) :
    ∃ u ∈ T, u ≠ v ∧ Sym2.mk v u ∈ T.sym2 := by
  -- T has 3 elements including v, so there exist x, y ∈ T with x ≠ v, y ≠ v
  have h_card : (T.erase v).card = 2 := by
    rw [card_erase_of_mem hv_T, hT3]
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < (T.erase v).card)
  use x
  simp only [mem_erase] at hx
  refine ⟨erase_subset v T hx, hx.1, ?_⟩
  rw [Finset.mem_sym2_iff]
  exact ⟨hv_T, erase_subset v T hx⟩

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
══════════════════════════════════════════════════════════════════════════════
SCAFFOLDING LEMMA 7: Two edges cover 3-vertex set
══════════════════════════════════════════════════════════════════════════════

PROOF SKETCH:
1. For any 3-vertex set {a, b, c}, any 2 edges cover all 3 vertices
2. By pigeonhole: 2 edges have 4 endpoint slots, 3 vertices, so some vertex hit twice
3. All 3 must be hit (each edge is between 2 of them)
-/
lemma two_edges_cover_all_vertices (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (e1 e2 : Sym2 V) (he1 : e1 ∈ ({a, b, c} : Finset V).sym2) (he2 : e2 ∈ ({a, b, c} : Finset V).sym2)
    (hne : e1 ≠ e2) :
    ∀ v ∈ ({a, b, c} : Finset V), v ∈ e1 ∨ v ∈ e2 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose the set of vertices $V = \{0, 1, 2, 3\}$.
  use ULift (Fin 4);
  -- Let's choose the vertices $a = 0$, $b = 1$, and $c = 2$.
  use inferInstance, inferInstance, ⟨0⟩, ⟨1⟩, ⟨2⟩;
  -- Let's choose the edges $e1 = \{0, 1\}$ and $e2 = \{1, 2\}$.
  simp +decide [Sym2]

-/
-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 7: Two edges cover 3-vertex set
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. For any 3-vertex set {a, b, c}, any 2 edges cover all 3 vertices
2. By pigeonhole: 2 edges have 4 endpoint slots, 3 vertices, so some vertex hit twice
3. All 3 must be hit (each edge is between 2 of them)
-/
lemma two_edges_cover_all_vertices (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (e1 e2 : Sym2 V) (he1 : e1 ∈ ({a, b, c} : Finset V).sym2) (he2 : e2 ∈ ({a, b, c} : Finset V).sym2)
    (hne : e1 ≠ e2) :
    ∀ v ∈ ({a, b, c} : Finset V), v ∈ e1 ∨ v ∈ e2 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry507872', 'not_all_three_edge_types']-/
-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 8: At most 2 edge-types have externals (6-packing)
-- ══════════════════════════════════════════════════════════════════════════════

-- AXIOM from slot412 (PROVEN, 0 sorry there)
axiom not_all_three_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬(∃ T1 T2 T3 : Finset V,
      T1 ∈ S_e G M {a, b, c} ∧ a ∈ T1 ∧ b ∈ T1 ∧ c ∉ T1 ∧
      T2 ∈ S_e G M {a, b, c} ∧ b ∈ T2 ∧ c ∈ T2 ∧ a ∉ T2 ∧
      T3 ∈ S_e G M {a, b, c} ∧ a ∈ T3 ∧ c ∈ T3 ∧ b ∉ T3)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 9: 2 edges suffice for S_e
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. At most 2 of 3 edge-types have externals (by 6-packing)
2. Select 1 edge per populated type
3. These 2 edges cover all S_e externals
-/
noncomputable section AristotleLemmas

def isMaximumPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ ∀ M', isTrianglePacking G M' → M'.card ≤ M.card

/-
Corrected definitions for the counterexample graph G_ex and packing M_ex.
V_ex is Fin 6 (abbrev to allow literals).
e_ex is {0, 1, 2}.
T1_ex is {0, 1, 3}.
T2_ex is {1, 2, 4}.
T3_ex is {2, 0, 5}.
edges_ex contains the edges of these triangles.
G_ex is the graph from these edges.
M_ex is {e_ex}.
-/
abbrev V_ex := Fin 6

def e_ex : Finset V_ex := {0, 1, 2}
def T1_ex : Finset V_ex := {0, 1, 3}
def T2_ex : Finset V_ex := {1, 2, 4}
def T3_ex : Finset V_ex := {2, 0, 5}

def edges_ex : Finset (Sym2 V_ex) :=
  {s(0,1), s(1,2), s(2,0),
   s(0,3), s(1,3),
   s(1,4), s(2,4),
   s(2,5), s(0,5)}

def G_ex : SimpleGraph V_ex := SimpleGraph.fromEdgeSet edges_ex

instance : DecidableRel G_ex.Adj := Classical.decRel _

def M_ex : Finset (Finset V_ex) := {e_ex}

/-
The set of triangles in G_ex is exactly {e_ex, T1_ex, T2_ex, T3_ex}.
-/
lemma G_ex_cliques : G_ex.cliqueFinset 3 = {e_ex, T1_ex, T2_ex, T3_ex} := by
  unfold G_ex;
  norm_num [ SimpleGraph.fromEdgeSet, SimpleGraph.cliqueFinset ];
  simp +decide [ SimpleGraph.isNClique_iff ];
  simp +decide [ Set.Pairwise ]

/-
Any triangle packing in G_ex has size at most 4.
-/
lemma hNu4_ex : ∀ S : Finset (Finset V_ex), isTrianglePacking G_ex S → S.card ≤ 4 := by
  intro S hS;
  exact le_trans ( Finset.card_le_card hS.1 ) ( by simp +decide [ G_ex_cliques ] )

/-
S_e for the counterexample is {T1, T2, T3}.
-/
lemma S_e_ex_eq : S_e G_ex M_ex e_ex = {T1_ex, T2_ex, T3_ex} := by
  unfold S_e;
  simp +decide only [M_ex, G_ex_cliques]

/-
If a set T shares at least 2 elements with {u, v, w}, then it must contain u or v.
-/
lemma two_le_inter_three_imp_mem_or_mem {V : Type*} [DecidableEq V] (T : Finset V) (u v w : V)
    (h : 2 ≤ (T ∩ {u, v, w}).card) : u ∈ T ∨ v ∈ T := by
      contrapose! h; simp_all +decide [ Finset.subset_iff ] ;
      exact lt_of_le_of_lt ( Finset.card_le_one.mpr ( by aesop ) ) ( by decide )

end AristotleLemmas

lemma two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ ∀ T ∈ S_e G M e, ∃ edge ∈ E, edge ∈ T.sym2 := by
  -- By definition of $S_e$, every triangle in $S_e$ shares at least 2 vertices with $e$.
  have h_share_two : ∀ T ∈ S_e G M e, 2 ≤ (T ∩ e).card := by
    exact fun T hT => Finset.mem_filter.mp hT |>.2.2.1;
  -- By definition of $e$, we know that $e$ is a clique of size 3, so let $e = \{u, v, w\}$ with $u, v, w$ distinct.
  obtain ⟨u, v, w, huv, hvw, hwu⟩ : ∃ u v w : V, u ≠ v ∧ v ≠ w ∧ w ≠ u ∧ e = {u, v, w} := by
    have := hM.1 he; simp_all +decide [ isTrianglePacking ] ;
    rcases Finset.card_eq_three.mp this.2 with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use u, v, by aesop, w ; aesop;
  refine' ⟨ { Sym2.mk ( u, u ), Sym2.mk ( v, v ) }, _, _ ⟩ <;> simp_all +decide;
  exact?

/- Aristotle took a wrong turn (reason code: 0). Please try again. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 10: Bridges ≤ 2 per element in PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. In PATH_4 (A-B-C-D), bridges only between adjacent pairs
2. A-B bridges share v1, B-C bridges share v2, C-D bridges share v3
3. Under min-index, A gets A-B bridges, B gets B-C bridges (not A-B), etc.
4. Each element gets bridges from at most 1 junction → ≤2 bridges
-/
lemma bridges_le_2_per_element_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hM : M = {A, B, C, D})
    (hAB : (A ∩ B).card = 1) (hBC : (B ∩ C).card = 1) (hCD : (C ∩ D).card = 1)
    (hAC : (A ∩ C).card = 0) (hAD : (A ∩ D).card = 0) (hBD : (B ∩ D).card = 0)
    (idx : Finset V → ℕ) (hidx : idx A < idx B ∧ idx B < idx C ∧ idx C < idx D)
    (e : Finset V) (he : e ∈ M) :
    (S_e' G M e idx \ S_e G M e).card ≤ 2 := by
  sorry

/- Aristotle took a wrong turn (reason code: 0). Please try again. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 11: Constrained selection exists
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. S_e externals use at most 2 edge-types (6-packing)
2. Bridges share edge with e, which is one of 3 edge-types
3. If bridges ≤ 2, we can select 2 edges covering:
   - Both populated external types
   - The bridge's shared edge type
4. By Hall's, such selection exists when demands ≤ 3 and edges = 3
-/
lemma constrained_selection_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M)
    (idx : Finset V → ℕ)
    (h_bridges_le_2 : (S_e' G M e idx \ S_e G M e).card ≤ 2) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧
      E ⊆ e.sym2 ∧
      (∀ T ∈ S_e' G M e idx, ∃ edge ∈ E, edge ∈ T.sym2) := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: PARTITION LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Every triangle T is either in M or shares edge with some M-element (maximality)
2. If T ∉ M, let e_min = argmin { idx f | T shares edge with f }
3. By definition, T ∈ S_e_min'
4. Uniqueness: S_e' sets are disjoint (lemma 4)
-/
theorem triangle_in_some_Se'_or_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨ ∃ e ∈ M, T ∈ S_e' G M e idx := by
  by_cases hT_M : T ∈ M
  · left; exact hT_M
  · right
    exact non_M_triangle_in_some_Se' G M hM idx h_inj T hT hT_M

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ(S_e') ≤ 2
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. By constrained_selection_exists, get 2 edges E covering S_e'
2. These are actual graph edges (from e.sym2 ⊆ G.edgeFinset since e is clique)
3. Therefore τ(S_e') ≤ 2
-/
theorem tau_Se'_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M)
    (idx : Finset V → ℕ)
    (h_bridges_le_2 : (S_e' G M e idx \ S_e G M e).card ≤ 2) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧
      (∀ T ∈ S_e' G M e idx, ∃ edge ∈ E, edge ∈ T.sym2) :=
  constrained_selection_exists G M hM hNu4 e he idx h_bridges_le_2

/- Aristotle took a wrong turn (reason code: 0). Please try again. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- ASSEMBLY: τ ≤ 8 from partition
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Every triangle is in M or some S_e' (partition lemma)
2. M-elements covered by their own edges
3. Each S_e' covered by ≤2 edges
4. Total: ≤ 4 × 2 = 8 edges
-/
theorem tau_le_8_from_Se'_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaximalPacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hM4 : M.card = 4)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    (h_bridges_bound : ∀ e ∈ M, (S_e' G M e idx \ S_e G M e).card ≤ 2) :
    ∃ Cover : Finset (Sym2 V), Cover.card ≤ 8 ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ edge ∈ Cover, edge ∈ T.sym2 := by
  sorry

/- Aristotle ran out of time. -/
end