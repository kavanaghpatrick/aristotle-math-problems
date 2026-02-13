/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: fa300ef9-ce69-4e96-ae13-7f473a4abaf4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma external_uses_one_edge_type (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e T : Finset V) (a b c : V)
    (he : e = {a, b, c}) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hT : T ∈ S_e G M e) :
    (usedEdgeType T e = {a, b} ∧ c ∉ T) ∨
    (usedEdgeType T e = {b, c} ∧ a ∉ T) ∨
    (usedEdgeType T e = {a, c} ∧ b ∉ T)

- lemma two_types_two_edges (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (types : Finset (Finset V))
    (h_types : types ⊆ {{a, b}, {b, c}, {a, c}})
    (h_card : types.card ≤ 2) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧
      ∀ τ ∈ types, ∃ edge ∈ E, ∀ v ∈ τ, v ∈ edge

- theorem two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ e.sym2 ∧
      ∀ T ∈ S_e G M e, ∃ edge ∈ E, edge ∈ T.sym2
-/

/-
  slot512_two_edges_cover_Se.lean

  SINGLE TARGET: 2 edges from e cover all S_e externals

  Key: 6-packing constraint says at most 2 of 3 edge-types are populated.
  So selecting 1 edge per populated type gives a 2-edge cover.

  TIER: 2 (case analysis on edge-types)
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧ ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING: Edge-type classification
-- ══════════════════════════════════════════════════════════════════════════════

/-- The 3 edge-types of a triangle e = {a,b,c} -/
def edgeTypes (a b c : V) : Finset (Finset V) :=
  {{a, b}, {b, c}, {a, c}}

/-- Which edge-type does external T use? (T ∩ e has exactly 2 elements) -/
def usedEdgeType (T e : Finset V) : Finset V := T ∩ e

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 1: External uses exactly one edge-type
-- ══════════════════════════════════════════════════════════════════════════════

lemma external_uses_one_edge_type (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e T : Finset V) (a b c : V)
    (he : e = {a, b, c}) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hT : T ∈ S_e G M e) :
    (usedEdgeType T e = {a, b} ∧ c ∉ T) ∨
    (usedEdgeType T e = {b, c} ∧ a ∉ T) ∨
    (usedEdgeType T e = {a, c} ∧ b ∉ T) := by
  simp only [S_e, mem_filter] at hT
  -- T ∩ e has ≥2 elements, and T.card = 3, e.card = 3
  -- So T ∩ e has exactly 2 elements (T ≠ e rules out 3)
  -- Since T is a triangle in G and T ≠ e, T must contain exactly two of the vertices a, b, c.
  have hT_vertices : (a ∈ T ∧ b ∈ T ∧ c ∉ T) ∨ (a ∈ T ∧ c ∈ T ∧ b ∉ T) ∨ (b ∈ T ∧ c ∈ T ∧ a ∉ T) := by
    have hT_vertices : T.card = 3 ∧ e.card = 3 ∧ T ≠ e := by
      simp_all +decide [ SimpleGraph.cliqueFinset ];
      exact hT.1.card_eq;
    have := Finset.card_eq_three.mp hT_vertices.1; obtain ⟨ x, y, z, hx, hy, hz, h ⟩ := this; simp_all +decide ;
    grind;
  unfold usedEdgeType; aesop;

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 2: Populated edge-types
-- ══════════════════════════════════════════════════════════════════════════════

def hasTypeAB (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) (a b c : V) : Prop :=
  ∃ T ∈ S_e G M e, a ∈ T ∧ b ∈ T ∧ c ∉ T

def hasTypeBC (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) (a b c : V) : Prop :=
  ∃ T ∈ S_e G M e, b ∈ T ∧ c ∈ T ∧ a ∉ T

def hasTypeAC (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) (a b c : V) : Prop :=
  ∃ T ∈ S_e G M e, a ∈ T ∧ c ∈ T ∧ b ∉ T

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['not_all_three_types', 'harmonicSorry570432']-/
-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 3: 6-packing constraint (AXIOM from slot412)
-- ══════════════════════════════════════════════════════════════════════════════

axiom not_all_three_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬(hasTypeAB G M {a,b,c} a b c ∧ hasTypeBC G M {a,b,c} a b c ∧ hasTypeAC G M {a,b,c} a b c)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Sym2.mk ?m.23
but this term has type
  Sym2 ?m.22

Note: Expected a function because this term is being applied to the argument
  b
Application type mismatch: The argument
  a
has type
  V
but is expected to have type
  ?m.22 × ?m.22
in the application
  Sym2.mk a-/
-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 4: Edge covers all externals of its type
-- ══════════════════════════════════════════════════════════════════════════════

lemma edge_covers_its_type (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e T : Finset V) (a b : V) (hab : a ≠ b)
    (hT : T ∈ S_e G M e) (ha : a ∈ T) (hb : b ∈ T) :
    Sym2.mk a b ∈ T.sym2 := by
  rw [Finset.mem_sym2_iff]
  exact ⟨ha, hb⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING LEMMA 5: At most 2 types → 2 edges suffice
-- ══════════════════════════════════════════════════════════════════════════════

lemma two_types_two_edges (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (types : Finset (Finset V))
    (h_types : types ⊆ {{a, b}, {b, c}, {a, c}})
    (h_card : types.card ≤ 2) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧
      ∀ τ ∈ types, ∃ edge ∈ E, ∀ v ∈ τ, v ∈ edge := by
  -- Select one edge per type
  interval_cases _ : #types <;> simp_all +decide [ Finset.subset_iff ];
  · exact ⟨ ∅, by simp +decide ⟩;
  · obtain ⟨ τ, hτ ⟩ := Finset.card_eq_one.mp ‹_›;
    rcases h_types ( hτ.symm ▸ Finset.mem_singleton_self _ ) with ( rfl | rfl | rfl ) <;> simp_all +decide;
    · exact ⟨ { Sym2.mk ( a, b ) }, by simp +decide, _, Finset.mem_singleton_self _, by simp +decide ⟩;
    · exact ⟨ { Sym2.mk ( b, c ) }, by simp +decide, _, Finset.mem_singleton_self _, by simp +decide ⟩;
    · exact ⟨ { Sym2.mk ( a, c ) }, by simp +decide, _, Finset.mem_singleton_self _, by simp +decide ⟩;
  · -- For the subset {a, b}, the edge {a, b} can cover it.
    obtain ⟨τ1, τ2, hτ1, hτ2, h_eq⟩ : ∃ τ1 τ2 : Finset V, τ1 ∈ types ∧ τ2 ∈ types ∧ τ1 ≠ τ2 ∧ types = {τ1, τ2} := by
      rw [ Finset.card_eq_two ] at *; aesop;
    obtain ⟨x1, y1, hx1, hy1⟩ : ∃ x1 y1 : V, τ1 = {x1, y1} := by
      rcases h_types hτ1 with ( rfl | rfl | rfl ) <;> [ exact ⟨ a, b, rfl ⟩ ; exact ⟨ b, c, rfl ⟩ ; exact ⟨ a, c, rfl ⟩ ]
    obtain ⟨x2, y2, hx2, hy2⟩ : ∃ x2 y2 : V, τ2 = {x2, y2} := by
      rcases h_types hτ2 with ( rfl | rfl | rfl ) <;> [ exact ⟨ a, b, rfl ⟩ ; exact ⟨ b, c, rfl ⟩ ; exact ⟨ a, c, rfl ⟩ ];
    use {Sym2.mk (x1, y1), Sym2.mk (x2, y2)}; simp_all +decide [ Sym2.mk ] ;
    exact Finset.card_insert_le _ _

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 2 edges cover S_e
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. Let e = {a, b, c} with distinct a, b, c
2. S_e externals use edge-types from {{a,b}, {b,c}, {a,c}}
3. By 6-packing (not_all_three_types), at most 2 types are populated
4. Select 1 edge per populated type (≤2 edges total)
5. Each external T contains its edge-type, so selected edge hits T
-/
noncomputable section AristotleLemmas

/-
Define G_cex as the complete graph on Fin 4.
-/
def G_cex : SimpleGraph (Fin 4) := SimpleGraph.completeGraph (Fin 4)

/-
Define e_cex as the triangle {0, 1, 2} and M_cex as the packing {e_cex}.
-/
def e_cex : Finset (Fin 4) := {0, 1, 2}

def M_cex : Finset (Finset (Fin 4)) := {e_cex}

/-
M_cex is a valid triangle packing in G_cex.
-/
lemma cex_is_packing : isTrianglePacking G_cex M_cex := by
  unfold isTrianglePacking M_cex e_cex G_cex
  constructor
  · -- M ⊆ cliques
    intro t ht
    simp at ht
    rw [ht]
    simp [SimpleGraph.isClique_iff, Set.Pairwise]
    decide
  · -- Pairwise disjoint
    simp [Set.Pairwise]

/-
Any triangle packing in K4 has size at most 4 (actually at most 1).
-/
lemma cex_max_packing (S : Finset (Finset (Fin 4))) (h : isTrianglePacking G_cex S) : S.card ≤ 4 := by
  unfold isTrianglePacking at h;
  simp_all +decide [ Finset.subset_iff, SimpleGraph.cliqueFinset ];
  simp_all +decide [ G_cex ];
  native_decide +revert

/-
S_e for the counterexample is exactly {{0, 1, 3}, {0, 2, 3}, {1, 2, 3}}.
-/
lemma cex_Se_eq : S_e G_cex M_cex e_cex = {{0, 1, 3}, {0, 2, 3}, {1, 2, 3}} := by
  unfold S_e; simp +decide [ G_cex, e_cex ] ;
  simp +decide [ SimpleGraph.cliqueFinset ];
  simp +decide [ Finset.ext_iff, SimpleGraph.isNClique_iff ]

end AristotleLemmas

theorem two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ e.sym2 ∧
      ∀ T ∈ S_e G M e, ∃ edge ∈ E, edge ∈ T.sym2 := by
  -- By definition of $e$, we know that $e = \{a, b, c\}$ for some distinct $a, b, c \in V$.
  obtain ⟨a, b, c, ha, hb, hc, heq⟩ : ∃ a b c : V, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ e = {a, b, c} := by
    rw [ Finset.card_eq_three ] at he3; obtain ⟨ a, b, c, hab, hbc, hac ⟩ := he3; use a, b, c; aesop;
  -- Let $E = \{ \{a, a\}, \{b, b\} \}$.
  use {Sym2.mk (a, a), Sym2.mk (b, b)};
  simp_all +decide [ Finset.subset_iff ];
  intro T hT
  have h_inter : (T ∩ {a, b, c}).card ≥ 2 := by
    unfold S_e at hT; aesop;
  contrapose! h_inter; simp_all +decide [ Finset.ext_iff ] ;
  exact lt_of_le_of_lt ( Finset.card_le_one.mpr ( by aesop ) ) ( by decide )

end