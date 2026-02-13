/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8cabb17e-0c7f-4784-b72e-7555b691e6de

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem apex_selection_covers_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (sel : ApexSelection V)
    (hM_pack : isMaxPacking G sel.M) (hM_card : sel.M.card = 4)
    -- The key hypothesis: for each bridge, some neighbor has apex in the bridge
    (h_apex_in_bridge : ∀ B, isBridgeTriangle G sel.M B →
                        ∃ X ∈ sel.M, sharesEdgeWith B X ∧ sel.apex X ∈ B) :
    ∀ B, isBridgeTriangle G sel.M B → ∃ e ∈ sel.cover, e ∈ B.sym2
-/

/-
  slot538: APEX COVERAGE CORE LEMMA

  The fundamental lemma that makes the apex-based cover work:
  If we select 2 apex-edges from each M-element, we cover:
  1. All M-elements themselves
  2. All externals (by two_edges_cover_X_and_externals)
  3. All bridges (because at least one neighbor has apex ON shared edge)

  This file focuses on item 3 - the bridge coverage.
-/

import Mathlib


set_option maxHeartbeats 600000

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

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
  ∃ u v, u ≠ v ∧ u ∈ t ∧ v ∈ t ∧ u ∈ S ∧ v ∈ S

def isBridgeTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧
  ∃ X Y : Finset V, X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧ sharesEdgeWith t X ∧ sharesEdgeWith t Y

-- ══════════════════════════════════════════════════════════════════════════════
-- APEX SELECTION STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

/-- An apex selection assigns to each M-element a vertex (the apex)
    and two edges containing that apex -/
structure ApexSelection (V : Type*) [DecidableEq V] where
  M : Finset (Finset V)
  apex : Finset V → V
  edge1 : Finset V → Sym2 V
  edge2 : Finset V → Sym2 V
  h_apex_in : ∀ X ∈ M, apex X ∈ X
  h_edge1_apex : ∀ X ∈ M, apex X ∈ edge1 X
  h_edge2_apex : ∀ X ∈ M, apex X ∈ edge2 X
  h_edge1_in_X : ∀ X ∈ M, ∀ v ∈ edge1 X, v ∈ X
  h_edge2_in_X : ∀ X ∈ M, ∀ v ∈ edge2 X, v ∈ X
  h_edges_distinct : ∀ X ∈ M, edge1 X ≠ edge2 X

/-- The cover induced by an apex selection -/
def ApexSelection.cover (sel : ApexSelection V) : Finset (Sym2 V) :=
  (sel.M.biUnion fun X => {sel.edge1 X, sel.edge2 X})

/-- The cover has at most 2|M| edges -/
lemma ApexSelection.cover_card_le (sel : ApexSelection V) :
    sel.cover.card ≤ 2 * sel.M.card := by
  unfold ApexSelection.cover
  calc sel.cover.card
      = (sel.M.biUnion fun X => {sel.edge1 X, sel.edge2 X}).card := rfl
    _ ≤ sel.M.card * 2 := Finset.card_biUnion_le_card_mul _ _ _ (fun X _ => by simp)
    _ = 2 * sel.M.card := by ring

-- ══════════════════════════════════════════════════════════════════════════════
-- BRIDGE COVERAGE THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- Key insight: If B shares edge with X, and apex of X is ON that shared edge,
    then one of the apex-edges covers B -/
lemma apex_on_shared_edge_covers_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (X B : Finset V)
    (hX_tri : X ∈ G.cliqueFinset 3) (hB_tri : B ∈ G.cliqueFinset 3)
    (h_share : sharesEdgeWith B X)
    (apex : V) (h_apex_in_X : apex ∈ X) (h_apex_in_B : apex ∈ B)
    (u v : V) (h_X_eq : X = {apex, u, v}) (h_distinct : apex ≠ u ∧ apex ≠ v ∧ u ≠ v)
    (edge1 edge2 : Sym2 V) (h_e1 : edge1 = s(apex, u)) (h_e2 : edge2 = s(apex, v)) :
    edge1 ∈ B.sym2 ∨ edge2 ∈ B.sym2 := by
  -- Since B shares edge with X and apex ∈ B, the shared edge contains apex
  -- B is a triangle containing apex, so it has form {apex, w, z} for some w, z
  -- The shared edge with X must be one of: {apex, u}, {apex, v}, or {u, v}
  -- Since apex ∈ B, if shared edge is {u,v} then both u,v ∈ B
  -- But also shared edge ⊆ B, so if {apex, u} ⊆ B, then u ∈ B
  -- We show one of s(apex, u) or s(apex, v) is in B.sym2

  -- From h_share: ∃ p q, p ≠ q ∧ p ∈ B ∧ q ∈ B ∧ p ∈ X ∧ q ∈ X
  obtain ⟨p, q, hpq, hp_B, hq_B, hp_X, hq_X⟩ := h_share

  -- p, q ∈ X = {apex, u, v}
  rw [h_X_eq] at hp_X hq_X
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp_X hq_X

  -- Case analysis on p and q
  rcases hp_X with rfl | rfl | rfl <;> rcases hq_X with rfl | rfl | rfl
  all_goals try exact absurd rfl hpq  -- p = q case

  -- p = apex, q = u: apex and u both in B, so s(apex, u) ∈ B.sym2
  · left
    rw [h_e1, Finset.mem_sym2_iff]
    intro x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> assumption

  -- p = apex, q = v: s(apex, v) ∈ B.sym2
  · right
    rw [h_e2, Finset.mem_sym2_iff]
    intro x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> assumption

  -- p = u, q = apex: s(apex, u) ∈ B.sym2
  · left
    rw [h_e1, Finset.mem_sym2_iff]
    intro x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> assumption

  -- p = u, q = v: both u, v ∈ B but apex ∈ B too
  -- Actually apex might not be on shared edge here...
  -- But we assumed h_apex_in_B, so apex ∈ B
  -- Need to check if this forces coverage
  · -- We have u, v ∈ B and apex ∈ B
    -- B has 3 vertices, so B = {apex, u, v} or B contains some other vertex
    -- If B = {apex, u, v} then both apex-edges are in B
    -- Otherwise B = {u, v, w} for some w, but then apex ∈ B means apex = u or v or w
    -- We have apex ∈ B and apex ∈ {apex, u, v} with apex ≠ u, apex ≠ v
    -- So if B = {u, v, w}, then apex = w
    -- In this case, s(apex, u) = s(w, u) is in B.sym2
    left
    rw [h_e1, Finset.mem_sym2_iff]
    intro x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact h_apex_in_B
    · exact hp_B

  -- p = v, q = apex: s(apex, v) ∈ B.sym2
  · right
    rw [h_e2, Finset.mem_sym2_iff]
    intro x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> assumption

  -- p = v, q = u: same as p = u, q = v
  · left
    rw [h_e1, Finset.mem_sym2_iff]
    intro x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact h_apex_in_B
    · exact hq_B

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Apex selection covers all bridges
-- ══════════════════════════════════════════════════════════════════════════════

/- If for each bridge B, at least one neighbor has apex in B,
    then the apex selection covers all bridges -/
noncomputable section AristotleLemmas

/-
If a triangle X in the selection shares an edge with a bridge B, and the apex of X is in B, then one of the edges of X in the selection covers an edge of B.
-/
lemma ApexSelection.exists_cover_edge_of_shared_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (sel : ApexSelection V) (B X : Finset V)
    (hX : X ∈ sel.M) (hX_tri : X ∈ G.cliqueFinset 3) (hB_tri : B ∈ G.cliqueFinset 3)
    (h_share : sharesEdgeWith B X) (h_apex : sel.apex X ∈ B) :
    ∃ e ∈ sel.cover, e ∈ B.sym2 := by
      -- Since $X$ is a triangle, it has exactly three vertices. Let's denote them as $a$, $b$, and $c$.
      obtain ⟨a, b, c, ha, hb, hc, hX_eq⟩ : ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ X = {a, b, c} := by
        have := Finset.card_eq_three.mp ( Finset.mem_filter.mp hX_tri |>.2.2 ) ; aesop;
      -- Since $sel.edge1 X$ and $sel.edge2 X$ are distinct edges in $X$ incident to $sel.apex X$, and $sel.apex X \in B$, one of these edges must be in $B$.
      have h_edge_in_B : sel.edge1 X ∈ B.sym2 ∨ sel.edge2 X ∈ B.sym2 := by
        have h_edge_in_B : sel.edge1 X ∈ ({s(sel.apex X, a), s(sel.apex X, b), s(sel.apex X, c)} : Finset (Sym2 V)) ∧ sel.edge2 X ∈ ({s(sel.apex X, a), s(sel.apex X, b), s(sel.apex X, c)} : Finset (Sym2 V)) := by
          have h_edge_in_B : ∀ e : Sym2 V, e ∈ X.sym2 → sel.apex X ∈ e → e ∈ ({s(sel.apex X, a), s(sel.apex X, b), s(sel.apex X, c)} : Finset (Sym2 V)) := by
            simp +decide [ Sym2.forall, hX_eq ];
            grind;
          have := sel.h_edge1_apex X hX; have := sel.h_edge2_apex X hX; have := sel.h_edge1_in_X X hX; have := sel.h_edge2_in_X X hX; simp_all +decide [ Sym2.mem_iff ] ;
        obtain ⟨ u, v, huv, hu, hv, hu', hv' ⟩ := h_share;
        simp_all +decide [ Finset.ext_iff ];
        rcases h_edge_in_B with ⟨ h | h | h, j | j | j ⟩ <;> simp_all +decide [ Sym2.eq ];
        all_goals have := sel.h_edges_distinct _ hX; simp_all +decide [ Sym2.eq ] ;
        all_goals rw [ show X = { a, b, c } by ext; aesop ] at h j; simp_all +decide [ Sym2.eq ] ;
        all_goals rw [ show X = { a, b, c } by ext; aesop ] ; aesop;
      exact h_edge_in_B.elim ( fun h => ⟨ _, Finset.mem_biUnion.mpr ⟨ X, hX, Finset.mem_insert_self _ _ ⟩, h ⟩ ) fun h => ⟨ _, Finset.mem_biUnion.mpr ⟨ X, hX, Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ⟩, h ⟩

end AristotleLemmas

theorem apex_selection_covers_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (sel : ApexSelection V)
    (hM_pack : isMaxPacking G sel.M) (hM_card : sel.M.card = 4)
    -- The key hypothesis: for each bridge, some neighbor has apex in the bridge
    (h_apex_in_bridge : ∀ B, isBridgeTriangle G sel.M B →
                        ∃ X ∈ sel.M, sharesEdgeWith B X ∧ sel.apex X ∈ B) :
    ∀ B, isBridgeTriangle G sel.M B → ∃ e ∈ sel.cover, e ∈ B.sym2 := by
  intro B hB
  obtain ⟨X, hX, h_share, h_apex_in_B⟩ := h_apex_in_bridge B hB
  -- X shares edge with B and apex X ∈ B
  -- By apex_on_shared_edge_covers_bridge, one of the apex-edges covers B
  apply ApexSelection.exists_cover_edge_of_shared_apex G sel B X hX (by
  exact hM_pack.1.1 hX) (by
  exact hB.1) h_share h_apex_in_B

end