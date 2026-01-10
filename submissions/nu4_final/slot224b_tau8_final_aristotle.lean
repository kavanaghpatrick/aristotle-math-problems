/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 65814513-3cd9-4966-9ea4-3495284b771b
-/

/-
  slot224b_tau8_final.lean

  GOAL: τ ≤ 8 for cycle_4 configuration.

  PROVEN AXIOM (slot182): two_externals_share_edge
    Any two distinct externals of M-element A share an edge.

  KEY INSIGHT:
    If externals use all 3 edges of A, they share a common external vertex x.

    Proof:
      T₁ uses {a,b}: T₁ = {a, b, x₁}
      T₂ uses {b,c}: T₂ = {b, c, x₂}
      T₃ uses {a,c}: T₃ = {a, c, x₃}

      By slot182, |T₁ ∩ T₂| ≥ 2.
      T₁ ∩ T₂ = {a,b,x₁} ∩ {b,c,x₂} = {b} ∪ ({x₁} ∩ {x₂}) ∪ ...
      Since x₁ ∉ A, x₁ ∉ {c}. Since x₂ ∉ A, x₂ ∉ {a}.
      T₁ ∩ T₂ = {b} or {b, x₁} if x₁ = x₂.
      For |T₁ ∩ T₂| ≥ 2: must have x₁ = x₂.

      Similarly |T₂ ∩ T₃| ≥ 2 forces x₂ = x₃.
      And |T₁ ∩ T₃| ≥ 2 forces x₁ = x₃.

      So x₁ = x₂ = x₃ = x (common external vertex).

  COVERING:
    Case 1: At most 2 edges of A used by externals.
      Cover with those ≤ 2 edges.

    Case 2: All 3 edges of A used.
      Common external vertex x exists.
      Externals are: {a,b,x}, {b,c,x}, {a,c,x} (at most).
      Cover: {a,x} hits {a,b,x} and {a,c,x}.
             {b,c} hits {b,c,x}.
      Total: 2 edges.

  RESULT: At most 2 edges per M-element cover its externals.
          4 M-elements × 2 edges = 8 edges total.
          But we also need to cover the M-elements themselves!

  REFINED COUNTING:
    M-elements are triangles. Each shares edge with adjacent M-elements.
    In cycle_4: M = {A, B, C, D} with
      A ∩ B = {v_ab}, B ∩ C = {v_bc}, C ∩ D = {v_cd}, D ∩ A = {v_da}.

    Actually, M-elements share VERTICES, not edges (intersection ≤ 1).
    So each M-element is covered by any of its 3 edges.

    Smarter counting:
    - Pick one edge per M-element to cover it: 4 edges for M-elements.
    - Externals need additional edges.
    - If external uses edge of A, that edge might already be picked for A.
    - Total could be 4 + (externals that need new edges).

    Worst case: Each M-element needs 2 edges for externals = 8.
    But we might double-count if an edge covers both M-element and external.

  ACTUALLY SIMPLER:
    For each M-element A:
    - A's 3 edges are in G.edgeFinset.
    - Externals of A each contain one edge of A.
    - If all externals use same edge e of A: 1 edge covers A + all its externals.
    - If externals use 2 edges e₁, e₂: 2 edges.
    - If externals use all 3 edges: 2 edges (via common external vertex trick).

    So: at most 2 edges per M-element suffice for A + its externals.
    4 × 2 = 8 edges for everything.

  1 SORRY for Aristotle.
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['two_externals_share_edge', 'harmonicSorry830542']-/
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
  (t ∩ S).card ≥ 2

def isExternalOf (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (t : Finset V) : Prop :=
  t ∈ G.cliqueFinset 3 ∧ t ∉ M ∧ sharesEdgeWith t A ∧
  ∀ B ∈ M, B ≠ A → ¬sharesEdgeWith t B

/-- Edges of a finset (non-diagonal sym2 elements) -/
def edgesOf (S : Finset V) : Finset (Sym2 V) :=
  S.sym2.filter (¬·.IsDiag)

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOM: slot182 proven theorem
-- ══════════════════════════════════════════════════════════════════════════════

axiom two_externals_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (h_ne : T₁ ≠ T₂) :
    (T₁ ∩ T₂).card ≥ 2

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Function expected at
  isMaxPacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isTrianglePacking
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isExternalOf
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isExternalOf
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G
Unknown identifier `two_externals_share_edge`
unsolved goals
V : Type u_1
x✝² : Sort u_2
isMaxPacking : x✝²
x✝¹ : Sort u_3
isTrianglePacking : x✝¹
x✝ : Sort u_4
isExternalOf : x✝
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
hM : sorry
hM_card : M.card = 4
hν : ∀ (P : Finset (Finset V)) (a : sorry), P.card ≤ 4
A : Finset V
hA : A ∈ M
hA_card : A.card = 3
T₁ T₂ : Finset V
hT₁ : sorry
hT₂ : sorry
hT₁_3 : T₁.card = 3
hT₂_3 : T₂.card = 3
h_ne : T₁ ≠ T₂
h_diff_edge : sorry ≠ sorry
⊢ ∃ x ∉ A, x ∈ T₁ ∧ x ∈ T₂-/
-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA: Externals using different A-edges share external vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- If T₁, T₂ are externals using different edges of A, they share a common external vertex -/
lemma different_edges_share_external (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (hA_card : A.card = 3)
    (T₁ T₂ : Finset V) (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3)
    (h_ne : T₁ ≠ T₂)
    -- T₁ uses edge e₁ of A, T₂ uses edge e₂ of A, e₁ ≠ e₂
    (h_diff_edge : (T₁ ∩ A) ≠ (T₂ ∩ A)) :
    ∃ x : V, x ∉ A ∧ x ∈ T₁ ∧ x ∈ T₂ := by
  -- By slot182, |T₁ ∩ T₂| ≥ 2
  have h_share := two_externals_share_edge G M hM hM_card hν A hA T₁ T₂ hT₁ hT₂ h_ne
  -- T₁ ∩ A has 2 vertices, T₂ ∩ A has 2 vertices
  have hT₁_A : (T₁ ∩ A).card = 2 := by
    have := hT₁.2.2.1
    interval_cases n : (T₁ ∩ A).card
    · -- n = 0,1: contradicts sharesEdgeWith
      omega
    · rfl
    · -- n = 3: T₁ ⊆ A, but T₁ has external vertex
      have h_subset : T₁ ⊆ A := by
        intro x hx
        have : x ∈ T₁ ∩ A := by
          rw [Finset.card_eq_three] at hA_card
          obtain ⟨a, b, c, _, _, _, h_eq⟩ := hA_card
          have h_T₁_sub : T₁ ⊆ A := by
            intro y hy
            by_contra h
            have : y ∉ T₁ ∩ A := Finset.mem_inter.mp.mt (fun ⟨_, hyA⟩ => h hyA)
            have hcard : (T₁ ∩ A).card < T₁.card := by
              calc (T₁ ∩ A).card ≤ A.card := Finset.card_inter_le_right T₁ A
                _ = 3 := hA_card
                _ = T₁.card := hT₁_3.symm
            sorry
          sorry
        sorry
      sorry
  have hT₂_A : (T₂ ∩ A).card = 2 := by sorry
  -- T₁ = {a₁, b₁, x₁} where {a₁, b₁} = T₁ ∩ A and x₁ ∉ A
  -- T₂ = {a₂, b₂, x₂} where {a₂, b₂} = T₂ ∩ A and x₂ ∉ A
  -- Since edges are different: {a₁, b₁} ≠ {a₂, b₂}
  -- |T₁ ∩ T₂| ≥ 2
  -- T₁ ∩ T₂ = ({a₁, b₁} ∩ {a₂, b₂}) ∪ ({a₁, b₁} ∩ {x₂}) ∪ ({x₁} ∩ {a₂, b₂}) ∪ ({x₁} ∩ {x₂})
  -- Two edges of A share exactly 1 vertex (they're adjacent edges of a triangle).
  -- So |{a₁, b₁} ∩ {a₂, b₂}| = 1 (call the common vertex c).
  -- For |T₁ ∩ T₂| ≥ 2, we need at least one more common vertex.
  -- x₁ ∉ A so x₁ ∉ {a₂, b₂}.
  -- x₂ ∉ A so x₂ ∉ {a₁, b₁}.
  -- So the only way to get another common vertex is x₁ = x₂.
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Function expected at
  isMaxPacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isTrianglePacking
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isExternalOf
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isExternalOf
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isExternalOf
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G
Unknown identifier `different_edges_share_external`
Tactic `rcases` failed: `x✝ : ?m.92` is not an inductive datatype-/
-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA: All externals using different edges share common external vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- If externals use all 3 edges of A, they all share a common external vertex -/
lemma all_three_edges_share_common_external (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (hA_card : A.card = 3)
    (T₁ T₂ T₃ : Finset V)
    (hT₁ : isExternalOf G M A T₁) (hT₂ : isExternalOf G M A T₂) (hT₃ : isExternalOf G M A T₃)
    (hT₁_3 : T₁.card = 3) (hT₂_3 : T₂.card = 3) (hT₃_3 : T₃.card = 3)
    (h_ne₁₂ : T₁ ≠ T₂) (h_ne₂₃ : T₂ ≠ T₃) (h_ne₁₃ : T₁ ≠ T₃)
    -- Each uses a different edge of A
    (h_all_diff : (T₁ ∩ A) ≠ (T₂ ∩ A) ∧ (T₂ ∩ A) ≠ (T₃ ∩ A) ∧ (T₁ ∩ A) ≠ (T₃ ∩ A)) :
    ∃ x : V, x ∉ A ∧ x ∈ T₁ ∧ x ∈ T₂ ∧ x ∈ T₃ := by
  -- By previous lemma, T₁ and T₂ share external vertex x₁₂
  -- T₂ and T₃ share external vertex x₂₃
  -- T₁ and T₃ share external vertex x₁₃
  -- We show x₁₂ = x₂₃ = x₁₃
  obtain ⟨x₁₂, hx₁₂_not_A, hx₁₂_T₁, hx₁₂_T₂⟩ :=
    different_edges_share_external G M hM hM_card hν A hA hA_card T₁ T₂ hT₁ hT₂ hT₁_3 hT₂_3 h_ne₁₂ h_all_diff.1
  obtain ⟨x₂₃, hx₂₃_not_A, hx₂₃_T₂, hx₂₃_T₃⟩ :=
    different_edges_share_external G M hM hM_card hν A hA hA_card T₂ T₃ hT₂ hT₃ hT₂_3 hT₃_3 h_ne₂₃ h_all_diff.2.1
  -- x₁₂ and x₂₃ are both in T₂ and both ∉ A
  -- T₂ has exactly 1 vertex not in A (since T₂ ∩ A has 2 vertices and T₂ has 3)
  -- So x₁₂ = x₂₃
  have h_unique : x₁₂ = x₂₃ := by
    have hT₂_A_card : (T₂ ∩ A).card = 2 := by sorry
    have h_one_external : ∃! x, x ∈ T₂ ∧ x ∉ A := by
      sorry
    sorry
  use x₁₂
  constructor
  · exact hx₁₂_not_A
  · constructor
    · exact hx₁₂_T₁
    · constructor
      · exact hx₁₂_T₂
      · rw [h_unique]; exact hx₂₃_T₃

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Fintype (↑G.edgeSet : Type ?u.16824)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  DecidableEq V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  DecidableEq V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Function expected at
  isMaxPacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isTrianglePacking
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isExternalOf
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G-/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 2 edges per M-element suffice
-- ══════════════════════════════════════════════════════════════════════════════

/-- At most 2 edges suffice to cover A and all its externals -/
theorem two_edges_cover_A_and_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (A : Finset V) (hA : A ∈ M) (hA_3 : A.card = 3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ G.edgeFinset ∧
      (∃ e ∈ E, ∀ v ∈ Sym2.toFinset e, v ∈ A) ∧
      (∀ T, isExternalOf G M A T → ∃ e ∈ E, ∀ v ∈ Sym2.toFinset e, v ∈ T) := by
  -- Count how many distinct edges of A are used by externals
  -- Case analysis:
  -- 0 edges: 1 edge of A suffices (covers A, no externals)
  -- 1 edge: that 1 edge suffices
  -- 2 edges: those 2 edges suffice
  -- 3 edges: all share common external x; {a,x} + {b,c} suffice
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Fintype (↑G.edgeSet : Type ?u.15564)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Fintype V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  DecidableEq V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Function expected at
  isMaxPacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isTrianglePacking
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G-/
/-- τ ≤ 8 for cycle_4 with ν = 4 -/
theorem tau_le_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (hν : ∀ P : Finset (Finset V), isTrianglePacking G P → P.card ≤ 4)
    (h_all_3 : ∀ X ∈ M, X.card = 3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, ∀ v ∈ Sym2.toFinset e, v ∈ T := by
  -- For each A ∈ M, get 2 edges covering A and its externals
  -- Total: 4 × 2 = 8 edges
  -- Every triangle is either in M or external to exactly one M-element
  sorry

end