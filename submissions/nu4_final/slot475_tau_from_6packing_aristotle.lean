/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 46c3e7b0-ec7a-4543-9a51-747efd9b1757

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot475_tau_from_6packing.lean

  KEY LEMMA: 6-packing constraint → τ(S_e) ≤ 2

  This file ASSUMES slot412's proven theorem (not_all_three_edge_types)
  and focuses on the NEW connection: "at most 2 edge-types" → "2 edges cover S_e"

  PROOF STRATEGY:
  1. slot412 proves: At most 2 of 3 edges of any packing element can have externals
  2. This file proves: Therefore, picking one edge per active type covers S_e
  3. 4 elements × 2 edges = 8 edges total

  TIER: 2 (uses proven 6-packing as axiom, focuses on cover construction)
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry149665', 'not_all_three_edge_types']-/
set_option maxHeartbeats 400000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (standard)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

/-- Triangles sharing edge with e -/
def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

/-- S_e: Triangles sharing edge with e but edge-disjoint from OTHER M-elements -/
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

/-- S_e elements using specific edge {a,b} of e = {a,b,c} -/
def S_e_edge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (a b c : V) : Finset (Finset V) :=
  (S_e G M {a, b, c}).filter (fun T => a ∈ T ∧ b ∈ T ∧ c ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOM: 6-PACKING CONSTRAINT (proven in slot412)
-- ══════════════════════════════════════════════════════════════════════════════

/--
AXIOM: slot412's proven theorem.
At most 2 of 3 edge-types can have externals when ν = 4.
Proof: If all 3 exist, get 6-packing contradicting ν = 4.
-/
axiom not_all_three_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ {a, b, c}) (hC_ne : C ≠ {a, b, c}) (hD_ne : D ≠ {a, b, c})
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hB_tri : B ∈ G.cliqueFinset 3) (hC_tri : C ∈ G.cliqueFinset 3) (hD_tri : D ∈ G.cliqueFinset 3) :
    ¬((S_e_edge G M a b c).Nonempty ∧
      (S_e_edge G M b c a).Nonempty ∧
      (S_e_edge G M a c b).Nonempty)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Fintype V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
overloaded, errors 
  failed to synthesize
    Insert V (Finset V)
  
  Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
  
  87:31 `a` is not a field of structure `Finset`
failed to synthesize
  Fintype V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Fintype V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Fintype V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Fintype (↑G.edgeSet : Type ?u.18479)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Function expected at
  isTrianglePacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isTrianglePacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  S_e
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Invalid field notation: Type of
  t
is not known; cannot resolve field `sym2`
Unknown identifier `not_all_three_edge_types`
unsolved goals
V : Type u_1
x✝¹ : Sort u_2
isTrianglePacking : x✝¹
x✝ : Sort u_3
S_e : x✝
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
hM : sorry
hNu4 : ∀ (S : Finset (Finset V)) (a : sorry), S.card ≤ 4
e : Finset V
he : e ∈ M
he_tri : e ∈ sorry
a b c : V
he_abc : e = sorry
hab : a ≠ b
hbc : b ≠ c
hac : a ≠ c
B C D : Finset V
hB : B ∈ M
hC : C ∈ M
hD : D ∈ M
hB_ne : B ≠ e
hC_ne : C ≠ e
hD_ne : D ≠ e
hBC : B ≠ C
hBD : B ≠ D
hCD : C ≠ D
hB_tri : B ∈ sorry
hC_tri : C ∈ sorry
hD_tri : D ∈ sorry
⊢ ∃ (E' : Finset (Sym2 V)), E'.card ≤ 2 ∧ E' ⊆ sorry ∧ ∀ t ∈ ?m.89, ∃ edge ∈ E', edge ∈ ?m.98-/
-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: 2 edges cover S_e
-- ══════════════════════════════════════════════════════════════════════════════

/--
If at most 2 edge-types have externals, then S_e can be covered by 2 edges.

PROOF SKETCH:
- Let e = {a,b,c}
- By 6-packing constraint, WLOG assume {a,c} has no externals
- Choose cover: {s(a,b), s(b,c)} (the two active edge-types)
- For any t ∈ S_e:
  - If t = e: s(a,b) ∈ e.sym2 ✓
  - If t uses edge {a,b}: a,b ∈ t so s(a,b) ∈ t.sym2 ✓
  - If t uses edge {b,c}: b,c ∈ t so s(b,c) ∈ t.sym2 ✓
  - If t uses edge {a,c}: impossible by constraint ✓
-/
theorem two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he_tri : e ∈ G.cliqueFinset 3)
    (a b c : V) (he_abc : e = {a, b, c}) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ e) (hC_ne : C ≠ e) (hD_ne : D ≠ e)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hB_tri : B ∈ G.cliqueFinset 3) (hC_tri : C ∈ G.cliqueFinset 3) (hD_tri : D ∈ G.cliqueFinset 3) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ G.edgeFinset ∧
      ∀ t ∈ S_e G M e, ∃ edge ∈ E', edge ∈ t.sym2 := by
  -- By 6-packing constraint, at least one edge-type is empty
  have h_constraint := not_all_three_edge_types G M hM hNu4 a b c
    (he_abc ▸ he) hab hbc hac B C D hB hC hD
    (he_abc ▸ hB_ne) (he_abc ▸ hC_ne) (he_abc ▸ hD_ne)
    hBC hBD hCD hB_tri hC_tri hD_tri
  push_neg at h_constraint
  -- Case analysis: which edge-type is empty
  -- Get that the edges of e are in G.edgeFinset
  have h_clique := SimpleGraph.mem_cliqueFinset_iff.mp he_tri
  have hab_edge : s(a, b) ∈ G.edgeFinset := by
    rw [he_abc] at h_clique
    exact h_clique.2 (by simp [hab]) (by simp) (by simp)
  have hbc_edge : s(b, c) ∈ G.edgeFinset := by
    rw [he_abc] at h_clique
    exact h_clique.2 (by simp [hbc]) (by simp) (by simp)
  have hac_edge : s(a, c) ∈ G.edgeFinset := by
    rw [he_abc] at h_clique
    exact h_clique.2 (by simp [hac]) (by simp) (by simp)
  -- Choose 2 edges based on which type is empty
  -- For now, use {s(a,b), s(b,c)} and prove it covers all of S_e
  use {s(a, b), s(b, c)}
  refine ⟨?_, ?_, ?_⟩
  · -- Card ≤ 2
    simp only [card_insert_of_not_mem, card_singleton]
    by_cases h : s(a, b) = s(b, c)
    · simp [h]
    · simp [h]
  · -- Subset of G.edgeFinset
    intro e' he'
    simp only [mem_insert, mem_singleton] at he'
    rcases he' with rfl | rfl
    · exact hab_edge
    · exact hbc_edge
  · -- Covers all of S_e
    intro t ht
    simp only [S_e, trianglesSharingEdge, mem_filter] at ht
    -- t shares ≥2 vertices with e = {a,b,c}
    have h_share := ht.1.2
    rw [he_abc] at h_share
    -- t ∩ {a,b,c} has card ≥ 2
    -- t has card 3 (it's a triangle)
    have ht_tri := ht.1.1
    have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht_tri).card_eq
    -- Since t shares ≥2 vertices with {a,b,c}, at least one of {a,b}, {b,c}, {a,c} is in t
    -- Need to show s(a,b) or s(b,c) is in t.sym2
    sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Fintype V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Fintype (↑G.edgeSet : Type ?u.15488)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Fintype V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Function expected at
  isTrianglePacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isTrianglePacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
-- Aristotle: case analysis on which 2 vertices are shared

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: τ ≤ 8 when ν = 4
-- ══════════════════════════════════════════════════════════════════════════════

/--
τ ≤ 8 for graphs with ν = 4.
Proof: Union of 2-edge covers for each of 4 packing elements.
-/
theorem tau_le_8_nu_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMax : ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2) :
    ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 8 ∧
      ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2 := by
  /-
  PROOF SKETCH:
  1. For each m ∈ M, by two_edges_cover_Se, get E_m with |E_m| ≤ 2
  2. Let E' = ⋃_{m ∈ M} E_m
  3. |E'| ≤ 4 × 2 = 8
  4. For any triangle t:
     - By maximality (hMax), t shares ≥2 vertices with some m ∈ M
     - So t ∈ S_e for some e ∈ M (or t = e)
     - E_m covers t
  -/
  sorry

-- Aristotle: construct union and verify coverage

end