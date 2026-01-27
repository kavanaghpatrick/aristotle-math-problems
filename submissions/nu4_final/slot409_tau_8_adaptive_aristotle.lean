/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 81bc617c-e267-4b95-848c-730d61b1e91e

The following was proved by Aristotle:

- lemma exists_two_edges_cover_all_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset V) (hE : E ∈ G.cliqueFinset 3)
    (a b c : V) (hE_eq : E = {a, b, c})
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h_not_all_three : ¬(hasExternalType G E a b ∧ hasExternalType G E b c ∧ hasExternalType G E a c)) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, T ∈ externalsUsingEdge G E a b → (e₁ = s(a, b) ∨ e₂ = s(a, b))) ∧
      (∀ T, T ∈ externalsUsingEdge G E b c → (e₁ = s(b, c) ∨ e₂ = s(b, c))) ∧
      (∀ T, T ∈ externalsUsingEdge G E a c → (e₁ = s(a, c) ∨ e₂ = s(a, c)))
-/

/-
  slot409_tau_8_adaptive.lean

  ADAPTIVE PROOF: τ ≤ 8 for PATH_4 with ν = 4

  KEY INSIGHT: By 6-packing contradiction, at most 2 external types exist
  per M-element. Choose the 2 edges adaptively based on which types exist.

  For A = {v₁, a₂, a₃}, external types are:
  - Type 1: {v₁, a₂, w} uses edge {v₁, a₂}
  - Type 2: {v₁, a₃, w} uses edge {v₁, a₃}
  - Type 3: {a₂, a₃, w} uses edge {a₂, a₃}

  At most 2 types exist, so 2 edges suffice.

  TIER: 2 (uses proven scaffolding from slot406)
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

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def isPath4Labeled (M : Finset (Finset V)) (A B C D : Finset V)
    (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V) : Prop :=
  M = {A, B, C, D} ∧
  A = {v₁, a₂, a₃} ∧ B = {v₁, v₂, b₃} ∧ C = {v₂, v₃, c₃} ∧ D = {v₃, d₂, d₃} ∧
  v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ a₂ ∧ v₁ ≠ a₃ ∧ v₁ ≠ b₃ ∧ v₁ ≠ c₃ ∧ v₁ ≠ d₂ ∧ v₁ ≠ d₃ ∧
  v₂ ≠ v₃ ∧ v₂ ≠ a₂ ∧ v₂ ≠ a₃ ∧ v₂ ≠ b₃ ∧ v₂ ≠ c₃ ∧ v₂ ≠ d₂ ∧ v₂ ≠ d₃ ∧
  v₃ ≠ a₂ ∧ v₃ ≠ a₃ ∧ v₃ ≠ b₃ ∧ v₃ ≠ c₃ ∧ v₃ ≠ d₂ ∧ v₃ ≠ d₃ ∧
  a₂ ≠ a₃ ∧ a₂ ≠ b₃ ∧ a₂ ≠ c₃ ∧ a₂ ≠ d₂ ∧ a₂ ≠ d₃ ∧
  a₃ ≠ b₃ ∧ a₃ ≠ c₃ ∧ a₃ ≠ d₂ ∧ a₃ ≠ d₃ ∧
  b₃ ≠ c₃ ∧ b₃ ≠ d₂ ∧ b₃ ≠ d₃ ∧
  c₃ ≠ d₂ ∧ c₃ ≠ d₃ ∧
  d₂ ≠ d₃

-- ══════════════════════════════════════════════════════════════════════════════
-- EXTERNAL TYPE DEFINITION
-- ══════════════════════════════════════════════════════════════════════════════

/-- External of E using edge {a,b}: triangles of form {a, b, w} with w fresh -/
def externalsUsingEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset V) (a b : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ E ∧ a ∈ T ∧ b ∈ T ∧ (T ∩ E).card = 2)

/-- Whether any external of E uses edge {a,b} -/
def hasExternalType (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset V) (a b : V) : Prop :=
  (externalsUsingEdge G E a b).Nonempty

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

`at_most_two_external_types` has already been declared-/
-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: At most 2 external types exist per M-element
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
If all 3 external types exist for A = {v₁, a₂, a₃}, we get triangles:
- T₁ = {v₁, a₂, w₁} (Type 1)
- T₂ = {v₁, a₃, w₂} (Type 2)
- T₃ = {a₂, a₃, w₃} (Type 3)

Together with B, C, D from M, we have 6 pairwise edge-disjoint triangles.
This contradicts ν = 4.
-/
theorem at_most_two_external_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V) (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V)
    (hpath : isPath4Labeled M A B C D v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃)
    (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4) :
    ¬(hasExternalType G A v₁ a₂ ∧ hasExternalType G A v₁ a₃ ∧ hasExternalType G A a₂ a₃) := by
  intro ⟨h1, h2, h3⟩
  -- Extract witness triangles for each type
  obtain ⟨T₁, hT1⟩ := h1
  obtain ⟨T₂, hT2⟩ := h2
  obtain ⟨T₃, hT3⟩ := h3
  -- These form a 6-packing with B, C, D
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- ADAPTIVE EDGE SELECTION
-- ══════════════════════════════════════════════════════════════════════════════

/-
Given that at most 2 types exist, we can choose 2 edges that cover all externals.
For E = {a, b, c} with edges e₁ = {a,b}, e₂ = {b,c}, e₃ = {a,c}:
- If Types 1,2 missing Type 3: use e₁, e₂ (or any pair not needing e₃)
- If Types 1,3 missing Type 2: use e₁, e₃
- If Types 2,3 missing Type 1: use e₂, e₃

Key: the chosen 2 edges cover E itself (any edge of a triangle covers it).
-/
lemma exists_two_edges_cover_all_externals (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset V) (hE : E ∈ G.cliqueFinset 3)
    (a b c : V) (hE_eq : E = {a, b, c})
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h_not_all_three : ¬(hasExternalType G E a b ∧ hasExternalType G E b c ∧ hasExternalType G E a c)) :
    ∃ (e₁ e₂ : Sym2 V), e₁ ∈ G.edgeFinset ∧ e₂ ∈ G.edgeFinset ∧
      (∀ T, T ∈ externalsUsingEdge G E a b → (e₁ = s(a, b) ∨ e₂ = s(a, b))) ∧
      (∀ T, T ∈ externalsUsingEdge G E b c → (e₁ = s(b, c) ∨ e₂ = s(b, c))) ∧
      (∀ T, T ∈ externalsUsingEdge G E a c → (e₁ = s(a, c) ∨ e₂ = s(a, c))) := by
  -- By h_not_all_three, at least one type is empty
  push_neg at h_not_all_three
  -- Case split on which type is missing
  by_cases h1 : hasExternalType G E a b
  · by_cases h2 : hasExternalType G E b c
    · -- Types 1, 2 exist, Type 3 must not exist
      have h3 : ¬hasExternalType G E a c := h_not_all_three h1 h2
      -- Use edges {a,b} and {b,c}
      use s(a, b), s(b, c)
      simp_all +decide [ hasExternalType ];
      have := hE.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    · -- Type 2 doesn't exist
      use s(a, b), s(a, c)
      simp_all +decide [ Finset.ext_iff, SimpleGraph.adj_comm ];
      refine' ⟨ _, _, _ ⟩;
      · exact hE.1 ( by aesop ) ( by aesop ) ( by aesop );
      · have := hE.1; aesop;
      · intro T hT; unfold hasExternalType at h2; aesop;
  · -- Type 1 doesn't exist
    use s(b, c), s(a, c)
    refine' ⟨ _, _, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.mem_edgeFinset ];
    · exact hE.1 ( by aesop ) ( by aesop ) ( by aesop );
    · have := hE.1; simp_all +decide [ Finset.card_insert_of_notMem, SimpleGraph.isNClique_iff ] ;
    · unfold hasExternalType at h1; aesop;

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown constant `SimpleGraph.isClique_iff.mp`
Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ?m.84 = {a, b, c}

V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
A B C D : Finset V
v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V
hpath : isPath4Labeled M A B C D v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃
hM : isTrianglePacking G M
hNu4 : ∀ (S : Finset (Finset V)), isTrianglePacking G S → #S ≤ 4
E : Finset V
hE : E ∈ M
hE_clique : E ∈ G.cliqueFinset 3
a b c : ?m.83
h✝ : a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ?m.84 = {a, b, c}
⊢ ∃ (S : Finset (Sym2 V)),
    #S ≤ 2 ∧
      S ⊆ G.edgeFinset ∧
        (E ∈ G.cliqueFinset 3 → ∃ e ∈ S, e ∈ E.sym2) ∧ ∀ T ∈ G.cliqueFinset 3, #(T ∩ E) ≥ 2 → ∃ e ∈ S, e ∈ T.sym2-/
-- ══════════════════════════════════════════════════════════════════════════════
-- LOCAL COVER LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
For each M-element E = {a,b,c}:
1. At most 2 external types exist (by 6-packing contradiction)
2. Choose 2 edges adaptively to cover existing types
3. These 2 edges also cover E itself
4. All triangles sharing edge with E are covered
-/
lemma exists_adaptive_local_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V) (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V)
    (hpath : isPath4Labeled M A B C D v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃)
    (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (E : Finset V) (hE : E ∈ M) :
    ∃ S : Finset (Sym2 V), S.card ≤ 2 ∧
      S ⊆ G.edgeFinset ∧
      (E ∈ G.cliqueFinset 3 → ∃ e ∈ S, e ∈ E.sym2) ∧
      ∀ T ∈ G.cliqueFinset 3, (T ∩ E).card ≥ 2 → ∃ e ∈ S, e ∈ T.sym2 := by
  -- E is one of A, B, C, D
  have hE_clique := hM.1 hE
  obtain ⟨a, b, c, rfl⟩ := Finset.card_eq_three.mp (SimpleGraph.isClique_iff.mp
    (SimpleGraph.mem_cliqueFinset_iff.mp hE_clique).1).2
  -- At most 2 external types exist
  have h_limit : ¬(hasExternalType G {a,b,c} a b ∧ hasExternalType G {a,b,c} b c ∧
                   hasExternalType G {a,b,c} a c) := by
    sorry  -- Follows from at_most_two_external_types applied to E
  -- Choose 2 edges adaptively
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_path4_adaptive (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V) (v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃ : V)
    (hpath : isPath4Labeled M A B C D v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃)
    (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2) :
    ∃ (cover : Finset (Sym2 V)), cover.card ≤ 8 ∧
      cover ⊆ G.edgeFinset ∧
      (∀ T ∈ G.cliqueFinset 3, ∃ e ∈ cover, e ∈ T.sym2) := by
  -- For each E ∈ M, get adaptive local cover
  have h_local : ∀ E ∈ M, ∃ S : Finset (Sym2 V), S.card ≤ 2 ∧
      S ⊆ G.edgeFinset ∧
      (E ∈ G.cliqueFinset 3 → ∃ e ∈ S, e ∈ E.sym2) ∧
      ∀ T ∈ G.cliqueFinset 3, (T ∩ E).card ≥ 2 → ∃ e ∈ S, e ∈ T.sym2 := by
    exact fun E hE => exists_adaptive_local_cover G M A B C D v₁ v₂ v₃ a₂ a₃ b₃ c₃ d₂ d₃
      hpath hM hNu4 E hE
  choose! S hS using h_local
  let cover := Finset.biUnion M S
  refine ⟨cover, ?_, ?_, ?_⟩
  · -- Card bound: |cover| ≤ |M| × 2 ≤ 4 × 2 = 8
    calc cover.card
        ≤ ∑ E ∈ M, (S E).card := Finset.card_biUnion_le
      _ ≤ ∑ _E ∈ M, 2 := Finset.sum_le_sum (fun E hE => (hS E hE).1)
      _ = M.card * 2 := by simp [Finset.sum_const, smul_eq_mul]
      _ ≤ 4 * 2 := by linarith [hNu4 M hM]
      _ = 8 := by norm_num
  · -- All edges are in G.edgeFinset
    intro e he
    rw [Finset.mem_biUnion] at he
    obtain ⟨E, hE, heS⟩ := he
    exact (hS E hE).2.1 heS
  · -- All triangles are covered
    intro T hT
    by_cases hTM : T ∈ M
    · -- T is in M, covered by S T
      have hT_clique := hM.1 hTM
      obtain ⟨e, he, heT⟩ := (hS T hTM).2.2.1 hT_clique
      exact ⟨e, Finset.mem_biUnion.mpr ⟨T, hTM, he⟩, heT⟩
    · -- T is not in M, by maximality shares edge with some E ∈ M
      obtain ⟨E, hE, hshare⟩ := hMaximal T hT hTM
      obtain ⟨e, he, heT⟩ := (hS E hE).2.2.2 T hT hshare
      exact ⟨e, Finset.mem_biUnion.mpr ⟨E, hE, he⟩, heT⟩

end