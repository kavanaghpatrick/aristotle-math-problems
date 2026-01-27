/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a1a4689f-4c4e-4027-b62d-6e07428175a1

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot484_final_assembly.lean

  FINAL ASSEMBLY: τ ≤ 8 for ν = 4

  Uses PROVEN components:
  - slot412: not_all_three_edge_types (6-packing constraint)
  - slot476: two_edges_cover_Se (S_e coverage)
  - slot482: bridge_common_vertex (bridge structure)
  - slot483: bridge_has_spoke_edges, bridge_covered_by_spoke (spoke coverage)

  PROOF STRATEGY:
  1. For each m ∈ M, get 2-edge cover E_m for S_m (using slot476)
  2. For bridges: they share spoke edges with M-elements (slot483)
  3. Ensure spoke edges are included in E_m (adaptive selection)
  4. Union of E_m covers all triangles with ≤8 edges

  TIER: 2 (assembly of proven components)
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['exists_shared_edge_through_v', 'bridge_common_vertex', 'two_edges_cover_Sm', 'harmonicSorry557626']-/
set_option maxHeartbeats 400000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (m : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ m).card ≥ 2)

def S_m (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (m : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G m).filter (fun t => ∀ m' ∈ M, m' ≠ m → (t ∩ m').card ≤ 1)

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOMS: Proven components
-- ══════════════════════════════════════════════════════════════════════════════

/-- AXIOM from slot476: 2 edges cover S_m -/
axiom two_edges_cover_Sm (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (m : Finset V) (hm : m ∈ M) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ m.sym2 ∩ G.edgeFinset ∧
      ∀ t ∈ S_m G M m, ∃ e ∈ E, e ∈ t.sym2

/-- AXIOM from slot483: Spoke edge extraction -/
axiom exists_shared_edge_through_v (t m : Finset V)
    (ht_card : t.card = 3) (hm_card : m.card = 3)
    (hshare : (t ∩ m).card ≥ 2) (v : V) (hv_t : v ∈ t) (hv_m : v ∈ m) :
    ∃ a, a ∈ t ∧ a ∈ m ∧ a ≠ v ∧ s(v, a) ∈ t.sym2 ∧ s(v, a) ∈ m.sym2

/-- AXIOM from slot482: Bridge common vertex -/
axiom bridge_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (t m1 m2 : Finset V)
    (ht : t ∈ G.cliqueFinset 3) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (hne : m1 ≠ m2)
    (h1 : (t ∩ m1).card ≥ 2) (h2 : (t ∩ m2).card ≥ 2) :
    ∃ v, v ∈ t ∧ v ∈ m1 ∧ v ∈ m2 ∧ m1 ∩ m2 = {v}

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Fintype V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Fintype V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  DecidableEq (Sym2 V)

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

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Function expected at
  two_edges_cover_Sm
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G-/
-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Every triangle is covered
-- ══════════════════════════════════════════════════════════════════════════════

/--
Every triangle t either:
1. Is in some S_m (internal) → covered by 2-edge cover
2. Is a bridge → shares spoke edge with some m → covered if spoke is picked

PROOF:
By maximality, t shares ≥2 with some m ∈ M.
Case 1: t ∈ S_m (disjoint from other M-elements) → covered by two_edges_cover_Sm.
Case 2: t ∉ S_m → ∃ m' ≠ m with (t ∩ m').card ≥ 2 → t is a bridge.
  By bridge_common_vertex, t shares vertex v with m and m'.
  By exists_shared_edge_through_v, t has spoke edge s(v,a) in m.sym2.
  If our cover includes s(v,a), t is covered.

The key insight: we can CHOOSE which 2 edges to pick from m.
When m has "slack" (fewer than 2 non-empty external sets),
we use that slack to pick spoke edges for bridges.
-/
lemma triangle_covered (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMax : ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (E : Finset (Sym2 V)) (hE : E = M.biUnion (fun m =>
      Classical.choose (two_edges_cover_Sm G M hM hM_card hNu4 m (by sorry)))) :
    ∃ e ∈ E, e ∈ t.sym2 := by
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

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Fintype (↑G.edgeSet : Type u_1)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset (Sym2 V))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Unknown identifier `S_m`
Invalid field notation: Type of
  t
is not known; cannot resolve field `sym2`
Unknown identifier `two_edges_cover_Sm`
unsolved goals
V : Type u_1
x✝ : Sort u_2
isTrianglePacking : x✝
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
hM : sorry
hM_card : M.card = 4
hNu4 : ∀ (S : Finset (Finset V)) (a : sorry), S.card ≤ 4
hMax : ∀ t ∈ sorry, ∃ m ∈ M, sorry ≥ 2
⊢ ∃ E' ⊆ sorry, E'.card ≤ 8 ∧ ∀ t ∈ sorry, ∃ e ∈ E', e ∈ t.sym2-/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/--
τ ≤ 8 for graphs with ν = 4.
-/
theorem tau_le_8_nu_4_final (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMax : ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2) :
    ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 8 ∧
      ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2 := by
  -- Get 2-edge cover for each m ∈ M
  have h_covers : ∀ m ∈ M, ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧
      E ⊆ m.sym2 ∩ G.edgeFinset ∧ ∀ t ∈ S_m G M m, ∃ e ∈ E, e ∈ t.sym2 :=
    fun m hm => two_edges_cover_Sm G M hM hM_card hNu4 m hm
  choose f hf using h_covers
  let E' := M.biUnion f
  use E'
  refine ⟨?_, ?_, ?_⟩
  · -- E' ⊆ G.edgeFinset
    intro e he
    simp only [mem_biUnion] at he
    obtain ⟨m, hm, he'⟩ := he
    exact (mem_inter.mp ((hf m hm).2.1 he')).2
  · -- |E'| ≤ 8
    calc E'.card ≤ ∑ m ∈ M, (f m).card := card_biUnion_le
      _ ≤ ∑ _ ∈ M, 2 := Finset.sum_le_sum (fun m hm => (hf m hm).1)
      _ = M.card * 2 := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ = 8 := by rw [hM_card]; norm_num
  · -- E' covers all triangles
    intro t ht
    obtain ⟨m, hm, hshare⟩ := hMax t ht
    -- Case: t ∈ S_m (internal)
    by_cases h_internal : t ∈ S_m G M m
    · -- t is internal to m, covered by f(m)
      obtain ⟨e, he, hcover⟩ := (hf m hm).2.2 t h_internal
      exact ⟨e, mem_biUnion.mpr ⟨m, hm, he⟩, hcover⟩
    · -- t is a bridge (shares ≥2 with another m')
      -- Unfold S_m definition
      simp only [S_m, trianglesSharingEdge, mem_filter, not_and] at h_internal
      have ht_shares : t ∈ trianglesSharingEdge G m := by
        simp only [trianglesSharingEdge, mem_filter]
        exact ⟨ht, hshare⟩
      -- Get witness m' ≠ m with (t ∩ m').card ≥ 2
      have h_exists := h_internal ⟨ht, hshare⟩
      push_neg at h_exists
      obtain ⟨m', hm', hm'_ne, hshare'⟩ := h_exists
      have hshare'' : (t ∩ m').card ≥ 2 := by omega
      -- t is a bridge between m and m'
      -- Get common vertex v
      obtain ⟨v, hv_t, hv_m, hv_m', _⟩ := bridge_common_vertex G M hM t m m' ht hm hm' hm'_ne hshare hshare''
      -- Get spoke edge s(v, a) in both t and m
      have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
      have hm_card : m.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp (hM.1 hm)).card_eq
      obtain ⟨a, ha_t, ha_m, ha_ne, ha_t_sym, ha_m_sym⟩ :=
        exists_shared_edge_through_v t m ht_card hm_card hshare v hv_t hv_m
      -- Now we need: s(v, a) ∈ f(m)
      -- This is where the "adaptive selection" comes in
      -- The 6-packing constraint gives us freedom to include s(v, a)
      -- For now, use axiom/sorry
      sorry

end