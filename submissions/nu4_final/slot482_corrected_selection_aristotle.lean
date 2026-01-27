/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 410b7287-fa9d-4a10-81ae-17ebf1314720

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot482_corrected_selection.lean

  CORRECTED APPROACH: Adaptive edge selection

  KEY INSIGHT: When an M-element has fewer than 2 non-empty external sets,
  we have FREEDOM to choose which edges to pick. We should use this freedom
  to cover bridges.

  SELECTION RULE:
  For each M-element m = {a, b, c}:
  1. Count non-empty external sets: n ∈ {0, 1, 2} (by 6-packing, n ≤ 2)
  2. Pick n edges for the non-empty externals.
  3. For the remaining (2 - n) slots, pick edges that are shared with bridges.

  This ensures:
  - All internals are covered (by step 2).
  - All bridges have at least one shared edge picked (by step 3).

  TIER: 2 (case analysis + counting)
-/

import Mathlib


set_option maxHeartbeats 400000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

-- Triangles sharing edge with m
def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (m : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ m).card ≥ 2)

-- S_m: triangles sharing edge with m, disjoint from other M-elements
def S_m (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (m : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G m).filter (fun t => ∀ m' ∈ M, m' ≠ m → (t ∩ m').card ≤ 1)

-- Bridges: triangles sharing ≥2 with multiple M-elements
def isBridge (t : Finset V) (M : Finset (Finset V)) : Prop :=
  (M.filter (fun m => (t ∩ m).card ≥ 2)).card ≥ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Bridge shares spoke vertex with M-elements
-- ══════════════════════════════════════════════════════════════════════════════

/--
If t bridges m1 and m2, there exists a unique vertex v ∈ t ∩ m1 ∩ m2.
-/
lemma bridge_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (t m1 m2 : Finset V)
    (ht : t ∈ G.cliqueFinset 3) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (hne : m1 ≠ m2)
    (h1 : (t ∩ m1).card ≥ 2) (h2 : (t ∩ m2).card ≥ 2) :
    ∃ v, v ∈ t ∧ v ∈ m1 ∧ v ∈ m2 ∧ m1 ∩ m2 = {v} := by
  have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  -- Pigeonhole: (t ∩ m1) and (t ∩ m2) overlap
  have h_overlap : ((t ∩ m1) ∩ (t ∩ m2)).Nonempty := by
    have h_sub : (t ∩ m1) ∪ (t ∩ m2) ⊆ t := by
      intro x hx; simp only [mem_union, mem_inter] at hx
      rcases hx with ⟨hxt, _⟩ | ⟨hxt, _⟩ <;> exact hxt
    have h_ie : (t ∩ m1).card + (t ∩ m2).card =
        ((t ∩ m1) ∪ (t ∩ m2)).card + ((t ∩ m1) ∩ (t ∩ m2)).card :=
      (card_union_add_card_inter (t ∩ m1) (t ∩ m2)).symm
    have h_bound : ((t ∩ m1) ∪ (t ∩ m2)).card ≤ t.card := card_le_card h_sub
    have h_pos : ((t ∩ m1) ∩ (t ∩ m2)).card ≥ 1 := by omega
    exact card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := h_overlap
  simp only [mem_inter] at hv
  use v
  refine ⟨hv.1.1, hv.1.2, hv.2.2, ?_⟩
  -- m1 ∩ m2 = {v} by packing
  have h_packing := hM.2 hm1 hm2 hne
  have hv_in : v ∈ m1 ∩ m2 := mem_inter.mpr ⟨hv.1.2, hv.2.2⟩
  have h_card_le : (m1 ∩ m2).card ≤ 1 := h_packing
  have h_card_ge : (m1 ∩ m2).card ≥ 1 := card_pos.mpr ⟨v, hv_in⟩
  exact card_eq_one.mp (by omega)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Tactic `rewrite` failed: Did not find an occurrence of the pattern
  1 < #?m.129
in the target expression
  #(t ∩ m1) ≥ 2

V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
hM : isTrianglePacking G M
t m1 m2 : Finset V
ht : t ∈ G.cliqueFinset 3
hm1 : m1 ∈ M
hm2 : m2 ∈ M
hne : m1 ≠ m2
h1 : #(t ∩ m1) ≥ 2
h2 : #(t ∩ m2) ≥ 2
v : V
hv_t : v ∈ t
hv_m1 : v ∈ m1
hv_m2 : v ∈ m2
hv_inter : m1 ∩ m2 = {v}
h1' : #(t ∩ m1) ≥ 2
⊢ ∃ (v : V) (a : V) (b : V),
    v ∈ t ∧ a ∈ t ∧ b ∈ t ∧ v ≠ a ∧ v ≠ b ∧ s(v, a) ∈ m1.sym2 ∧ s(v, b) ∈ m2.sym2 ∧ s(v, a) ∈ t.sym2 ∧ s(v, b) ∈ t.sym2-/
-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Bridge has spoke edges in multiple M-elements
-- ══════════════════════════════════════════════════════════════════════════════

/--
If t bridges m1 and m2 via common vertex v, then:
- t = {v, a, b} for some a, b
- {v, a} ∈ m1.sym2 (edge of m1)
- {v, b} ∈ m2.sym2 (edge of m2)
- At least one of these spoke edges will be in our cover.
-/
lemma bridge_has_spoke_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (t m1 m2 : Finset V)
    (ht : t ∈ G.cliqueFinset 3) (hm1 : m1 ∈ M) (hm2 : m2 ∈ M)
    (hne : m1 ≠ m2)
    (h1 : (t ∩ m1).card ≥ 2) (h2 : (t ∩ m2).card ≥ 2) :
    ∃ v a b, v ∈ t ∧ a ∈ t ∧ b ∈ t ∧ v ≠ a ∧ v ≠ b ∧
      s(v, a) ∈ m1.sym2 ∧ s(v, b) ∈ m2.sym2 ∧
      s(v, a) ∈ t.sym2 ∧ s(v, b) ∈ t.sym2 := by
  obtain ⟨v, hv_t, hv_m1, hv_m2, hv_inter⟩ := bridge_common_vertex G M hM t m1 m2 ht hm1 hm2 hne h1 h2
  -- t ∩ m1 = {v, a} for some a
  have h1' : (t ∩ m1).card ≥ 2 := h1
  rw [Finset.one_lt_card] at h1'
  obtain ⟨x, hx, y, hy, hxy⟩ := h1'
  simp only [mem_inter] at hx hy
  -- One of x, y is v
  have hv_in_inter : v ∈ t ∩ m1 := mem_inter.mpr ⟨hv_t, hv_m1⟩
  -- Similar for t ∩ m2
  have h2' : (t ∩ m2).card ≥ 2 := h2
  rw [Finset.one_lt_card] at h2'
  obtain ⟨p, hp, q, hq, hpq⟩ := h2'
  simp only [mem_inter] at hp hq
  -- Extract the spoke structure
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry94915', 'adaptive_edge_selection']-/
-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOM: 6-packing constraint gives edge selection freedom
-- ══════════════════════════════════════════════════════════════════════════════

/--
AXIOM: For any M-element m in a 4-packing:
- At most 2 of m's 3 edge-types have non-empty S_m-externals.
- We can always select 2 edges of m such that:
  (a) All S_m triangles are covered, AND
  (b) At least one spoke edge through each "shared vertex" is picked.

The "shared vertex" is a vertex in m that's also in another M-element.
Spoke edges through shared vertices cover bridges.
-/
axiom adaptive_edge_selection (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (m : Finset V) (hm : m ∈ M) (hm_tri : m ∈ G.cliqueFinset 3) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ m.sym2 ∩ G.edgeFinset ∧
      -- Covers all S_m triangles
      (∀ t ∈ S_m G M m, ∃ e ∈ E', e ∈ t.sym2) ∧
      -- Covers all bridges through shared vertices
      (∀ v ∈ m, (∃ m' ∈ M, m' ≠ m ∧ v ∈ m') →
        ∃ e ∈ E', ∃ a ∈ m, e = s(v, a) ∧ v ≠ a)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `adaptive_edge_selection`
Application type mismatch: The argument
  f
has type
  (m : Finset V) → m ∈ M → Finset (Sym2 V)
but is expected to have type
  Finset V → Finset ?m.163
in the application
  M.biUnion f-/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/--
τ ≤ 8 for graphs with ν = 4, using adaptive edge selection.

PROOF SKETCH:
1. For each m ∈ M, use adaptive_edge_selection to get E_m.
2. E' = ⋃ E_m has |E'| ≤ 8.
3. For any triangle t:
   a. If t ∈ some S_m, covered by E_m.
   b. If t is a bridge between m1, m2: t has spoke edges through v.
      By adaptive selection, E_{m1} or E_{m2} contains a spoke.
      That spoke edge covers t.
-/
theorem tau_le_8_adaptive (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMax : ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2) :
    ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 8 ∧
      ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2 := by
  -- Get adaptive covers for each M-element
  have h_covers : ∀ m ∈ M, ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧
      E' ⊆ m.sym2 ∩ G.edgeFinset ∧
      (∀ t ∈ S_m G M m, ∃ e ∈ E', e ∈ t.sym2) ∧
      (∀ v ∈ m, (∃ m' ∈ M, m' ≠ m ∧ v ∈ m') →
        ∃ e ∈ E', ∃ a ∈ m, e = s(v, a) ∧ v ≠ a) := by
    intro m hm
    have hm_tri : m ∈ G.cliqueFinset 3 := hM.1 hm
    exact adaptive_edge_selection G M hM hM_card hNu4 m hm hm_tri
  choose f hf using h_covers
  let E' := M.biUnion f
  use E'
  refine ⟨?_, ?_, ?_⟩
  · -- E' ⊆ G.edgeFinset
    intro e he
    simp only [mem_biUnion] at he
    obtain ⟨m, hm, he'⟩ := he
    have h := (hf m hm).2.1 he'
    exact (mem_inter.mp h).2
  · -- |E'| ≤ 8
    calc E'.card ≤ ∑ m ∈ M, (f m).card := card_biUnion_le
      _ ≤ ∑ _ ∈ M, 2 := Finset.sum_le_sum (fun m hm => (hf m hm).1)
      _ = M.card * 2 := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ = 8 := by rw [hM_card]; norm_num
  · -- E' covers all triangles
    intro t ht
    obtain ⟨m, hm, hshare⟩ := hMax t ht
    -- Check if t is internal to m
    by_cases h_internal : t ∈ S_m G M m
    · -- t is internal: covered by f(m)
      obtain ⟨e, he, h_cover⟩ := (hf m hm).2.2.1 t h_internal
      exact ⟨e, mem_biUnion.mpr ⟨m, hm, he⟩, h_cover⟩
    · -- t is a bridge: not in S_m
      -- t shares ≥2 with m, but fails S_m condition
      -- So ∃ m' ∈ M, m' ≠ m with (t ∩ m').card ≥ 2
      simp only [S_m, trianglesSharingEdge, mem_filter, not_and] at h_internal
      have ht_sharing : t ∈ trianglesSharingEdge G m := by
        simp only [trianglesSharingEdge, mem_filter]
        exact ⟨ht, hshare⟩
      have h_exists_m' := h_internal ⟨ht, hshare⟩
      push_neg at h_exists_m'
      obtain ⟨m', hm', hm'_ne, hshare'⟩ := h_exists_m'
      have hshare'' : (t ∩ m').card ≥ 2 := by omega
      -- t is a bridge between m and m'
      -- Get common vertex
      obtain ⟨v, hv_t, hv_m, hv_m', _⟩ := bridge_common_vertex G M hM t m m' ht hm hm' hm'_ne hshare hshare''
      -- By adaptive selection, f(m) has a spoke through v
      have h_spoke := (hf m hm).2.2.2 v hv_m ⟨m', hm', hm'_ne, hv_m'⟩
      obtain ⟨e, he, a, ha, he_eq, hva⟩ := h_spoke
      -- e = s(v, a) is in f(m) and passes through v
      -- If t contains edge {v, a}, we're done
      -- But we need to show e ∈ t.sym2
      -- This requires more careful analysis of t's structure
      sorry

end