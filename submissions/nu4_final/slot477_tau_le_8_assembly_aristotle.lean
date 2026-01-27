/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ca3aface-5fd1-419b-a8b9-a43aa14ce7c5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot477_tau_le_8_assembly.lean

  FINAL ASSEMBLY: τ ≤ 8 from proven components

  Uses as AXIOMS:
  1. not_all_three_edge_types (slot412)
  2. two_edges_cover_Se (slot476) - proven using #1

  This file ONLY proves the final union construction.

  TIER: 2 (biUnion + card bounds)
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry666932', 'two_edges_cover_Se_exists']-/
set_option maxHeartbeats 400000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (standard)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOM: Two edges cover S_e (proven in slot476)
-- ══════════════════════════════════════════════════════════════════════════════

/--
AXIOM: Proven in slot476 using slot412's 6-packing constraint.
For any element e ∈ M in a 4-packing, there exist ≤2 edges covering all of S_e.
-/
axiom two_edges_cover_Se_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ G.edgeFinset ∧
      ∀ t ∈ S_e G M e, ∃ edge ∈ E', edge ∈ t.sym2

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Fintype V

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
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Function expected at
  S_e
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G-/
-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Every triangle is in some S_e
-- ══════════════════════════════════════════════════════════════════════════════

/--
By maximality, every triangle t shares ≥2 vertices with some m ∈ M.
If t also shares edge with some other m' ∈ M, then t ∈ S_{m'} (its "home").
If t only shares edge with m, then t ∈ S_m.
Either way, t is in some S_e for e ∈ M.

PROOF SKETCH:
1. By hMax, ∃ m ∈ M such that (t ∩ m).card ≥ 2
2. This means t ∈ trianglesSharingEdge G m
3. For t to be in S_m, we need: ∀ f ∈ M, f ≠ m → (t ∩ f).card ≤ 1
4. If this holds, t ∈ S_m ✓
5. If not, ∃ f ∈ M, f ≠ m with (t ∩ f).card ≥ 2
6. Then t ∈ trianglesSharingEdge G f
7. Check if t ∈ S_f... if not, repeat
8. Since M is finite and triangles are edge-disjoint, this terminates
-/
lemma triangle_in_some_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hMax : ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ e ∈ M, t ∈ S_e G M e := by
  -- By maximality, t shares ≥2 vertices with some m ∈ M
  obtain ⟨m, hm, hshare⟩ := hMax t ht
  -- Check if t ∈ S_m
  by_cases h_in_Sm : t ∈ S_e G M m
  · exact ⟨m, hm, h_in_Sm⟩
  · -- t ∉ S_m means ∃ f ∈ M, f ≠ m with (t ∩ f).card ≥ 2
    simp only [S_e, trianglesSharingEdge, mem_filter, not_and] at h_in_Sm
    -- t ∈ trianglesSharingEdge G m since hshare gives (t ∩ m).card ≥ 2
    have ht_sharing : t ∈ trianglesSharingEdge G m := by
      simp only [trianglesSharingEdge, mem_filter]
      exact ⟨ht, hshare⟩
    -- So h_in_Sm gives us a witness f
    have h_exists_f := h_in_Sm ⟨ht, hshare⟩
    push_neg at h_exists_f
    obtain ⟨f, hf, hfne, hf_share⟩ := h_exists_f
    -- f ∈ M, f ≠ m, and (t ∩ f).card ≥ 2
    have hf_share' : (t ∩ f).card ≥ 2 := by omega
    -- Now check if t ∈ S_f
    by_cases h_in_Sf : t ∈ S_e G M f
    · exact ⟨f, hf, h_in_Sf⟩
    · -- t ∉ S_f, so there's another g with (t ∩ g).card ≥ 2
      -- But M is a packing: pairwise edge-disjoint
      -- t can share ≥2 vertices with at most 1 element of M (since they're edge-disjoint!)
      -- Wait, this isn't quite right...
      -- Actually, t could share 1 vertex with many elements of M
      -- The key is: if t shares ≥2 with m and ≥2 with f, then m ∩ f ≥ 1 vertex
      -- But since t is a triangle (3 vertices), t ∩ m and t ∩ f overlap
      -- Let's use that M is pairwise edge-disjoint: (m ∩ f).card ≤ 1
      -- If t shares 2 vertices with both m and f, then those overlapping vertices
      -- would force m and f to share ≥2 vertices, contradicting packing
      exfalso
      -- t shares ≥2 vertices with both m and f
      -- t has 3 vertices total
      -- By pigeonhole, t ∩ m and t ∩ f share at least 1 vertex
      have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
      -- |t ∩ m| ≥ 2 and |t ∩ f| ≥ 2
      -- |t ∩ m| + |t ∩ f| ≥ 4 > |t| = 3
      -- So (t ∩ m) and (t ∩ f) must overlap in at least 1 vertex
      have h_overlap : ((t ∩ m) ∩ (t ∩ f)).Nonempty := by
        have h1 : (t ∩ m).card ≥ 2 := hshare
        have h2 : (t ∩ f).card ≥ 2 := hf_share'
        -- (t ∩ m) ∪ (t ∩ f) ⊆ t
        have h_sub : (t ∩ m) ∪ (t ∩ f) ⊆ t := by
          intro x hx
          simp only [mem_union, mem_inter] at hx
          rcases hx with ⟨hxt, _⟩ | ⟨hxt, _⟩ <;> exact hxt
        have h_card_bound : ((t ∩ m) ∪ (t ∩ f)).card ≤ t.card := card_le_card h_sub
        -- By inclusion-exclusion
        have h_ie : (t ∩ m).card + (t ∩ f).card = ((t ∩ m) ∪ (t ∩ f)).card + ((t ∩ m) ∩ (t ∩ f)).card := by
          exact (card_union_add_card_inter (t ∩ m) (t ∩ f)).symm
        -- Rearranging
        have h_inter_card : ((t ∩ m) ∩ (t ∩ f)).card ≥ 2 + 2 - 3 := by
          omega
        simp at h_inter_card
        exact card_pos.mp (by omega)
      -- So ∃ v ∈ (t ∩ m) ∩ (t ∩ f)
      obtain ⟨v, hv⟩ := h_overlap
      simp only [mem_inter] at hv
      -- v ∈ t ∩ m and v ∈ t ∩ f, so v ∈ m and v ∈ f
      have hvm : v ∈ m := hv.1.2
      have hvf : v ∈ f := hv.2.2
      -- So v ∈ m ∩ f
      -- Now we need another vertex in m ∩ f to get (m ∩ f).card ≥ 2
      -- Actually, we need to be more careful...
      -- The packing condition says (m ∩ f).card ≤ 1, which is satisfied by having just v
      -- We need to show they share 2 vertices
      -- Let's think again: t shares ≥2 with m, so t ∩ m contains at least an edge {u,v}
      -- t shares ≥2 with f, so t ∩ f contains at least an edge {w,x}
      -- t has only 3 vertices, so {u,v} and {w,x} must share at least one vertex
      -- ...but that doesn't immediately give m ∩ f ≥ 2
      -- Hmm, let me reconsider.
      -- Actually the issue is that externals can share vertex with multiple M elements!
      -- The correct argument is: t must be "homed" to exactly one S_e
      -- The S_e definition ensures this by the "edge-disjoint from OTHER" condition
      -- Let me look at this differently: use well-foundedness or finiteness
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
-- Aristotle: show that the search terminates

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 when ν = 4
-- ══════════════════════════════════════════════════════════════════════════════

/--
τ ≤ 8 for graphs with ν = 4.

PROOF SKETCH:
1. M = {e₁, e₂, e₃, e₄} is a maximal 4-packing
2. For each eᵢ ∈ M, by two_edges_cover_Se_exists, get Eᵢ with |Eᵢ| ≤ 2
3. Let E' = ⋃_{e ∈ M} Eᵢ
4. |E'| ≤ 4 × 2 = 8 (by card_biUnion_le)
5. For any triangle t ∈ G.cliqueFinset 3:
   - By triangle_in_some_Se, t ∈ S_e for some e ∈ M
   - By two_edges_cover_Se_exists, Eₑ covers t
   - Since Eₑ ⊆ E', some edge in E' covers t
-/
theorem tau_le_8_nu_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMax : ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2) :
    ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 8 ∧
      ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2 := by
  -- For each e ∈ M, get the 2-edge cover
  -- Use classical choice to get a function M → Finset (Sym2 V)
  have h_covers : ∀ e ∈ M, ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ G.edgeFinset ∧
      ∀ t ∈ S_e G M e, ∃ edge ∈ E', edge ∈ t.sym2 := fun e he =>
    two_edges_cover_Se_exists G M hM hM_card hNu4 e he
  -- Use choice to get a function
  choose f hf using h_covers
  -- Define E' = ⋃_{e ∈ M} f(e)
  let E' := M.biUnion f
  use E'
  refine ⟨?_, ?_, ?_⟩
  · -- E' ⊆ G.edgeFinset
    intro e he
    simp only [mem_biUnion] at he
    obtain ⟨m, hm, he'⟩ := he
    exact (hf m hm).2.1 he'
  · -- |E'| ≤ 8
    calc E'.card = (M.biUnion f).card := rfl
      _ ≤ ∑ e ∈ M, (f e).card := card_biUnion_le
      _ ≤ ∑ _ ∈ M, 2 := Finset.sum_le_sum (fun e he => (hf e he).1)
      _ = M.card * 2 := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ = 4 * 2 := by rw [hM_card]
      _ = 8 := by norm_num
  · -- E' covers all triangles
    intro t ht
    -- By triangle_in_some_Se, t ∈ S_e for some e ∈ M
    obtain ⟨e, he, ht_in_Se⟩ := triangle_in_some_Se G M hM hMax t ht
    -- By choice, f(e) covers t
    obtain ⟨edge, hedge, h_cover⟩ := (hf e he).2.2 t ht_in_Se
    -- edge ∈ f(e) ⊆ E'
    use edge
    constructor
    · simp only [mem_biUnion]
      exact ⟨e, he, hedge⟩
    · exact h_cover

end