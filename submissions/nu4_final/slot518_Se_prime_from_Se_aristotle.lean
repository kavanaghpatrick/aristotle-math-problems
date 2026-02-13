/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d7d59c86-6741-41dd-9f05-8034e209b5bc

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem tau_le_8_assembly (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM4 : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    -- S_e' partitions non-M triangles
    (h_partition : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃! e, e ∈ M ∧ T ∈ S_e' G M e idx)
    -- Each element has card 3
    (h_cards : ∀ e ∈ M, e.card = 3)
    -- 2 edges cover each S_e'
    (h_cover : ∀ e ∈ M, ∃ C : Finset (Sym2 V), C.card ≤ 2 ∧ C ⊆ e.sym2 ∧
      ∀ T ∈ S_e' G M e idx, ∃ edge ∈ C, edge ∈ T.sym2) :
    ∃ Cover : Finset (Sym2 V), Cover.card ≤ 8 ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ edge ∈ Cover, edge ∈ T.sym2

The following was negated by Aristotle:

- lemma at_most_two_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3) (idx : Finset V → ℕ) :
    (usedEdgeTypes G M e idx).card ≤ 2

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
  slot518_Se_prime_from_Se.lean

  BUILD two_edges_cover_Se_prime FROM PROVEN two_edges_cover_Se

  Strategy:
  1. S_e ⊆ S_e' (externals exclusive to e are trivially min-index)
  2. Bridges in S_e' share an edge with e (by definition)
  3. The 2 edges covering S_e also cover bridges (they share edges with e)

  PROVEN BUILDING BLOCKS (from slot512):
  - two_edges_cover_Se: 2 edges from e cover all S_e
  - external_uses_one_edge_type: each external uses exactly one edge-type

  TIER: 2 (subset + bridge handling)
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

/-- S_e: triangles sharing edge with e, exclusive to e -/
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧ ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

/-- Which M-elements does T share an edge with? -/
def sharesEdgeWith (M : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  M.filter (fun e => 2 ≤ (T ∩ e).card)

/-- S_e': triangles assigned to e by min-index rule -/
def S_e' (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V)
    (idx : Finset V → ℕ) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧
    (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅)

/-- A bridge is a triangle sharing edges with multiple M-elements -/
def isBridge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ T ∉ M ∧ 2 ≤ (sharesEdgeWith M T).card

-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA 1: S_e ⊆ S_e' (externals exclusive to e are trivially assigned to e)
-- ══════════════════════════════════════════════════════════════════════════════

lemma S_e_subset_S_e' (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e ∈ M) (idx : Finset V → ℕ) :
    S_e G M e ⊆ S_e' G M e idx := by
  intro T hT
  simp only [S_e, S_e', mem_filter, sharesEdgeWith] at hT ⊢
  refine ⟨hT.1, hT.2.1, hT.2.2.1, ?_⟩
  -- T only shares edge with e, so no f with idx f < idx e shares edge with T
  ext f
  simp only [mem_filter, mem_empty_iff_false, iff_false, not_and]
  intro hfM hf_inter _
  -- f shares edge with T, so f = e (by exclusivity in S_e)
  by_contra hfe
  have := hT.2.2.2 f hfM hfe
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA 2: Bridges in S_e' share an edge with e
-- ══════════════════════════════════════════════════════════════════════════════

lemma bridge_in_Se'_shares_edge_with_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (idx : Finset V → ℕ)
    (T : Finset V) (hT : T ∈ S_e' G M e idx) :
    2 ≤ (T ∩ e).card := by
  simp only [S_e', mem_filter] at hT
  exact hT.2.2.1

-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA 3: The shared edge covers the triangle
-- ══════════════════════════════════════════════════════════════════════════════

lemma shared_edge_in_both_sym2 (T e : Finset V) (hT3 : T.card = 3) (he3 : e.card = 3)
    (h_inter : 2 ≤ (T ∩ e).card) :
    ∃ edge ∈ e.sym2, edge ∈ T.sym2 := by
  -- T ∩ e has ≥2 elements, so there exist a, b ∈ T ∩ e with a ≠ b
  have hne : (T ∩ e).Nonempty := by
    rw [← card_pos]
    omega
  obtain ⟨a, ha⟩ := hne
  simp only [mem_inter] at ha
  have hcard2 : 2 ≤ (T ∩ e).card := h_inter
  have : 1 < (T ∩ e).card := by omega
  rw [one_lt_card] at this
  obtain ⟨x, hx, y, hy, hxy⟩ := this
  simp only [mem_inter] at hx hy
  use Sym2.mk x y
  constructor
  · exact Finset.mk_mem_sym2_iff.mpr ⟨hx.2, hy.2⟩
  · exact Finset.mk_mem_sym2_iff.mpr ⟨hx.1, hy.1⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- LEMMA 4: At most 3 edge-types, so at most 2 are populated (6-packing constraint)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Edge-types used by S_e' -/
def usedEdgeTypes (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) 
    (e : Finset V) (idx : Finset V → ℕ) : Finset (Finset V) :=
  (S_e' G M e idx).image (fun T => T ∩ e)

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Constructing a counterexample using K4 to show the lemma is false.
-/
def K4 : SimpleGraph (Fin 4) := ⊤

instance : DecidableRel K4.Adj := fun a b => inferInstanceAs (Decidable (a ≠ b))

def e_K4 : Finset (Fin 4) := {0, 1, 2}
def M_K4 : Finset (Finset (Fin 4)) := {e_K4}
def idx_K4 : Finset (Fin 4) → ℕ := fun _ => 0

theorem K4_counterexample :
  ∃ (G : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj)
    (M : Finset (Finset (Fin 4))) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset (Fin 4)) (he : e ∈ M) (he3 : e.card = 3) (idx : Finset (Fin 4) → ℕ),
    ¬ ((usedEdgeTypes G M e idx).card ≤ 2) := by
      unfold isTrianglePacking usedEdgeTypes;
      unfold S_e';
      refine' ⟨ ⊤, _, _ ⟩ <;> norm_num;
      exact?;
      refine' ⟨ _, _ ⟩;
      · decide +revert;
      · refine' ⟨ { { 0, 1, 2 } }, _, _ ⟩ <;> simp +decide [ sharesEdgeWith ]

theorem at_most_two_edge_types_false : ¬ (∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3) (idx : Finset V → ℕ),
    (usedEdgeTypes G M e idx).card ≤ 2) := by
      push_neg;
      refine' ⟨ _, _, _, _, _, _, _ ⟩;
      exact ULift ( Fin 4 );
      all_goals try infer_instance;
      exact ⊤;
      infer_instance;
      exact { { ⟨ 0 ⟩, ⟨ 1 ⟩, ⟨ 2 ⟩ } };
      refine' ⟨ _, _, _ ⟩;
      · constructor <;> simp +decide [ isTrianglePacking ];
      · intro S hS; have := hS.1; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
        exact le_trans ( Finset.card_le_card this ) ( by decide );
      · refine' ⟨ _, Finset.mem_singleton_self _, _, _ ⟩;
        · grind;
        · exists fun _ => 0

lemma at_most_two_edge_types_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3) (idx : Finset V → ℕ) :
    (usedEdgeTypes G M e idx).card ≤ 3 := by
      -- Since $e$ is a triangle, its subsets of size 2 are exactly the edges of $e$.
      have h_edge_subsets : ∀ T ∈ S_e' G M e idx, T ∩ e ∈ (Finset.powerset e).filter (fun s => s.card = 2) := by
        intro T hT
        have h_inter_card : 2 ≤ (T ∩ e).card := by
          exact?
        have h_inter_card_le : (T ∩ e).card ≤ 3 := by
          exact le_trans ( Finset.card_le_card ( Finset.inter_subset_right ) ) he3.le
        have h_inter_card_eq : (T ∩ e).card = 2 := by
          interval_cases _ : # ( T ∩ e ) <;> simp_all +decide [S_e'];
          have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : T ∩ e ⊆ T ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : T ∩ e ⊆ e ) ; simp_all +decide ;
          exact hT.2.1 ( Eq.symm ( ‹#T ≤ 3 → e = T› ( by linarith [ hT.1.2 ] ) ) )
        simp [h_inter_card_eq];
      have := Finset.card_le_card ( show Finset.image ( fun T => T ∩ e ) ( S_e' G M e idx ) ⊆ Finset.filter ( fun s => #s = 2 ) ( Finset.powerset e ) from Finset.image_subset_iff.2 h_edge_subsets ) ; simp_all +decide ;
      exact this.trans ( by simp +decide [ ← Finset.powersetCard_eq_filter, he3 ] ) ;

end AristotleLemmas

/-
6-packing constraint: if all 3 edge-types populated, we get a 6-packing
-/
lemma at_most_two_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3) (idx : Finset V → ℕ) :
    (usedEdgeTypes G M e idx).card ≤ 2 := by
  -- If 3 edge-types used, we get triangles T_ab, T_bc, T_ac all in S_e'
  -- Together with e and 3 other M-elements, this would give 6-packing
  -- Contradicts ν = 4
  by_contra h
  push_neg at h
  convert at_most_two_edge_types_false using 1;
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  refine' ⟨ ULift ( Fin 4 ), inferInstance, inferInstance, _, _, _ ⟩;
  exact ⊤;
  infer_instance;
  refine' ⟨ { { ⟨ 0 ⟩, ⟨ 1 ⟩, ⟨ 2 ⟩ } }, _, _, _ ⟩ <;> norm_num [ isTrianglePacking ];
  all_goals norm_cast;
  refine' ⟨ _, _, _ ⟩ <;> try native_decide +revert;
  refine' ⟨ fun _ => 0, _ ⟩ ; simp +decide [ usedEdgeTypes ];
  refine' ⟨ Fin 4, inferInstance, inferInstance, ⊤, inferInstance, { { 0, 1, 2 } }, _, _, _ ⟩ <;> simp +decide [ usedEdgeTypes ];
  exists fun _ => 0

-/
/-- 6-packing constraint: if all 3 edge-types populated, we get a 6-packing -/
lemma at_most_two_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3) (idx : Finset V → ℕ) :
    (usedEdgeTypes G M e idx).card ≤ 2 := by
  -- If 3 edge-types used, we get triangles T_ab, T_bc, T_ac all in S_e'
  -- Together with e and 3 other M-elements, this would give 6-packing
  -- Contradicts ν = 4
  by_contra h
  push_neg at h
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `at_most_two_edge_types`
unsolved goals
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
hM : isTrianglePacking G M
hNu4 : ∀ (S : Finset (Finset V)), isTrianglePacking G S → #S ≤ 4
e : Finset V
he : e ∈ M
he3 : #e = 3
idx : Finset V → ℕ
⊢ ∃ (E : Finset (Sym2 V)), #E ≤ 2 ∧ E ⊆ e.sym2 ∧ ∀ T ∈ S_e' G M e idx, ∃ edge ∈ E, edge ∈ T.sym2-/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: 2 edges cover S_e'
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH:
1. S_e' = S_e ∪ (bridges assigned to e)
2. S_e is covered by 2 edges (proven in slot512)
3. Bridges share an edge with e, so covered by same 2 edges
4. At most 2 edge-types are populated (6-packing constraint)
5. Therefore 2 edges (one per populated type) cover all of S_e'
-/
theorem two_edges_cover_Se_prime (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he3 : e.card = 3)
    (idx : Finset V → ℕ) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ E ⊆ e.sym2 ∧
      ∀ T ∈ S_e' G M e idx, ∃ edge ∈ E, edge ∈ T.sym2 := by
  -- Get the 2 edges covering S_e (from slot512 proof pattern)
  -- Every T in S_e' shares edge with e, and at most 2 edge-types are used
  -- So 2 edges suffice
  have h_types := at_most_two_edge_types G M hM hNu4 e he he3 idx
  -- Select one edge per used type
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- ASSEMBLY: τ ≤ 8 from 2 edges per element
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable section AristotleLemmas

/-
If S_e' can be covered by a subset of edges of e of size at most 2, then we can find a subset of edges of e of size at most 2 that covers both S_e' and e itself.
-/
lemma exists_cover_Se'_and_e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) (he : e ∈ M) (idx : Finset V → ℕ)
    (h_card : e.card = 3)
    (h_cover_e : ∃ C : Finset (Sym2 V), C.card ≤ 2 ∧ C ⊆ e.sym2 ∧
      ∀ T ∈ S_e' G M e idx, ∃ edge ∈ C, edge ∈ T.sym2) :
    ∃ C' : Finset (Sym2 V), C'.card ≤ 2 ∧ C' ⊆ e.sym2 ∧
      (∀ T ∈ S_e' G M e idx, ∃ edge ∈ C', edge ∈ T.sym2) ∧
      (∃ edge ∈ C', edge ∈ e.sym2) := by
        rcases h_cover_e with ⟨ C, hC₁, hC₂, hC₃ ⟩;
        by_cases hC : C.Nonempty;
        · exact ⟨ C, hC₁, hC₂, hC₃, by obtain ⟨ x, hx ⟩ := hC; exact ⟨ x, hx, hC₂ hx ⟩ ⟩;
        · rcases Finset.card_eq_three.mp h_card with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; use { Sym2.mk ( x, y ) } ; aesop

end AristotleLemmas

theorem tau_le_8_assembly (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM4 : M.card = 4)
    (hNu4 : ∀ S, isTrianglePacking G S → S.card ≤ 4)
    (idx : Finset V → ℕ) (h_inj : Function.Injective idx)
    -- S_e' partitions non-M triangles
    (h_partition : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃! e, e ∈ M ∧ T ∈ S_e' G M e idx)
    -- Each element has card 3
    (h_cards : ∀ e ∈ M, e.card = 3)
    -- 2 edges cover each S_e'
    (h_cover : ∀ e ∈ M, ∃ C : Finset (Sym2 V), C.card ≤ 2 ∧ C ⊆ e.sym2 ∧
      ∀ T ∈ S_e' G M e idx, ∃ edge ∈ C, edge ∈ T.sym2) :
    ∃ Cover : Finset (Sym2 V), Cover.card ≤ 8 ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ edge ∈ Cover, edge ∈ T.sym2 := by
  -- Collect 2 edges from each of 4 elements = 8 edges
  -- For each e in M, we can find a cover C' of size <= 2 which covers S_e' and also contains an edge of e.
  obtain ⟨C', hC'⟩ : ∃ C' : Finset (Finset (Finset V)), (∀ e ∈ M, ∃ C'' : Finset (Sym2 V), C''.card ≤ 2 ∧ C'' ⊆ e.sym2 ∧ (∀ T ∈ S_e' G M e idx, ∃ edge ∈ C'', edge ∈ T.sym2) ∧ (∃ edge ∈ C'', edge ∈ e.sym2)) := by
    choose! C hC₁ hC₂ hC₃ using h_cover;
    refine' ⟨ ∅, fun e he => _ ⟩;
    have := exists_cover_Se'_and_e G M e he idx ( h_cards e he ) ⟨ C e, hC₁ e he, hC₂ e he, hC₃ e he ⟩ ; aesop;
  choose! C' hC' using hC';
  refine' ⟨ Finset.biUnion M C', _, _ ⟩;
  · exact le_trans ( Finset.card_biUnion_le ) ( by exact le_trans ( Finset.sum_le_sum fun e he => hC' e he |>.1 ) ( by simp +decide [ hM4 ] ) );
  · intro T hT
    by_cases hT_M : T ∈ M;
    · exact Exists.elim ( hC' T hT_M |>.2.2.2 ) fun edge hedge => ⟨ edge, Finset.mem_biUnion.mpr ⟨ T, hT_M, hedge.1 ⟩, hedge.2 ⟩;
    · obtain ⟨ e, he₁, he₂ ⟩ := h_partition T hT hT_M |> ExistsUnique.exists;
      rcases hC' e he₁ with ⟨ hC₁, hC₂, hC₃, hC₄ ⟩ ; rcases hC₃ T he₂ with ⟨ edge, hC₅, hC₆ ⟩ ; exact ⟨ edge, Finset.mem_biUnion.mpr ⟨ e, he₁, hC₅ ⟩, hC₆ ⟩ ;

end