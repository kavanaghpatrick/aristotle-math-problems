/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c0dd7186-7496-4e63-b8dd-0759662d6304

The following was proved by Aristotle:

- lemma tau_Te_le_2_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 1)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2

- lemma tau_Te_le_2_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2

- lemma tau_Te_le_2_nu_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2

- theorem tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G ≤ 3) : coveringNumber G ≤ 2 * packingNumber G
-/

/-
Tuza ν≤3: The Missing Lemma
Target: Prove τ(T_e) ≤ 2 for some e ∈ M when ν ≤ 3

This is the gap between:
- tau_S_le_2: τ(S_e) ≤ 2 (PROVEN)
- inductive_bound: τ(G) ≤ τ(T_e) + τ(rest) (PROVEN)

We need: τ(T_e) ≤ 2 for the induction to work.

Key insight: T_e = triangles sharing edge with e
All such triangles share one of the 3 edges of e.
For ν ≤ 3, the structure is constrained enough that τ(T_e) ≤ 2.
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image (fun x => Sym2.mk (x.1, x.2))

def IsEdgeDisjoint (T : Finset (Finset V)) : Prop :=
  (T : Set (Finset V)).PairwiseDisjoint triangleEdges

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ IsEdgeDisjoint M

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}

def IsTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) : Prop :=
  ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) E

def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ IsTriangleCover G E}

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ¬Disjoint (triangleEdges t) (triangleEdges e))

def coveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E}

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

/- Aristotle failed to find a proof. -/
-- THE KEY LEMMA: τ(T_e) ≤ 2 for some e when ν ≤ 3
-- For ν = 1: Only one packing element, T_e covers all triangles, τ(T_e) ≤ 2 by star/K4
-- For ν = 2, 3: Can choose e such that T_e has nice structure

lemma exists_e_tau_Te_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3) (hpos : M.Nonempty) :
    ∃ e ∈ M, coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

/- Aristotle failed to find a proof. -/
-- Alternative: Direct bound for any e when ν ≤ 3
lemma tau_Te_le_2_of_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card ≤ 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  sorry

-- Case ν = 1: T_e is all triangles, they all share edge with e
lemma tau_Te_le_2_nu_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 1)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  exact tau_Te_le_2_of_nu_le_3 G M hM ( by linarith ) e he

-- Case ν = 2
lemma tau_Te_le_2_nu_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  exact tau_Te_le_2_of_nu_le_3 G M hM ( le_trans ( le_of_eq hnu ) ( by decide ) ) e he

-- Case ν = 3
lemma tau_Te_le_2_nu_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2 := by
  -- Apply the lemma tau_Te_le_2_of_nu_le_3 with the given M and hnu.
  apply tau_Te_le_2_of_nu_le_3 G M hM (by linarith) e he

-- Main theorem using the lemma
theorem tuza_nu_le_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G ≤ 3) : coveringNumber G ≤ 2 * packingNumber G := by
  -- By definition of packing number, there exists a maximum packing $M$ with $M.card = packingNumber G$.
  obtain ⟨M, hM⟩ : ∃ M : Finset (Finset V), IsMaxPacking G M ∧ M.card = packingNumber G := by
    have h_max_packing : ∃ M : Finset (Finset V), IsTrianglePacking G M ∧ M.card = packingNumber G := by
      have h_finite : Set.Finite {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M} := by
        exact Set.finite_iff_bddAbove.mpr ⟨ _, fun n hn => hn.choose_spec.1 ▸ Finset.card_le_univ _ ⟩
      have h_nonempty : {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}.Nonempty := by
        exact ⟨ 0, ⟨ ∅, rfl, ⟨ by simp +decide, by simp +decide [ IsEdgeDisjoint ] ⟩ ⟩ ⟩;
      have := h_finite.isCompact.sSup_mem h_nonempty; aesop;
    exact ⟨ h_max_packing.choose, ⟨ h_max_packing.choose_spec.1, h_max_packing.choose_spec.2 ⟩, h_max_packing.choose_spec.2 ⟩;
  -- Since $M$ is a maximum packing, $T_e(G)$ covers all triangles in $G$.
  have h_cover : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ M, ¬Disjoint (triangleEdges t) (triangleEdges e) := by
    intro t ht
    by_contra h_no_edge;
    have h_contradiction : IsTrianglePacking G (insert t M) := by
      refine' ⟨ _, _ ⟩;
      · exact Finset.insert_subset ht ( hM.1.1.1 );
      · intro e he f hf hne;
        simp +zetaDelta at *;
        cases he <;> cases hf <;> simp_all +decide [ IsMaxPacking ];
        · exact Disjoint.symm ( h_no_edge e ‹_› );
        · exact hM.1.2 ‹_› ‹_› hne;
    have h_contradiction : (insert t M).card > M.card := by
      rw [ Finset.card_insert_of_notMem ] ; aesop;
      intro h; specialize h_no_edge; simp_all +decide [ IsTrianglePacking ] ;
      specialize h_no_edge t h ; simp_all +decide [ Finset.disjoint_left ];
      unfold triangleEdges at h_no_edge; simp_all +decide [ Finset.ext_iff ] ;
      obtain ⟨ x, y, z, hx, hy, hz, hxyz ⟩ := Finset.card_eq_three.mp ht.card_eq; specialize h_no_edge ( Sym2.mk ( x, y ) ) x y; aesop;
    have h_contradiction : (insert t M).card ≤ packingNumber G := by
      exact le_csSup ⟨ Finset.card ( Finset.univ : Finset ( Finset V ) ), fun n hn => by obtain ⟨ M, rfl, hM ⟩ := hn; exact Finset.card_le_univ _ ⟩ ⟨ _, rfl, by assumption ⟩;
    linarith;
  -- Since $T_e(G)$ covers all triangles in $G$, we can cover all triangles in $G$ by covering each $T_e(G)$ with $2$ edges.
  have h_cover_all : ∃ E : Finset (Sym2 V), E.card ≤ 2 * M.card ∧ ∀ t ∈ G.cliqueFinset 3, ¬Disjoint (triangleEdges t) E := by
    have h_cover_all : ∀ e ∈ M, ∃ E_e : Finset (Sym2 V), E_e.card ≤ 2 ∧ ∀ t ∈ T_e G e, ¬Disjoint (triangleEdges t) E_e := by
      intro e he
      have h_tau_Te : coveringNumberOn G (T_e G e) ≤ 2 := by
        exact tau_Te_le_2_of_nu_le_3 G M hM.1 ( by linarith ) e he;
      obtain ⟨ E, hE₁, hE₂ ⟩ := Nat.sInf_mem ( show { n : ℕ | ∃ E : Finset ( Sym2 V ), E.card = n ∧ ∀ t ∈ T_e G e, ¬Disjoint ( triangleEdges t ) E }.Nonempty from by
                                                refine' ⟨ _, ⟨ Finset.biUnion ( T_e G e ) triangleEdges, rfl, _ ⟩ ⟩;
                                                simp +contextual [ Finset.disjoint_left ];
                                                intro t ht; use Classical.choose ( Finset.nonempty_of_ne_empty ( show triangleEdges t ≠ ∅ from by
                                                                                                                  unfold T_e at ht; aesop; ) ), Classical.choose_spec ( Finset.nonempty_of_ne_empty ( show triangleEdges t ≠ ∅ from by
                                                                                                                                                                                                                    unfold T_e at ht; aesop; ) ), t, ht, Classical.choose_spec ( Finset.nonempty_of_ne_empty ( show triangleEdges t ≠ ∅ from by
                                                                                                                                                                                                                                                                                                                              unfold T_e at ht; aesop; ) ) ; );
      exact ⟨ E, hE₁.symm ▸ h_tau_Te, hE₂ ⟩;
    choose! E hE₁ hE₂ using h_cover_all;
    refine' ⟨ Finset.biUnion M E, _, _ ⟩;
    · exact le_trans ( Finset.card_biUnion_le ) ( by simpa [ mul_comm ] using Finset.sum_le_sum hE₁ );
    · intro t ht; obtain ⟨ e, he, he' ⟩ := h_cover t ht; specialize hE₂ e he t; simp_all +decide [ Finset.disjoint_left ] ;
      exact Exists.elim ( hE₂ ( Finset.mem_filter.mpr ⟨ by
        exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, ht ⟩, by
        exact Finset.not_disjoint_iff.mpr he' ⟩ ) ) fun x hx => ⟨ x, hx.1, e, he, hx.2 ⟩;
  obtain ⟨ E, hE₁, hE₂ ⟩ := h_cover_all; exact le_trans ( csInf_le ⟨ 0, fun n hn => by obtain ⟨ E, rfl, hE ⟩ := hn; exact Nat.zero_le _ ⟩ ⟨ E, rfl, hE₂ ⟩ ) ( by linarith ) ;

end