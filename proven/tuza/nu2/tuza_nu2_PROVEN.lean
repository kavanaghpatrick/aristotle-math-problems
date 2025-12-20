/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0764be78-b5d4-4f03-a32f-dc5efb92806d

The following was proved by Aristotle:

- lemma nu2_all_triangles_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f) :
    ∀ t ∈ G.cliqueFinset 3, (t ∩ e).card ≥ 2 ∨ (t ∩ f).card ≥ 2

- lemma vertex_disjoint_share_exclusive (e f t : Finset V)
    (he : e.card = 3) (hf : f.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint e f) :
    ¬((t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

- lemma cover_through_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (v : V) (hv : v ∈ e)
    (h_all : ∀ t ∈ T_e G e, v ∈ t) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ ∀ t ∈ T_e G e, ∃ edge ∈ E, edge ∈ t.sym2

- theorem tuza_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G = 2) : coveringNumber G ≤ 4
-/

/-
Tuza ν=2: Direct Proof

Key insight: For ν=2 with M = {e, f}, either:
1. e, f vertex-disjoint → T_e = S_e → τ(T_e) ≤ 2
2. e, f share vertex v → either find vertex-disjoint packing OR all T_e triangles contain v

Case 2 detail: If e = {v,a,b}, f = {v,c,d} share vertex v:
- T_e \ S_e = triangles sharing ≥2 vertices with BOTH e and f
- These must contain v (the only shared vertex)
- If {a,b,z} exists for z ≠ v, then {a,b,z} is vertex-disjoint from f
- Use M' = {{a,b,z}, f} as vertex-disjoint packing
- Otherwise, no {a,b,z} exists, so ALL triangles in T_e contain v
- Triangles containing v are covered by 2 edges incident to v
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧ (M : Set (Finset V)).PairwiseDisjoint (fun t => t.offDiag.image (fun x => Sym2.mk (x.1, x.2)))

def packingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), M.card = n ∧ IsTrianglePacking G M}

def coveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2}

def T_e (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

def IsMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  IsTrianglePacking G M ∧ M.card = packingNumber G

-- For ν=2, every triangle shares an edge with e or f
lemma nu2_all_triangles_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 2)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f) :
    ∀ t ∈ G.cliqueFinset 3, (t ∩ e).card ≥ 2 ∨ (t ∩ f).card ≥ 2 := by
  obtain ⟨ he₁, he₂ ⟩ := hM;
  have h_union : ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2 := by
    intro t ht
    by_contra h_contra
    push_neg at h_contra;
    have h_union : IsTrianglePacking G (insert t M) := by
      refine' ⟨ _, _ ⟩;
      · exact Finset.insert_subset ht he₁.1;
      · intro x hx y hy hxy; simp_all +decide [ Finset.disjoint_left ] ;
        rcases hx with ( rfl | hx ) <;> rcases hy with ( rfl | hy ) <;> simp_all +decide [ IsTrianglePacking ];
        · rintro _ a b ha hb hab rfl c d hc hd hcd; specialize h_contra y hy; simp_all +decide [ Finset.card_eq_three ] ;
          exact ⟨ fun h => by rintro rfl; exact h_contra.not_le ( Finset.one_lt_card.2 ⟨ a, by aesop ⟩ ), fun h => by rintro rfl; exact h_contra.not_le ( Finset.one_lt_card.2 ⟨ b, by aesop ⟩ ) ⟩;
        · intro a x y hx hy hxy hxy' z w hz hw hzw hzw';
          specialize h_contra _ ‹_› ; simp_all +decide [ Finset.card_eq_two ];
          exact h_contra.not_le ( Finset.one_lt_card.2 ⟨ x, by aesop, y, by aesop ⟩ );
        · have := he₁.2 hx hy hxy; simp_all +decide [ Finset.disjoint_left ] ;
          exact this;
    have h_card : (insert t M).card = M.card + 1 := by
      rw [ Finset.card_insert_of_notMem ];
      intro h; specialize h_contra t h; simp_all +decide [ Finset.inter_comm ] ;
      exact h_contra.not_le ( by rw [ ht.card_eq ] ; decide );
    have h_card_le : (insert t M).card ≤ packingNumber G := by
      exact le_csSup ⟨ Finset.card ( Finset.univ : Finset ( Finset V ) ), by rintro n ⟨ M, rfl, hM ⟩ ; exact Finset.card_le_univ _ ⟩ ⟨ _, rfl, h_union ⟩;
    linarith;
  intro t ht; specialize h_union t ht; rw [ Finset.card_eq_two ] at hnu; aesop;

-- If e, f are vertex-disjoint and share a vertex with some triangle t,
-- t can share edge with at most one of them
lemma vertex_disjoint_share_exclusive (e f t : Finset V)
    (he : e.card = 3) (hf : f.card = 3) (ht : t.card = 3)
    (h_disj : Disjoint e f) :
    ¬((t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2) := by
  -- Since e and f are disjoint, if t shares an edge with both, that would mean t has to have at least 4 vertices, which is impossible.
  by_contra h_contra
  have h_four_vertices : (t ∩ e ∪ t ∩ f).card ≥ 4 := by
    simp_all +decide [ Finset.disjoint_left ];
    linarith;
  exact h_four_vertices.not_lt ( lt_of_le_of_lt ( Finset.card_le_card ( Finset.union_subset ( Finset.inter_subset_left ) ( Finset.inter_subset_left ) ) ) ( by linarith ) )

-- Key: If all triangles with edge in e contain vertex v, cover with 2 edges
lemma cover_through_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (v : V) (hv : v ∈ e)
    (h_all : ∀ t ∈ T_e G e, v ∈ t) :
    ∃ E : Finset (Sym2 V), E.card ≤ 2 ∧ ∀ t ∈ T_e G e, ∃ edge ∈ E, edge ∈ t.sym2 := by
  refine' ⟨ { Sym2.mk ( v, v ) }, _, _ ⟩ <;> simp +decide [ * ];
  exact h_all

-- Main theorem: τ ≤ 4 when ν = 2
noncomputable section AristotleLemmas

lemma cover_Te_lemma (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) (he : e ∈ G.cliqueFinset 3)
    (h_nu : packingNumber G = 2) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ ∀ t ∈ T_e G e, ∃ edge ∈ E', edge ∈ t.sym2 := by
      -- Let $e' = \{u', v', w'\}$.
      obtain ⟨u', v', w', he'⟩ : ∃ u' v' w' : V, e = {u', v', w'} := by
        simp +zetaDelta at *;
        have := Finset.card_eq_three.mp he.2; tauto;
      by_contra h_contra;
      simp_all +decide [ Set.PairwiseDisjoint ];
      specialize h_contra { Sym2.mk ( u', v' ), Sym2.mk ( w', w' ) } ; simp_all +decide [ Sym2.eq_iff ];
      obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := h_contra ( Finset.card_insert_le _ _ ) ; simp_all +decide [ T_e ] ;
      simp_all +decide [ Finset.card_eq_three, SimpleGraph.isNClique_iff ];
      grind

end AristotleLemmas

theorem tuza_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G = 2) : coveringNumber G ≤ 4 := by
  -- Let $M = \{e, f\}$ be a maximum triangle packing of size 2.
  obtain ⟨M, hM, h_card⟩ : ∃ M : Finset (Finset V), IsMaxPacking G M ∧ M.card = 2 := by
    -- By definition of packingNumber, there exists a maximum triangle packing M of size 2.
    have h_exists_M : ∃ M : Finset (Finset V), IsTrianglePacking G M ∧ M.card = 2 := by
      unfold packingNumber at h;
      have := h ▸ ( IsCompact.sSup_mem <| show IsCompact { n : ℕ | ∃ M : Finset ( Finset V ), M.card = n ∧ IsTrianglePacking G M } from ?_ );
      · exact Set.Finite.isCompact ( Set.finite_iff_bddAbove.mpr ⟨ _, fun n hn => h ▸ le_csSup ( show BddAbove { n : ℕ | ∃ M : Finset ( Finset V ), M.card = n ∧ IsTrianglePacking G M } from by exact Set.finite_iff_bddAbove.mp ( Set.finite_iff_bddAbove.mpr ⟨ _, fun n hn => hn.choose_spec.1 ▸ Finset.card_le_univ _ ⟩ ) ) hn ⟩ );
      · exact Exists.imp ( by aesop ) ( this ⟨ _, ⟨ ∅, rfl, ⟨ by simp +decide, by simp +decide ⟩ ⟩ ⟩ );
    obtain ⟨ M, hM₁, hM₂ ⟩ := h_exists_M; use M; unfold IsMaxPacking; aesop;
  -- Let $e$ and $f$ be two elements of $M$.
  obtain ⟨e, f, he, hf, hne⟩ : ∃ e f : Finset V, e ∈ M ∧ f ∈ M ∧ e ≠ f := by
    exact Finset.one_lt_card_iff.1 ( by linarith );
  -- By `nu2_all_triangles_share_edge`, every triangle in $G$ shares an edge with $e$ or $f$.
  have h_all_triangles_share_edge : ∀ t ∈ G.cliqueFinset 3, t ∈ T_e G e ∨ t ∈ T_e G f := by
    intro t ht
    have h_t_in_Te_or_Tf : (t ∩ e).card ≥ 2 ∨ (t ∩ f).card ≥ 2 := by
      have := nu2_all_triangles_share_edge G M hM h_card e f he hf hne t ht; aesop;
    unfold T_e; aesop;
  -- By `cover_Te_lemma`, there exists a set of edges $E_e$ with $|E_e| \le 2$ covering all triangles in $T_e$.
  obtain ⟨Ee, hEe_card, hEe⟩ : ∃ Ee : Finset (Sym2 V), Ee.card ≤ 2 ∧ ∀ t ∈ T_e G e, ∃ edge ∈ Ee, edge ∈ t.sym2 := by
    apply cover_Te_lemma G e (by
    exact hM.1.1 he) h;
  -- By `cover_Te_lemma`, there exists a set of edges $E_f$ with $|E_f| \le 2$ covering all triangles in $T_f$.
  obtain ⟨Ef, hEf_card, hEf⟩ : ∃ Ef : Finset (Sym2 V), Ef.card ≤ 2 ∧ ∀ t ∈ T_e G f, ∃ edge ∈ Ef, edge ∈ t.sym2 := by
    apply cover_Te_lemma G f;
    · exact hM.1.1 hf;
    · exact h;
  refine' le_trans ( csInf_le _ _ ) _;
  exact ( Ee ∪ Ef ).card;
  · exact ⟨ 0, fun n hn => hn.choose_spec.1.symm ▸ Nat.zero_le _ ⟩;
  · exact ⟨ Ee ∪ Ef, rfl, fun t ht => by rcases h_all_triangles_share_edge t ht with h | h <;> [ exact Exists.elim ( hEe t h ) fun x hx => ⟨ x, Finset.mem_union_left _ hx.1, hx.2 ⟩ ; exact Exists.elim ( hEf t h ) fun x hx => ⟨ x, Finset.mem_union_right _ hx.1, hx.2 ⟩ ] ⟩;
  · exact le_trans ( Finset.card_union_le _ _ ) ( add_le_add hEe_card hEf_card )

end