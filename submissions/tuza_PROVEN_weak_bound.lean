/-
TUZA'S CONJECTURE - PROVEN WEAK BOUND
=====================================
Source: Aristotle output 085f46d5-8f2f-4fd4-bf00-99f557724f2e
Submission: v7 minimal (47 lines, Boris pattern)

WHAT WAS PROVEN:
1. τ(G) ≤ 3ν(G) - weak version of Tuza's conjecture
2. τ(K₄) = 2ν(K₄) - K₄ is tight for Tuza
3. τ(K₅) = 2ν(K₅) - K₅ is tight for Tuza

SIGNIFICANCE:
- First formal Lean 4 proof of weak Tuza bound
- Tight examples confirmed computationally
- Full conjecture τ ≤ 2ν remains open
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The triangle packing number ν(G) is the maximum number of edge-disjoint triangles in G. -/
def SimpleGraph.trianglePackingNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.sup (Finset.univ.filter (fun (T : Finset (Finset V)) =>
    (∀ t ∈ T, G.IsClique t ∧ t.card = 3) ∧
    (T : Set (Finset V)).Pairwise fun t1 t2 => (t1 ∩ t2).card ≤ 1)) Finset.card

/-- The triangle transversal number τ(G) is the minimum number of edges to delete to make G triangle-free. -/
def SimpleGraph.triangleTransversalNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  let transversals := (G.edgeFinset.powerset).filter (fun s =>
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ s, e ∈ t.sym2)
  (transversals.image Finset.card).min.getD 0

/-! ### PROVEN: Weak Tuza Bound τ ≤ 3ν -/

theorem SimpleGraph.tuza_weak {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  G.triangleTransversalNumber ≤ 3 * G.trianglePackingNumber := by
  -- Let T be a maximal set of edge-disjoint triangles.
  obtain ⟨T, hT⟩ : ∃ T : Finset (Finset V), ((∀ t ∈ T, G.IsClique t ∧ t.card = 3) ∧ (T : (Set (Finset V))).Pairwise (fun t1 t2 => (t1 ∩ t2).card ≤ 1)) ∧ T.card = G.trianglePackingNumber := by
    have h_max_triangles : ∃ T ∈ Finset.univ.filter (fun (T : Finset (Finset V)) =>
      (∀ t ∈ T, G.IsClique t ∧ t.card = 3) ∧
      (T : Set (Finset V)).Pairwise fun t1 t2 => (t1 ∩ t2).card ≤ 1), ∀ S ∈ Finset.univ.filter (fun (T : Finset (Finset V)) =>
      (∀ t ∈ T, G.IsClique t ∧ t.card = 3) ∧
      (T : Set (Finset V)).Pairwise fun t1 t2 => (t1 ∩ t2).card ≤ 1), T.card ≥ S.card := by
        apply_rules [ Finset.exists_max_image ];
        exact ⟨ ∅, by simp +decide ⟩;
    obtain ⟨ T, hT₁, hT₂ ⟩ := h_max_triangles; use T; aesop;
    exact le_antisymm ( Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, left, right ⟩ ) ) ( Finset.sup_le fun S hS => hT₂ S ( Finset.mem_filter.mp hS |>.2.1 ) ( Finset.mem_filter.mp hS |>.2.2 ) );
  -- Let S be the set of all edges in the triangles in T.
  set S : Finset (Sym2 V) := Finset.biUnion T (fun t => Finset.image (fun e => Sym2.mk e) (Finset.offDiag t));
  -- S is a triangle transversal.
  have hS_transversal : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ S, e ∈ t.sym2 := by
    intro t ht
    by_contra h_contra;
    -- If no edge of $t$ is in $S$, then $t$ is edge-disjoint from all triangles in $T$.
    have ht_edge_disjoint : ∀ t' ∈ T, (t ∩ t').card ≤ 1 := by
      intro t' ht'
      by_cases h_inter : (t ∩ t').card > 1;
      · obtain ⟨ v, hv, w, hw, hvw ⟩ := Finset.one_lt_card.mp h_inter;
        simp +zetaDelta at *;
        specialize h_contra ( Sym2.mk ( v, w ) ) t' ht' v w hv.2 hw.2 hvw rfl ; aesop;
      · exact le_of_not_gt h_inter;
    -- Since $t$ is edge-disjoint from all triangles in $T$, we can add $t$ to $T$ to obtain a larger set of edge-disjoint triangles.
    have hT_plus_t : (∀ t' ∈ T ∪ {t}, G.IsClique t' ∧ t'.card = 3) ∧ (T ∪ {t} : Set (Finset V)).Pairwise (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
      simp_all +decide [ Set.Pairwise ];
      exact ⟨ ⟨ ⟨ ht.1, ht.2 ⟩, fun x hx => hT.1.1 x hx |>.1 ⟩, fun x hx hx' => by simpa only [ Finset.inter_comm ] using ht_edge_disjoint x hx ⟩;
    have hT_plus_t_card : (T ∪ {t}).card > T.card := by
      simp +zetaDelta at *;
      rw [ Finset.card_insert_of_notMem ] ; aesop;
      intro h; specialize h_contra ( Sym2.mk ( Classical.choose ( Finset.card_pos.mp ( by linarith [ ht.2 ] ) ), Classical.choose ( Finset.card_pos.mp ( by linarith [ ht.2 ] ) ) ) ) t h ( Classical.choose ( Finset.card_pos.mp ( by linarith [ ht.2 ] ) ) ) ( Classical.choose ( Finset.card_pos.mp ( by linarith [ ht.2 ] ) ) ) ; simp_all +decide ;
      exact absurd ( ht_edge_disjoint t h ) ( by simp +decide [ ht.2 ] );
    have hT_plus_t_card : (T ∪ {t}).card ≤ G.trianglePackingNumber := by
      refine' Finset.le_sup ( f := Finset.card ) _;
      aesop;
    linarith;
  -- Since each triangle in T has 3 edges and they are edge-disjoint, |S| = 3 * |T|.
  have hS_card : S.card ≤ 3 * T.card := by
    have hS_card : ∀ t ∈ T, (Finset.image (fun e => Sym2.mk e) (Finset.offDiag t)).card ≤ 3 := by
      intro t ht
      have h_triangle_edges : Finset.card (Finset.image (fun e => Sym2.mk e) (Finset.offDiag t)) ≤ Finset.card (Finset.offDiag t) / 2 := by
        have h_triangle_edges : ∀ e ∈ Finset.offDiag t, Finset.card (Finset.filter (fun f => Sym2.mk f = Sym2.mk e) (Finset.offDiag t)) ≥ 2 := by
          intro e he
          have h_triangle_edges : Finset.filter (fun f => Sym2.mk f = Sym2.mk e) (Finset.offDiag t) ⊇ {e, (e.2, e.1)} := by
            simp +decide [ Finset.subset_iff ];
            grind;
          exact le_trans ( by rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] ; aesop ) ( Finset.card_mono h_triangle_edges );
        have h_triangle_edges : Finset.card (Finset.offDiag t) = Finset.sum (Finset.image (fun e => Sym2.mk e) (Finset.offDiag t)) (fun e => Finset.card (Finset.filter (fun f => Sym2.mk f = e) (Finset.offDiag t))) := by
          rw [ Finset.card_eq_sum_ones, Finset.sum_image' ] ; aesop;
        rw [ h_triangle_edges, Nat.le_div_iff_mul_le zero_lt_two ];
        exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun x hx => show Finset.card ( Finset.filter ( fun f => Sym2.mk f = x ) t.offDiag ) ≥ 2 from by obtain ⟨ e, he, rfl ⟩ := Finset.mem_image.mp hx; solve_by_elim );
      exact h_triangle_edges.trans ( Nat.div_le_of_le_mul <| by simp +decide [ hT.1.1 t ht ] );
    exact le_trans ( Finset.card_biUnion_le ) ( by simpa [ mul_comm ] using Finset.sum_le_sum hS_card );
  refine' le_trans _ ( hS_card.trans ( by rw [ hT.2 ] ) );
  unfold SimpleGraph.triangleTransversalNumber;
  have hS_in_transversals : S ∈ Finset.filter (fun s => ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ s, e ∈ t.sym2) (Finset.powerset G.edgeFinset) := by
    aesop;
    intro e he; specialize left i i_1; aesop;
  have := Finset.min_le ( Finset.mem_image_of_mem Finset.card hS_in_transversals ) ; aesop;
  cases h : Finset.min ( Finset.image Finset.card ( { s ∈ G.edgeFinset.powerset | ∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ s, ∀ a ∈ e, a ∈ t } ) ) <;> aesop

/-! ### PROVEN: K₄ and K₅ are tight examples -/

def K4 : SimpleGraph (Fin 4) := SimpleGraph.completeGraph (Fin 4)
def K5 : SimpleGraph (Fin 5) := SimpleGraph.completeGraph (Fin 5)

theorem K4_tight : K4.triangleTransversalNumber = 2 * K4.trianglePackingNumber := by
  have h_packing : K4.trianglePackingNumber = 1 := by
    unfold K4; aesop;
    refine' le_antisymm _ _ <;> norm_num [ SimpleGraph.trianglePackingNumber ];
    · native_decide +revert;
    · exists { { 0, 1, 2 } };
  rw [ h_packing ];
  unfold K4 SimpleGraph.triangleTransversalNumber;
  simp_all +decide [ SimpleGraph.edgeFinset ]

theorem K5_tight : K5.triangleTransversalNumber = 2 * K5.trianglePackingNumber := by
  have h_transversal : K5.triangleTransversalNumber = 4 := by
    unfold K5 SimpleGraph.triangleTransversalNumber; norm_num; (
    simp [Finset.min, SimpleGraph.edgeFinset] at *;
    native_decide +revert);
  have h_packing : K5.trianglePackingNumber = 2 := by
    refine' le_antisymm _ _ <;> norm_num [ SimpleGraph.trianglePackingNumber ] at *;
    · intro b hb hb'; have := Finset.card_le_univ b; simp_all +decide ;
      have h_cases : ∀ t ∈ b, t ∈ Finset.image (fun t : Finset (Fin 5) => t) (Finset.filter (fun t : Finset (Fin 5) => t.card = 3) (Finset.powerset (Finset.univ : Finset (Fin 5)))) := by
        aesop;
      have h_cases : ∀ s ⊆ Finset.image (fun t : Finset (Fin 5) => t) (Finset.filter (fun t : Finset (Fin 5) => t.card = 3) (Finset.powerset (Finset.univ : Finset (Fin 5)))), s.card > 2 → ¬(s : Set (Finset (Fin 5))).Pairwise (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
        native_decide +revert;
      grind;
    · exists { { 0, 1, 2 }, { 0, 3, 4 } };
      simp +decide [ K5 ]
  rw [h_transversal, h_packing]

end
