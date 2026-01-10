/-
  PATH_4 case for Tuza's conjecture with ν=4

  Scaffolding from Aristotle iterations, with main theorem target added.

  PROVEN LEMMAS:
  - triangle_shares_edge_with_packing
  - extract_two_from_triple
  - two_edges_hit_sharing
  - union_covers_union
  - card_union_le_four
  - active_eq_private_union_bridges
  - private_neighbor_intersection_le_one
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

open Finset BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧ Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def isPath4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧ A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧ (C ∩ D).card = 1 ∧
  (A ∩ C).card = 0 ∧ (A ∩ D).card = 0 ∧ (B ∩ D).card = 0

def active_edges (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) : Finset (Sym2 V) :=
  T.sym2.filter (fun e => ∃ t ∈ trianglesSharingEdge G T, e ∈ t.sym2)

def private_neighbors (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G T).filter (fun t => ∀ T' ∈ M, T' ≠ T → t ∉ trianglesSharingEdge G T')

def bridge_neighbors (G : SimpleGraph V) [DecidableRel G.Adj] (T T' : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G T).filter (fun t => t ∈ trianglesSharingEdge G T')

def bridge_edges (G : SimpleGraph V) [DecidableRel G.Adj] (T T' : Finset V) : Finset (Sym2 V) :=
  T.sym2.filter (fun e => ∃ t ∈ bridge_neighbors G T T', e ∈ t.sym2)

def private_edges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (T : Finset V) : Finset (Sym2 V) :=
  T.sym2.filter (fun e => ∃ t ∈ private_neighbors G M T, e ∈ t.sym2)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMAS (from Aristotle scaffolding)
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not_in_M : t ∉ M) :
    ∃ e ∈ M, (t ∩ e).card ≥ 2 := by
      by_contra h_contra;
      have h_packing : M ∪ {t} ⊆ G.cliqueFinset 3 ∧ Set.Pairwise (M ∪ {t}) (fun t1 t2 => (t1 ∩ t2).card ≤ 1) := by
        simp_all +decide [ Finset.subset_iff, Set.Pairwise ];
        simp_all +decide [ Finset.inter_comm ];
        exact ⟨ fun x hx => by have := hM.1; exact (by
        have := this.1 hx; simp_all +decide [ SimpleGraph.isNClique_iff ] ;), fun x hx hx' => Nat.le_of_lt_succ ( h_contra x hx ), fun x hx => ⟨ fun hx' => Nat.le_of_lt_succ ( h_contra x hx ), fun y hy hxy => by have := hM.1; exact (by
        exact this.2 hx hy hxy |> le_trans <| by decide;) ⟩ ⟩;
      have h_card_le_packing_number : (M ∪ {t}).card ≤ trianglePackingNumber G := by
        have h_card_le_packing_number : ∃ S ∈ Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset, S.card = (M ∪ {t}).card := by
          refine' ⟨ M ∪ { t }, _, _ ⟩ <;> simp_all +decide [ isTrianglePacking ];
        have h_card_le_packing_number_max : ∀ S ∈ Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset, S.card ≤ (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)).max.getD 0 := by
          intro S hS;
          have := Finset.le_max ( Finset.mem_image_of_mem Finset.card hS );
          cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 ).powerset ) ) <;> aesop;
        exact h_card_le_packing_number.choose_spec.2 ▸ h_card_le_packing_number_max _ h_card_le_packing_number.choose_spec.1;
      have := hM.2; simp_all +decide [ Finset.card_union_add_card_inter ] ;

lemma extract_two_from_triple (T : Finset V) (v : V) (hv : v ∈ T) (hcard : T.card = 3) :
    ∃ u w, u ∈ T ∧ w ∈ T ∧ u ≠ v ∧ w ≠ v ∧ u ≠ w ∧ T = {v, u, w} := by
      rw [ Finset.card_eq_three ] at hcard; aesop;

lemma two_edges_hit_sharing (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (a b c : V) (hT_eq : T = {a, b, c}) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ t ∈ trianglesSharingEdge G T, s(a, b) ∈ t.sym2 ∨ s(a, c) ∈ t.sym2 ∨ s(b, c) ∈ t.sym2 := by
      intros t ht
      have h_inter : (t ∩ {a, b, c}).card ≥ 2 := by
        unfold trianglesSharingEdge at ht; aesop;
      have h_inter : ∃ x y : V, x ∈ t ∧ y ∈ t ∧ x ≠ y ∧ (x = a ∧ y = b ∨ x = a ∧ y = c ∨ x = b ∧ y = c ∨ x = b ∧ y = a ∨ x = c ∧ y = a ∨ x = c ∧ y = b) := by
        obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.mp h_inter; use x, y; aesop;
      obtain ⟨x, y, hx, hy, hxy, h_cases⟩ := h_inter;
      aesop

lemma union_covers_union (A B : Finset (Finset V)) (XA XB : Finset (Sym2 V))
    (hA : ∀ t ∈ A, ∃ e ∈ XA, e ∈ t.sym2) (hB : ∀ t ∈ B, ∃ e ∈ XB, e ∈ t.sym2) :
    ∀ t ∈ A ∪ B, ∃ e ∈ XA ∪ XB, e ∈ t.sym2 := by
      grind

lemma card_union_le_four (A B : Finset (Sym2 V)) (hA : A.card ≤ 2) (hB : B.card ≤ 2) :
    (A ∪ B).card ≤ 4 := by
      apply le_trans (Finset.card_union_le A B) (add_le_add hA hB)

lemma active_eq_private_union_bridges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T : Finset V) (hT : T ∈ M) :
    active_edges G T = private_edges G M T ∪ (M.erase T).biUnion (fun T' => bridge_edges G T T') := by
  ext e
  simp [active_edges, private_edges, bridge_edges];
  constructor <;> intro h;
  · by_cases h₂ : ∃ T' ∈ M.erase T, e ∈ T.sym2.filter (fun e => ∃ t ∈ trianglesSharingEdge G T, t ∈ trianglesSharingEdge G T' ∧ e ∈ t.sym2) <;> simp_all +decide [ private_neighbors, bridge_neighbors ];
    · exact Or.inr ⟨ h₂.choose, h₂.choose_spec.1, h₂.choose_spec.2.choose, ⟨ h₂.choose_spec.2.choose_spec.1, h₂.choose_spec.2.choose_spec.2.1 ⟩, h₂.choose_spec.2.choose_spec.2.2 ⟩;
    · grind +ring;
  · rcases h with ( ⟨ h₁, t, ht₁, ht₂ ⟩ | ⟨ a, ⟨ ha₁, ha₂ ⟩, h₁, t, ht₁, ht₂ ⟩ ) <;> refine' ⟨ h₁, t, _, _ ⟩ <;> simp_all +decide [ private_neighbors, bridge_neighbors ]

lemma private_neighbor_intersection_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T : Finset V)
    (t : Finset V) (ht : t ∈ private_neighbors G M T)
    (T' : Finset V) (hT' : T' ∈ M) (hdiff : T' ≠ T) :
    (t ∩ T').card ≤ 1 := by
      have h_not_in_sharing : ¬∃ T' ∈ M, T' ≠ T ∧ t ∈ trianglesSharingEdge G T' := by
        unfold private_neighbors at ht; aesop;
      contrapose! h_not_in_sharing;
      unfold private_neighbors trianglesSharingEdge at *; aesop;

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET THEOREM: τ ≤ 8 for PATH_4 configuration
-- ══════════════════════════════════════════════════════════════════════════════

/--
  Main theorem: For a graph G with ν(G) = 4 where the maximal packing M
  forms a path A-B-C-D (each consecutive pair shares exactly one vertex,
  non-consecutive pairs are disjoint), we have τ(G) ≤ 8.

  Proof strategy:
  - Each triangle in G shares an edge with some element of M
  - Partition triangles by which M-element they share edge with
  - For endpoints A, D: each needs ≤2 edges (private externals)
  - For middle elements B, C: each needs ≤2 edges (private externals)
  - Bridges between adjacent pairs need additional edges
  - Total: at most 8 edges suffice
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (A B C D : Finset V) (hPath : isPath4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  sorry

end
