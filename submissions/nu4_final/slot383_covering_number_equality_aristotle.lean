/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 98cbb539-419e-4f73-9c3f-44dbead10a68

The following was proved by Aristotle:

- theorem covering_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (S₁ S₂ : Finset (Finset V)) :
    triangleCoveringNumberOn G (S₁ ∪ S₂) ≤
    triangleCoveringNumberOn G S₁ + triangleCoveringNumberOn G S₂
-/

/-
Tuza ν=4 Strategy - Slot 383: Covering Number Definitional Bridge

DEBATE CONSENSUS (Grok, Gemini, Codex):
  The mathematics is COMPLETE. The gap is DEFINITIONAL:
  - slot257 proves τ(S_e) ≤ 2 for each packing element
  - slot257 proves path4_triangle_partition (all triangles in union of S_e)
  - BUT: can't assemble because of type mismatch

THE ISSUE:
  - triangleCoveringNumber G uses G.cliqueFinset 3
  - triangleCoveringNumberOn G S has different type signature
  - Need: triangleCoveringNumberOn G (G.cliqueFinset 3) = triangleCoveringNumber G

THIS SUBMISSION:
  Proves the definitional equality that unlocks assembly of τ ≤ 8 proof.

TIER: 2 (Definition manipulation, should be straightforward)
-/

import Mathlib


set_option maxHeartbeats 800000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Edge covering number: minimum edges to hit all triangles -/
noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { n | ∃ E : Finset (Sym2 V), E.card = n ∧ E ⊆ G.edgeFinset ∧
         ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2.filter (· ∈ G.edgeFinset) }

/-- Edge covering number on a specific set of triangles -/
noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : ℕ :=
  sInf { n | ∃ E : Finset (Sym2 V), E.card = n ∧ E ⊆ G.edgeFinset ∧
         ∀ T ∈ S, ∃ e ∈ E, e ∈ T.sym2.filter (· ∈ G.edgeFinset) }

-- ══════════════════════════════════════════════════════════════════════════════
-- SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

/-- Covering all triangles is the same as covering cliqueFinset 3 -/
lemma covering_all_eq_covering_cliques (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset (Sym2 V)) (hE : E ⊆ G.edgeFinset) :
    (∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2.filter (· ∈ G.edgeFinset)) ↔
    (∀ T : Finset V, T ∈ G.cliqueFinset 3 → ∃ e ∈ E, e ∈ T.sym2.filter (· ∈ G.edgeFinset)) := by
  constructor <;> intro h T hT <;> exact h T hT

/-- The set of valid covers is the same for G and for cliqueFinset 3 -/
lemma cover_sets_equal (G : SimpleGraph V) [DecidableRel G.Adj] :
    { n | ∃ E : Finset (Sym2 V), E.card = n ∧ E ⊆ G.edgeFinset ∧
          ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2.filter (· ∈ G.edgeFinset) } =
    { n | ∃ E : Finset (Sym2 V), E.card = n ∧ E ⊆ G.edgeFinset ∧
          ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ T.sym2.filter (· ∈ G.edgeFinset) } := rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: Covering G.cliqueFinset 3 equals covering G
-- ══════════════════════════════════════════════════════════════════════════════

/--
PROOF SKETCH:
triangleCoveringNumber G is defined via G.cliqueFinset 3.
triangleCoveringNumberOn G (G.cliqueFinset 3) covers exactly the same set.
Therefore they have the same infimum.
-/
theorem covering_number_on_all_triangles (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringNumberOn G (G.cliqueFinset 3) = triangleCoveringNumber G := by
  unfold triangleCoveringNumberOn triangleCoveringNumber
  rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- SUBADDITIVITY FOR UNION
-- ══════════════════════════════════════════════════════════════════════════════

/-- If S ⊆ T, covering T also covers S -/
lemma covering_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset (Finset V)) (hST : S ⊆ T) :
    triangleCoveringNumberOn G S ≤ triangleCoveringNumberOn G T := by
  unfold triangleCoveringNumberOn
  apply Nat.sInf_le_sInf
  intro n hn
  obtain ⟨E, hE_card, hE_sub, hE_cover⟩ := hn
  exact ⟨E, hE_card, hE_sub, fun t ht => hE_cover t (hST ht)⟩

/-- Covering a union requires at most the sum of individual covering numbers -/
theorem covering_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (S₁ S₂ : Finset (Finset V)) :
    triangleCoveringNumberOn G (S₁ ∪ S₂) ≤
    triangleCoveringNumberOn G S₁ + triangleCoveringNumberOn G S₂ := by
  by_contra h_contra;
  rw [ triangleCoveringNumberOn ] at h_contra;
  -- Let $E₁$ and $E₂$ be edge covers for $S₁$ and $S₂$, respectively.
  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : Finset (Sym2 V), E₁ ⊆ G.edgeFinset ∧ (∀ T ∈ S₁, ∃ e ∈ E₁, e ∈ T.sym2.filter (· ∈ G.edgeFinset)) ∧ E₁.card = triangleCoveringNumberOn G S₁ := by
    have h_exists_E₁ : ∃ E₁ : Finset (Sym2 V), E₁ ⊆ G.edgeFinset ∧ (∀ T ∈ S₁, ∃ e ∈ E₁, e ∈ T.sym2.filter (· ∈ G.edgeFinset)) := by
      push_neg at h_contra;
      have := Nat.sInf_mem ( show { n : ℕ | ∃ E : Finset ( Sym2 V ), #E = n ∧ E ⊆ G.edgeFinset ∧ ∀ T ∈ S₁ ∪ S₂, ∃ e ∈ E, e ∈ { x ∈ T.sym2 | x ∈ G.edgeFinset } }.Nonempty from ?_ );
      · exact ⟨ this.choose, this.choose_spec.2.1, fun T hT => this.choose_spec.2.2 T ( Finset.mem_union_left _ hT ) ⟩;
      · exact Nat.nonempty_of_pos_sInf ( pos_of_gt h_contra );
    obtain ⟨E₁, hE₁⟩ : ∃ E₁ : Finset (Sym2 V), E₁ ⊆ G.edgeFinset ∧ (∀ T ∈ S₁, ∃ e ∈ E₁, e ∈ T.sym2.filter (· ∈ G.edgeFinset)) ∧ ∀ E₂ : Finset (Sym2 V), E₂ ⊆ G.edgeFinset → (∀ T ∈ S₁, ∃ e ∈ E₂, e ∈ T.sym2.filter (· ∈ G.edgeFinset)) → E₁.card ≤ E₂.card := by
      have h_exists_E₁_min : ∃ E₁ ∈ {E : Finset (Sym2 V) | E ⊆ G.edgeFinset ∧ (∀ T ∈ S₁, ∃ e ∈ E, e ∈ T.sym2.filter (· ∈ G.edgeFinset))}, ∀ E₂ ∈ {E : Finset (Sym2 V) | E ⊆ G.edgeFinset ∧ (∀ T ∈ S₁, ∃ e ∈ E, e ∈ T.sym2.filter (· ∈ G.edgeFinset))}, E₁.card ≤ E₂.card := by
        apply_rules [ Set.exists_min_image ];
        exact Set.finite_iff_bddAbove.mpr ⟨ G.edgeFinset, fun E hE => Finset.le_iff_subset.mpr hE.1 ⟩;
      exact ⟨ h_exists_E₁_min.choose, h_exists_E₁_min.choose_spec.1.1, h_exists_E₁_min.choose_spec.1.2, fun E₂ hE₂₁ hE₂₂ => h_exists_E₁_min.choose_spec.2 E₂ ⟨ hE₂₁, hE₂₂ ⟩ ⟩;
    refine' ⟨ E₁, hE₁.1, hE₁.2.1, le_antisymm _ _ ⟩;
    · exact le_csInf ⟨ _, ⟨ E₁, rfl, hE₁.1, hE₁.2.1 ⟩ ⟩ fun n hn => hn.choose_spec.1 ▸ hE₁.2.2 _ hn.choose_spec.2.1 hn.choose_spec.2.2;
    · exact Nat.sInf_le ⟨ E₁, rfl, hE₁.1, hE₁.2.1 ⟩
  obtain ⟨E₂, hE₂⟩ : ∃ E₂ : Finset (Sym2 V), E₂ ⊆ G.edgeFinset ∧ (∀ T ∈ S₂, ∃ e ∈ E₂, e ∈ T.sym2.filter (· ∈ G.edgeFinset)) ∧ E₂.card = triangleCoveringNumberOn G S₂ := by
    have := Nat.sInf_mem ( show { n : ℕ | ∃ E : Finset ( Sym2 V ), #E = n ∧ E ⊆ G.edgeFinset ∧ ∀ T ∈ S₂, ∃ e ∈ E, e ∈ T.sym2.filter ( · ∈ G.edgeFinset ) }.Nonempty from ?_ );
    · exact ⟨ this.choose, this.choose_spec.2.1, this.choose_spec.2.2, this.choose_spec.1 ⟩;
    · exact ⟨ _, ⟨ G.edgeFinset, rfl, Finset.Subset.refl _, fun T hT => by
        simp_all +decide [ Finset.ext_iff ];
        contrapose! h_contra;
        rw [ Nat.sInf_eq_zero.mpr ];
        · exact Nat.zero_le _;
        · exact Or.inr <| Set.eq_empty_of_forall_notMem fun n hn => by obtain ⟨ E, hE₁, hE₂, hE₃ ⟩ := hn; obtain ⟨ e, he₁, he₂, he₃ ⟩ := hE₃ T ( Or.inr hT ) ; exact h_contra e he₃ he₂ he₃; ⟩ ⟩;
  refine' h_contra ( le_trans ( Nat.sInf_le _ ) _ );
  exact # ( E₁ ∪ E₂ );
  · refine' ⟨ E₁ ∪ E₂, rfl, Finset.union_subset hE₁.1 hE₂.1, _ ⟩;
    grind;
  · exact le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( hE₁.2.2.le ) ( hE₂.2.2.le ) )

-- Standard subadditivity argument

/-- Four-way union bound -/
theorem covering_union4_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (S₁ S₂ S₃ S₄ : Finset (Finset V)) :
    triangleCoveringNumberOn G (S₁ ∪ S₂ ∪ S₃ ∪ S₄) ≤
    triangleCoveringNumberOn G S₁ + triangleCoveringNumberOn G S₂ +
    triangleCoveringNumberOn G S₃ + triangleCoveringNumberOn G S₄ := by
  calc triangleCoveringNumberOn G (S₁ ∪ S₂ ∪ S₃ ∪ S₄)
      ≤ triangleCoveringNumberOn G (S₁ ∪ S₂ ∪ S₃) + triangleCoveringNumberOn G S₄ :=
          covering_union_le_sum G (S₁ ∪ S₂ ∪ S₃) S₄
    _ ≤ triangleCoveringNumberOn G (S₁ ∪ S₂) + triangleCoveringNumberOn G S₃ +
        triangleCoveringNumberOn G S₄ := by
          have h := covering_union_le_sum G (S₁ ∪ S₂) S₃
          omega
    _ ≤ triangleCoveringNumberOn G S₁ + triangleCoveringNumberOn G S₂ +
        triangleCoveringNumberOn G S₃ + triangleCoveringNumberOn G S₄ := by
          have h := covering_union_le_sum G S₁ S₂
          omega

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY THEOREM: If triangles partition into 4 sets, each coverable by 2 edges
-- ══════════════════════════════════════════════════════════════════════════════

/--
PROOF SKETCH:
1. All triangles in S₁ ∪ S₂ ∪ S₃ ∪ S₄ (by partition hypothesis)
2. Each Sᵢ coverable by ≤ 2 edges (by local bound)
3. By subadditivity: τ(union) ≤ τ(S₁) + τ(S₂) + τ(S₃) + τ(S₄) ≤ 2+2+2+2 = 8
4. By coverage: τ(G) ≤ τ(union) ≤ 8
-/
theorem tau_le_8_from_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (S₁ S₂ S₃ S₄ : Finset (Finset V))
    (h_cover : G.cliqueFinset 3 ⊆ S₁ ∪ S₂ ∪ S₃ ∪ S₄)
    (h₁ : triangleCoveringNumberOn G S₁ ≤ 2)
    (h₂ : triangleCoveringNumberOn G S₂ ≤ 2)
    (h₃ : triangleCoveringNumberOn G S₃ ≤ 2)
    (h₄ : triangleCoveringNumberOn G S₄ ≤ 2) :
    triangleCoveringNumber G ≤ 8 := by
  -- Use: τ(G) = τ(cliqueFinset 3) ≤ τ(S₁ ∪ S₂ ∪ S₃ ∪ S₄)
  rw [← covering_number_on_all_triangles]
  calc triangleCoveringNumberOn G (G.cliqueFinset 3)
      ≤ triangleCoveringNumberOn G (S₁ ∪ S₂ ∪ S₃ ∪ S₄) := covering_mono G _ _ h_cover
    _ ≤ triangleCoveringNumberOn G S₁ + triangleCoveringNumberOn G S₂ +
        triangleCoveringNumberOn G S₃ + triangleCoveringNumberOn G S₄ :=
          covering_union4_le_sum G S₁ S₂ S₃ S₄
    _ ≤ 2 + 2 + 2 + 2 := by omega
    _ = 8 := by norm_num

-- ══════════════════════════════════════════════════════════════════════════════
-- APPLICATION: PATH_4 τ ≤ 8
-- ══════════════════════════════════════════════════════════════════════════════

/-- S_e: triangles sharing edge with packing element e -/
def trianglesSharingEdgeGeneral (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) : Finset (Finset V) :=
  G.cliqueFinset 3 |>.filter (fun T => (T ∩ e).card ≥ 2)

/-- For PATH_4 with τ(S_A) ≤ 2, τ(S_B) ≤ 2, τ(S_C) ≤ 2, τ(S_D) ≤ 2
    and all triangles in S_A ∪ S_B ∪ S_C ∪ S_D, we get τ ≤ 8 -/
theorem tau_le_8_path4_assembly (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V)
    (h_partition : G.cliqueFinset 3 ⊆
        trianglesSharingEdgeGeneral G A ∪ trianglesSharingEdgeGeneral G B ∪
        trianglesSharingEdgeGeneral G C ∪ trianglesSharingEdgeGeneral G D)
    (hA : triangleCoveringNumberOn G (trianglesSharingEdgeGeneral G A) ≤ 2)
    (hB : triangleCoveringNumberOn G (trianglesSharingEdgeGeneral G B) ≤ 2)
    (hC : triangleCoveringNumberOn G (trianglesSharingEdgeGeneral G C) ≤ 2)
    (hD : triangleCoveringNumberOn G (trianglesSharingEdgeGeneral G D) ≤ 2) :
    triangleCoveringNumber G ≤ 8 :=
  tau_le_8_from_partition G
    (trianglesSharingEdgeGeneral G A) (trianglesSharingEdgeGeneral G B)
    (trianglesSharingEdgeGeneral G C) (trianglesSharingEdgeGeneral G D)
    h_partition hA hB hC hD

end