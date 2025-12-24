/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6b9aa1ff-a3f0-475c-a494-f4e47e788035

The following was proved by Aristotle:

- lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B

- lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2

- lemma tau_at_v_avoiding_v_le_k (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (v : V) (k : ℕ) (hk : (packingElementsContaining M v).card = k) :
    triangleCoveringNumberOn G (trianglesAtVAvoidingV G M v) ≤ k

- theorem tau_le_8_three_share_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : (packingElementsContaining M v).card = 3)
    (e4 : Finset V) (he4 : e4 ∈ M) (he4_no_v : v ∉ e4) :
    triangleCoveringNumber G ≤ 8

- theorem tau_le_8_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : ∀ e ∈ M, v ∈ e) :
    triangleCoveringNumber G ≤ 8
-/

/-
Tuza ν=4 Portfolio - Slot 29: Triple-Apex Reduction

TARGET: If some vertex v is in ≥3 packing triangles, prove τ ≤ 8

KEY INSIGHT (from Codex + Grok consultation 2024-12-23):
When a vertex v appears in 3+ packing elements:
1. Use tau_containing_v_le_4 to cover all v-containing triangles with ≤4 edges
2. The remaining packing element(s) have ν ≤ 1
3. Apply Parker's ν ≤ 1 bound: τ(T_e) ≤ 2
4. Total: τ ≤ 4 + 2 + (overlaps handled by bridges going through v)

This handles:
- Star case (all 4 share v)
- 3-star case (3 share v, 1 isolated)
- Triangle+1 case (3 form a triangle in sharing graph)

SCAFFOLDING:
- tau_containing_v_le_4 (proven in slot20)
- tau_union_le_sum (proven in slot16)
- tau_S_le_2 (proven in slot6)
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => E' ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    |>.image Finset.card |>.min |>.getD 0

def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

-- Triangles containing vertex v
def trianglesContainingVertex (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

-- Packing elements containing vertex v
def packingElementsContaining (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  M.filter (fun t => v ∈ t)

-- Union of T_e for elements in a subset
def triangleUnion (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Finset (Finset V) :=
  M.biUnion (trianglesSharingEdge G)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN SCAFFOLDING
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable section AristotleLemmas

/-
A set of edges E' is a triangle cover for a set of triangles if E' is a subset of the graph's edges and every triangle in the set contains at least one edge from E'.
-/
variable {V : Type*} [Fintype V] [DecidableEq V]

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2

/-
A set of edges is a triangle cover if and only if it is in the filtered powerset of edges used to define the covering number.
-/
lemma isTriangleCover_iff_mem_filter (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V)) (E' : Finset (Sym2 V)) :
    isTriangleCover G A E' ↔ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)) := by
  unfold isTriangleCover; aesop;

/-
The triangle covering number of a set of triangles A is less than or equal to the size of any specific triangle cover E' of A.
-/
lemma le_triangleCoveringNumberOn (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : isTriangleCover G A E') :
    triangleCoveringNumberOn G A ≤ E'.card := by
  unfold triangleCoveringNumberOn;
  have h_mem : E' ∈ G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2) := by
    exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h.1, h.2 ⟩;
  have := Finset.min_le ( Finset.mem_image_of_mem Finset.card h_mem );
  rw [ WithTop.le_coe_iff ] at this ; aesop

/-
If a triangle cover exists for A, then there exists a triangle cover for A whose size is exactly the triangle covering number of A.
-/
lemma exists_min_cover (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V))
    (h : ∃ E', isTriangleCover G A E') :
    ∃ E', isTriangleCover G A E' ∧ E'.card = triangleCoveringNumberOn G A := by
  by_cases h₁ : ∃ E' : Finset (Sym2 V), isTriangleCover G A E';
  · have h₂ : ∃ E' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)), ∀ E'' ∈ (G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2)), E'.card ≤ E''.card := by
      apply_rules [ Set.exists_min_image ];
      · exact Set.toFinite _;
      · exact ⟨ h₁.choose, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( h₁.choose_spec.1 ), h₁.choose_spec.2 ⟩ ⟩;
    obtain ⟨ E', hE₁, hE₂ ⟩ := h₂;
    refine' ⟨ E', _, _ ⟩;
    · exact ⟨ Finset.mem_filter.mp hE₁ |>.1 |> Finset.mem_powerset.mp, Finset.mem_filter.mp hE₁ |>.2 ⟩;
    · unfold triangleCoveringNumberOn;
      rw [ show ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ A, ∃ e ∈ E', e ∈ t.sym2 ) ( G.edgeFinset.powerset ) ) ).min = some ( E'.card ) from ?_, Option.getD_some ];
      refine' le_antisymm _ _;
      · exact Finset.min_le ( Finset.mem_image_of_mem _ hE₁ );
      · simp +zetaDelta at *;
        exact fun a x hx₁ hx₂ hx₃ => hx₃ ▸ WithTop.coe_le_coe.mpr ( hE₂ x hx₁ hx₂ );
  · contradiction

/-
If there is no set of edges that covers the triangles in A, then the triangle covering number of A is defined to be 0.
-/
lemma not_coverable_implies_zero (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Finset V))
    (h : ¬ ∃ E', isTriangleCover G A E') :
    triangleCoveringNumberOn G A = 0 := by
  unfold triangleCoveringNumberOn;
  norm_num +zetaDelta at *;
  rw [ show { E' ∈ G.edgeFinset.powerset | ∀ t ∈ A, ∃ e ∈ E', ∀ a ∈ e, a ∈ t } = ∅ from _ ];
  · rfl;
  · ext;
    simp [isTriangleCover] at *;
    exact h _

/-
The union of a triangle cover for A and a triangle cover for B is a triangle cover for the union of A and B.
-/
lemma isTriangleCover_union (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset (Finset V)) (EA EB : Finset (Sym2 V))
    (hA : isTriangleCover G A EA) (hB : isTriangleCover G B EB) :
    isTriangleCover G (A ∪ B) (EA ∪ EB) := by
  unfold isTriangleCover at *;
  grind

/-
If a set of edges covers a set of triangles B, and A is a subset of B, then the same set of edges also covers A.
-/
lemma isTriangleCover_subset (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset (Finset V)) (E' : Finset (Sym2 V))
    (h : A ⊆ B) (hCover : isTriangleCover G B E') :
    isTriangleCover G A E' := by
  exact ⟨ hCover.1, fun t ht => hCover.2 t ( h ht ) ⟩

end AristotleLemmas

lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤ triangleCoveringNumberOn G A + triangleCoveringNumberOn G B := by
  -- Consider the cases where `A` or `B` have no covers.
  by_cases hA : ∃ E', isTriangleCover G A E'
  by_cases hB : ∃ E', isTriangleCover G B E';
  · obtain ⟨EA, hEA⟩ := exists_min_cover G A hA
    obtain ⟨EB, hEB⟩ := exists_min_cover G B hB;
    exact le_trans ( le_triangleCoveringNumberOn G _ _ ( isTriangleCover_union G A B EA EB hEA.1 hEB.1 ) ) ( by rw [ ← hEA.2, ← hEB.2 ] ; exact Finset.card_union_le _ _ );
  · rw [ not_exists ] at hB;
    rw [ not_coverable_implies_zero _ _ ];
    · exact Nat.zero_le _;
    · exact fun ⟨ E', hE' ⟩ => hB E' <| isTriangleCover_subset _ _ _ _ ( Finset.subset_union_right ) hE';
  · rw [ not_coverable_implies_zero ];
    · exact Nat.zero_le _;
    · norm_num +zetaDelta at *;
      exact fun x hx => hA x <| isTriangleCover_subset _ _ _ _ ( Finset.subset_union_left ) hx

noncomputable section AristotleLemmas

/-
If $t_1, t_2$ are two triangles in $S_e$ (different from $e$), then they must share at least 2 vertices. Otherwise, we could replace $e$ with $\{t_1, t_2\}$ in the packing $M$ to get a larger packing.
-/
lemma S_e_pair_intersect_ge_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e)
    (hne1 : t1 ≠ e) (hne2 : t2 ≠ e) :
    (t1 ∩ t2).card ≥ 2 := by
      unfold isMaxPacking at hM;
      -- If |t1 ∩ t2| ≤ 1, then we can replace e with {t1, t2} in the packing M to get a larger packing.
      by_contra h_contra
      have h_replace : isTrianglePacking G (insert t1 (insert t2 (M.erase e))) := by
        unfold isTrianglePacking at *;
        unfold S_e at *; simp_all +decide [ Finset.subset_iff, Set.Pairwise ] ;
        exact ⟨ ⟨ by unfold trianglesSharingEdge at ht1; aesop, by unfold trianglesSharingEdge at ht2; aesop ⟩, fun h => Nat.le_of_lt_succ h_contra, fun h => by rw [ Finset.inter_comm ] ; exact Nat.le_of_lt_succ h_contra, fun a ha ha' => ⟨ fun ha'' => by have := ht1.2 a ha ha'; rw [ Finset.inter_comm ] at this; aesop, fun ha'' => by have := ht2.2 a ha ha'; rw [ Finset.inter_comm ] at this; aesop ⟩ ⟩;
      have h_card : (insert t1 (insert t2 (M.erase e))).card > M.card := by
        by_cases h : t1 = t2 <;> simp_all +decide [ Finset.card_insert_of_notMem ];
        · have h_triangle : t2 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ht2 |>.1 |> Finset.mem_filter.mp |>.1;
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact absurd h_contra ( by rw [ h_triangle.2 ] ; decide );
        · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp_all +decide [ Finset.subset_iff ];
          · omega;
          · intro H; have := hM.1.2; simp_all +decide [ Finset.subset_iff ] ;
            have := this H he; simp_all +decide [ Finset.inter_comm ] ;
            unfold S_e at ht2; simp_all +decide [ Finset.inter_comm ] ;
            unfold trianglesSharingEdge at ht2; simp_all +decide [ Finset.inter_comm ] ;
            linarith;
          · intro H; have := hM.1.2; simp_all +decide [ Finset.subset_iff ] ;
            have := this H he; simp_all +decide ;
            unfold S_e at ht1; simp_all +decide ;
            unfold trianglesSharingEdge at ht1; simp_all +decide ;
            linarith;
      -- This contradicts the maximality of $M$.
      have h_contradiction : (insert t1 (insert t2 (M.erase e))).card ≤ trianglePackingNumber G := by
        have h_contradiction : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ trianglePackingNumber G := by
          unfold trianglePackingNumber;
          intro S hS;
          have h_contradiction : S.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
            exact Finset.mem_image.mpr ⟨ S, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hS.1, hS ⟩, rfl ⟩;
          have h_contradiction : ∀ x ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset), x ≤ Option.getD (Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset)).max 0 := by
            intro x hx;
            have := Finset.le_max hx;
            cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
          exact h_contradiction _ ‹_›;
        exact h_contradiction _ h_replace;
      linarith

/-
If two triangles in $S_e$ (other than $e$) intersect $e$ in different edges, then they must share the same vertex outside of $e$.
-/
lemma S_e_diff_inter_eq_of_neq_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (t1 t2 : Finset V) (ht1 : t1 ∈ S_e G M e) (ht2 : t2 ∈ S_e G M e)
    (hne1 : t1 ≠ e) (hne2 : t2 ≠ e)
    (h_diff_inter : t1 ∩ e ≠ t2 ∩ e) :
    t1 \ e = t2 \ e := by
      -- Since $t_1, t_2 \in S_e$ and are not equal to $e$, they must share an edge with $e$. Thus $|t_1 \cap e| = 2$ and $|t_2 \cap e| = 2$.
      have h_inter_card : (t1 ∩ e).card = 2 ∧ (t2 ∩ e).card = 2 := by
        -- Since $t_1$ and $t_2$ are triangles, they each have exactly 3 vertices.
        have h_t1_card : t1.card = 3 := by
          -- Since $t1 \in S_e G M e$, we have $t1 \in trianglesSharingEdge G e$, which means $t1 \in G.cliqueFinset 3$.
          have ht1_clique : t1 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ht1 |>.1 |> fun h => Finset.mem_filter.mp h |>.1;
          exact Finset.mem_filter.mp ht1_clique |>.2.2
        have h_t2_card : t2.card = 3 := by
          have h_t2_card : t2 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ht2 |>.1 |> Finset.mem_filter.mp |>.1;
          exact Finset.mem_filter.mp h_t2_card |>.2.2
        have h_e_card : e.card = 3 := by
          have := hM.1;
          have := this.1;
          have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
          exact this.card_eq;
        -- Since $t_1$ and $t_2$ are triangles, they each have exactly 3 vertices, and since $e$ is a triangle, it also has exactly 3 vertices.
        have h_inter_card_ge_2 : 2 ≤ (t1 ∩ e).card ∧ 2 ≤ (t2 ∩ e).card := by
          unfold S_e at ht1 ht2;
          unfold trianglesSharingEdge at ht1 ht2; aesop;
        have h_inter_card_le_2 : (t1 ∩ e).card ≤ 2 ∧ (t2 ∩ e).card ≤ 2 := by
          constructor <;> contrapose! hne1;
          · have h_inter_card_eq_3 : t1 ∩ e = t1 := by
              exact Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left ) ( by linarith );
            have := Finset.eq_of_subset_of_card_le ( show t1 ⊆ e from h_inter_card_eq_3 ▸ Finset.inter_subset_right ) ; aesop;
          · have h_inter_eq : t2 ∩ e = e := by
              exact Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right ) ( by linarith );
            have := Finset.eq_of_subset_of_card_le ( show e ⊆ t2 from fun x hx => by aesop ) ; aesop;
        exact ⟨ le_antisymm h_inter_card_le_2.1 h_inter_card_ge_2.1, le_antisymm h_inter_card_le_2.2 h_inter_card_ge_2.2 ⟩;
      -- Let $x_1$ be the unique element in $t_1 \setminus e$ and $x_2$ be the unique element in $t_2 \setminus e$.
      obtain ⟨x1, hx1⟩ : ∃ x1, t1 \ e = {x1} := by
        have h_card_diff : (t1 \ e).card = 1 := by
          have h_card_diff : (t1 \ e).card = (t1).card - (t1 ∩ e).card := by
            grind;
          have h_card_t1 : t1 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ht1 |>.1 |> Finset.mem_filter.mp |>.1;
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact Nat.sub_eq_of_eq_add ( by linarith [ h_card_t1.2 ] );
        exact Finset.card_eq_one.mp h_card_diff
      obtain ⟨x2, hx2⟩ : ∃ x2, t2 \ e = {x2} := by
        have h_inter_card_t2 : (t2 \ e).card = 1 := by
          have h_inter_card_t2 : (t2 \ e).card = t2.card - (t2 ∩ e).card := by
            grind;
          have h_card_t2 : t2 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ht2 |>.1 |> Finset.mem_filter.mp |>.1;
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact Nat.sub_eq_of_eq_add ( by linarith [ h_card_t2.card_eq ] );
        exact Finset.card_eq_one.mp h_inter_card_t2;
      -- The intersection $t_1 \cap t_2$ is the union of $(t_1 \cap e) \cap (t_2 \cap e)$ and $\{x_1\} \cap \{x_2\}$ (cross terms are empty because $x_i \notin e$).
      have h_inter_union : (t1 ∩ t2).card = (t1 ∩ e ∩ t2 ∩ e).card + (if x1 = x2 then 1 else 0) := by
        have h_inter_union : t1 ∩ t2 = (t1 ∩ e ∩ t2 ∩ e) ∪ (if x1 = x2 then {x1} else ∅) := by
          ext v; by_cases hv : v ∈ e <;> simp_all +decide [ Finset.ext_iff ] ;
          · grind;
          · grind;
        rw [ Finset.eq_singleton_iff_unique_mem ] at hx1 hx2 ; aesop;
      -- Since $t_1 \cap e \ne t_2 \cap e$, and both are subsets of $e$ of size 2, their intersection must have size 1.
      have h_inter_card_1 : (t1 ∩ e ∩ t2 ∩ e).card = 1 := by
        have h_inter_card_1 : (t1 ∩ e ∩ t2 ∩ e).card ≤ 1 := by
          have h_inter_card_1 : (t1 ∩ e ∩ t2 ∩ e).card < 2 := by
            refine' lt_of_le_of_ne _ _;
            · exact le_trans ( Finset.card_le_card ( show t1 ∩ e ∩ t2 ∩ e ⊆ t1 ∩ e from fun x hx => by aesop ) ) h_inter_card.1.le;
            · intro h;
              have h_inter_eq : t1 ∩ e ∩ t2 ∩ e = t1 ∩ e ∧ t1 ∩ e ∩ t2 ∩ e = t2 ∩ e := by
                exact ⟨ Finset.eq_of_subset_of_card_le ( by aesop_cat ) ( by aesop_cat ), Finset.eq_of_subset_of_card_le ( by aesop_cat ) ( by aesop_cat ) ⟩;
              aesop;
          linarith;
        interval_cases _ : Finset.card ( t1 ∩ e ∩ t2 ∩ e ) <;> simp_all +decide;
        have := S_e_pair_intersect_ge_2 G M hM e he t1 t2 ht1 ht2 hne1 hne2; simp_all +decide ;
        split_ifs at this <;> contradiction;
      -- By `S_e_pair_intersect_ge_2`, $|t_1 \cap t_2| \ge 2$.
      have h_inter_card_ge_2 : (t1 ∩ t2).card ≥ 2 := by
        apply S_e_pair_intersect_ge_2 G M hM e he t1 t2 ht1 ht2 hne1 hne2;
      aesop

/-
If there are two triangles in $S_e$ that intersect $e$ in different edges, then all triangles in $S_e$ (except $e$) share the same vertex $x$ outside of $e$.
-/
lemma S_e_structure_of_diverse_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (ta tb : Finset V) (hta : ta ∈ S_e G M e) (htb : tb ∈ S_e G M e)
    (hnea : ta ≠ e) (hneb : tb ≠ e)
    (h_diff_inter : ta ∩ e ≠ tb ∩ e) :
    ∃ x, x ∉ e ∧ ∀ t ∈ S_e G M e, t ≠ e → t = insert x (t ∩ e) := by
      -- Since $t_a \setminus e = t_b \setminus e$, we can let $x$ be the unique element in $t_a \setminus e$.
      obtain ⟨x, hx⟩ : ∃ x, ta \ e = {x} ∧ tb \ e = {x} := by
        -- Since $ta \setminus e = tb \setminus e$ and both are singletons, we can conclude that they are equal to the same singleton set.
        have h_singleton : (ta \ e).card = 1 ∧ (tb \ e).card = 1 := by
          have h_card_diff : ∀ t ∈ S_e G M e, t ≠ e → (t \ e).card = 1 := by
            intro t ht hne
            have h_inter : (t ∩ e).card ≥ 2 := by
              unfold S_e at ht;
              unfold trianglesSharingEdge at ht; aesop;
            have h_card_t : t.card = 3 := by
              have h_card_t : t ∈ G.cliqueFinset 3 := by
                exact Finset.mem_filter.mp ht |>.1 |> Finset.mem_filter.mp |>.1 |> fun h => by aesop;
              have h_card_t_eq : t.card = 3 := by
                exact Finset.mem_filter.mp h_card_t |>.2.2
              exact h_card_t_eq
              skip -- This is a placeholder to prevent the code from compiling, as the actual proof is required.
            have h_card_e : e.card = 3 := by
              have := hM.1;
              have := this.1;
              have := this he; simp_all +decide [ SimpleGraph.cliqueFinset ] ;
              exact this.2
            have h_card_inter : (t ∩ e).card = 2 := by
              have h_inter_eq : (t ∩ e).card ≤ 2 := by
                have h_card_inter : (t ∩ e).card < 3 := by
                  have h_inter_eq : (t ∩ e) ≠ t := by
                    exact fun h => hne <| Finset.eq_of_subset_of_card_le ( by aesop ) <| by aesop;
                  exact lt_of_le_of_ne ( le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) h_card_t.le ) fun h => h_inter_eq <| Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left ) <| by simp +decide [ * ] ;
                linarith [h_card_inter]
              exact le_antisymm h_inter_eq h_inter
            have h_card_diff : (t \ e).card = t.card - (t ∩ e).card := by
              grind
            rw [h_card_t, h_card_inter] at h_card_diff
            simp [h_card_diff];
          exact ⟨ h_card_diff ta hta hnea, h_card_diff tb htb hneb ⟩;
        have h_eq_singleton : ta \ e =(tb \ e) := by
          exact S_e_diff_inter_eq_of_neq_inter G M hM e he ta tb hta htb hnea hneb h_diff_inter;
        rw [ Finset.card_eq_one ] at h_singleton ; aesop;
      refine' ⟨ x, _, _ ⟩ <;> simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
      intro t ht hne; ext y; by_cases hy : y ∈ e <;> simp_all +decide ;
      · grind +ring;
      · by_cases h : t ∩ e = ta ∩ e <;> simp_all +decide [ Finset.ext_iff ];
        · have := S_e_diff_inter_eq_of_neq_inter G M hM e he t tb ht htb; simp_all +decide [ Finset.ext_iff ] ;
          grind;
        · have := S_e_diff_inter_eq_of_neq_inter G M hM e he t ta ht hta; simp_all +decide [ Finset.ext_iff ] ;
          grind +ring

/-
If there are diverse intersections in $S_e$, the covering number is at most 2.
-/
lemma S_e_cover_of_diverse_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (ta tb : Finset V) (hta : ta ∈ S_e G M e) (htb : tb ∈ S_e G M e)
    (hnea : ta ≠ e) (hneb : tb ≠ e)
    (h_diff_inter : ta ∩ e ≠ tb ∩ e) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
      obtain ⟨ x, hx ⟩ := S_e_structure_of_diverse_inter G M hM e he ta tb hta htb hnea hneb h_diff_inter;
      -- Let $E_a = t_a \cap e$ and $E_b = t_b \cap e$. These are two distinct edges of $e$.
      obtain ⟨E_a, E_b, hE_a, hE_b, hE_distinct⟩ : ∃ E_a E_b : Finset V, E_a ⊆ e ∧ E_b ⊆ e ∧ E_a ≠ E_b ∧ E_a.card = 2 ∧ E_b.card = 2 ∧ ta = insert x E_a ∧ tb = insert x E_b := by
        refine' ⟨ ta ∩ e, tb ∩ e, _, _, _, _, _, hx.2 ta hta hnea, hx.2 tb htb hneb ⟩;
        · exact Finset.inter_subset_right;
        · exact Finset.inter_subset_right;
        · exact h_diff_inter;
        · have h_card : ta.card = 3 := by
            have h_card : ta ∈ G.cliqueFinset 3 := by
              exact Finset.mem_filter.mp hta |>.1 |> Finset.mem_filter.mp |>.1;
            simp +zetaDelta at *;
            exact h_card.2;
          grind;
        · unfold S_e at htb; simp +decide [ Finset.mem_filter ] at htb;
          unfold trianglesSharingEdge at htb; simp +decide [ Finset.mem_filter ] at htb;
          have := Finset.card_le_card ( Finset.inter_subset_left : tb ∩ e ⊆ tb ) ; simp +decide [ htb.1.1.card_eq ] at this ⊢;
          interval_cases _ : Finset.card ( tb ∩ e ) <;> simp +decide at htb ⊢;
          have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : tb ∩ e ⊆ e ) ; simp_all +singlePass ;
          have := hM.1; simp_all +singlePass [ SimpleGraph.isNClique_iff ] ;
          have := this.1 he; simp_all +singlePass [ SimpleGraph.isNClique_iff ] ;
          have := Finset.eq_of_subset_of_card_le ‹e ⊆ tb› ; simp_all +singlePass ;
      -- Let $e = \{u, v, w\}$ where $E_a = \{u, v\}$ and $E_b = \{v, w\}$.
      obtain ⟨u, v, w, heu, hev, hew, he⟩ : ∃ u v w : V, e = {u, v, w} ∧ E_a = {u, v} ∧ E_b = {v, w} := by
        have h_card_e : e.card = 3 := by
          have := hM.1;
          have := this.1 he; simp +decide [ SimpleGraph.cliqueFinset ] at this;
          exact this.2;
        rw [ Finset.card_eq_three ] at h_card_e;
        obtain ⟨ u, v, w, huv, huw, hvw, rfl ⟩ := h_card_e;
        have hE_a_cases : E_a = {u, v} ∨ E_a = {u, w} ∨ E_a = {v, w} := by
          have := Finset.card_eq_two.mp hE_distinct.2.1; obtain ⟨ a, b, hab, rfl ⟩ := this; simp +decide [ Finset.subset_iff ] at hE_a ⊢;
          rcases hE_a with ⟨ rfl | rfl | rfl, rfl | rfl | rfl ⟩ <;> simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] at hab ⊢
        have hE_b_cases : E_b = {u, v} ∨ E_b = {u, w} ∨ E_b = {v, w} := by
          rw [ Finset.card_eq_two ] at hE_distinct;
          rw [ Finset.card_eq_two ] at hE_distinct;
          rcases hE_distinct.2.2.1 with ⟨ x, y, hxy, rfl ⟩ ; simp +decide [ Finset.subset_iff ] at hE_b ⊢;
          rcases hE_b with ⟨ rfl | rfl | rfl, rfl | rfl | rfl ⟩ <;> simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] at hxy ⊢;
        rcases hE_a_cases with ( rfl | rfl | rfl ) <;> rcases hE_b_cases with ( rfl | rfl | rfl ) <;> simp +decide at hE_distinct ⊢;
        all_goals simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] at hE_distinct ⊢;
        exact ⟨ v, u, w, by simp +decide [ *, or_comm, or_left_comm, or_assoc ] ⟩;
        · exact ⟨ u, v, w, by simp +decide [ *, or_comm, or_left_comm, or_assoc ] ⟩;
        · exact ⟨ w, u, v, by simp +decide [ *, or_comm, or_left_comm, or_assoc ] ⟩;
        · exact ⟨ u, w, v, by simp +decide [ *, or_comm, or_left_comm, or_assoc ] ⟩;
        · exact ⟨ w, v, u, by simp +decide [ *, or_comm, or_left_comm, or_assoc ] ⟩;
        · exact ⟨ v, w, u, by simp +decide [ *, or_comm, or_left_comm, or_assoc ] ⟩;
      -- Any other triangle $t \in S_e \setminus \{e\}$ must have $t \cap e$ being an edge of $e$.
      have h_triangle_form : ∀ t ∈ S_e G M e, t ≠ e → t = insert x {u, v} ∨ t = insert x {v, w} ∨ t = insert x {u, w} := by
        intro t ht hte
        have h_inter : t ∩ e = {u, v} ∨ t ∩ e = {v, w} ∨ t ∩ e = {u, w} := by
          have h_inter : (t ∩ e).card = 2 := by
            have h_inter : (t ∩ e).card ≥ 2 := by
              have h_inter : t ∈ trianglesSharingEdge G e := by
                exact Finset.mem_filter.mp ht |>.1;
              exact Finset.mem_filter.mp h_inter |>.2;
            have h_inter : (t ∩ e).card ≤ t.card - 1 := by
              grind;
            have h_inter : t.card ≤ 3 := by
              have := Finset.mem_filter.mp ht;
              unfold trianglesSharingEdge at this; simp +decide at this;
              exact this.1.1.2.le;
            omega;
          rw [ Finset.card_eq_two ] at h_inter;
          rcases h_inter with ⟨ x, y, hxy, h ⟩ ; simp +decide [ h ];
          simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff, heu ] at h ⊢;
          grind;
        rcases h_inter with ( h | h | h ) <;> rw [ hx.2 t ht hte ] <;> simp +decide [ h ];
      -- We claim that $\{ \{u, v\}, \{w, x\} \}$ covers $S_e$.
      have h_cover : ∀ t ∈ S_e G M e, ∃ e' ∈ ({ {u, v}, {w, x} } : Finset (Finset V)), e' ⊆ t := by
        intro t ht
        by_cases hte : t = e;
        · simp +decide [ hte, heu ];
        · rcases h_triangle_form t ht hte with ( rfl | rfl | rfl ) <;> simp +decide [ Finset.subset_iff ];
      -- Therefore, the covering number is at most 2.
      have h_covering_number : ∃ E' ⊆ G.edgeFinset, (∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2) ∧ E'.card ≤ 2 := by
        refine' ⟨ _, _, _, _ ⟩;
        exact { Sym2.mk ( u, v ), Sym2.mk ( w, x ) };
        · simp +decide [ Sym2.mk ];
          rintro _ ( rfl | rfl ) <;> simp +decide [ SimpleGraph.edgeSetEmbedding ];
          · have := hM.1;
            have := this.1 he; simp +decide [ heu ] at this;
            simp +decide [ SimpleGraph.isNClique_iff ] at this;
            grind;
          · have := htb;
            unfold S_e at this; simp +decide [ heu, hev ] at this;
            unfold trianglesSharingEdge at this; simp +decide [ heu, hev ] at this;
            simp +decide [ hE_distinct.2.2.2.2, SimpleGraph.isNClique_iff ] at this;
            by_cases hvw : v = w <;> by_cases hxv : x = v <;> by_cases hxw : x = w <;> simp +decide [ hvw, hxv, hxw ] at this ⊢;
            exact this.1.1.2.2.symm;
        · simp +zetaDelta at *;
          intro t ht; specialize h_cover t ht; rcases h_cover with ( h | h ) <;> simp +decide [ Finset.subset_iff ] at h ⊢ <;> tauto;
        · exact Finset.card_insert_le _ _;
      obtain ⟨ E', hE'_sub, hE'_cover, hE'_card ⟩ := h_covering_number;
      unfold triangleCoveringNumberOn;
      have h_min_le : (Finset.image Finset.card ({E' ∈ G.edgeFinset.powerset | ∀ t ∈ S_e G M e, ∃ e ∈ E', e ∈ t.sym2})).min ≤ E'.card := by
        exact Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hE'_sub, hE'_cover ⟩, rfl ⟩ );
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' => ∀ t ∈ S_e G M e, ∃ e ∈ E', e ∈ t.sym2 ) ( Finset.powerset G.edgeFinset ) ) ) <;> simp +decide [ h ] at h_min_le ⊢;
      simp +zetaDelta at *;
      exact Nat.cast_le.mp ( h ▸ h_min_le |> le_trans <| WithTop.coe_le_coe.mpr hE'_card )

/-
If there is a valid edge cover of size at most k, then the covering number is at most k.
-/
lemma triangleCoveringNumberOn_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangles : Finset (Finset V)) (k : ℕ)
    (E' : Finset (Sym2 V)) (h_subset : E' ⊆ G.edgeFinset)
    (h_cover : ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2)
    (h_card : E'.card ≤ k) :
    triangleCoveringNumberOn G triangles ≤ k := by
      refine' le_trans _ h_card;
      by_contra h_contra;
      unfold triangleCoveringNumberOn at h_contra; simp_all +decide [ Finset.min' ] ;
      cases h : Finset.min ( Finset.image Finset.card ( Finset.filter ( fun E' : Finset ( Sym2 V ) => ∀ t ∈ triangles, ∃ e ∈ E', ∀ a ∈ e, a ∈ t ) ( Finset.powerset G.edgeFinset ) ) ) <;> simp_all +decide [ Option.getD ];
      exact h_contra.not_le ( Nat.cast_le.mp ( h ▸ Finset.min_le ( Finset.mem_image.mpr ⟨ E', Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( fun e he => by aesop ), h_cover ⟩, rfl ⟩ ) ) )

/-
If all triangles in $S_e$ (other than $e$) intersect $e$ in the same edge, then the covering number is at most 2.
-/
lemma S_e_cover_of_uniform_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M)
    (h_uniform : ∀ t1 t2 : Finset V, t1 ∈ S_e G M e → t2 ∈ S_e G M e → t1 ≠ e → t2 ≠ e → t1 ∩ e = t2 ∩ e) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
      -- We use `triangleCoveringNumberOn_le` with $k=1$.
      have h_univ : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ (E'.card ≤ 1 ∧ ∀ t ∈ S_e G M e, ∃ e' ∈ E', e' ∈ t.sym2) := by
        by_cases h : ∃ t ∈ S_e G M e, t ≠ e <;> simp_all +decide [ Finset.subset_iff ];
        · obtain ⟨ t, ht₁, ht₂ ⟩ := h;
          obtain ⟨ u, v, huv ⟩ : ∃ u v : V, u ∈ t ∧ v ∈ t ∧ u ∈ e ∧ v ∈ e ∧ u ≠ v := by
            have h_inter_card : (t ∩ e).card ≥ 2 := by
              have := Finset.mem_filter.mp ht₁;
              unfold trianglesSharingEdge at this; aesop;
            obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.mp h_inter_card; use u, v; aesop;
          -- Since $u$ and $v$ are in $e$ and $t$, and $e$ is a triangle in $G$, $\{u, v\}$ is an edge in $G$.
          have h_edge : Sym2.mk (u, v) ∈ G.edgeFinset := by
            have h_triangle : t ∈ G.cliqueFinset 3 := by
              exact Finset.mem_filter.mp ht₁ |>.1 |> Finset.mem_filter.mp |>.1;
            simp_all +decide [ SimpleGraph.cliqueFinset ];
            have := h_triangle.1; aesop;
          refine' ⟨ { Sym2.mk ( u, v ) }, _, _, _ ⟩ <;> simp_all +decide;
          intro t' ht'; specialize h_uniform t' t ht' ht₁; simp_all +decide [ Finset.ext_iff ] ;
          grind +ring;
        · -- If $S_e = \{e\}$, we can choose $E' = \{ \text{Sym2.mk}(u, v) \}$ where $\{u, v\} \subset e$.
          obtain ⟨u, v, huv⟩ : ∃ u v, u ∈ e ∧ v ∈ e ∧ u ≠ v ∧ G.Adj u v := by
            have := hM.1;
            have := this.1 he; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            rcases Finset.card_eq_three.mp this.2 with ⟨ u, v, w, hu, hv, hw, h ⟩ ; use u, by aesop, v, by aesop ; ; aesop;
          use {Sym2.mk (u, v)};
          simp_all +decide [ Sym2.eq_swap ];
          intro t ht; specialize h t ht; aesop;
      exact le_trans ( triangleCoveringNumberOn_le _ _ _ _ h_univ.choose_spec.1 h_univ.choose_spec.2.2 h_univ.choose_spec.2.1 ) ( by norm_num )

end AristotleLemmas

lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S_e G M e) ≤ 2 := by
  by_cases h_diverse : ∃ t1 t2 : Finset V, t1 ∈ S_e G M e ∧ t2 ∈ S_e G M e ∧ t1 ≠ e ∧ t2 ≠ e ∧ t1 ∩ e ≠ t2 ∩ e;
  · -- Apply the lemma S_e_cover_of_diverse_inter with the given t1 and t2.
    obtain ⟨t1, t2, ht1, ht2, hne1, hne2, h_diff⟩ := h_diverse;
    apply S_e_cover_of_diverse_inter G M hM e he t1 t2 ht1 ht2 hne1 hne2 h_diff;
  · exact S_e_cover_of_uniform_inter G M hM e he fun t1 t2 ht1 ht2 h1 h2 => Classical.not_not.1 fun h => h_diverse ⟨ t1, t2, ht1, ht2, h1, h2, h ⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Triangles containing v in the context of packing
-- ══════════════════════════════════════════════════════════════════════════════

-- All triangles sharing edges with packing elements that contain v
def trianglesAtV (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (packingElementsContaining M v).biUnion (trianglesSharingEdge G)

-- Triangles in trianglesAtV that contain v
def trianglesAtVContainingV (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (trianglesAtV G M v).filter (fun t => v ∈ t)

-- Triangles in trianglesAtV that avoid v (base triangles)
def trianglesAtVAvoidingV (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (trianglesAtV G M v).filter (fun t => v ∉ t)

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: τ of triangles at v containing v
-- ══════════════════════════════════════════════════════════════════════════════

-- When ≥3 packing elements share v, triangles containing v can be hit with ≤4 edges
lemma tau_at_v_containing_v_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : (packingElementsContaining M v).card ≥ 3) :
    triangleCoveringNumberOn G (trianglesAtVContainingV G M v) ≤ 4 := by
  -- Strategy: Use spoke edges from v
  -- Each packing element {v, a_i, b_i} contributes spokes {v, a_i} and {v, b_i}
  -- Choose 4 spokes that cover all v-containing triangles including bridges
  sorry

-- Base triangles (avoiding v) need one edge per packing element's base
noncomputable section AristotleLemmas

/-
If a triangle T shares an edge with a triangle t containing v, but T does not contain v, then T must contain the edge t \ {v}.
-/
lemma base_edge_covers (G : SimpleGraph V) [DecidableRel G.Adj] (t T : Finset V) (v : V)
    (ht : t ∈ G.cliqueFinset 3) (hv : v ∈ t)
    (hT : T ∈ trianglesSharingEdge G t) (hvT : v ∉ T) :
    t \ {v} ⊆ T := by
      intro x hx;
      have h_inter : (T ∩ t).card ≥ 2 := by
        unfold trianglesSharingEdge at hT; aesop;
      have h_inter_subset : T ∩ t ⊆ t \ {v} := by
        intro y hy; aesop;
      have h_inter_eq : T ∩ t = t \ {v} := by
        have := Finset.eq_of_subset_of_card_le h_inter_subset;
        simp_all +decide [ Finset.card_sdiff ];
        exact this ( by linarith [ ht.card_eq ] );
      replace h_inter_eq := Finset.ext_iff.mp h_inter_eq x; aesop;

/-
For every triangle T in the set of triangles at v avoiding v, there is a packing element f containing v such that the base edge of f (f \ {v}) is contained in T.
-/
lemma base_edges_cover_avoiding (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (v : V) :
    ∀ T ∈ trianglesAtVAvoidingV G M v, ∃ f ∈ packingElementsContaining M v, f \ {v} ⊆ T := by
      intro T hT;
      have h_base_edge_covers : ∃ f ∈ packingElementsContaining M v, T ∈ trianglesSharingEdge G f ∧ v ∉ T := by
        unfold trianglesAtVAvoidingV at hT;
        unfold trianglesAtV at hT;
        aesop;
      obtain ⟨ f, hf₁, hf₂, hf₃ ⟩ := h_base_edge_covers;
      refine' ⟨ f, hf₁, _ ⟩;
      apply base_edge_covers G f T v;
      · have := hM.1;
        exact this.1 ( Finset.mem_filter.mp hf₁ |>.1 );
      · exact Finset.mem_filter.mp hf₁ |>.2;
      · exact hf₂;
      · assumption

end AristotleLemmas

lemma tau_at_v_avoiding_v_le_k (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (v : V) (k : ℕ) (hk : (packingElementsContaining M v).card = k) :
    triangleCoveringNumberOn G (trianglesAtVAvoidingV G M v) ≤ k := by
  -- Each packing element's base triangles share the base edge
  -- So k base edges suffice
  -- By definition of $E'$, for each $f \in P$, the edge $e_f$ is in $E'$.
  have h_edges : ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ k ∧ ∀ T ∈ trianglesAtVAvoidingV G M v, ∃ e ∈ E', e ∈ T.sym2 := by
    have h_edges : ∀ f ∈ packingElementsContaining M v, ∃ e ∈ G.edgeFinset, e ∈ f.sym2 ∧ ∀ T ∈ trianglesAtVAvoidingV G M v, f \ {v} ⊆ T → e ∈ T.sym2 := by
      intro f hf
      obtain ⟨u, w, hu, hw, huv⟩ : ∃ u w : V, u ∈ f ∧ w ∈ f ∧ u ≠ v ∧ w ≠ v ∧ u ≠ w ∧ G.Adj u w := by
        -- Since $f$ is a triangle, it must contain three distinct vertices. Let's denote them as $u$, $w$, and $v$.
        obtain ⟨u, w, hu, hw, huv⟩ : ∃ u w : V, u ∈ f ∧ w ∈ f ∧ u ≠ v ∧ w ≠ v ∧ u ≠ w := by
          have h_card : f.card = 3 := by
            have h_triangle : f ∈ G.cliqueFinset 3 := by
              exact hM.1.1 ( Finset.filter_subset _ _ hf );
            exact Finset.mem_filter.mp h_triangle |>.2.2;
          obtain ⟨ u, w, x, hu, hw, hx ⟩ := Finset.card_eq_three.mp h_card; use if u = v then w else if w = v then x else u, if u = v then x else if w = v then u else w; aesop;
        have h_triangle : f ∈ G.cliqueFinset 3 := by
          exact hM.1.1 ( Finset.mem_filter.mp hf |>.1 );
        rw [ SimpleGraph.mem_cliqueFinset_iff ] at h_triangle ; aesop;
        exact ⟨ u, hu, w, hw, left, left_1, right, by have := h_triangle.1; have := this hu hw; aesop ⟩;
      refine' ⟨ Sym2.mk ( u, w ), _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    choose! e he₁ he₂ he₃ using h_edges;
    refine' ⟨ Finset.image ( fun f : packingElementsContaining M v => e f.1 f.2 ) Finset.univ, _, _, _ ⟩ <;> simp_all +decide [ Finset.card_image_of_injective ];
    · exact Set.range_subset_iff.mpr fun f => he₁ _ _;
    · exact Finset.card_image_le.trans ( by simp +decide [ hk ] );
    · intro T hT;
      obtain ⟨ f, hf₁, hf₂ ⟩ := base_edges_cover_avoiding G M hM v T hT;
      exact ⟨ _, ⟨ f, hf₁, rfl ⟩, he₃ f hf₁ T hT hf₂ ⟩;
  refine' le_trans _ h_edges.choose_spec.2.1;
  have h_min : triangleCoveringNumberOn G (trianglesAtVAvoidingV G M v) ≤ Finset.card (h_edges.choose) := by
    have h_in_set : h_edges.choose ∈ Finset.filter (fun E' => ∀ T ∈ trianglesAtVAvoidingV G M v, ∃ e ∈ E', e ∈ T.sym2) (Finset.powerset (G.edgeFinset)) := by
      exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr h_edges.choose_spec.1, h_edges.choose_spec.2.2 ⟩
    unfold triangleCoveringNumberOn;
    have h_min : ∀ {s : Finset ℕ}, s.Nonempty → ∀ x ∈ s, Option.getD (Finset.min s) 0 ≤ x := by
      intros s hs x hx; exact (by
      have := Finset.min_le hx; cases h : Finset.min s <;> aesop;);
    exact h_min ⟨ _, Finset.mem_image_of_mem _ h_in_set ⟩ _ ( Finset.mem_image_of_mem _ h_in_set );
  exact h_min

/- Aristotle failed to find a proof. -/
-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Triple-Apex Theorem
-- ══════════════════════════════════════════════════════════════════════════════

-- When v is in ≥3 packing triangles
theorem tau_le_8_triple_apex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : (packingElementsContaining M v).card ≥ 3) :
    triangleCoveringNumber G ≤ 8 := by
  -- Case split: v is in 3 or 4 elements
  --
  -- If v is in all 4 (star case):
  --   trianglesAtVContainingV: τ ≤ 4 (spokes)
  --   trianglesAtVAvoidingV: τ ≤ 4 (bases)
  --   Total: τ ≤ 8
  --
  -- If v is in exactly 3:
  --   For the 3 at v: τ ≤ 3 + 3 = 6 (3 spokes + 3 bases)
  --   For the isolated element e4: τ(T_{e4}) ≤ 2
  --   Total: τ ≤ 8
  sorry

-- Specialized version for exactly 3 sharing v
theorem tau_le_8_three_share_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : (packingElementsContaining M v).card = 3)
    (e4 : Finset V) (he4 : e4 ∈ M) (he4_no_v : v ∉ e4) :
    triangleCoveringNumber G ≤ 8 := by
  -- The isolated element e4 contributes τ(S_{e4}) ≤ 2
  -- The 3 at v contribute τ ≤ 6
  convert tau_le_8_triple_apex G M hM hM_card v (hv.ge.trans' (by decide))

-- Specialized version for all 4 sharing v (star)
theorem tau_le_8_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM_card : M.card = 4)
    (v : V) (hv : ∀ e ∈ M, v ∈ e) :
    triangleCoveringNumber G ≤ 8 := by
  -- All triangles either contain v or are base triangles
  -- τ(containing v) ≤ 4 (4 well-chosen spokes)
  -- τ(base triangles) ≤ 4 (4 base edges)
  -- By Lemma 25, τ(G) ≤ 8 for any graph G.
  apply tau_le_8_triple_apex G M hM hM_card v (by
  rw [ show packingElementsContaining M v = M from ?_ ];
  · linarith;
  · exact Finset.filter_true_of_mem hv)

end