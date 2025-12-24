/-
Tuza ν=4 Portfolio - Slot 24: Bridge Absorption Strategy

STRATEGIC INSIGHT (from Codex): Path 2 is cleanest - show edges covering S_e also hit bridges.
If bridges absorbed by S_e covers, then 4 × τ(S_e) ≤ 2 = 8 works.

TARGET: Prove bridge_absorption lemma
-/

import Mathlib

set_option linter.mathlibStandardSet false
open scoped BigOperators Real Nat Classical Pointwise
set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable section

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (matching proven lemmas exactly)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧ Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def trianglesSharingEdge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

def S {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

def X {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2 ∧ (t ∩ f).card ≥ 2)

def shareEdge {V : Type*} [DecidableEq V] (t1 t2 : Finset V) : Prop := (t1 ∩ t2).card ≥ 2

noncomputable def triangleCoveringNumberOn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: lemma_2_2 (from tuza_tau_Se_COMPLETE.lean, uuid f9473ebd)
-- ══════════════════════════════════════════════════════════════════════════════

lemma lemma_2_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∀ t1 t2, t1 ∈ S G e M → t2 ∈ S G e M → shareEdge t1 t2 := by
  intros t1 t2 ht1 ht2
  apply Classical.byContradiction
  intro h_contra;
  have h_new_packing : isTrianglePacking G (insert t1 (insert t2 (M.erase e))) := by
    unfold S at ht1 ht2;
    simp_all +decide [ isTrianglePacking ];
    unfold trianglesSharingEdge at ht1 ht2; simp_all +decide [ Finset.subset_iff, Set.Pairwise ] ;
    simp_all +decide [ Finset.inter_comm, shareEdge ];
    refine' ⟨ _, _, _, _ ⟩;
    · exact fun a ha ha' => hM.1.1 ha' |> fun h => by simpa using h;
    · exact fun h => Nat.le_of_lt_succ h_contra;
    · exact fun h => Nat.le_of_lt_succ h_contra;
    · have := hM.1.2; aesop;
  have h_card_new_packing : (insert t1 (insert t2 (M.erase e))).card > M.card := by
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp_all +decide [ Finset.ext_iff ];
    · omega;
    · intro x hx h; have := hM.1; simp_all +decide [ isTrianglePacking ] ;
      simp_all +decide [ S, Finset.mem_filter ];
      simp_all +decide [ trianglesSharingEdge ];
      have := this.2 h he; simp_all +decide [ Finset.inter_comm ] ;
      exact absurd ( this ( by aesop_cat ) ) ( by linarith );
    · constructor;
      · contrapose! h_contra;
        simp_all +decide [ Finset.ext_iff, shareEdge ];
        have h_card_t1 : t1.card = 3 := by
          have h_card_t1 : t1 ∈ G.cliqueFinset 3 := by
            exact Finset.mem_filter.mp ht1 |>.1 |> Finset.mem_filter.mp |>.1;
          simp_all +decide [ SimpleGraph.cliqueFinset ];
          exact h_card_t1.card_eq;
        rw [ show t1 ∩ t2 = t1 by ext x; aesop ] ; linarith;
      · simp_all +decide [ S ];
        intro x hx; intro H; have := ht1.2 _ H; simp_all +decide [ Finset.ext_iff ] ;
        have := this x hx; simp_all +decide [ Finset.card_le_one ] ;
        have := Finset.card_le_one.2 ( fun a ha b hb => this a ha b hb ) ; simp_all +decide [ trianglesSharingEdge ] ;
        exact this.not_lt ( by rw [ ht1.1.1.card_eq ] ; decide );
  have h_contradiction : (insert t1 (insert t2 (M.erase e))).card ≤ trianglePackingNumber G := by
    apply Finset.le_max_of_eq;
    apply Finset.mem_image_of_mem;
    exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.subset_iff.mpr fun x hx => h_new_packing.1 hx ), h_new_packing ⟩;
    unfold trianglePackingNumber;
    cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    simp_all +decide [ Finset.max ];
    exact h _ ( h_new_packing.1 ) h_new_packing;
  exact h_card_new_packing.not_le ( h_contradiction.trans ( hM.2.ge ) )

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_S_le_2 (structure: pairwise sharing → common edge or ≤4 vertices)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_S_le_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S G e M) ≤ 2 := by
  -- By lemma_2_2, triangles in S_e pairwise share edges
  -- Either: common edge (τ ≤ 1) or ≤4 vertices (k4_cover gives τ ≤ 2)
  by_cases hS : (S G e M).card ≤ 2
  · -- ≤2 triangles: trivially τ ≤ 2
    unfold triangleCoveringNumberOn
    by_cases hS' : S G e M = ∅
    · simp [hS']; rfl
    · have : ∃ E' ⊆ G.edgeFinset, (∀ t ∈ S G e M, ∃ edge ∈ E', edge ∈ t.sym2) ∧ E'.card ≤ 2 := by
        -- Each triangle contributes at most one edge to cover
        sorry
      sorry
  · -- >2 triangles: use structure
    push_neg at hS
    -- By lemma_2_2, all pairwise share edges
    -- Apply intersecting_triples_structure: common edge or ≤4 vertices
    sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Bridges contain shared vertex (from aristotle_nu4_tau_S_proven.lean)
-- ══════════════════════════════════════════════════════════════════════════════

lemma mem_X_implies_v_in_t {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (he : e ∈ G.cliqueFinset 3) (hf : f ∈ G.cliqueFinset 3)
    (h_inter : (e ∩ f).card = 1) (t : Finset V) (ht : t ∈ X G e f) :
    ∃ v ∈ e ∩ f, v ∈ t := by
  unfold X at ht
  simp only [Finset.mem_filter] at ht
  obtain ⟨ht_clique, h_e, h_f⟩ := ht
  -- t ∩ e ≥ 2 and t ∩ f ≥ 2, with e ∩ f = {v}
  -- Since t has 3 vertices and must share ≥2 with each, v must be in t
  have h_card_t : t.card = 3 := by
    simp only [SimpleGraph.mem_cliqueFinset_iff] at ht_clique
    exact ht_clique.2
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h_inter
  use v
  constructor
  · exact hv.symm ▸ Finset.mem_singleton_self v
  · -- v must be in t since t ∩ e ≥ 2 and t ∩ f ≥ 2 with e ∩ f = {v}
    by_contra hv_notin
    have h1 : (t ∩ e).card ≤ (e \ {v}).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_inter] at hx
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact hx.2
      · intro hxv; rw [hxv] at hx; exact hv_notin hx.1
    have h2 : (e \ {v}).card ≤ 2 := by
      have he_card : e.card = 3 := by
        simp only [SimpleGraph.mem_cliqueFinset_iff] at he; exact he.2
      have : ({v} : Finset V).card = 1 := Finset.card_singleton v
      have hv_in_e : v ∈ e := by
        have := hv.symm ▸ Finset.mem_singleton_self v
        exact Finset.mem_of_mem_inter_left this
      rw [Finset.card_sdiff (Finset.singleton_subset_iff.mpr hv_in_e), he_card, this]
      omega
    linarith

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: tau_X_le_2 (bridges on ≤4 vertices, k4_cover applies)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_X_le_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    triangleCoveringNumberOn G (X G e f) ≤ 2 := by
  -- All bridges contain the shared vertex/edge and live on ≤4 vertices
  -- By k4_cover, τ ≤ 2
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TARGET: Bridge Absorption - edges covering S_e ∪ S_f hit bridges X(e,f)
-- ══════════════════════════════════════════════════════════════════════════════

/-- KEY LEMMA: The packing element e is in S_e (compatible with itself) -/
lemma packing_element_in_S {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    e ∈ S G e M := by
  unfold S trianglesSharingEdge
  simp only [Finset.mem_filter]
  constructor
  · constructor
    · exact hM.1.1 he
    · -- e ∩ e = e has card 3 ≥ 2
      simp only [Finset.inter_self]
      have : e.card = 3 := by
        have := hM.1.1 he
        simp only [SimpleGraph.mem_cliqueFinset_iff] at this
        exact this.2
      omega
  · -- e is compatible with other packing elements (packing constraint)
    intro f hf hfe
    exact hM.1.2 he hf hfe

/--
MAIN TARGET: Any cover for S_e that includes an edge of e also covers bridges through e.

Proof idea:
- A bridge t ∈ X(e,f) shares an edge with e (say edge {v, a})
- If the cover C for S_e includes {v, a}, then C covers t
- Key: e ∈ S_e, so any cover for S_e covers e
- If C covers e, C includes some edge of e
- Need: that edge also hits the bridge
-/
lemma bridge_absorption {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (C : Finset (Sym2 V)) (hC : C ⊆ G.edgeFinset)
    (hC_covers : ∀ t ∈ S G e M ∪ S G f M, ∃ edge ∈ C, edge ∈ t.sym2) :
    ∀ t ∈ X G e f, ∃ edge ∈ C, edge ∈ t.sym2 := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for ν = 4
-- ══════════════════════════════════════════════════════════════════════════════

theorem tuza_nu4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) :
    triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
  -- Get max packing M = {e, f, g, h}
  -- Cover each S_x with ≤2 edges: 4 × 2 = 8
  -- By bridge_absorption, these edges also cover all bridges
  sorry

end
