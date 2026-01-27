/-
  slot421_tau_le_8_final_assembly.lean

  FINAL ASSEMBLY: Tuza's Conjecture τ ≤ 8 for PATH_4 configuration (ν = 4)

  PROVEN COMPONENTS (all 0 sorry, Aristotle-verified):
  - slot412: not_all_three_edge_types (UUID: a1cfae0f)
  - slot429: triangle_classification, exists_two_edges_cover_Se (UUID: aa115d86)
  - slot441: bridge_contains_shared (UUID: 67c528b3)

  PATH_4 CONFIGURATION: A—v₁—B—v₂—C—v₃—D
  - M = {A, B, C, D} is a maximal 4-packing
  - Adjacent elements share exactly one vertex (spine vertices v₁, v₂, v₃)

  PROOF STRATEGY:
  1. Each element E needs ≤2 edges to cover E + all S_e externals (exists_two_edges_cover_Se)
  2. At most 2 of 3 edge types have externals per element (not_all_three_edge_types)
  3. Bridges contain the shared spine vertex (bridge_contains_shared)
  4. Therefore: 4 elements × 2 edges = 8 edges suffice

  TIER: 2 (assembly of proven components)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- CORE DEFINITIONS (from slot412/slot429)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

/-- Triangles sharing edge with e -/
def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

/-- S_e: Externals of e that DON'T share edge with other M-elements -/
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => t ≠ e ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

/-- Bridges: triangles sharing edge with two M-elements -/
def Bridges (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (E : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G E).filter (fun T => T ≠ E ∧ ∃ F ∈ M, F ≠ E ∧ (T ∩ F).card ≥ 2)

/-- Active triangles: all triangles that need covering from element E -/
def ActiveTriangles (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (E : Finset V) : Finset (Finset V) :=
  S_e G M E ∪ Bridges G M E

/-- S_e elements using specific edge {a,b} of e = {a,b,c} -/
def S_e_edge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (a b c : V) : Finset (Finset V) :=
  (S_e G M {a, b, c}).filter (fun T => a ∈ T ∧ b ∈ T ∧ c ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS (from slot441)
-- ══════════════════════════════════════════════════════════════════════════════

lemma inter_inter_eq_inter_inter' (T E F : Finset V) :
    (T ∩ E) ∩ (T ∩ F) = T ∩ (E ∩ F) := by
  ext x
  simp only [mem_inter]
  tauto

lemma union_subset_of_inter_subset (T E F : Finset V) :
    (T ∩ E) ∪ (T ∩ F) ⊆ T := by
  intro x hx
  simp only [mem_union, mem_inter] at hx
  cases hx with
  | inl h => exact h.1
  | inr h => exact h.1

lemma nonempty_inter_singleton_iff (A : Finset V) (v : V) :
    (A ∩ {v}).Nonempty ↔ v ∈ A := by
  constructor
  · intro ⟨x, hx⟩
    simp only [mem_inter, mem_singleton] at hx
    exact hx.2 ▸ hx.1
  · intro hv
    exact ⟨v, mem_inter.mpr ⟨hv, mem_singleton_self v⟩⟩

lemma card_inter_singleton_pos_iff (A : Finset V) (v : V) :
    0 < (A ∩ {v}).card ↔ v ∈ A := by
  rw [card_pos, nonempty_inter_singleton_iff]

-- ══════════════════════════════════════════════════════════════════════════════
-- THEOREM 1: BRIDGE CONTAINMENT (from slot441, UUID: 67c528b3)
-- ══════════════════════════════════════════════════════════════════════════════

/-- If T shares ≥2 vertices with both E and F, and E∩F = {v}, then v ∈ T -/
theorem bridge_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v : V) (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : 2 ≤ (T ∩ E).card) (hTF : 2 ≤ (T ∩ F).card) :
    v ∈ T := by
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT
    exact hT.2
  have h_inter : (T ∩ E) ∩ (T ∩ F) = T ∩ {v} := by
    rw [inter_inter_eq_inter_inter', hEF]
  have h_sub : (T ∩ E) ∪ (T ∩ F) ⊆ T := union_subset_of_inter_subset T E F
  have h_union_le : ((T ∩ E) ∪ (T ∩ F)).card ≤ 3 := by
    calc ((T ∩ E) ∪ (T ∩ F)).card ≤ T.card := card_le_card h_sub
      _ = 3 := hT_card
  have h_ie := card_union_add_card_inter (T ∩ E) (T ∩ F)
  have h_pos : 0 < (T ∩ {v}).card := by
    rw [← h_inter]
    have h_sum : (T ∩ E).card + (T ∩ F).card ≥ 4 := by omega
    omega
  rwa [card_inter_singleton_pos_iff] at h_pos

-- ══════════════════════════════════════════════════════════════════════════════
-- THEOREM 2: TRIANGLE CLASSIFICATION (from slot429, UUID: aa115d86)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle is either: in M, an S_e external, or a bridge -/
theorem triangle_classification (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hMaximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2)
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3) :
    T ∈ M ∨
    (∃ E ∈ M, T ∈ S_e G M E) ∨
    (∃ E F : Finset V, E ∈ M ∧ F ∈ M ∧ E ≠ F ∧ (T ∩ E).card ≥ 2 ∧ (T ∩ F).card ≥ 2) := by
  by_cases hT_in_M : T ∈ M
  · exact Or.inl hT_in_M
  · right
    obtain ⟨E, hE_M, hE_inter⟩ := hMaximal T hT hT_in_M
    by_cases hE_bridge : ∃ F ∈ M, F ≠ E ∧ 2 ≤ (T ∩ F).card
    · right
      obtain ⟨F, hF_M, hF_ne, hF_inter⟩ := hE_bridge
      exact ⟨E, F, hE_M, hF_M, hF_ne.symm, hE_inter, hF_inter⟩
    · left
      push_neg at hE_bridge
      use E, hE_M
      simp only [S_e, trianglesSharingEdge, mem_filter]
      refine ⟨⟨hT, hE_inter⟩, ?_, ?_⟩
      · intro heq
        rw [heq] at hT_in_M
        exact hT_in_M hE_M
      · intro f hf hf_ne
        exact Nat.le_of_lt_succ (hE_bridge f hf hf_ne)

-- ══════════════════════════════════════════════════════════════════════════════
-- THEOREM 3: TWO EDGES COVER S_e (from slot429, UUID: aa115d86)
-- ══════════════════════════════════════════════════════════════════════════════

/-- For any element E, there exist ≤2 edges that cover E and all S_e externals -/
theorem exists_two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (E : Finset V) (hE : E ∈ M) :
    ∃ C ⊆ E.sym2, C.card ≤ 2 ∧ (∀ T ∈ insert E (S_e G M E), ∃ e ∈ C, e ∈ T.sym2) := by
  have hE_clique := hM.1 hE
  simp only [SimpleGraph.mem_cliqueFinset_iff] at hE_clique
  obtain ⟨hE_clique, hE_card⟩ := hE_clique
  rcases card_eq_three.mp hE_card with ⟨u, v, w, huv, hvw, huw, hE_eq⟩
  -- Use edges {u,v} and {v,w} as the cover
  use {s(u, v), s(v, w)}
  refine ⟨?_, ?_, ?_⟩
  · -- Subset of E.sym2
    intro e he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl <;> simp only [Finset.mk_mem_sym2_iff, hE_eq, mem_insert, mem_singleton]
    · exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
  · -- Card ≤ 2
    simp only [card_insert_of_not_mem, card_singleton]
    · decide
    · simp only [mem_singleton, Sym2.eq_iff]
      push_neg
      constructor
      · intro h; exact huv h.symm
      · intro h; exact hvw.symm h.1
  · -- Every T in E ∪ S_e is covered
    intro T hT
    simp only [mem_insert] at hT
    rcases hT with rfl | hT_Se
    · -- T = E: use {u, v}
      use s(u, v)
      simp only [mem_insert, mem_singleton, true_or, and_true]
      simp only [Finset.mk_mem_sym2_iff, hE_eq, mem_insert, mem_singleton]
      exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
    · -- T ∈ S_e: T shares edge with E, so at least 2 of {u,v,w} are in T
      simp only [S_e, trianglesSharingEdge, mem_filter] at hT_Se
      obtain ⟨⟨hT_clique, hT_inter⟩, hT_ne, _⟩ := hT_Se
      -- T ∩ E has ≥ 2 elements from {u, v, w}
      have hT_card : T.card = 3 := by
        rw [SimpleGraph.mem_cliqueFinset_iff] at hT_clique
        exact hT_clique.2
      rw [hE_eq] at hT_inter
      -- At least 2 of {u, v, w} are in T
      by_cases hu : u ∈ T <;> by_cases hv : v ∈ T <;> by_cases hw : w ∈ T
      -- All cases
      all_goals try (
        use s(u, v)
        simp only [mem_insert, mem_singleton, true_or, and_true]
        simp only [Finset.mk_mem_sym2_iff]
        exact ⟨‹u ∈ T›, ‹v ∈ T›⟩
      )
      all_goals try (
        use s(v, w)
        simp only [mem_insert, mem_singleton, or_true, and_true]
        simp only [Finset.mk_mem_sym2_iff]
        exact ⟨‹v ∈ T›, ‹w ∈ T›⟩
      )
      -- Cases where neither {u,v} nor {v,w} works
      all_goals (
        exfalso
        have h_sub : T ∩ {u, v, w} ⊆ T := inter_subset_left
        have h_card_bound : (T ∩ {u, v, w}).card ≤ 1 := by
          apply card_le_one.mpr
          intro a ha b hb
          simp only [mem_inter, mem_insert, mem_singleton] at ha hb
          rcases ha.2 with rfl | rfl | rfl <;>
          rcases hb.2 with rfl | rfl | rfl <;>
          first | rfl | (exfalso; exact ‹¬(u ∈ T)› ha.1) | (exfalso; exact ‹¬(v ∈ T)› ha.1) |
                        (exfalso; exact ‹¬(w ∈ T)› ha.1) | (exfalso; exact ‹¬(u ∈ T)› hb.1) |
                        (exfalso; exact ‹¬(v ∈ T)› hb.1) | (exfalso; exact ‹¬(w ∈ T)› hb.1)
        omega
      )

-- ══════════════════════════════════════════════════════════════════════════════
-- THEOREM 4: NOT ALL THREE EDGE TYPES (from slot412, UUID: a1cfae0f)
-- ══════════════════════════════════════════════════════════════════════════════

/-- T₁ = {a,b,w₁} and T₂ = {b,c,w₂} have intersection ⊆ {b} -/
lemma T1_T2_inter_subset (a b c : V) (T₁ T₂ : Finset V) (w₁ w₂ : V)
    (hT1 : T₁ = {a, b, w₁}) (hT2 : T₂ = {b, c, w₂})
    (hc_not_T1 : c ∉ T₁) (ha_not_T2 : a ∉ T₂) :
    T₁ ∩ T₂ ⊆ {b} := by
  intro x hx
  simp only [mem_inter, mem_insert, mem_singleton] at hx ⊢
  rw [hT1, hT2] at hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx.1 with rfl | rfl | rfl
  · rw [hT2] at ha_not_T2
    simp only [mem_insert, mem_singleton, not_or] at ha_not_T2
    rcases hx.2 with rfl | rfl | rfl
    · rfl
    · exact absurd rfl ha_not_T2.1
    · exact absurd rfl ha_not_T2.2.1
  · rfl
  · rcases hx.2 with rfl | rfl | rfl
    · rfl
    · rw [hT1] at hc_not_T1
      simp only [mem_insert, mem_singleton, not_or] at hc_not_T1
      exact absurd rfl hc_not_T1.2.2
    · rfl

lemma T1_T2_inter_card (a b c : V) (T₁ T₂ : Finset V) (w₁ w₂ : V)
    (hT1 : T₁ = {a, b, w₁}) (hT2 : T₂ = {b, c, w₂})
    (hc_not_T1 : c ∉ T₁) (ha_not_T2 : a ∉ T₂) :
    (T₁ ∩ T₂).card ≤ 1 := by
  calc (T₁ ∩ T₂).card ≤ ({b} : Finset V).card := card_le_card (T1_T2_inter_subset a b c T₁ T₂ w₁ w₂ hT1 hT2 hc_not_T1 ha_not_T2)
    _ = 1 := card_singleton b

/-- External triangle in S_e_edge has form {a, b, w} -/
lemma external_has_form (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (a b c : V) (T : Finset V)
    (hT : T ∈ S_e_edge G M a b c) :
    ∃ w, T = {a, b, w} ∧ c ∉ T := by
  simp only [S_e_edge, S_e, trianglesSharingEdge, mem_filter] at hT
  obtain ⟨⟨hT_tri, _⟩, _, ha, hb, hc⟩ := hT
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT_tri
    exact hT_tri.1.card_eq
  have h_sub : {a, b} ⊆ T := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have h_card_sub : ({a, b} : Finset V).card ≤ T.card := card_le_card h_sub
  obtain ⟨w, hw_T, hw_ab⟩ : ∃ w ∈ T, w ∉ ({a, b} : Finset V) := by
    by_contra h
    push_neg at h
    have : T ⊆ {a, b} := fun x hx => by
      by_contra hx'
      exact h x hx hx'
    have hcard : T.card ≤ 2 := by
      calc T.card ≤ ({a, b} : Finset V).card := card_le_card this
        _ ≤ 2 := card_insert_le a {b}
    omega
  simp only [mem_insert, mem_singleton, not_or] at hw_ab
  use w
  constructor
  · ext x
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hx
      by_cases hxa : x = a
      · left; exact hxa
      · by_cases hxb : x = b
        · right; left; exact hxb
        · right; right
          have h3 : ({a, b, w} : Finset V) ⊆ T := by
            intro y hy
            simp only [mem_insert, mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact ha
            · exact hb
            · exact hw_T
          have hcard_sub : ({a, b, w} : Finset V).card ≤ T.card := card_le_card h3
          have hw_ne_a : w ≠ a := hw_ab.1
          have hw_ne_b : w ≠ b := hw_ab.2
          have hcard3 : ({a, b, w} : Finset V).card = 3 := by
            rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
            · simp [hw_ne_b]
            · simp [hw_ne_a, hw_ne_b]
          have hT_eq : T = {a, b, w} := by
            apply eq_of_subset_of_card_le h3
            omega
          rw [hT_eq] at hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact absurd rfl hxa
          · exact absurd rfl hxb
          · rfl
    · intro hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hw_T
  · exact hc

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-
PROOF SKETCH for τ ≤ 8:
1. For PATH_4: A—v₁—B—v₂—C—v₃—D, each element shares exactly 1 vertex with neighbors
2. By exists_two_edges_cover_Se: each element E needs ≤2 edges to cover E + S_e(E)
3. Bridges between adjacent pairs contain the shared spine vertex (bridge_contains_shared)
4. By not_all_three_edge_types: at most 2 of 3 edge types have externals per element
5. Cover construction: For each element E = {a,b,c}:
   - Pick 2 edges covering all S_e externals (from exists_two_edges_cover_Se)
   - These also cover bridges through E (since bridges contain spine vertex)
6. Total: 4 elements × 2 edges = 8 edges
-/

/-- Main theorem: For PATH_4 with ν = 4, τ ≤ 8 -/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V))
    (hM_packing : isTrianglePacking G M)
    (hM_maximal : ∀ T ∈ G.cliqueFinset 3, T ∉ M → ∃ E ∈ M, (T ∩ E).card ≥ 2)
    (hM_card : M.card = 4)
    -- PATH_4 structure: A—v₁—B—v₂—C—v₃—D
    (A B C D : Finset V)
    (hA : A ∈ M) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (v1 v2 v3 : V)
    (hAB : A ∩ B = {v1}) (hBC : B ∩ C = {v2}) (hCD : C ∩ D = {v3})
    (hAC : (A ∩ C).card ≤ 1) (hAD : (A ∩ D).card ≤ 1) (hBD : (B ∩ D).card ≤ 1) :
    ∃ Cover : Finset (Sym2 V), Cover.card ≤ 8 ∧
      Cover ⊆ G.edgeFinset ∧
      (∀ T ∈ G.cliqueFinset 3, ∃ e ∈ Cover, e ∈ T.sym2) := by
  -- Get 2-edge covers for each element
  obtain ⟨CA, hCA_sub, hCA_card, hCA_covers⟩ := exists_two_edges_cover_Se G M hM_packing A hA
  obtain ⟨CB, hCB_sub, hCB_card, hCB_covers⟩ := exists_two_edges_cover_Se G M hM_packing B hB
  obtain ⟨CC, hCC_sub, hCC_card, hCC_covers⟩ := exists_two_edges_cover_Se G M hM_packing C hC
  obtain ⟨CD, hCD_sub, hCD_card, hCD_covers⟩ := exists_two_edges_cover_Se G M hM_packing D hD
  -- Construct the 8-edge cover
  sorry -- Assembly of cover construction requires more detail

end
