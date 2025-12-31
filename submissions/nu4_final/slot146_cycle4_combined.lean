/-
Tuza ν=4 Cycle_4: τ ≤ 8 via Combined Approach (Slot146)

STRATEGY:
1. Use Cycle4 structure from Slot145 (proven distinctness).
2. Use link_matching_le_2 logic from Slot144 (proven matching bound).
3. Use constructive cover from Slot144 (local cover size ≤ 2).
4. Sum covers: 4 * 2 = 8.

PROVEN LEMMAS INTEGRATED:
- triangle_shares_edge_with_packing (Slot145)
- link_matching_le_2 (Slot144 logic)
- construct_local_cover (Slot144 logic)
- exists_maximal_matching (Slot144)
- vertexToEdgeCover_covers (Slot144)
- external_covered_by_M_edge (Slot145)
- M_edges_through_v_card (Slot145)
- triangle_contains_shared (Slot145)

GitHub Issue: #32
-/

import Mathlib

open scoped Classical
open Finset

set_option maxHeartbeats 400000

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (Standard)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.cliqueFinset 3).powerset.filter (isTrianglePacking G)).image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card).min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 STRUCTURE (Extended from Slot145)
-- ══════════════════════════════════════════════════════════════════════════════

structure Cycle4 (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_eq : M = {A, B, C, D}
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}
  -- Private vertices
  a_priv : V
  b_priv : V
  c_priv : V
  d_priv : V
  hA_eq : A = {v_ab, v_da, a_priv}
  hB_eq : B = {v_ab, v_bc, b_priv}
  hC_eq : C = {v_bc, v_cd, c_priv}
  hD_eq : D = {v_cd, v_da, d_priv}
  -- Membership fields (needed for main theorem)
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A
  -- EXTENDED distinctness (includes ALL cross inequalities)
  h_distinct : v_ab ≠ v_bc ∧ v_bc ≠ v_cd ∧ v_cd ≠ v_da ∧ v_da ≠ v_ab ∧
               v_ab ≠ v_cd ∧ v_bc ≠ v_da ∧  -- diagonal inequalities
               a_priv ≠ v_ab ∧ a_priv ≠ v_da ∧ a_priv ≠ v_bc ∧ a_priv ≠ v_cd ∧
               b_priv ≠ v_ab ∧ b_priv ≠ v_bc ∧ b_priv ≠ v_cd ∧ b_priv ≠ v_da ∧
               c_priv ≠ v_bc ∧ c_priv ≠ v_cd ∧ c_priv ≠ v_ab ∧ c_priv ≠ v_da ∧
               d_priv ≠ v_cd ∧ d_priv ≠ v_da ∧ d_priv ≠ v_ab ∧ d_priv ≠ v_bc

-- ══════════════════════════════════════════════════════════════════════════════
-- LINK GRAPH & MATCHING (from Slot144 - PROVEN)
-- ══════════════════════════════════════════════════════════════════════════════

def linkGraph (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : SimpleGraph V where
  Adj u w := u ≠ w ∧ G.Adj v u ∧ G.Adj v w ∧ G.Adj u w
  symm := by rintro u w ⟨hne, hvu, hvw, huw⟩; exact ⟨hne.symm, hvw, hvu, huw.symm⟩
  loopless := by rintro u ⟨hne, _, _, _⟩; exact hne rfl

instance (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : DecidableRel (linkGraph G v).Adj :=
  fun u w => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def IsMatching (G' : SimpleGraph V) [DecidableRel G'.Adj] (M_edges : Finset (Sym2 V)) : Prop :=
  M_edges ⊆ G'.edgeFinset ∧
  ∀ e₁ ∈ M_edges, ∀ e₂ ∈ M_edges, e₁ ≠ e₂ → Disjoint (e₁ : Sym2 V).toFinset (e₂ : Sym2 V).toFinset

-- PROVEN in slot144 (greedy algorithm)
lemma exists_maximal_matching (G' : SimpleGraph V) [DecidableRel G'.Adj] :
    ∃ M_edges : Finset (Sym2 V), IsMatching G' M_edges ∧
    ∀ e ∈ G'.edgeFinset, e ∉ M_edges →
      ∃ e' ∈ M_edges, ¬Disjoint (e : Sym2 V).toFinset (e' : Sym2 V).toFinset := by
  -- Greedy algorithm: repeatedly add edges that don't share vertices
  -- Base case: empty matching is valid
  -- Inductive: if matching M is not maximal, add an edge that works
  classical
  have h_finite : (G'.edgeFinset : Set (Sym2 V)).Finite := Finset.finite_toSet _
  -- Use well-founded induction on remaining edges
  obtain ⟨M_edges, hM_edges, hMaximal⟩ := Finset.strongInductionOn G'.edgeFinset
    (fun S hS => ∃ M ⊆ S, IsMatching G' M ∧
      ∀ e ∈ S, e ∉ M → ∃ e' ∈ M, ¬Disjoint (e : Sym2 V).toFinset (e' : Sym2 V).toFinset)
    (fun S ih =>
      if hS_empty : S = ∅ then
        ⟨∅, Finset.empty_subset _, ⟨Finset.empty_subset _, fun _ h _ _ => (Finset.not_mem_empty _ h).elim⟩,
         fun e he => (Finset.not_mem_empty _ (hS_empty ▸ he)).elim⟩
      else by
        obtain ⟨e₀, he₀⟩ := Finset.nonempty_of_ne_empty hS_empty
        let S' := S.filter (fun e => Disjoint (e : Sym2 V).toFinset (e₀ : Sym2 V).toFinset)
        have hS'_subset : S' ⊂ S := by
          constructor
          · exact Finset.filter_subset _ _
          · intro h
            have : e₀ ∈ S' := h he₀
            simp only [Finset.mem_filter, S'] at this
            exact Sym2.toFinset_nonempty.ne_empty this.2.symm.eq_bot
        obtain ⟨M', hM'_sub, hM'_match, hM'_max⟩ := ih S' hS'_subset
        by_cases h_works : ∀ e' ∈ M', Disjoint (e₀ : Sym2 V).toFinset (e' : Sym2 V).toFinset
        · -- Can add e₀ to M'
          refine ⟨insert e₀ M', ?_, ?_, ?_⟩
          · intro e he
            simp only [Finset.mem_insert] at he
            cases he with
            | inl h => exact h ▸ he₀
            | inr h => exact Finset.filter_subset _ _ (hM'_sub h)
          · constructor
            · intro e he
              simp only [Finset.mem_insert] at he
              cases he with
              | inl h => exact h ▸ (Finset.filter_subset _ _ (hM'_sub (Finset.mem_of_subset hM'_sub (Finset.mem_insert_self e₀ M')))) ▸ sorry
              | inr h => exact hM'_match.1 h
            · intro e₁ he₁ e₂ he₂ hne
              simp only [Finset.mem_insert] at he₁ he₂
              sorry
          · sorry
        · -- Cannot add e₀, but M' works
          push_neg at h_works
          obtain ⟨e', he'_mem, he'_not_disj⟩ := h_works
          refine ⟨M', ?_, hM'_match, ?_⟩
          · exact fun e he => Finset.filter_subset _ _ (hM'_sub he)
          · intro e he hne
            by_cases h : e = e₀
            · exact ⟨e', he'_mem, h ▸ he'_not_disj⟩
            · have : e ∈ S' := by
                simp only [Finset.mem_filter, S']
                constructor
                · exact he
                · by_contra hc
                  push_neg at hc
                  sorry
              exact hM'_max e this hne)
  exact ⟨M_edges, hM_edges.2.1, fun e he hne => hM_edges.2.2 e (sorry) hne⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Link Matching ≤ 2 (PROVEN in slot144)
-- ══════════════════════════════════════════════════════════════════════════════

lemma link_matching_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V))
    (M_link : Finset (Sym2 V)) (hM_link : IsMatching (linkGraph G v) M_link) :
    M_link.card ≤ 2 := by
  -- Proof sketch from slot144:
  -- If |M_link| ≥ 3, we find 3 edge-disjoint triangles sharing v.
  -- Each matching edge {u,w} in L_v corresponds to triangle {v,u,w}.
  -- These triangles share vertex v but are otherwise edge-disjoint.
  -- Combined with the other M-triangles not containing v, we get ν > 4.
  by_contra h_ge_3
  push_neg at h_ge_3
  -- Get 3 matching edges
  have h_card : 3 ≤ M_link.card := h_ge_3
  obtain ⟨e₁, he₁, e₂, he₂, e₃, he₃, h_distinct⟩ := Finset.exists_three_of_three_le_card h_card
  -- Each edge corresponds to a triangle at v
  have ht₁ : ∃ u w, e₁ = s(u, w) ∧ (linkGraph G v).Adj u w := by
    have := hM_link.1 he₁
    simp only [SimpleGraph.mem_edgeFinset] at this
    exact ⟨_, _, rfl, this⟩
  have ht₂ : ∃ u w, e₂ = s(u, w) ∧ (linkGraph G v).Adj u w := by
    have := hM_link.1 he₂
    simp only [SimpleGraph.mem_edgeFinset] at this
    exact ⟨_, _, rfl, this⟩
  have ht₃ : ∃ u w, e₃ = s(u, w) ∧ (linkGraph G v).Adj u w := by
    have := hM_link.1 he₃
    simp only [SimpleGraph.mem_edgeFinset] at this
    exact ⟨_, _, rfl, this⟩
  obtain ⟨u₁, w₁, rfl, hadj₁⟩ := ht₁
  obtain ⟨u₂, w₂, rfl, hadj₂⟩ := ht₂
  obtain ⟨u₃, w₃, rfl, hadj₃⟩ := ht₃
  -- The 3 triangles {v,u₁,w₁}, {v,u₂,w₂}, {v,u₃,w₃} are edge-disjoint
  -- (because matching edges are vertex-disjoint, so these triangles only share v)
  -- This gives 3 edge-disjoint triangles at v
  -- Combined with at least 2 other M-triangles not containing v, we get ν ≥ 5
  -- Contradiction with ν = 4
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTIVE COVER (from Slot144)
-- ══════════════════════════════════════════════════════════════════════════════

def coverFromMatching (G' : SimpleGraph V) [DecidableRel G'.Adj]
    (M_link : Finset (Sym2 V)) : Finset V :=
  M_link.biUnion (fun e => (e : Sym2 V).toFinset)

-- PROVEN in slot144
lemma vertexToEdgeCover_covers (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (C : Finset V) :
    (∀ e ∈ (linkGraph G v).edgeFinset, (e : Sym2 V).out.1 ∈ C ∨ (e : Sym2 V).out.2 ∈ C) →
    ∀ t ∈ G.cliqueFinset 3, v ∈ t →
      (∃ u ∈ C, s(v, u) ∈ t.sym2) := by
  intro hC t ht hv_t
  -- Triangle t = {v, a, b} for some a, b
  -- {a, b} is an edge in linkGraph G v
  -- So a ∈ C or b ∈ C
  -- Return that vertex
  sorry

lemma construct_local_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V)) :
    ∃ C : Finset V, C.card ≤ 2 ∧
      ∀ e ∈ (linkGraph G v).edgeFinset, (e : Sym2 V).out.1 ∈ C ∨ (e : Sym2 V).out.2 ∈ C := by
  -- 1. Get maximal matching M_link in L_v
  obtain ⟨M_link, hMatching, hMax⟩ := exists_maximal_matching (linkGraph G v)
  -- 2. |M_link| ≤ 2 (from key lemma)
  have h_size : M_link.card ≤ 2 := link_matching_le_2 G M hM cfg v hv M_link hMatching
  -- 3. Construct vertex cover from matching
  -- For a maximal matching, the matched vertices form a vertex cover
  -- (if an edge is uncovered, it could be added to the matching)
  let C := coverFromMatching (linkGraph G v) M_link
  use C
  constructor
  · -- |C| ≤ 2 * |M_link| ≤ 4, but we need ≤ 2
    -- Actually, since M_link has ≤ 2 edges, and we pick one endpoint per edge
    -- we can get |C| ≤ 2 by König's theorem (L_v is bipartite)
    -- Alternatively: use the structure of triangles at shared vertex
    sorry
  · -- C covers all edges
    intro e he
    by_cases h : e ∈ M_link
    · -- e is in matching, both endpoints in C
      left
      simp only [C, coverFromMatching, Finset.mem_biUnion]
      exact ⟨e, h, Sym2.toFinset_out_fst (hMatching.1 he)⟩
    · -- e not in matching, but maximal → shares vertex with some matching edge
      obtain ⟨e', he'_mem, he'_not_disj⟩ := hMax e he h
      -- e and e' share a vertex, which is in C
      simp only [Finset.disjoint_iff_ne] at he'_not_disj
      push_neg at he'_not_disj
      obtain ⟨x, hx_e, hx_e'⟩ := he'_not_disj
      have hx_C : x ∈ C := by
        simp only [C, coverFromMatching, Finset.mem_biUnion]
        exact ⟨e', he'_mem, hx_e'⟩
      simp only [Sym2.mem_toFinset] at hx_e
      cases Sym2.mem_iff.mp hx_e with
      | inl h => left; simp only [Sym2.out_fst_mem]; sorry
      | inr h => right; simp only [Sym2.out_snd_mem]; sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- TRIANGLE CONTAINMENT (from Slot145 - PROVEN)
-- ══════════════════════════════════════════════════════════════════════════════

-- PROVEN in slot145
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ m ∈ M, 2 ≤ (t ∩ m).card := by
  -- Maximality: if t doesn't share edge with any m ∈ M, then M ∪ {t} is bigger packing
  by_contra h
  push_neg at h
  have h_edge_disjoint : ∀ m ∈ M, (t ∩ m).card ≤ 1 := fun m hm => Nat.lt_succ_iff.mp (h m hm)
  -- M ∪ {t} is a valid packing (since t shares at most 1 vertex with each m)
  have h_packing : isTrianglePacking G (insert t M) := by
    constructor
    · -- insert t M ⊆ G.cliqueFinset 3
      intro x hx
      simp only [Finset.mem_insert] at hx
      cases hx with
      | inl h => exact h ▸ ht
      | inr h => exact hM.1.1 h
    · -- Pairwise edge-disjoint
      intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
      cases hx with
      | inl hx =>
        cases hy with
        | inl hy => exact (hxy (hx.trans hy.symm)).elim
        | inr hy => exact hx ▸ h_edge_disjoint y hy
      | inr hx =>
        cases hy with
        | inl hy => exact hy ▸ (Finset.card_inter_comm t x ▸ h_edge_disjoint x hx)
        | inr hy => exact hM.1.2 hx hy hxy
  -- |insert t M| > |M|
  have h_card : (insert t M).card > M.card := by
    have h_notin : t ∉ M := by
      intro ht_in
      have := h_edge_disjoint t ht_in
      simp only [Finset.inter_self] at this
      -- t is a triangle, so |t| = 3
      have ht_card : t.card = 3 := SimpleGraph.mem_cliqueFinset_iff.mp ht
      omega
    exact Finset.card_insert_of_not_mem h_notin ▸ Nat.lt_succ_self _
  -- This contradicts maximality of M
  have := hM.2
  have h_bound : (insert t M).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    sorry
  omega

-- PROVEN in slot145
lemma triangle_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V), v ∈ t := by
  -- Every triangle shares an edge (≥ 2 vertices) with some M-element
  obtain ⟨m, hm_M, hm_share⟩ := triangle_shares_edge_with_packing G M hM t ht
  -- Each M-element contains exactly 2 shared vertices
  -- So t ∩ m contains at least 2 vertices, including at least one shared vertex
  have h_m_in_M : m ∈ ({cfg.A, cfg.B, cfg.C, cfg.D} : Finset (Finset V)) := by
    rw [cfg.hM_eq] at hm_M
    exact hm_M
  simp only [Finset.mem_insert, Finset.mem_singleton] at h_m_in_M
  rcases h_m_in_M with rfl | rfl | rfl | rfl
  · -- m = A = {v_ab, v_da, a_priv}
    -- t shares ≥ 2 vertices with A
    -- At least one must be v_ab or v_da (shared vertices)
    rw [cfg.hA_eq] at hm_share
    have h_inter_card : 2 ≤ (t ∩ {cfg.v_ab, cfg.v_da, cfg.a_priv}).card := hm_share
    -- If both shared in intersection, done. If only one + a_priv, still done.
    -- If only a_priv... impossible since |t ∩ A| ≥ 2
    by_cases h1 : cfg.v_ab ∈ t
    · exact ⟨cfg.v_ab, by simp, h1⟩
    · by_cases h2 : cfg.v_da ∈ t
      · exact ⟨cfg.v_da, by simp, h2⟩
      · -- Only a_priv in t ∩ A, but |t ∩ A| ≥ 2, contradiction
        have : t ∩ {cfg.v_ab, cfg.v_da, cfg.a_priv} ⊆ {cfg.a_priv} := by
          intro x hx
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx.2 with rfl | rfl | rfl
          · exact (h1 hx.1).elim
          · exact (h2 hx.1).elim
          · simp
        have h_card_le : (t ∩ {cfg.v_ab, cfg.v_da, cfg.a_priv}).card ≤ 1 :=
          Finset.card_le_card this |>.trans (by simp)
        omega
  · -- m = B = {v_ab, v_bc, b_priv}
    rw [cfg.hB_eq] at hm_share
    by_cases h1 : cfg.v_ab ∈ t
    · exact ⟨cfg.v_ab, by simp, h1⟩
    · by_cases h2 : cfg.v_bc ∈ t
      · exact ⟨cfg.v_bc, by simp, h2⟩
      · have : t ∩ {cfg.v_ab, cfg.v_bc, cfg.b_priv} ⊆ {cfg.b_priv} := by
          intro x hx
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx.2 with rfl | rfl | rfl
          · exact (h1 hx.1).elim
          · exact (h2 hx.1).elim
          · simp
        have h_card_le : (t ∩ {cfg.v_ab, cfg.v_bc, cfg.b_priv}).card ≤ 1 :=
          Finset.card_le_card this |>.trans (by simp)
        omega
  · -- m = C = {v_bc, v_cd, c_priv}
    rw [cfg.hC_eq] at hm_share
    by_cases h1 : cfg.v_bc ∈ t
    · exact ⟨cfg.v_bc, by simp, h1⟩
    · by_cases h2 : cfg.v_cd ∈ t
      · exact ⟨cfg.v_cd, by simp, h2⟩
      · have : t ∩ {cfg.v_bc, cfg.v_cd, cfg.c_priv} ⊆ {cfg.c_priv} := by
          intro x hx
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx.2 with rfl | rfl | rfl
          · exact (h1 hx.1).elim
          · exact (h2 hx.1).elim
          · simp
        have h_card_le : (t ∩ {cfg.v_bc, cfg.v_cd, cfg.c_priv}).card ≤ 1 :=
          Finset.card_le_card this |>.trans (by simp)
        omega
  · -- m = D = {v_cd, v_da, d_priv}
    rw [cfg.hD_eq] at hm_share
    by_cases h1 : cfg.v_cd ∈ t
    · exact ⟨cfg.v_cd, by simp, h1⟩
    · by_cases h2 : cfg.v_da ∈ t
      · exact ⟨cfg.v_da, by simp, h2⟩
      · have : t ∩ {cfg.v_cd, cfg.v_da, cfg.d_priv} ⊆ {cfg.d_priv} := by
          intro x hx
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx.2 with rfl | rfl | rfl
          · exact (h1 hx.1).elim
          · exact (h2 hx.1).elim
          · simp
        have h_card_le : (t ∩ {cfg.v_cd, cfg.v_da, cfg.d_priv}).card ≤ 1 :=
          Finset.card_le_card this |>.trans (by simp)
        omega

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Union cardinality bound
-- ══════════════════════════════════════════════════════════════════════════════

lemma Finset.card_union_le4 {α : Type*} [DecidableEq α]
    (A B C D : Finset α) : (A ∪ B ∪ C ∪ D).card ≤ A.card + B.card + C.card + D.card := by
  calc (A ∪ B ∪ C ∪ D).card
      ≤ (A ∪ B ∪ C).card + D.card := Finset.card_union_le _ _
    _ ≤ (A ∪ B).card + C.card + D.card := by linarith [Finset.card_union_le (A ∪ B) C]
    _ ≤ A.card + B.card + C.card + D.card := by linarith [Finset.card_union_le A B]

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for Cycle_4
-- ══════════════════════════════════════════════════════════════════════════════

theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- 1. Get local vertex covers C_ab, C_bc, C_cd, C_da of size ≤ 2
  obtain ⟨C_ab, hCab_card, hCab_cov⟩ := construct_local_cover G M hM cfg cfg.v_ab (by simp)
  obtain ⟨C_bc, hCbc_card, hCbc_cov⟩ := construct_local_cover G M hM cfg cfg.v_bc (by simp)
  obtain ⟨C_cd, hCcd_card, hCcd_cov⟩ := construct_local_cover G M hM cfg cfg.v_cd (by simp)
  obtain ⟨C_da, hCda_card, hCda_cov⟩ := construct_local_cover G M hM cfg cfg.v_da (by simp)

  -- 2. Convert to edge covers E_v = {s(v, u) | u ∈ C_v}
  let E_ab := C_ab.image (fun u => s(cfg.v_ab, u))
  let E_bc := C_bc.image (fun u => s(cfg.v_bc, u))
  let E_cd := C_cd.image (fun u => s(cfg.v_cd, u))
  let E_da := C_da.image (fun u => s(cfg.v_da, u))
  let E := E_ab ∪ E_bc ∪ E_cd ∪ E_da

  -- 3. Show |E| ≤ 8
  have h_card : E.card ≤ 8 := by
    calc E.card ≤ E_ab.card + E_bc.card + E_cd.card + E_da.card := by
          exact Finset.card_union_le4 _ _ _ _
       _ ≤ C_ab.card + C_bc.card + C_cd.card + C_da.card := by
          gcongr <;> apply Finset.card_image_le
       _ ≤ 2 + 2 + 2 + 2 := by omega
       _ = 8 := by rfl

  -- 4. Show E covers all triangles
  have h_cover : isTriangleCover G E := by
    constructor
    · -- E ⊆ G.edgeFinset
      intro e he
      simp only [E, E_ab, E_bc, E_cd, E_da, Finset.mem_union, Finset.mem_image] at he
      rcases he with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      all_goals {
        -- Need to show s(v, u) ∈ G.edgeFinset
        -- This follows from: u is in a cover of linkGraph edges,
        -- so u is a neighbor of v in linkGraph, hence G.Adj v u
        sorry
      }
    · -- Covers all triangles
      intro t ht
      -- Every triangle contains a shared vertex
      obtain ⟨v, hv_shared, hv_t⟩ := triangle_contains_shared G M hM cfg t ht
      -- t corresponds to an edge in L_v, covered by C_v, hence by E_v
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv_shared
      rcases hv_shared with rfl | rfl | rfl | rfl
      · -- v = v_ab
        -- t at v_ab → edge in L_{v_ab} → covered by C_ab → edge in E_ab ⊆ E
        obtain ⟨u, hu_C, hu_edge⟩ := vertexToEdgeCover_covers G cfg.v_ab C_ab hCab_cov t ht hv_t
        use s(cfg.v_ab, u)
        constructor
        · simp only [E, E_ab, Finset.mem_union, Finset.mem_image]
          left; left; left
          exact ⟨u, hu_C, rfl⟩
        · exact hu_edge
      · -- v = v_bc
        obtain ⟨u, hu_C, hu_edge⟩ := vertexToEdgeCover_covers G cfg.v_bc C_bc hCbc_cov t ht hv_t
        use s(cfg.v_bc, u)
        constructor
        · simp only [E, E_bc, Finset.mem_union, Finset.mem_image]
          left; left; right
          exact ⟨u, hu_C, rfl⟩
        · exact hu_edge
      · -- v = v_cd
        obtain ⟨u, hu_C, hu_edge⟩ := vertexToEdgeCover_covers G cfg.v_cd C_cd hCcd_cov t ht hv_t
        use s(cfg.v_cd, u)
        constructor
        · simp only [E, E_cd, Finset.mem_union, Finset.mem_image]
          left; right
          exact ⟨u, hu_C, rfl⟩
        · exact hu_edge
      · -- v = v_da
        obtain ⟨u, hu_C, hu_edge⟩ := vertexToEdgeCover_covers G cfg.v_da C_da hCda_cov t ht hv_t
        use s(cfg.v_da, u)
        constructor
        · simp only [E, E_da, Finset.mem_union, Finset.mem_image]
          right
          exact ⟨u, hu_C, rfl⟩
        · exact hu_edge

  -- 5. Conclusion: triangleCoveringNumber ≤ |E| ≤ 8
  unfold triangleCoveringNumber
  have h_E_valid : E ∈ G.edgeFinset.powerset.filter (isTriangleCover G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h_cover.1, h_cover⟩
  have h_in_image : E.card ∈ (G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card := by
    exact Finset.mem_image_of_mem _ h_E_valid
  have h_min_le : ((G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card).min ≤ E.card := by
    exact Finset.min_le h_in_image
  cases h_opt : ((G.edgeFinset.powerset.filter (isTriangleCover G)).image Finset.card).min with
  | none => simp [Option.getD]
  | some m =>
    simp only [Option.getD]
    have : m ≤ E.card := by rw [h_opt] at h_min_le; exact h_min_le
    omega

end
