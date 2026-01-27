/-
  slot476_tau_from_6packing_v2.lean

  IMPROVED VERSION: Handles all 3 cases of which edge-type is empty

  KEY LEMMA: 6-packing constraint → τ(S_e) ≤ 2

  PROOF STRATEGY:
  1. slot412 proves: At most 2 of 3 edges of any packing element can have externals
  2. Case split on WHICH edge-type is empty:
     - Case {a,c} empty: use {s(a,b), s(b,c)}
     - Case {a,b} empty: use {s(b,c), s(a,c)}
     - Case {b,c} empty: use {s(a,b), s(a,c)}
  3. In each case, the 2 edges cover all triangles in S_e
  4. 4 elements × 2 edges = 8 edges total

  TIER: 2 (uses proven 6-packing as axiom, focuses on cover construction)
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (standard)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

/-- Triangles sharing edge with e -/
def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => (t ∩ e).card ≥ 2)

/-- S_e: Triangles sharing edge with e but edge-disjoint from OTHER M-elements -/
def S_e (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e).filter (fun t => ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1)

/-- S_e elements using specific edge {a,b} of e = {a,b,c} -/
def S_e_edge (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V))
    (a b c : V) : Finset (Finset V) :=
  (S_e G M {a, b, c}).filter (fun T => a ∈ T ∧ b ∈ T ∧ c ∉ T)

-- ══════════════════════════════════════════════════════════════════════════════
-- AXIOM: 6-PACKING CONSTRAINT (proven in slot412)
-- ══════════════════════════════════════════════════════════════════════════════

/--
AXIOM: slot412's proven theorem.
At most 2 of 3 edge-types can have externals when ν = 4.
Proof: If all 3 exist, get 6-packing contradicting ν = 4.
-/
axiom not_all_three_edge_types (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (a b c : V) (hE : {a, b, c} ∈ M) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ {a, b, c}) (hC_ne : C ≠ {a, b, c}) (hD_ne : D ≠ {a, b, c})
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hB_tri : B ∈ G.cliqueFinset 3) (hC_tri : C ∈ G.cliqueFinset 3) (hD_tri : D ∈ G.cliqueFinset 3) :
    ¬((S_e_edge G M a b c).Nonempty ∧
      (S_e_edge G M b c a).Nonempty ∧
      (S_e_edge G M a c b).Nonempty)

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Triangle shares edge with {a,b,c} iff shares 2+ vertices
-- ══════════════════════════════════════════════════════════════════════════════

/--
If t shares ≥2 vertices with {a,b,c}, then t contains one of the edges:
{a,b}, {b,c}, or {a,c}.

PROOF SKETCH:
1. t ∩ {a,b,c} has card ≥ 2
2. Since |{a,b,c}| = 3 and |t ∩ {a,b,c}| ≥ 2:
   - Either 2 or 3 vertices are shared
3. If 3 shared: {a,b} ⊆ t (and all other pairs too)
4. If 2 shared: exactly one of {a,b}, {b,c}, {a,c} is in t
5. In any case, at least one pair is in t
-/
lemma triangle_shares_pair_with_abc (t : Finset V)
    (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h_share : (t ∩ {a, b, c}).card ≥ 2) :
    ({a, b} ⊆ t) ∨ ({b, c} ⊆ t) ∨ ({a, c} ⊆ t) := by
  -- t shares ≥2 vertices with {a,b,c}
  -- Case analysis on which vertices are shared
  by_cases ha : a ∈ t <;> by_cases hb : b ∈ t <;> by_cases hc : c ∈ t
  · -- a, b, c all in t: {a,b} ⊆ t
    left; simp [ha, hb]
  · -- a, b in t, c not in t: {a,b} ⊆ t
    left; simp [ha, hb]
  · -- a, c in t, b not in t: {a,c} ⊆ t
    right; right; simp [ha, hc]
  · -- Only a in t: can't have card ≥ 2
    exfalso
    have : t ∩ {a, b, c} = {a} := by
      ext x; simp [mem_inter, mem_insert, mem_singleton]
      constructor
      · intro ⟨hx, hx'⟩
        rcases hx' with rfl | rfl | rfl
        · rfl
        · exact absurd hx hb
        · exact absurd hx hc
      · intro hx; rw [hx]; exact ⟨ha, Or.inl rfl⟩
    rw [this] at h_share
    simp at h_share
  · -- b, c in t, a not in t: {b,c} ⊆ t
    right; left; simp [hb, hc]
  · -- Only b in t: can't have card ≥ 2
    exfalso
    have : t ∩ {a, b, c} = {b} := by
      ext x; simp [mem_inter, mem_insert, mem_singleton]
      constructor
      · intro ⟨hx, hx'⟩
        rcases hx' with rfl | rfl | rfl
        · exact absurd hx ha
        · rfl
        · exact absurd hx hc
      · intro hx; rw [hx]; exact ⟨hb, Or.inr (Or.inl rfl)⟩
    rw [this] at h_share
    simp at h_share
  · -- Only c in t: can't have card ≥ 2
    exfalso
    have : t ∩ {a, b, c} = {c} := by
      ext x; simp [mem_inter, mem_insert, mem_singleton]
      constructor
      · intro ⟨hx, hx'⟩
        rcases hx' with rfl | rfl | rfl
        · exact absurd hx ha
        · exact absurd hx hb
        · rfl
      · intro hx; rw [hx]; exact ⟨hc, Or.inr (Or.inr rfl)⟩
    rw [this] at h_share
    simp at h_share
  · -- None in t: can't have card ≥ 2
    exfalso
    have : t ∩ {a, b, c} = ∅ := by
      ext x; simp [mem_inter, mem_insert, mem_singleton]
      intro hx hx'
      rcases hx' with rfl | rfl | rfl
      · exact ha hx
      · exact hb hx
      · exact hc hx
    rw [this] at h_share
    simp at h_share

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Edge in sym2
-- ══════════════════════════════════════════════════════════════════════════════

lemma pair_subset_implies_sym2 (t : Finset V) (a b : V) (hab : a ≠ b)
    (h : {a, b} ⊆ t) : s(a, b) ∈ t.sym2 := by
  rw [Finset.mem_sym2_iff]
  constructor
  · exact h (mem_insert_self a _)
  · exact h (mem_insert_of_mem (mem_singleton_self b))

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: 2 edges cover S_e
-- ══════════════════════════════════════════════════════════════════════════════

/--
If at most 2 edge-types have externals, then S_e can be covered by 2 edges.

PROOF SKETCH:
1. Let e = {a,b,c}
2. By 6-packing constraint (slot412), not all 3 edge-types have externals
3. Case split on which edge-type is empty:
   - If {a,c} empty: cover = {s(a,b), s(b,c)}
   - If {a,b} empty: cover = {s(b,c), s(a,c)}
   - If {b,c} empty: cover = {s(a,b), s(a,c)}
4. For any t ∈ S_e:
   - t shares ≥2 vertices with e (by S_e definition)
   - So t contains one of {a,b}, {b,c}, {a,c} (by triangle_shares_pair_with_abc)
   - If t contains the "empty" edge: t is NOT an external (in S_e_edge)
     - Either t = e (covered by our 2 edges since e contains all 3 pairs)
     - Or t is the original triangle e itself
   - If t contains one of the "active" edges: covered by our 2-edge set
-/
theorem two_edges_cover_Se (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (e : Finset V) (he : e ∈ M) (he_tri : e ∈ G.cliqueFinset 3)
    (a b c : V) (he_abc : e = {a, b, c}) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (B C D : Finset V) (hB : B ∈ M) (hC : C ∈ M) (hD : D ∈ M)
    (hB_ne : B ≠ e) (hC_ne : C ≠ e) (hD_ne : D ≠ e)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hB_tri : B ∈ G.cliqueFinset 3) (hC_tri : C ∈ G.cliqueFinset 3) (hD_tri : D ∈ G.cliqueFinset 3) :
    ∃ E' : Finset (Sym2 V), E'.card ≤ 2 ∧ E' ⊆ G.edgeFinset ∧
      ∀ t ∈ S_e G M e, ∃ edge ∈ E', edge ∈ t.sym2 := by
  -- Get that the edges of e are in G.edgeFinset
  have h_clique := SimpleGraph.mem_cliqueFinset_iff.mp he_tri
  have hab_edge : s(a, b) ∈ G.edgeFinset := by
    rw [he_abc] at h_clique
    exact h_clique.2 (by simp [hab]) (by simp) (by simp)
  have hbc_edge : s(b, c) ∈ G.edgeFinset := by
    rw [he_abc] at h_clique
    exact h_clique.2 (by simp [hbc]) (by simp) (by simp)
  have hac_edge : s(a, c) ∈ G.edgeFinset := by
    rw [he_abc] at h_clique
    exact h_clique.2 (by simp [hac]) (by simp) (by simp)
  -- By 6-packing constraint, at least one edge-type is empty
  have h_constraint := not_all_three_edge_types G M hM hNu4 a b c
    (he_abc ▸ he) hab hbc hac B C D hB hC hD
    (he_abc ▸ hB_ne) (he_abc ▸ hC_ne) (he_abc ▸ hD_ne)
    hBC hBD hCD hB_tri hC_tri hD_tri
  push_neg at h_constraint
  -- Case split: which edge-type is empty
  /-
  PROOF SKETCH for the case split:
  h_constraint says: one of the three S_e_edge sets is empty
  - If (S_e_edge G M a b c) empty: no externals use {a,b} avoiding c
    → use cover {s(b,c), s(a,c)}
  - If (S_e_edge G M b c a) empty: no externals use {b,c} avoiding a
    → use cover {s(a,b), s(a,c)}
  - If (S_e_edge G M a c b) empty: no externals use {a,c} avoiding b
    → use cover {s(a,b), s(b,c)}
  -/
  obtain h_ab_empty | h_bc_or_ac := h_constraint
  -- Case: {a,b}-externals empty (no triangle uses {a,b} while avoiding c)
  case inl =>
    use {s(b, c), s(a, c)}
    refine ⟨?_, ?_, ?_⟩
    · -- card ≤ 2
      simp only [card_insert_of_not_mem, card_singleton]
      by_cases h : s(b, c) = s(a, c)
      · simp [h]
      · simp [h]
    · -- subset of G.edgeFinset
      intro e' he'
      simp only [mem_insert, mem_singleton] at he'
      rcases he' with rfl | rfl
      · exact hbc_edge
      · exact hac_edge
    · -- covers all of S_e
      intro t ht
      simp only [S_e, trianglesSharingEdge, mem_filter] at ht
      have h_share := ht.1.2
      rw [he_abc] at h_share
      -- t shares ≥2 vertices with {a,b,c}
      have h_pair := triangle_shares_pair_with_abc t a b c hab hbc hac h_share
      rcases h_pair with hab_in | hbc_in | hac_in
      · -- t contains {a,b}
        -- Either t = e, or t is an external using {a,b}
        -- If t = e: e contains {b,c}, so s(b,c) ∈ e.sym2
        -- If t ≠ e and t uses {a,b}: either c ∈ t or c ∉ t
        --   If c ∈ t: t = e (same triangle)
        --   If c ∉ t: t ∈ S_e_edge G M a b c, contradicting h_ab_empty
        by_cases hte : t = e
        · -- t = e: s(b,c) ∈ e.sym2
          use s(b, c)
          constructor
          · simp
          · rw [hte, he_abc]
            apply pair_subset_implies_sym2
            · exact hbc
            · simp
        · -- t ≠ e
          by_cases hc_in_t : c ∈ t
          · -- a, b, c all in t: t is a triangle with same vertices as e
            -- Since t is a 3-clique and {a,b,c} ⊆ t and |t| = 3, t = {a,b,c} = e
            have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht.1.1).card_eq
            have : {a, b, c} ⊆ t := by
              intro x hx
              simp at hx
              rcases hx with rfl | rfl | rfl
              · exact hab_in (mem_insert_self a _)
              · exact hab_in (mem_insert_of_mem (mem_singleton_self b))
              · exact hc_in_t
            have heq : t = {a, b, c} := by
              apply Finset.eq_of_subset_of_card_le this
              simp [hab, hbc, hac]
              omega
            rw [← he_abc] at heq
            exact absurd heq hte
          · -- a, b in t, c not in t: t ∈ S_e_edge G M a b c
            -- But h_ab_empty says this set is empty!
            exfalso
            have ht_in_Se_edge : t ∈ S_e_edge G M a b c := by
              simp only [S_e_edge, mem_filter]
              constructor
              · rw [← he_abc]; exact ht
              · exact ⟨hab_in (mem_insert_self a _),
                       hab_in (mem_insert_of_mem (mem_singleton_self b)),
                       hc_in_t⟩
            exact h_ab_empty ⟨t, ht_in_Se_edge⟩
      · -- t contains {b,c}: s(b,c) ∈ t.sym2
        use s(b, c)
        constructor
        · simp
        · exact pair_subset_implies_sym2 t b c hbc hbc_in
      · -- t contains {a,c}: s(a,c) ∈ t.sym2
        use s(a, c)
        constructor
        · simp
        · exact pair_subset_implies_sym2 t a c hac hac_in
  -- Remaining cases: {b,c}-externals empty OR {a,c}-externals empty
  case inr =>
    obtain h_bc_empty | h_ac_empty := h_bc_or_ac
    -- Case: {b,c}-externals empty
    case inl =>
      use {s(a, b), s(a, c)}
      refine ⟨?_, ?_, ?_⟩
      · simp only [card_insert_of_not_mem, card_singleton]
        by_cases h : s(a, b) = s(a, c); simp [h]; simp [h]
      · intro e' he'; simp at he'
        rcases he' with rfl | rfl; exact hab_edge; exact hac_edge
      · intro t ht
        simp only [S_e, trianglesSharingEdge, mem_filter] at ht
        have h_share := ht.1.2; rw [he_abc] at h_share
        have h_pair := triangle_shares_pair_with_abc t a b c hab hbc hac h_share
        rcases h_pair with hab_in | hbc_in | hac_in
        · use s(a, b); constructor; simp; exact pair_subset_implies_sym2 t a b hab hab_in
        · by_cases hte : t = e
          · use s(a, b); constructor; simp; rw [hte, he_abc]
            apply pair_subset_implies_sym2; exact hab; simp
          · by_cases ha_in_t : a ∈ t
            · have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht.1.1).card_eq
              have : {a, b, c} ⊆ t := by
                intro x hx; simp at hx
                rcases hx with rfl | rfl | rfl
                · exact ha_in_t
                · exact hbc_in (mem_insert_self b _)
                · exact hbc_in (mem_insert_of_mem (mem_singleton_self c))
              have heq : t = {a, b, c} := by
                apply Finset.eq_of_subset_of_card_le this; simp [hab, hbc, hac]; omega
              rw [← he_abc] at heq; exact absurd heq hte
            · exfalso
              have ht_in_Se_edge : t ∈ S_e_edge G M b c a := by
                simp only [S_e_edge, mem_filter]; constructor
                · rw [← he_abc]; exact ht
                · exact ⟨hbc_in (mem_insert_self b _),
                         hbc_in (mem_insert_of_mem (mem_singleton_self c)),
                         ha_in_t⟩
              exact h_bc_empty ⟨t, ht_in_Se_edge⟩
        · use s(a, c); constructor; simp; exact pair_subset_implies_sym2 t a c hac hac_in
    -- Case: {a,c}-externals empty
    case inr =>
      use {s(a, b), s(b, c)}
      refine ⟨?_, ?_, ?_⟩
      · simp only [card_insert_of_not_mem, card_singleton]
        by_cases h : s(a, b) = s(b, c); simp [h]; simp [h]
      · intro e' he'; simp at he'
        rcases he' with rfl | rfl; exact hab_edge; exact hbc_edge
      · intro t ht
        simp only [S_e, trianglesSharingEdge, mem_filter] at ht
        have h_share := ht.1.2; rw [he_abc] at h_share
        have h_pair := triangle_shares_pair_with_abc t a b c hab hbc hac h_share
        rcases h_pair with hab_in | hbc_in | hac_in
        · use s(a, b); constructor; simp; exact pair_subset_implies_sym2 t a b hab hab_in
        · use s(b, c); constructor; simp; exact pair_subset_implies_sym2 t b c hbc hbc_in
        · by_cases hte : t = e
          · use s(a, b); constructor; simp; rw [hte, he_abc]
            apply pair_subset_implies_sym2; exact hab; simp
          · by_cases hb_in_t : b ∈ t
            · have ht_card : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht.1.1).card_eq
              have : {a, b, c} ⊆ t := by
                intro x hx; simp at hx
                rcases hx with rfl | rfl | rfl
                · exact hac_in (mem_insert_self a _)
                · exact hb_in_t
                · exact hac_in (mem_insert_of_mem (mem_singleton_self c))
              have heq : t = {a, b, c} := by
                apply Finset.eq_of_subset_of_card_le this; simp [hab, hbc, hac]; omega
              rw [← he_abc] at heq; exact absurd heq hte
            · exfalso
              have ht_in_Se_edge : t ∈ S_e_edge G M a c b := by
                simp only [S_e_edge, mem_filter]; constructor
                · rw [← he_abc]; exact ht
                · exact ⟨hac_in (mem_insert_self a _),
                         hac_in (mem_insert_of_mem (mem_singleton_self c)),
                         hb_in_t⟩
              exact h_ac_empty ⟨t, ht_in_Se_edge⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- COROLLARY: τ ≤ 8 when ν = 4
-- ══════════════════════════════════════════════════════════════════════════════

/--
τ ≤ 8 for graphs with ν = 4.

PROOF SKETCH:
1. M = {e₁, e₂, e₃, e₄} is a maximal 4-packing
2. For each eᵢ ∈ M, by two_edges_cover_Se, get Eᵢ with |Eᵢ| ≤ 2
3. Let E' = E₁ ∪ E₂ ∪ E₃ ∪ E₄
4. |E'| ≤ 4 × 2 = 8 (by card_union bounds)
5. For any triangle t ∈ G.cliqueFinset 3:
   - By maximality (hMax), t shares ≥2 vertices with some eᵢ ∈ M
   - t ∈ trianglesSharingEdge G eᵢ
   - Either t shares edge with some other eⱼ (then t ∈ S_eⱼ) or t ∈ S_eᵢ
   - In either case, t is covered by some Eⱼ ⊆ E'
-/
theorem tau_le_8_nu_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isTrianglePacking G M) (hM_card : M.card = 4)
    (hNu4 : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ 4)
    (hMax : ∀ t ∈ G.cliqueFinset 3, ∃ m ∈ M, (t ∩ m).card ≥ 2) :
    ∃ E' : Finset (Sym2 V), E' ⊆ G.edgeFinset ∧ E'.card ≤ 8 ∧
      ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2 := by
  /-
  PROOF SKETCH:
  This requires instantiating two_edges_cover_Se for each element of M.
  The main technical challenge is:
  1. Extract a,b,c from each m ∈ M (since m ∈ G.cliqueFinset 3)
  2. Get the other 3 elements B,C,D for each
  3. Apply two_edges_cover_Se to get E_m
  4. Take union ⋃ E_m

  For Aristotle: Use Finset.biUnion over M, bounding card by sum.
  -/
  sorry -- Aristotle: construct union and verify coverage

end
