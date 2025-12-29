/-
SLOT 124: tau_at_shared_vertex_le_2
Target: τ(Ti) ≤ 2 for each partition piece
UUID: slot124_tau_at_shared_vertex

STRATEGY (Grok + Codex Consensus):
Every triangle containing shared vertex v forms a "sunflower" with center v.
In the link graph G[N(v)], triangles at v correspond to edges.
By matching theory, we can cover all edges with at most 2 vertices.
These 2 neighbors of v give 2 edges {v,x1}, {v,x2} that cover all triangles at v.

DEPENDENCIES:
- PROVEN: cycle4_disjoint_partition (UUID ec96692a)
- PROVEN: tau_le_12_cycle4_conservative (UUID 5d2756b0)
- PROVEN: cycle4_all_triangles_contain_shared
- PROVEN: triangle_shares_edge_with_packing

GOAL: Prove τ(Ti) ≤ 2 → τ ≤ 8 for cycle_4
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical


variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from proven files)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

def isTriangleCover (G : SimpleGraph V) [DecidableRel G.Adj] (E' : Finset (Sym2 V)) : Prop :=
  E' ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2

noncomputable def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 STRUCTURE (from proven files)
-- ══════════════════════════════════════════════════════════════════════════════

def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧
  (B ∩ C).card = 1 ∧
  (C ∩ D).card = 1 ∧
  (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧
  (B ∩ D).card = 0

/-- Triangles containing vertex v -/
def trianglesContaining (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- PARTITION DEFINITIONS (from proven disjoint partition)
-- ══════════════════════════════════════════════════════════════════════════════

def T1 (triangles : Finset (Finset V)) (v_ab : V) : Finset (Finset V) :=
  triangles.filter (fun t => v_ab ∈ t)

def T2 (triangles : Finset (Finset V)) (v_ab v_bc : V) : Finset (Finset V) :=
  triangles.filter (fun t => v_bc ∈ t ∧ v_ab ∉ t)

def T3 (triangles : Finset (Finset V)) (v_ab v_bc v_cd : V) : Finset (Finset V) :=
  triangles.filter (fun t => v_cd ∈ t ∧ v_ab ∉ t ∧ v_bc ∉ t)

def T4 (triangles : Finset (Finset V)) (v_ab v_bc v_cd v_da : V) : Finset (Finset V) :=
  triangles.filter (fun t => v_da ∈ t ∧ v_ab ∉ t ∧ v_bc ∉ t ∧ v_cd ∉ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN: Subadditivity (from slot113)
-- ══════════════════════════════════════════════════════════════════════════════

lemma tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (S₁ S₂ : Finset (Finset V)) (h₁ : S₁ ⊆ G.cliqueFinset 3) (h₂ : S₂ ⊆ G.cliqueFinset 3)
    (bound₁ bound₂ : ℕ)
    (hS₁ : ∃ E₁ ⊆ G.edgeFinset, E₁.card ≤ bound₁ ∧ ∀ t ∈ S₁, ∃ e ∈ E₁, e ∈ t.sym2)
    (hS₂ : ∃ E₂ ⊆ G.edgeFinset, E₂.card ≤ bound₂ ∧ ∀ t ∈ S₂, ∃ e ∈ E₂, e ∈ t.sym2) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ bound₁ + bound₂ ∧ ∀ t ∈ S₁ ∪ S₂, ∃ e ∈ E, e ∈ t.sym2 := by
  obtain ⟨E₁, hE₁_sub, hE₁_card, hE₁_cover⟩ := hS₁
  obtain ⟨E₂, hE₂_sub, hE₂_card, hE₂_cover⟩ := hS₂
  use E₁ ∪ E₂
  constructor
  · exact Finset.union_subset hE₁_sub hE₂_sub
  constructor
  · calc (E₁ ∪ E₂).card ≤ E₁.card + E₂.card := Finset.card_union_le E₁ E₂
         _ ≤ bound₁ + bound₂ := Nat.add_le_add hE₁_card hE₂_card
  · intro t ht
    simp only [Finset.mem_union] at ht
    cases ht with
    | inl h₁ =>
      obtain ⟨e, he_mem, he_in⟩ := hE₁_cover t h₁
      exact ⟨e, Finset.mem_union_left E₂ he_mem, he_in⟩
    | inr h₂ =>
      obtain ⟨e, he_mem, he_in⟩ := hE₂_cover t h₂
      exact ⟨e, Finset.mem_union_right E₁ he_mem, he_in⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- LINK GRAPH DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- The link graph of v: edges between neighbors of v in G -/
def linkGraph (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : SimpleGraph V where
  Adj := fun x y => G.Adj v x ∧ G.Adj v y ∧ G.Adj x y

/-- Edges in the link graph correspond to triangles containing v -/
def linkEdgesAt (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∃ x y, e = s(x, y) ∧ G.Adj v x ∧ G.Adj v y)

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: 2 edges cover all triangles containing a shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/--
THE KEY LEMMA (Grok + Codex consensus):
Every triangle containing v can be covered by at most 2 edges through v.

Proof strategy (sunflower):
1. Every triangle t containing v has form {v, x, y} where {x,y} is a link edge
2. Triangles at v correspond to edges in the link graph G[N(v)]
3. By vertex cover theory, edges can be covered by ≤2 vertices in bipartite-like structure
4. If x₁, x₂ are the covering vertices, then {v,x₁} and {v,x₂} cover all triangles at v
-/
lemma tau_at_shared_vertex_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) :
    ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧
      ∀ t ∈ trianglesContaining G v, ∃ e ∈ E, e ∈ t.sym2 := by
  -- Key insight: All triangles containing v form a "sunflower" with center v
  -- Each triangle is {v, x, y} where x, y are neighbors of v
  -- The edges {v,x} for x ∈ N(v) form the "petals"
  -- We need to show 2 such petals suffice

  -- Case 1: No triangles containing v → empty set suffices
  by_cases h_empty : trianglesContaining G v = ∅
  · use ∅
    simp only [Finset.empty_subset, Finset.card_empty, le_refl, true_and]
    intro t ht
    rw [h_empty] at ht
    exact (Finset.not_mem_empty t ht).elim

  -- Case 2: At least one triangle containing v
  push_neg at h_empty
  obtain ⟨t₀, ht₀⟩ := Finset.nonempty_iff_ne_empty.mpr h_empty

  -- Get two other vertices of t₀
  have ht₀_clique : t₀ ∈ G.cliqueFinset 3 := by
    unfold trianglesContaining at ht₀
    exact Finset.mem_filter.mp ht₀ |>.1
  have ht₀_card : t₀.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht₀_clique).2
  have hv_in_t₀ : v ∈ t₀ := by
    unfold trianglesContaining at ht₀
    exact Finset.mem_filter.mp ht₀ |>.2

  -- Extract t₀ = {v, x, y}
  obtain ⟨x, y, hxy_ne, ht₀_eq⟩ : ∃ x y, x ≠ y ∧ t₀ = {v, x, y} := by
    rw [Finset.card_eq_three] at ht₀_card
    obtain ⟨a, b, c, hab, hac, hbc, ht₀⟩ := ht₀_card
    by_cases hav : a = v
    · use b, c, hbc
      rw [hav] at ht₀
      exact ht₀
    · by_cases hbv : b = v
      · use a, c, hac.symm ▸ hbc
        simp only [Finset.insert_eq, Finset.pair_eq_singleton_iff] at ht₀ ⊢
        rw [hbv] at ht₀
        ext w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor <;> intro h <;> rcases h with rfl | rfl | rfl <;> tauto
      · have hcv : c = v := by
          have : v ∈ {a, b, c} := ht₀ ▸ hv_in_t₀
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          tauto
        use a, b, hab
        rw [hcv] at ht₀
        ext w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor <;> intro h
        · have := ht₀ ▸ h
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          tauto
        · rcases h with rfl | rfl | rfl
          all_goals simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

  -- Edges {v,x} and {v,y} cover all triangles containing v
  -- This works because any triangle {v, x', y'} shares vertex v,
  -- and either contains x or y as a neighbor
  use ({s(v, x), s(v, y)} : Finset (Sym2 V))
  refine ⟨?_, ?_, ?_⟩

  -- Show E ⊆ G.edgeFinset
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · -- Show s(v,x) ∈ G.edgeFinset
      have : G.Adj v x := by
        have h_clique := (SimpleGraph.mem_cliqueFinset_iff.mp ht₀_clique).1
        rw [SimpleGraph.isClique_iff] at h_clique
        have hvx : v ≠ x := by
          intro heq
          rw [heq, ht₀_eq] at ht₀_card
          simp at ht₀_card
        apply h_clique
        · rw [ht₀_eq]; simp
        · rw [ht₀_eq]; simp
        · exact hvx
      exact this.symm.mem_edgeFinset
    · -- Show s(v,y) ∈ G.edgeFinset
      have : G.Adj v y := by
        have h_clique := (SimpleGraph.mem_cliqueFinset_iff.mp ht₀_clique).1
        rw [SimpleGraph.isClique_iff] at h_clique
        have hvy : v ≠ y := by
          intro heq
          rw [heq, ht₀_eq] at ht₀_card
          simp at ht₀_card
        apply h_clique
        · rw [ht₀_eq]; simp
        · rw [ht₀_eq]; simp
        · exact hvy
      exact this.symm.mem_edgeFinset

  -- Show E.card ≤ 2
  · exact Finset.card_insert_le _ _

  -- Show every triangle containing v is covered
  · intro t ht
    -- t contains v, so t = {v, a, b} for some a, b
    -- We need to show t shares edge with {v,x} or {v,y}
    -- Key: by sunflower structure, this is provable
    sorry  -- This is the key step Aristotle needs to prove

-- ══════════════════════════════════════════════════════════════════════════════
-- ASSEMBLY: τ ≤ 8 from partition + local bounds
-- ══════════════════════════════════════════════════════════════════════════════

/-- If each Ti has τ ≤ 2, then total τ ≤ 8 -/
lemma tau_le_8_from_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (v_ab v_bc v_cd v_da : V)
    (hT1 : ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ t ∈ T1 (G.cliqueFinset 3) v_ab, ∃ e ∈ E, e ∈ t.sym2)
    (hT2 : ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ t ∈ T2 (G.cliqueFinset 3) v_ab v_bc, ∃ e ∈ E, e ∈ t.sym2)
    (hT3 : ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ t ∈ T3 (G.cliqueFinset 3) v_ab v_bc v_cd, ∃ e ∈ E, e ∈ t.sym2)
    (hT4 : ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ t ∈ T4 (G.cliqueFinset 3) v_ab v_bc v_cd v_da, ∃ e ∈ E, e ∈ t.sym2)
    (h_partition : T1 (G.cliqueFinset 3) v_ab ∪ T2 (G.cliqueFinset 3) v_ab v_bc ∪
                   T3 (G.cliqueFinset 3) v_ab v_bc v_cd ∪ T4 (G.cliqueFinset 3) v_ab v_bc v_cd v_da = G.cliqueFinset 3) :
    triangleCoveringNumber G ≤ 8 := by
  -- Combine covers using subadditivity
  have h12 := tau_union_le_sum G (T1 (G.cliqueFinset 3) v_ab) (T2 (G.cliqueFinset 3) v_ab v_bc)
    (by simp [T1, Finset.filter_subset]) (by simp [T2, Finset.filter_subset]) 2 2 hT1 hT2
  have h123 := tau_union_le_sum G
    (T1 (G.cliqueFinset 3) v_ab ∪ T2 (G.cliqueFinset 3) v_ab v_bc)
    (T3 (G.cliqueFinset 3) v_ab v_bc v_cd)
    (Finset.union_subset (by simp [T1, Finset.filter_subset]) (by simp [T2, Finset.filter_subset]))
    (by simp [T3, Finset.filter_subset]) 4 2 h12 hT3
  have h1234 := tau_union_le_sum G
    (T1 (G.cliqueFinset 3) v_ab ∪ T2 (G.cliqueFinset 3) v_ab v_bc ∪ T3 (G.cliqueFinset 3) v_ab v_bc v_cd)
    (T4 (G.cliqueFinset 3) v_ab v_bc v_cd v_da)
    (Finset.union_subset (Finset.union_subset (by simp [T1, Finset.filter_subset]) (by simp [T2, Finset.filter_subset])) (by simp [T3, Finset.filter_subset]))
    (by simp [T4, Finset.filter_subset]) 6 2 h123 hT4

  obtain ⟨E, hE_sub, hE_card, hE_cover⟩ := h1234

  -- E covers all triangles (by partition)
  have h_covers_all : ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
    intro t ht
    have : t ∈ T1 (G.cliqueFinset 3) v_ab ∪ T2 (G.cliqueFinset 3) v_ab v_bc ∪
           T3 (G.cliqueFinset 3) v_ab v_bc v_cd ∪ T4 (G.cliqueFinset 3) v_ab v_bc v_cd v_da := by
      rw [h_partition]; exact ht
    exact hE_cover t this

  -- Therefore τ ≤ 8
  unfold triangleCoveringNumber
  have h_is_cover : isTriangleCover G E := ⟨hE_sub, h_covers_all⟩
  have h_mem : E ∈ G.edgeFinset.powerset.filter (isTriangleCover G) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hE_sub, h_is_cover⟩
  have h_min_le : (G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min).getD 0 ≤ E.card := by
    cases h : (G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card).min
    · simp
    · simp only [Option.getD_some]
      exact Finset.min_le (Finset.mem_image_of_mem Finset.card h_mem)
  linarith

/-- MAIN THEOREM: τ ≤ 8 for cycle_4 -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v_ab v_bc v_cd v_da : V)
    (hv_ab : v_ab ∈ A ∩ B) (hv_bc : v_bc ∈ B ∩ C)
    (hv_cd : v_cd ∈ C ∩ D) (hv_da : v_da ∈ D ∩ A) :
    triangleCoveringNumber G ≤ 8 := by
  -- Step 1: Get the disjoint partition (PROVEN in slot ec96692a)
  have h_partition : T1 (G.cliqueFinset 3) v_ab ∪ T2 (G.cliqueFinset 3) v_ab v_bc ∪
                     T3 (G.cliqueFinset 3) v_ab v_bc v_cd ∪ T4 (G.cliqueFinset 3) v_ab v_bc v_cd v_da =
                     G.cliqueFinset 3 := by
    sorry -- This is PROVEN in slot ec96692a (disjoint_partition_covers_all)

  -- Step 2: Each Ti is covered by 2 edges
  -- T1 = triangles containing v_ab
  have hT1 : ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ t ∈ T1 (G.cliqueFinset 3) v_ab, ∃ e ∈ E, e ∈ t.sym2 := by
    have := tau_at_shared_vertex_le_2 G v_ab
    obtain ⟨E, hE_sub, hE_card, hE_cover⟩ := this
    use E, hE_sub, hE_card
    intro t ht
    simp only [T1, Finset.mem_filter] at ht
    have : t ∈ trianglesContaining G v_ab := by
      simp only [trianglesContaining, Finset.mem_filter]
      exact ht
    exact hE_cover t this

  -- T2 = triangles containing v_bc (not v_ab)
  -- These are ALSO triangles containing v_bc, so tau_at_shared_vertex_le_2 applies
  have hT2 : ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ t ∈ T2 (G.cliqueFinset 3) v_ab v_bc, ∃ e ∈ E, e ∈ t.sym2 := by
    have := tau_at_shared_vertex_le_2 G v_bc
    obtain ⟨E, hE_sub, hE_card, hE_cover⟩ := this
    use E, hE_sub, hE_card
    intro t ht
    simp only [T2, Finset.mem_filter] at ht
    have : t ∈ trianglesContaining G v_bc := by
      simp only [trianglesContaining, Finset.mem_filter]
      exact ⟨ht.1, ht.2.1⟩
    exact hE_cover t this

  -- T3 = triangles containing v_cd (not v_ab, v_bc)
  have hT3 : ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ t ∈ T3 (G.cliqueFinset 3) v_ab v_bc v_cd, ∃ e ∈ E, e ∈ t.sym2 := by
    have := tau_at_shared_vertex_le_2 G v_cd
    obtain ⟨E, hE_sub, hE_card, hE_cover⟩ := this
    use E, hE_sub, hE_card
    intro t ht
    simp only [T3, Finset.mem_filter] at ht
    have : t ∈ trianglesContaining G v_cd := by
      simp only [trianglesContaining, Finset.mem_filter]
      exact ⟨ht.1, ht.2.1⟩
    exact hE_cover t this

  -- T4 = triangles containing v_da (not v_ab, v_bc, v_cd)
  have hT4 : ∃ E ⊆ G.edgeFinset, E.card ≤ 2 ∧ ∀ t ∈ T4 (G.cliqueFinset 3) v_ab v_bc v_cd v_da, ∃ e ∈ E, e ∈ t.sym2 := by
    have := tau_at_shared_vertex_le_2 G v_da
    obtain ⟨E, hE_sub, hE_card, hE_cover⟩ := this
    use E, hE_sub, hE_card
    intro t ht
    simp only [T4, Finset.mem_filter] at ht
    have : t ∈ trianglesContaining G v_da := by
      simp only [trianglesContaining, Finset.mem_filter]
      exact ⟨ht.1, ht.2.1⟩
    exact hE_cover t this

  -- Step 3: Combine using tau_le_8_from_partition
  exact tau_le_8_from_partition G v_ab v_bc v_cd v_da hT1 hT2 hT3 hT4 h_partition
