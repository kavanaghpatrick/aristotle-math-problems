/-
slot131: External Triangles Share Common Vertex

GOAL: Prove that at a shared vertex v in Cycle4, all "external" triangles
(triangles that share an M-edge at v but are NOT in M) share a common external vertex x.

WHY THIS MATTERS:
- This means we can cover ALL external triangles at v with ONE edge {v, x}
- Combined with covering M with 4 edges (one per element), we get τ ≤ 8

PROOF STRATEGY (Gemini, Dec 28 2025):
By contradiction. Suppose external triangles T1, T2 at v have DIFFERENT external vertices x1 ≠ x2.

1. T1 = {v, m1, x1} where {v, m1} is M-edge, x1 external
2. T2 = {v, m2, x2} where {v, m2} is M-edge, x2 external
3. If x1 ≠ x2, then T1 ∩ T2 contains at most {v, m1} ∩ {v, m2} = {v} (if m1 = m2) or {v} (if m1 ≠ m2)

Actually, for T1 ∩ T2 to have ≤1 element (edge-disjoint), we need:
- m1 ≠ m2 (else they share edge {v, m1})
- x1 ≠ x2 (assumed)
- m1 ≠ x2 and m2 ≠ x1

If T1, T2 are edge-disjoint (share only vertex v):
- Consider {T1, T2, C, D} - check if valid packing
- T1, T2 share edge with A or B (since they use M-edges from A or B)
- But T1 ∉ M means T1 ≠ A, B
- The key: external vertices x1, x2 are NOT in M-vertices

Build packing {T1, T2, C, D} to contradict ν = 4:
- T1 ∩ T2 = {v}, card = 1 ✓
- T1 ∩ C: If v = v_ab, then v ∉ C (diagonal disjoint). x1 ∉ M-vertices means x1 might be in C...
  Actually x1 could be anywhere. Need careful analysis.

KEY INSIGHT: Use the bipartite link graph argument (Gemini):
- In the link graph at v, external triangles correspond to edges {m, x}
- m is M-neighbor (in A or B), x is external
- These form a BIPARTITE structure (M-neighbors vs externals)
- Pairwise intersecting edges in bipartite graph = STAR
- Therefore they all share a common vertex (either same m or same x)
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (standard Tuza setup)
-- ══════════════════════════════════════════════════════════════════════════════

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

/-- M-edges incident to vertex v -/
def M_edges_at (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion (fun X => X.sym2.filter (fun e => v ∈ e))

/-- Triangles that share an M-edge containing v -/
def trianglesSharingMEdgeAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => ∃ e ∈ M_edges_at M v, e ∈ t.sym2)

/-- External triangles at v: those sharing M-edge at v but NOT in M -/
def externalTrianglesAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  trianglesSharingMEdgeAt G M v \ M

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 STRUCTURE (from slot128 proven)
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
  h_vab_A : v_ab ∈ A
  h_vab_B : v_ab ∈ B
  h_vbc_B : v_bc ∈ B
  h_vbc_C : v_bc ∈ C
  h_vcd_C : v_cd ∈ C
  h_vcd_D : v_cd ∈ D
  h_vda_D : v_da ∈ D
  h_vda_A : v_da ∈ A
  h_diag_AC : (A ∩ C).card ≤ 1
  h_diag_BD : (B ∩ D).card ≤ 1
  -- Distinctness (from slot127 proven)
  h_vab_ne_vbc : v_ab ≠ v_bc
  h_vbc_ne_vcd : v_bc ≠ v_cd
  h_vcd_ne_vda : v_cd ≠ v_da
  h_vda_ne_vab : v_da ≠ v_ab

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER LEMMAS
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every triangle in cliqueFinset 3 has exactly 3 vertices -/
lemma triangle_card_eq_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : t.card = 3 :=
  (SimpleGraph.mem_cliqueFinset_iff.mp ht).2

/-- v ∈ A ∩ B means v is in both A and B -/
lemma mem_inter_iff' (v : V) (A B : Finset V) : v ∈ A ∩ B ↔ v ∈ A ∧ v ∈ B :=
  Finset.mem_inter

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: External triangles contain v (proven structure)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Any triangle in trianglesSharingMEdgeAt contains v -/
lemma triangle_sharing_M_edge_contains_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) (t : Finset V)
    (ht : t ∈ trianglesSharingMEdgeAt G M v) : v ∈ t := by
  simp only [trianglesSharingMEdgeAt, Finset.mem_filter] at ht
  obtain ⟨_, e, he_M, he_t⟩ := ht
  simp only [M_edges_at, Finset.mem_biUnion, Finset.mem_filter] at he_M
  obtain ⟨X, _, _, hv_e⟩ := he_M
  -- e is an edge containing v, and e ∈ t.sym2
  simp only [Finset.mem_sym2_iff] at he_t
  obtain ⟨a, b, _, ha, hb, he_eq⟩ := he_t
  simp only [he_eq, Sym2.mem_iff] at hv_e
  cases hv_e with
  | inl h => exact h ▸ ha
  | inr h => exact h ▸ hb

/-- External triangles also contain v -/
lemma external_triangle_contains_v (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) (t : Finset V)
    (ht : t ∈ externalTrianglesAt G M v) : v ∈ t := by
  simp only [externalTrianglesAt, Finset.mem_sdiff] at ht
  exact triangle_sharing_M_edge_contains_v G M v t ht.1

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: External triangles share a common external vertex
-- ══════════════════════════════════════════════════════════════════════════════

/--
Any two external triangles at v share at least TWO vertices (i.e., share an edge).
This means they cannot be edge-disjoint.

PROOF STRATEGY:
By contradiction. If T1 ∩ T2 = {v} (share only v):
- T1 = {v, m1, x1}, T2 = {v, m2, x2}
- T1, T2 use different M-edges (else share that edge)
- Build packing contradicting ν = 4

The bipartite link graph argument shows this is impossible.
-/
theorem external_triangles_share_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (v : V) (h_shared : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da)
    (T1 T2 : Finset V)
    (hT1 : T1 ∈ externalTrianglesAt G M v)
    (hT2 : T2 ∈ externalTrianglesAt G M v)
    (hne : T1 ≠ T2) :
    (T1 ∩ T2).card ≥ 2 := by
  -- Both T1 and T2 contain v
  have hv_T1 := external_triangle_contains_v G M v T1 hT1
  have hv_T2 := external_triangle_contains_v G M v T2 hT2

  -- By contradiction: assume |T1 ∩ T2| ≤ 1
  by_contra h_small
  push_neg at h_small

  -- Since v ∈ T1 ∩ T2, we have |T1 ∩ T2| ≥ 1
  have h_ge_1 : (T1 ∩ T2).card ≥ 1 := by
    apply Finset.one_le_card.mpr
    exact ⟨v, Finset.mem_inter.mpr ⟨hv_T1, hv_T2⟩⟩

  -- So |T1 ∩ T2| = 1, meaning T1 ∩ T2 = {v}
  have h_eq_1 : (T1 ∩ T2).card = 1 := by omega

  -- T1 and T2 are triangles (card = 3)
  have hT1_tri : T1 ∈ G.cliqueFinset 3 := by
    simp only [externalTrianglesAt, trianglesSharingMEdgeAt, Finset.mem_sdiff,
               Finset.mem_filter] at hT1
    exact hT1.1.1
  have hT2_tri : T2 ∈ G.cliqueFinset 3 := by
    simp only [externalTrianglesAt, trianglesSharingMEdgeAt, Finset.mem_sdiff,
               Finset.mem_filter] at hT2
    exact hT2.1.1

  -- Extract the M-edges that T1 and T2 share
  have hT1_shares : ∃ e ∈ M_edges_at M v, e ∈ T1.sym2 := by
    simp only [externalTrianglesAt, trianglesSharingMEdgeAt, Finset.mem_sdiff,
               Finset.mem_filter] at hT1
    exact hT1.1.2
  have hT2_shares : ∃ e ∈ M_edges_at M v, e ∈ T2.sym2 := by
    simp only [externalTrianglesAt, trianglesSharingMEdgeAt, Finset.mem_sdiff,
               Finset.mem_filter] at hT2
    exact hT2.1.2

  -- T1 ∉ M and T2 ∉ M
  have hT1_not_M : T1 ∉ M := by
    simp only [externalTrianglesAt, Finset.mem_sdiff] at hT1; exact hT1.2
  have hT2_not_M : T2 ∉ M := by
    simp only [externalTrianglesAt, Finset.mem_sdiff] at hT2; exact hT2.2

  -- The core contradiction argument:
  -- If T1, T2 share only v, then {T1, T2, C, D} forms a valid packing
  -- that can be extended beyond size 4, contradicting ν = 4

  -- This requires showing that T1, T2 are edge-disjoint from C and D
  -- At v = v_ab, v ∉ C and v ∉ D (diagonal disjointness)
  -- The external vertices x1, x2 may or may not be in C or D

  -- Key case analysis based on which shared vertex v is
  -- (Aristotle should complete this by case analysis)
  sorry

/--
Corollary: All external triangles at v share a common vertex beyond v.

If all pairs share ≥2 vertices (including v), and all contain v,
then either:
1. They all share some edge {v, x} for common x, OR
2. They form a chain where adjacent pairs share different edges through v

Case 2 would require at least 3 external triangles sharing pairwise different
edges through v, but each external triangle uses a different M-neighbor.
At v_ab, M-neighbors are {v_da, a_priv} from A and {v_bc, b_priv} from B (4 total).
With only 4 M-neighbors, and each external triangle using one, we can have
at most 4 external triangles.

By the bipartite link graph argument, if all pairs share an edge, they
form a "star" pattern - all sharing one common vertex (either same M-neighbor
or same external vertex).
-/
theorem external_share_common_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (v : V) (h_shared : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da) :
    ∃ x : V, x ≠ v ∧ ∀ t ∈ externalTrianglesAt G M v, x ∈ t := by
  -- If externalTrianglesAt is empty, any x works vacuously
  by_cases h_empty : externalTrianglesAt G M v = ∅
  · use cfg.v_da  -- arbitrary choice
    constructor
    · rcases h_shared with rfl | rfl | rfl | rfl <;>
      · simp only [ne_eq]
        first | exact cfg.h_vda_ne_vab.symm | exact cfg.h_vda_ne_vab.symm
               | exact cfg.h_vcd_ne_vda.symm | exact Ne.refl _
    · intro t ht; simp [h_empty] at ht

  -- If non-empty, pick an arbitrary external triangle T0
  push_neg at h_empty
  obtain ⟨T0, hT0⟩ := Finset.nonempty_iff_ne_empty.mpr h_empty

  -- T0 = {v, m, x} for some M-neighbor m and external vertex x
  have hT0_tri : T0 ∈ G.cliqueFinset 3 := by
    simp only [externalTrianglesAt, trianglesSharingMEdgeAt, Finset.mem_sdiff,
               Finset.mem_filter] at hT0
    exact hT0.1.1
  have hT0_card : T0.card = 3 := triangle_card_eq_3 G T0 hT0_tri

  -- v ∈ T0
  have hv_T0 := external_triangle_contains_v G M v T0 hT0

  -- T0 has two other vertices besides v
  -- Claim: there exists x ≠ v such that all external triangles contain x
  -- This follows from external_triangles_share_edge: any two share ≥2 vertices
  -- Since they all contain v, and pairs share ≥2, they must share something else

  -- Pick any vertex of T0 other than v as candidate x
  have h_exists : ∃ x ∈ T0, x ≠ v := by
    by_contra h_all_v
    push_neg at h_all_v
    -- If all vertices of T0 equal v, then T0 = {v}, but |T0| = 3
    have : T0 = {v} := by
      ext y
      constructor
      · intro hy; exact Finset.mem_singleton.mpr (h_all_v y hy)
      · intro hy; simp only [Finset.mem_singleton] at hy; exact hy ▸ hv_T0
    rw [this] at hT0_card
    simp at hT0_card

  obtain ⟨x0, hx0_T0, hx0_ne_v⟩ := h_exists

  -- Claim: x0 is in every external triangle at v
  use x0
  constructor
  · exact hx0_ne_v
  · intro t ht
    by_cases h_eq : t = T0
    · exact h_eq ▸ hx0_T0
    · -- t ≠ T0, so by external_triangles_share_edge, |t ∩ T0| ≥ 2
      have h_inter := external_triangles_share_edge G M hM cfg v h_shared t T0 ht hT0 h_eq
      -- t ∩ T0 contains v and at least one other vertex
      have hv_inter : v ∈ t ∩ T0 := by
        apply Finset.mem_inter.mpr
        exact ⟨external_triangle_contains_v G M v t ht, hv_T0⟩
      -- |t ∩ T0| ≥ 2 means there's another vertex in the intersection
      have h_card_inter : (t ∩ T0).card ≥ 2 := h_inter
      -- The intersection contains at least 2 elements, one being v
      -- We need to show x0 is also in the intersection

      -- If x0 ∉ t ∩ T0, then t ∩ T0 ⊆ T0 \ {x0}
      -- But T0 = {v, m, x0} for some m, so T0 \ {x0} = {v, m}
      -- Then t ∩ T0 ⊆ {v, m}, so |t ∩ T0| ≤ 2
      -- If |t ∩ T0| = 2, then t ∩ T0 = {v, m}, so t contains v and m
      -- This means t shares edge {v, m} with T0

      -- We need to show this common edge structure propagates x0
      sorry

/--
Covering external triangles: If all external triangles share {v, x}, then one edge covers them.
-/
theorem external_cover_le_1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M)
    (v : V) (h_shared : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da) :
    ∃ (E : Finset (Sym2 V)), E.card ≤ 1 ∧
    ∀ t ∈ externalTrianglesAt G M v, ∃ e ∈ E, e ∈ t.sym2 := by
  -- Get the common vertex x
  obtain ⟨x, hx_ne_v, hx_all⟩ := external_share_common_vertex G M hM cfg v h_shared

  -- The edge {v, x} covers all external triangles
  use {s(v, x)}
  constructor
  · simp only [Finset.card_singleton, le_refl]
  · intro t ht
    use s(v, x)
    constructor
    · simp only [Finset.mem_singleton]
    · -- s(v, x) ∈ t.sym2 because v ∈ t and x ∈ t
      simp only [Finset.mem_sym2_iff]
      exact ⟨v, x, (hx_ne_v).symm,
             external_triangle_contains_v G M v t ht, hx_all t ht, rfl⟩

end
