/-
Tuza ν=4 Cycle_4: τ ≤ 8 via Constructive Cover

APPROACH 3: Constructive Cover from Matching
=============================================
Given a maximal matching M at each vertex, explicitly construct the cover
by taking one endpoint from each part (for bipartite graphs).

Key insight: In a bipartite graph with matching M of size k,
the set of A-endpoints of M is a vertex cover of size k.

From AI research (Dec 30, 2025):
- Codex: "Convert maximality into 'no edge disjoint from M exists'"
- Estimated 80-120 lines, 60% success probability

GitHub Issue: #32
-/

import Mathlib

open scoped Classical

set_option maxHeartbeats 400000

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- DEFINITIONS (from proven slot139)
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
-- LINK GRAPH DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- The link graph at vertex v -/
def linkGraph (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : SimpleGraph V where
  Adj u w := u ≠ w ∧ G.Adj v u ∧ G.Adj v w ∧ G.Adj u w
  symm := by
    rintro u w ⟨hne, hvu, hvw, huw⟩
    exact ⟨hne.symm, hvw, hvu, huw.symm⟩
  loopless := by
    rintro u ⟨hne, -, -, -⟩
    exact hne rfl

instance (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : DecidableRel (linkGraph G v).Adj :=
  fun u w => inferInstance

-- ══════════════════════════════════════════════════════════════════════════════
-- BIPARTITE STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

/-- Bipartite graph with explicit parts -/
structure BipartiteWith (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : Prop where
  disjoint : Disjoint A B
  edges_cross : ∀ e ∈ G.edgeFinset,
    ((e : Sym2 V).out.1 ∈ A ∧ (e : Sym2 V).out.2 ∈ B) ∨
    ((e : Sym2 V).out.1 ∈ B ∧ (e : Sym2 V).out.2 ∈ A)

-- ══════════════════════════════════════════════════════════════════════════════
-- MATCHING DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A matching in graph G -/
def IsMatching (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Sym2 V)) : Prop :=
  M ⊆ G.edgeFinset ∧
  ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint (e₁ : Sym2 V).toFinset (e₂ : Sym2 V).toFinset

/-- A matching is maximal if no edge can be added -/
def IsMaximalMatching (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Sym2 V)) : Prop :=
  IsMatching G M ∧ ∀ e ∈ G.edgeFinset, e ∉ M →
    ∃ e' ∈ M, ¬Disjoint (e : Sym2 V).toFinset (e' : Sym2 V).toFinset

-- ══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTIVE COVER FROM MATCHING
-- ══════════════════════════════════════════════════════════════════════════════

/-- For bipartite graph, take A-endpoints of matching edges -/
def coverFromMatching (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (M : Finset (Sym2 V)) : Finset V :=
  M.biUnion (fun e =>
    if (e : Sym2 V).out.1 ∈ A then {(e : Sym2 V).out.1}
    else if (e : Sym2 V).out.2 ∈ A then {(e : Sym2 V).out.2}
    else ∅)

/-- The cover has size at most |M| -/
lemma coverFromMatching_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (M : Finset (Sym2 V)) :
    (coverFromMatching G A B M).card ≤ M.card := by
  unfold coverFromMatching
  calc (M.biUnion _).card
      ≤ M.sum (fun e => if (e : Sym2 V).out.1 ∈ A then 1
                        else if (e : Sym2 V).out.2 ∈ A then 1
                        else 0) := by
        apply le_trans (Finset.card_biUnion_le _ _)
        apply Finset.sum_le_sum
        intro e _
        split_ifs <;> simp
    _ ≤ M.sum (fun _ => 1) := by
        apply Finset.sum_le_sum
        intro e _
        split_ifs <;> omega
    _ = M.card := by simp

/-- Key lemma: coverFromMatching is a vertex cover when M is maximal -/
lemma coverFromMatching_is_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hBip : BipartiteWith G A B)
    (M : Finset (Sym2 V)) (hM : IsMaximalMatching G M) :
    ∀ e ∈ G.edgeFinset, (e : Sym2 V).out.1 ∈ coverFromMatching G A B M ∨
                        (e : Sym2 V).out.2 ∈ coverFromMatching G A B M := by
  intro e he
  -- If e ∈ M, one of its endpoints is in the cover by construction
  by_cases h_in : e ∈ M
  · left
    unfold coverFromMatching
    simp only [Finset.mem_biUnion]
    use e, h_in
    rcases hBip.edges_cross e he with ⟨h1, _⟩ | ⟨_, h2⟩
    · simp [h1]
    · simp [h2]
      -- e.out.1 ∈ B, e.out.2 ∈ A, so we take e.out.2
      sorry -- Aristotle: handle the case where we need out.2

  -- If e ∉ M, then e shares a vertex with some e' ∈ M (maximality)
  · obtain ⟨e', he'_mem, he'_share⟩ := hM.2 e he h_in
    -- e and e' share a vertex
    rw [Finset.not_disjoint_iff] at he'_share
    obtain ⟨v, hv_e, hv_e'⟩ := he'_share
    -- v is in the cover (from e')
    simp only [Sym2.mem_toFinset, Finset.mem_insert, Finset.mem_singleton] at hv_e hv_e'
    sorry -- Aristotle: show v ∈ coverFromMatching via e'

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 CONFIGURATION
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

-- ══════════════════════════════════════════════════════════════════════════════
-- LINK GRAPH BIPARTITION
-- ══════════════════════════════════════════════════════════════════════════════

/-- At shared vertex v between M-triangles X and Y, the link graph has natural bipartition:
    Part A = neighbors of v in X (excluding v)
    Part B = neighbors of v in Y (excluding v) + external vertices -/
def linkPartA (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (X : Finset V) : Finset V :=
  (X.filter (fun u => u ≠ v ∧ G.Adj v u))

def linkPartB (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (X Y : Finset V) : Finset V :=
  (Y.filter (fun u => u ≠ v ∧ G.Adj v u)) ∪
  (Finset.univ.filter (fun u => u ∉ X ∧ u ∉ Y ∧ u ≠ v ∧ (linkGraph G v).Adj u u = false ∧
                                ∃ w, (linkGraph G v).Adj u w))

/-- The link graph at a shared vertex is bipartite -/
lemma link_bipartite (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (v : V) (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (hv_X : v ∈ X) (hv_Y : v ∈ Y) :
    BipartiteWith (linkGraph G v) (linkPartA G v X) (linkPartB G v X Y) := by
  constructor
  · -- Parts are disjoint
    sorry -- Aristotle: X and Y share only v, external vertices not in X
  · -- Edges cross parts
    sorry -- Aristotle: link graph edge {u,w} means u,w form triangle with v
           -- If both in same part, contradicts bipartite structure

-- ══════════════════════════════════════════════════════════════════════════════
-- EXISTENCE OF MAXIMAL MATCHING
-- ══════════════════════════════════════════════════════════════════════════════

/-- Every finite graph has a maximal matching -/
lemma exists_maximal_matching (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M : Finset (Sym2 V), IsMaximalMatching G M := by
  -- Greedy: start empty, add edges until can't
  sorry -- Aristotle: standard greedy argument, or use Finset.strongInduction

-- ══════════════════════════════════════════════════════════════════════════════
-- LINK MATCHING BOUND
-- ══════════════════════════════════════════════════════════════════════════════

/-- Matching in link graph at shared vertex has size ≤ 2 -/
lemma link_matching_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (v : V) (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (hv_X : v ∈ X) (hv_Y : v ∈ Y)
    (Mlink : Finset (Sym2 V)) (hMlink : IsMatching (linkGraph G v) Mlink) :
    Mlink.card ≤ 2 := by
  -- Each edge in link matching corresponds to a triangle through v
  -- Only X and Y are M-triangles through v
  -- More than 2 matching edges would give 3+ almost-disjoint triangles at v
  -- Combined with the other 2 M-triangles not at v, this exceeds ν = 4
  sorry -- Aristotle: packing argument

-- ══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTIVE COVER AT EACH VERTEX
-- ══════════════════════════════════════════════════════════════════════════════

/-- Constructive 2-edge cover at shared vertex -/
lemma construct_local_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (v : V) (X Y : Finset V) (hX : X ∈ M) (hY : Y ∈ M) (hXY : X ≠ Y)
    (hv_X : v ∈ X) (hv_Y : v ∈ Y) :
    ∃ C : Finset V, C.card ≤ 2 ∧
      ∀ e ∈ (linkGraph G v).edgeFinset, (e : Sym2 V).out.1 ∈ C ∨ (e : Sym2 V).out.2 ∈ C := by
  -- Get a maximal matching in link graph
  obtain ⟨Mlink, hMlink⟩ := exists_maximal_matching (linkGraph G v)
  -- It has size ≤ 2
  have h_card : Mlink.card ≤ 2 := link_matching_le_2 G M hM hM4 v X Y hX hY hXY hv_X hv_Y Mlink hMlink.1
  -- Construct cover from matching
  let A := linkPartA G v X
  let B := linkPartB G v X Y
  let C := coverFromMatching (linkGraph G v) A B Mlink
  use C
  constructor
  · calc C.card ≤ Mlink.card := coverFromMatching_card _ _ _ _
      _ ≤ 2 := h_card
  · intro e he
    exact coverFromMatching_is_cover (linkGraph G v) A B (link_bipartite G M hM v X Y hX hY hXY hv_X hv_Y) Mlink hMlink e he

-- ══════════════════════════════════════════════════════════════════════════════
-- VERTEX COVER TO EDGE COVER CONVERSION
-- ══════════════════════════════════════════════════════════════════════════════

/-- Convert vertex cover of link graph to edge cover through v -/
def vertexToEdgeCover (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (C : Finset V) : Finset (Sym2 V) :=
  C.image (fun u => s(v, u))

lemma vertexToEdgeCover_card (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (C : Finset V) :
    (vertexToEdgeCover G v C).card ≤ C.card := by
  unfold vertexToEdgeCover
  exact Finset.card_image_le

/-- Triangles at v are covered by edge cover through v -/
lemma vertexToEdgeCover_covers (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (C : Finset V)
    (hC : ∀ e ∈ (linkGraph G v).edgeFinset, (e : Sym2 V).out.1 ∈ C ∨ (e : Sym2 V).out.2 ∈ C) :
    ∀ t, t ∈ G.cliqueFinset 3 → v ∈ t → ∃ e ∈ vertexToEdgeCover G v C, e ∈ t.sym2 := by
  intro t ht hv
  -- t is a triangle containing v
  -- t = {v, u, w} for some u, w adjacent to v
  -- {u, w} is an edge in link graph
  -- By hC, u ∈ C or w ∈ C
  -- So s(v,u) or s(v,w) is in vertexToEdgeCover
  sorry -- Aristotle: extract u, w from t, apply hC

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: τ ≤ 8 for cycle_4 via constructive cover -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- Construct 2-vertex cover at each shared vertex
  have hM4 : M.card = 4 := by rw [cfg.hM_eq]; simp

  obtain ⟨C_ab, hC_ab_card, hC_ab_cov⟩ := construct_local_cover G M hM hM4
    cfg.v_ab cfg.A cfg.B cfg.hA cfg.hB
    (fun h => by simp [cfg.hAB, h] at *)
    (by rw [← cfg.hAB]; simp) (by rw [← cfg.hAB]; simp)

  obtain ⟨C_bc, hC_bc_card, hC_bc_cov⟩ := construct_local_cover G M hM hM4
    cfg.v_bc cfg.B cfg.C cfg.hB cfg.hC
    (fun h => by simp [cfg.hBC, h] at *)
    (by rw [← cfg.hBC]; simp) (by rw [← cfg.hBC]; simp)

  obtain ⟨C_cd, hC_cd_card, hC_cd_cov⟩ := construct_local_cover G M hM hM4
    cfg.v_cd cfg.C cfg.D cfg.hC cfg.hD
    (fun h => by simp [cfg.hCD, h] at *)
    (by rw [← cfg.hCD]; simp) (by rw [← cfg.hCD]; simp)

  obtain ⟨C_da, hC_da_card, hC_da_cov⟩ := construct_local_cover G M hM hM4
    cfg.v_da cfg.D cfg.A cfg.hD cfg.hA
    (fun h => by simp [cfg.hDA, h] at *)
    (by rw [← cfg.hDA]; simp) (by rw [← cfg.hDA]; simp)

  -- Convert to edge covers
  let E_ab := vertexToEdgeCover G cfg.v_ab C_ab
  let E_bc := vertexToEdgeCover G cfg.v_bc C_bc
  let E_cd := vertexToEdgeCover G cfg.v_cd C_cd
  let E_da := vertexToEdgeCover G cfg.v_da C_da

  -- Union has size ≤ 8
  have h_total_card : (E_ab ∪ E_bc ∪ E_cd ∪ E_da).card ≤ 8 := by
    calc (E_ab ∪ E_bc ∪ E_cd ∪ E_da).card
        ≤ E_ab.card + E_bc.card + E_cd.card + E_da.card := by
          apply le_trans (Finset.card_union_le _ _)
          apply le_trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
          apply le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _)
          omega
      _ ≤ C_ab.card + C_bc.card + C_cd.card + C_da.card := by
          apply Nat.add_le_add
          apply Nat.add_le_add
          apply Nat.add_le_add
          · exact vertexToEdgeCover_card G cfg.v_ab C_ab
          · exact vertexToEdgeCover_card G cfg.v_bc C_bc
          · exact vertexToEdgeCover_card G cfg.v_cd C_cd
          · exact vertexToEdgeCover_card G cfg.v_da C_da
      _ ≤ 2 + 2 + 2 + 2 := by omega
      _ = 8 := by ring

  -- It covers all triangles
  sorry -- Aristotle: every triangle contains a shared vertex, apply vertexToEdgeCover_covers

end
