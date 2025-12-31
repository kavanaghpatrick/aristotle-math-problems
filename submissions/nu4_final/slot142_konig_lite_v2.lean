/-
Tuza ν=4 Cycle_4: τ ≤ 8 via König-Lite (Case Analysis)

APPROACH 1: König-Lite Case Analysis (FIXED v2)
===============================================
Fixed syntax errors from v1:
- Use `rintro` instead of `intros` for pattern matching
- Explicit Finset operations instead of notation

From AI consensus (Gemini, Codex, Grok - Dec 30, 2025):
- "Do NOT formalize general König" - all agents agree
- Case analysis on ν ∈ {0,1,2} is exponentially easier

GitHub Issue: #32
-/

import Mathlib

open scoped Classical
open Finset

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
-- LINK GRAPH DEFINITIONS (FIXED SYNTAX)
-- ══════════════════════════════════════════════════════════════════════════════

/-- The link graph at vertex v: vertices are neighbors of v, edges are pairs
    that form a triangle with v -/
def linkGraph (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : SimpleGraph V where
  Adj u w := u ≠ w ∧ G.Adj v u ∧ G.Adj v w ∧ G.Adj u w
  symm := by
    rintro u w ⟨hne, hvu, hvw, huw⟩
    exact ⟨hne.symm, hvw, hvu, huw.symm⟩
  loopless := by
    rintro u ⟨hne, -, -, -⟩
    exact hne rfl

instance linkGraphDecidable (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    DecidableRel (linkGraph G v).Adj :=
  fun u w => inferInstance

-- ══════════════════════════════════════════════════════════════════════════════
-- VERTEX COVER DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A set C is a vertex cover of G if every edge has at least one endpoint in C -/
def IsVertexCover (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) : Prop :=
  ∀ e ∈ G.edgeFinset, (e : Sym2 V).out.1 ∈ C ∨ (e : Sym2 V).out.2 ∈ C

/-- Minimum vertex cover number -/
noncomputable def vertexCoverNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.filter (IsVertexCover G) |>.image Finset.card |>.min |>.getD 0

-- ══════════════════════════════════════════════════════════════════════════════
-- MATCHING DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A matching is a set of pairwise vertex-disjoint edges -/
def IsMatching (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Sym2 V)) : Prop :=
  M ⊆ G.edgeFinset ∧
  ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint (e₁ : Sym2 V).toFinset (e₂ : Sym2 V).toFinset

/-- Maximum matching number -/
noncomputable def matchingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (IsMatching G) |>.image Finset.card |>.max |>.getD 0

/-- A matching is maximal if no edge can be added -/
def IsMaximalMatching (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Sym2 V)) : Prop :=
  IsMatching G M ∧ ∀ e ∈ G.edgeFinset, e ∉ M →
    ∃ e' ∈ M, ¬Disjoint (e : Sym2 V).toFinset (e' : Sym2 V).toFinset

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY LEMMA: Edge hits maximal matching endpoints
-- ══════════════════════════════════════════════════════════════════════════════

/-- The endpoints of a matching -/
def matchingEndpoints (M : Finset (Sym2 V)) : Finset V :=
  M.biUnion (fun e => (e : Sym2 V).toFinset)

/-- Every edge in a graph with maximal matching M hits an endpoint of M -/
lemma edge_hits_maximal_matching (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) (hM : IsMaximalMatching G M)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (e : Sym2 V).out.1 ∈ matchingEndpoints M ∨ (e : Sym2 V).out.2 ∈ matchingEndpoints M := by
  by_contra h
  push_neg at h
  have h_not_in : e ∉ M := by
    intro he_mem
    have : e.out.1 ∈ matchingEndpoints M := by
      simp only [matchingEndpoints, Finset.mem_biUnion]
      exact ⟨e, he_mem, Sym2.mem_toFinset.mpr (Sym2.out_fst_mem e)⟩
    exact h.1 this
  have h_disjoint : ∀ e' ∈ M, Disjoint (e : Sym2 V).toFinset (e' : Sym2 V).toFinset := by
    intro e' he'
    rw [Finset.disjoint_iff_ne]
    intro v hv w hw
    simp only [Sym2.mem_toFinset] at hv hw
    have hv_not : v ∉ matchingEndpoints M := by
      rcases hv with rfl | rfl <;> [exact h.1; exact h.2]
    simp only [matchingEndpoints, Finset.mem_biUnion, not_exists, not_and] at hv_not
    intro heq
    subst heq
    exact hv_not e' he' (Sym2.mem_toFinset.mpr hw)
  have h_contra := hM.2 e he h_not_in
  push_neg at h_contra
  -- h_contra says: ∀ e' ∈ M, Disjoint e.toFinset e'.toFinset
  -- But h_disjoint says the same thing, so we have a contradiction
  -- with the definition of IsMaximalMatching
  sorry -- Aristotle: derive contradiction

/-- Main König-Lite lemma: For any graph, matching endpoints form a vertex cover -/
lemma matching_endpoints_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) (hM : IsMaximalMatching G M) :
    IsVertexCover G (matchingEndpoints M) := by
  intro e he
  exact edge_hits_maximal_matching G M hM e he

/-- Cardinality bound on matching endpoints -/
lemma matching_endpoints_card (M : Finset (Sym2 V)) :
    (matchingEndpoints M).card ≤ 2 * M.card := by
  simp only [matchingEndpoints]
  calc (M.biUnion (fun e => (e : Sym2 V).toFinset)).card
      ≤ M.sum (fun e => (e : Sym2 V).toFinset.card) := Finset.card_biUnion_le _ _
    _ ≤ M.sum (fun _ => 2) := by
        apply Finset.sum_le_sum
        intro e _
        -- Each Sym2 element has at most 2 elements in its toFinset
        sorry -- Aristotle: Sym2.card_toFinset shows card ≤ 2
    _ = 2 * M.card := by simp [Finset.sum_const, smul_eq_mul]

-- ══════════════════════════════════════════════════════════════════════════════
-- BIPARTITE DEFINITION
-- ══════════════════════════════════════════════════════════════════════════════

/-- A graph is bipartite if it can be 2-colored -/
def IsBipartite (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ A B : Finset V, Disjoint A B ∧ A ∪ B = Finset.univ ∧
    ∀ e ∈ G.edgeFinset, (e : Sym2 V).out.1 ∈ A ∧ (e : Sym2 V).out.2 ∈ B ∨
                        (e : Sym2 V).out.1 ∈ B ∧ (e : Sym2 V).out.2 ∈ A

-- ══════════════════════════════════════════════════════════════════════════════
-- KÖNIG-LITE: Case Analysis for ν ≤ 2
-- ══════════════════════════════════════════════════════════════════════════════

/-- König's theorem for ν ≤ 2: If G is bipartite with matching number ≤ 2,
    then vertex cover number ≤ matching number -/
theorem konig_nu_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hBip : IsBipartite G) (hNu : matchingNumber G ≤ 2) :
    vertexCoverNumber G ≤ matchingNumber G := by
  -- Case analysis on matching number
  rcases Nat.lt_or_ge (matchingNumber G) 1 with h0 | h1
  · -- Case ν = 0: No edges, empty cover
    simp only [Nat.lt_one_iff] at h0
    sorry -- Aristotle: if matchingNumber = 0, graph has no edges, τ = 0
  · -- Case ν ≥ 1
    rcases Nat.lt_or_ge (matchingNumber G) 2 with h1' | h2
    · -- Case ν = 1: One matching edge
      have hν1 : matchingNumber G = 1 := by omega
      sorry -- Aristotle: τ ≤ 1 for matching number 1
    · -- Case ν = 2: Two matching edges
      have hν2 : matchingNumber G = 2 := by omega
      sorry -- Aristotle: bipartiteness ensures τ ≤ 2

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 CONFIGURATION
-- ══════════════════════════════════════════════════════════════════════════════

structure Cycle4Config (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) where
  A : Finset V
  B : Finset V
  C : Finset V
  D : Finset V
  hA : A ∈ M
  hB : B ∈ M
  hC : C ∈ M
  hD : D ∈ M
  hM_card : M.card = 4
  v_ab : V
  v_bc : V
  v_cd : V
  v_da : V
  hAB : A ∩ B = {v_ab}
  hBC : B ∩ C = {v_bc}
  hCD : C ∩ D = {v_cd}
  hDA : D ∩ A = {v_da}

-- ══════════════════════════════════════════════════════════════════════════════
-- LINK GRAPH PROPERTIES
-- ══════════════════════════════════════════════════════════════════════════════

/-- The link graph at a shared vertex is bipartite -/
lemma link_graph_bipartite (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4Config G M) (v : V)
    (hv : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da) :
    IsBipartite (linkGraph G v) := by
  sorry -- Aristotle: construct the bipartition from M-triangles at v

/-- Matching number of link graph at shared vertex is ≤ 2 -/
lemma link_matching_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4Config G M) (v : V)
    (hv : v = cfg.v_ab ∨ v = cfg.v_bc ∨ v = cfg.v_cd ∨ v = cfg.v_da) :
    matchingNumber (linkGraph G v) ≤ 2 := by
  sorry -- Aristotle: only 2 M-triangles at v

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: τ ≤ 8 for cycle_4 configuration -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4Config G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- At each shared vertex v, link graph L_v is bipartite with ν(L_v) ≤ 2
  -- By König-lite, τ(L_v) ≤ 2
  have h_vab : vertexCoverNumber (linkGraph G cfg.v_ab) ≤ 2 := by
    have h1 := link_graph_bipartite G M hM cfg cfg.v_ab (Or.inl rfl)
    have h2 := link_matching_le_2 G M hM cfg cfg.v_ab (Or.inl rfl)
    calc vertexCoverNumber (linkGraph G cfg.v_ab)
        ≤ matchingNumber (linkGraph G cfg.v_ab) := konig_nu_le_2 _ h1 h2
      _ ≤ 2 := h2
  have h_vbc : vertexCoverNumber (linkGraph G cfg.v_bc) ≤ 2 := by
    have h1 := link_graph_bipartite G M hM cfg cfg.v_bc (Or.inr (Or.inl rfl))
    have h2 := link_matching_le_2 G M hM cfg cfg.v_bc (Or.inr (Or.inl rfl))
    calc vertexCoverNumber (linkGraph G cfg.v_bc)
        ≤ matchingNumber (linkGraph G cfg.v_bc) := konig_nu_le_2 _ h1 h2
      _ ≤ 2 := h2
  have h_vcd : vertexCoverNumber (linkGraph G cfg.v_cd) ≤ 2 := by
    have h1 := link_graph_bipartite G M hM cfg cfg.v_cd (Or.inr (Or.inr (Or.inl rfl)))
    have h2 := link_matching_le_2 G M hM cfg cfg.v_cd (Or.inr (Or.inr (Or.inl rfl)))
    calc vertexCoverNumber (linkGraph G cfg.v_cd)
        ≤ matchingNumber (linkGraph G cfg.v_cd) := konig_nu_le_2 _ h1 h2
      _ ≤ 2 := h2
  have h_vda : vertexCoverNumber (linkGraph G cfg.v_da) ≤ 2 := by
    have h1 := link_graph_bipartite G M hM cfg cfg.v_da (Or.inr (Or.inr (Or.inr rfl)))
    have h2 := link_matching_le_2 G M hM cfg cfg.v_da (Or.inr (Or.inr (Or.inr rfl)))
    calc vertexCoverNumber (linkGraph G cfg.v_da)
        ≤ matchingNumber (linkGraph G cfg.v_da) := konig_nu_le_2 _ h1 h2
      _ ≤ 2 := h2
  -- Convert vertex covers of link graphs to edge cover of original graph
  -- Each vertex cover of size ≤ 2 gives edge cover of size ≤ 2 through that vertex
  -- Union over 4 vertices: 4 × 2 = 8
  sorry -- Aristotle: complete the connection

end
