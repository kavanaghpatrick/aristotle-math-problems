/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8021f12c-2e86-42da-9af5-4bfd19165507
-/

/-
Tuza ν=4 Cycle_4: τ ≤ 8 via König-Lite (Case Analysis)

APPROACH 1: König-Lite Case Analysis
=====================================
Instead of formalizing general König's theorem, prove directly for ν ≤ 2:
- Case ν = 0: Empty cover (no edges to cover)
- Case ν = 1: Two endpoints of single matching edge suffice
- Case ν = 2: One endpoint from each bipartite part suffices

Key insight: For bipartite graph with matching M of size 2, taking one endpoint
from part A for each matching edge gives a vertex cover.

From AI consensus (Gemini, Codex, Grok - Dec 30, 2025):
- "Do NOT formalize general König" - all agents agree
- Case analysis on ν ∈ {0,1,2} is exponentially easier
- Estimated 40-80 lines, 75% success probability

GitHub Issue: #32
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token '⟨'; expected command-/
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

/-- The link graph at vertex v: vertices are neighbors of v, edges are pairs
    that form a triangle with v -/
def linkGraph (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : SimpleGraph V where
  Adj u w := u ≠ w ∧ G.Adj v u ∧ G.Adj v w ∧ G.Adj u w
  symm := by
    intros u w

⟨hne, hvu, hvw, huw⟩
    exact ⟨hne.symm, hvw, hvu, huw.symm⟩
  loopless := by
    intro u ⟨hne, _, _, _⟩
    exact hne rfl

instance (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : DecidableRel (linkGraph G v).Adj :=
  fun u w => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

-- ══════════════════════════════════════════════════════════════════════════════
-- VERTEX COVER DEFINITIONS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A set C is a vertex cover of G if every edge has at least one endpoint in C -/
def IsVertexCover (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) : Prop :=
  ∀ e ∈ G.edgeFinset, (e : Sym2 V).out.1 ∈ C ∨ (e : Sym2 V).out.2 ∈ C

/-- Minimum vertex cover number -/
noncomputable def vertexCoverNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ : Finset (Finset V)).filter (IsVertexCover G) |>.image Finset.card |>.min |>.getD 0

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
  -- If neither endpoint is in matching endpoints, e could be added to M
  have h_can_add : e ∉ M ∧ ∀ e' ∈ M, Disjoint (e : Sym2 V).toFinset (e' : Sym2 V).toFinset := by
    constructor
    · intro he_mem
      have : e.out.1 ∈ matchingEndpoints M := by
        unfold matchingEndpoints
        simp only [Finset.mem_biUnion]
        use e, he_mem
        simp [Sym2.toFinset_eq]
      exact h.1 this
    · intro e' he'
      rw [Finset.disjoint_iff_ne]
      intro v hv w hw
      simp only [Sym2.toFinset_eq, Finset.mem_insert, Finset.mem_singleton] at hv hw
      have hv_not : v ∉ matchingEndpoints M := by
        cases hv with
        | inl h => rw [h]; exact h.1
        | inr h => rw [h]; exact h.2
      unfold matchingEndpoints at hv_not
      simp only [Finset.mem_biUnion, not_exists, not_and] at hv_not
      exact fun heq => by
        subst heq
        exact hv_not e' he' (by simp [Sym2.toFinset_eq, hw])
  exact hM.2 e he h_can_add.1 (by
    push_neg
    intro e' he'
    exact h_can_add.2 e' he')

-- ══════════════════════════════════════════════════════════════════════════════
-- KÖNIG-LITE: Case Analysis for ν ≤ 2
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main König-Lite lemma: For any graph, matching endpoints form a vertex cover
    with |C| ≤ 2|M| -/
lemma matching_endpoints_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) (hM : IsMaximalMatching G M) :
    IsVertexCover G (matchingEndpoints M) := by
  intro e he
  exact edge_hits_maximal_matching G M hM e he

/-- Cardinality bound on matching endpoints -/
lemma matching_endpoints_card (M : Finset (Sym2 V)) :
    (matchingEndpoints M).card ≤ 2 * M.card := by
  unfold matchingEndpoints
  calc (M.biUnion (fun e => (e : Sym2 V).toFinset)).card
      ≤ M.sum (fun e => (e : Sym2 V).toFinset.card) := Finset.card_biUnion_le _ _
    _ = M.sum (fun _ => 2) := by simp [Sym2.toFinset_eq]
    _ = 2 * M.card := by ring

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  vertexCoverNumber
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  matchingNumber
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Tactic `unfold` failed: Local variable `vertexCoverNumber` has no definition-/
/-- König-Lite: If matching number ≤ k, then vertex cover number ≤ 2k -/
lemma vertex_cover_le_two_matching (G : SimpleGraph V) [DecidableRel G.Adj] :
    vertexCoverNumber G ≤ 2 * matchingNumber G := by
  -- Get a maximum matching
  unfold vertexCoverNumber matchingNumber
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  matchingNumber
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  vertexCoverNumber
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G-/
-- Aristotle: prove existence of maximal matching and apply bounds

/-- For bipartite graphs specifically, König says τ = ν. We prove the ≤ direction
    directly for the case ν ≤ 2 -/
lemma bipartite_konig_lite (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNu : matchingNumber G ≤ 2) :
    vertexCoverNumber G ≤ 2 := by
  calc vertexCoverNumber G
      ≤ 2 * matchingNumber G := vertex_cover_le_two_matching G
    _ ≤ 2 * 2 := by omega
    _ = 4 := by ring

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Union (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Fintype (↑G.edgeSet : Type ?u.15456)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
-- Note: This gives τ ≤ 4, not τ ≤ 2. For the tight bound τ ≤ ν,
  -- we need bipartiteness. But τ ≤ 4 at each vertex × 4 vertices
  -- still gives τ ≤ 16, not good enough.
  -- The real König-lite needs the bipartite structure.

-- ══════════════════════════════════════════════════════════════════════════════
-- TRUE KÖNIG-LITE: Using bipartiteness for ν ≤ 2
-- ══════════════════════════════════════════════════════════════════════════════

/-- A graph is bipartite if it can be 2-colored -/
def IsBipartite (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ A B : Finset V, A ∩ B = ∅ ∧ A ∪ B = Finset.univ ∧
    ∀ e ∈ G.edgeFinset, (e : Sym2 V).out.1 ∈ A ∧ (e : Sym2 V).out.2 ∈ B ∨
                        (e : Sym2 V).out.1 ∈ B ∧ (e : Sym2 V).out.2 ∈ A

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  IsBipartite
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  matchingNumber
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  vertexCoverNumber
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  matchingNumber
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  matchingNumber
but this term has type
  x✝¹

Note: Expected a function because this term is being applied to the argument
  G-/
/-- König's theorem for ν ≤ 2: If G is bipartite with matching number ≤ 2,
    then vertex cover number ≤ 2 -/
theorem konig_nu_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hBip : IsBipartite G) (hNu : matchingNumber G ≤ 2) :
    vertexCoverNumber G ≤ matchingNumber G := by
  -- Case analysis on matching number
  interval_cases h : matchingNumber G
  -- Case ν = 0: No edges, empty cover
  · simp only [Nat.lt_one_iff] at h
    sorry -- Aristotle: if matchingNumber = 0, graph has no edges, τ = 0
  -- Case ν = 1: One matching edge, its endpoints cover all
  · sorry -- Aristotle: if matchingNumber = 1, star-like structure, τ ≤ 1
  -- Case ν = 2: Two matching edges, pick one endpoint from each part
  · sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

overloaded, errors 
  failed to synthesize
    Insert (Finset V) (Finset (Finset V))
  
  Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
  
  98:15 `A` is not a field of structure `Finset`
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Inter (Finset V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
-- Aristotle: bipartiteness ensures {u₁, u₂} from part A covers all

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 CONFIGURATION (from slot139)
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

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isMaxPacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  linkGraph
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
No goals to be solved-/
-- ══════════════════════════════════════════════════════════════════════════════
-- LINK GRAPH IS BIPARTITE
-- ══════════════════════════════════════════════════════════════════════════════

/-- External vertices in link graph cannot form edges (maximality) -/
lemma link_external_independent (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hNu4 : M.card = 4)
    (v : V) (u w : V) (hu : ∀ X ∈ M, v ∈ X → u ∉ X) (hw : ∀ X ∈ M, v ∈ X → w ∉ X) :
    ¬(linkGraph G v).Adj u w := by
  intro ⟨_, hvu, hvw, huw⟩
  -- If u and w are external and adjacent in link graph, {v,u,w} is a triangle
  -- not sharing edge with M, contradicting maximality
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

overloaded, errors 
  failed to synthesize
    Insert ?m.21 (Finset V)
  
  Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
  
  85:43 `cfg` is not a field of structure `Finset`
Function expected at
  isMaxPacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  Cycle4
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  IsBipartite
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  (linkGraph G v)-/
-- Aristotle: derive contradiction from maximality

/-- The link graph at a shared vertex is bipartite -/
lemma link_graph_bipartite (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V)) :
    IsBipartite (linkGraph G v) := by
  -- The two M-triangles at v partition the M-neighbors of v into two parts
  -- External vertices form an independent set, so they can go in either part
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

overloaded, errors 
  failed to synthesize
    Insert ?m.21 (Finset V)
  
  Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
  
  85:43 `cfg` is not a field of structure `Finset`
Function expected at
  isMaxPacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  Cycle4
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  matchingNumber
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  (linkGraph G v)-/
-- Aristotle: construct the bipartition

/-- Matching number of link graph at shared vertex is ≤ 2 -/
lemma link_matching_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (v : V) (hv : v ∈ ({cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da} : Finset V)) :
    matchingNumber (linkGraph G v) ≤ 2 := by
  -- Only 2 M-triangles at v, each contributes at most 1 matching edge
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isMaxPacking
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  Cycle4
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  triangleCoveringNumber
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G
Unknown identifier `vertexCoverNumber`
Unknown identifier `konig_nu_le_2`
No goals to be solved
Unknown identifier `vertexCoverNumber`
Unknown identifier `konig_nu_le_2`
No goals to be solved
Unknown identifier `vertexCoverNumber`
Unknown identifier `konig_nu_le_2`
No goals to be solved
Unknown identifier `vertexCoverNumber`
Unknown identifier `konig_nu_le_2`
No goals to be solved-/
-- Aristotle: use packing constraint

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 FOR CYCLE_4
-- ══════════════════════════════════════════════════════════════════════════════

/-- Main theorem: τ ≤ 8 for cycle_4 configuration -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  -- At each shared vertex v, link graph L_v is bipartite with ν(L_v) ≤ 2
  -- By König-lite, τ(L_v) ≤ 2
  -- Four shared vertices × 2 edges = 8 edges total
  have h_vab : vertexCoverNumber (linkGraph G cfg.v_ab) ≤ 2 := by
    apply konig_nu_le_2
    · exact link_graph_bipartite G M hM cfg cfg.v_ab (by simp)
    · exact link_matching_le_2 G M hM cfg cfg.v_ab (by simp)
  have h_vbc : vertexCoverNumber (linkGraph G cfg.v_bc) ≤ 2 := by
    apply konig_nu_le_2
    · exact link_graph_bipartite G M hM cfg cfg.v_bc (by simp)
    · exact link_matching_le_2 G M hM cfg cfg.v_bc (by simp)
  have h_vcd : vertexCoverNumber (linkGraph G cfg.v_cd) ≤ 2 := by
    apply konig_nu_le_2
    · exact link_graph_bipartite G M hM cfg cfg.v_cd (by simp)
    · exact link_matching_le_2 G M hM cfg cfg.v_cd (by simp)
  have h_vda : vertexCoverNumber (linkGraph G cfg.v_da) ≤ 2 := by
    apply konig_nu_le_2
    · exact link_graph_bipartite G M hM cfg cfg.v_da (by simp)
    · exact link_matching_le_2 G M hM cfg cfg.v_da (by simp)
  -- Convert vertex covers of link graphs to edge cover of original graph
  sorry

-- Aristotle: vertex cover of L_v → edge cover through v in G
         -- Sum over 4 vertices: 4 × 2 = 8

end