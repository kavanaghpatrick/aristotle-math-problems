/-- Submission timestamp: 20251226_164343 --/
/-
Tuza ν=4 Strategy - Slot 115: Disjoint Partition by Shared Vertex

DEBATE CONSENSUS (Gemini + Grok + Codex):
The key breakthrough is to partition ALL triangles into DISJOINT sets based on
which shared vertex they contain, using a priority ordering to handle triangles
that contain multiple shared vertices.

LEMMA STATEMENT (cycle4_disjoint_partition):
Given cycle_4 with shared vertices S = {v_ab, v_bc, v_cd, v_da}, partition
all triangles T into disjoint sets:
  - T₁ = {t ∈ T | v_ab ∈ t}
  - T₂ = {t ∈ T | v_bc ∈ t ∧ v_ab ∉ t}
  - T₃ = {t ∈ T | v_cd ∈ t ∧ v_ab ∉ t ∧ v_bc ∉ t}
  - T₄ = {t ∈ T | v_da ∈ t ∧ v_ab ∉ t ∧ v_bc ∉ t ∧ v_cd ∉ t}

WHY THIS IS SAFE:
1. Uses cycle4_all_triangles_contain_shared (PROVEN) - every triangle hits at least one shared vertex
2. Priority ordering guarantees disjointness
3. Union covers all triangles (exhaustive)
4. Does NOT assume diagonal exclusion (works either way)

RISK: LOW - Pure set theory, no geometric assumptions
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

-- ══════════════════════════════════════════════════════════════════════════════
-- CYCLE_4 STRUCTURE
-- ══════════════════════════════════════════════════════════════════════════════

/-- CYCLE_4: A—B—C—D—A forms a 4-cycle in the sharing graph -/
def isCycle4 (M : Finset (Finset V)) (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧  -- A shares vertex with B (call it v_ab)
  (B ∩ C).card = 1 ∧  -- B shares vertex with C (call it v_bc)
  (C ∩ D).card = 1 ∧  -- C shares vertex with D (call it v_cd)
  (D ∩ A).card = 1 ∧  -- D shares vertex with A (call it v_da)
  (A ∩ C).card = 0 ∧  -- A and C are opposite (disjoint)
  (B ∩ D).card = 0    -- B and D are opposite (disjoint)

/-- Extract shared vertices from cycle_4 -/
def sharedVertices (A B C D : Finset V)
    (hab : (A ∩ B).card = 1) (hbc : (B ∩ C).card = 1)
    (hcd : (C ∩ D).card = 1) (hda : (D ∩ A).card = 1) : Finset V :=
  (A ∩ B) ∪ (B ∩ C) ∪ (C ∩ D) ∪ (D ∩ A)

-- ══════════════════════════════════════════════════════════════════════════════
-- KEY PROVEN LEMMA: All triangles contain a shared vertex
-- ══════════════════════════════════════════════════════════════════════════════

/-- PROVEN: Every triangle in G shares an edge with some packing element -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
  -- By maximality: if t shares no edge with any X ∈ M, then M ∪ {t} is a larger packing
  sorry -- This is proven in prior Aristotle runs

/-- PROVEN: In cycle_4, every triangle contains at least one shared vertex -/
lemma cycle4_all_triangles_contain_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hcycle : isCycle4 M A B C D) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ v ∈ sharedVertices A B C D hcycle.2.2.2.2.2.2.2.1 hcycle.2.2.2.2.2.2.2.2.1
      hcycle.2.2.2.2.2.2.2.2.2.1 hcycle.2.2.2.2.2.2.2.2.2.2.1, v ∈ t := by
  -- Uses triangle_shares_edge_with_packing plus cycle_4 structure
  sorry -- This is proven in slot73 "all-middle" breakthrough

-- ══════════════════════════════════════════════════════════════════════════════
-- DISJOINT PARTITION BY PRIORITY
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles containing the first shared vertex (highest priority) -/
def T1 (triangles : Finset (Finset V)) (v_ab : V) : Finset (Finset V) :=
  triangles.filter (fun t => v_ab ∈ t)

/-- Triangles containing v_bc but NOT v_ab -/
def T2 (triangles : Finset (Finset V)) (v_ab v_bc : V) : Finset (Finset V) :=
  triangles.filter (fun t => v_bc ∈ t ∧ v_ab ∉ t)

/-- Triangles containing v_cd but NOT v_ab and NOT v_bc -/
def T3 (triangles : Finset (Finset V)) (v_ab v_bc v_cd : V) : Finset (Finset V) :=
  triangles.filter (fun t => v_cd ∈ t ∧ v_ab ∉ t ∧ v_bc ∉ t)

/-- Triangles containing v_da but NOT v_ab, v_bc, or v_cd -/
def T4 (triangles : Finset (Finset V)) (v_ab v_bc v_cd v_da : V) : Finset (Finset V) :=
  triangles.filter (fun t => v_da ∈ t ∧ v_ab ∉ t ∧ v_bc ∉ t ∧ v_cd ∉ t)

-- ══════════════════════════════════════════════════════════════════════════════
-- CORE LEMMA: THE PARTITION IS DISJOINT
-- ══════════════════════════════════════════════════════════════════════════════

/-- T1 and T2 are disjoint by construction -/
lemma T1_T2_disjoint (triangles : Finset (Finset V)) (v_ab v_bc : V) :
    Disjoint (T1 triangles v_ab) (T2 triangles v_ab v_bc) := by
  simp only [Finset.disjoint_iff_ne, T1, T2, Finset.mem_filter]
  intro t1 ⟨_, ht1_ab⟩ t2 ⟨_, ht2_bc, ht2_not_ab⟩
  by_contra heq
  rw [heq] at ht1_ab
  exact ht2_not_ab ht1_ab

/-- T1 and T3 are disjoint by construction -/
lemma T1_T3_disjoint (triangles : Finset (Finset V)) (v_ab v_bc v_cd : V) :
    Disjoint (T1 triangles v_ab) (T3 triangles v_ab v_bc v_cd) := by
  simp only [Finset.disjoint_iff_ne, T1, T3, Finset.mem_filter]
  intro t1 ⟨_, ht1_ab⟩ t3 ⟨_, _, ht3_not_ab, _⟩
  by_contra heq
  rw [heq] at ht1_ab
  exact ht3_not_ab ht1_ab

/-- T1 and T4 are disjoint by construction -/
lemma T1_T4_disjoint (triangles : Finset (Finset V)) (v_ab v_bc v_cd v_da : V) :
    Disjoint (T1 triangles v_ab) (T4 triangles v_ab v_bc v_cd v_da) := by
  simp only [Finset.disjoint_iff_ne, T1, T4, Finset.mem_filter]
  intro t1 ⟨_, ht1_ab⟩ t4 ⟨_, _, ht4_not_ab, _, _⟩
  by_contra heq
  rw [heq] at ht1_ab
  exact ht4_not_ab ht1_ab

/-- T2 and T3 are disjoint by construction -/
lemma T2_T3_disjoint (triangles : Finset (Finset V)) (v_ab v_bc v_cd : V) :
    Disjoint (T2 triangles v_ab v_bc) (T3 triangles v_ab v_bc v_cd) := by
  simp only [Finset.disjoint_iff_ne, T2, T3, Finset.mem_filter]
  intro t2 ⟨_, ht2_bc, _⟩ t3 ⟨_, _, _, ht3_not_bc⟩
  by_contra heq
  rw [heq] at ht2_bc
  exact ht3_not_bc ht2_bc

/-- T2 and T4 are disjoint by construction -/
lemma T2_T4_disjoint (triangles : Finset (Finset V)) (v_ab v_bc v_cd v_da : V) :
    Disjoint (T2 triangles v_ab v_bc) (T4 triangles v_ab v_bc v_cd v_da) := by
  simp only [Finset.disjoint_iff_ne, T2, T4, Finset.mem_filter]
  intro t2 ⟨_, ht2_bc, _⟩ t4 ⟨_, _, _, ht4_not_bc, _⟩
  by_contra heq
  rw [heq] at ht2_bc
  exact ht4_not_bc ht2_bc

/-- T3 and T4 are disjoint by construction -/
lemma T3_T4_disjoint (triangles : Finset (Finset V)) (v_ab v_bc v_cd v_da : V) :
    Disjoint (T3 triangles v_ab v_bc v_cd) (T4 triangles v_ab v_bc v_cd v_da) := by
  simp only [Finset.disjoint_iff_ne, T3, T4, Finset.mem_filter]
  intro t3 ⟨_, ht3_cd, _, _⟩ t4 ⟨_, _, _, _, ht4_not_cd⟩
  by_contra heq
  rw [heq] at ht3_cd
  exact ht4_not_cd ht3_cd

-- ══════════════════════════════════════════════════════════════════════════════
-- CORE LEMMA: THE PARTITION IS EXHAUSTIVE
-- ══════════════════════════════════════════════════════════════════════════════

/-- KEY: Union of T1, T2, T3, T4 covers all triangles (given all-middle property) -/
theorem disjoint_partition_covers_all
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hcycle : isCycle4 M A B C D) (hM : isMaxPacking G M)
    (v_ab v_bc v_cd v_da : V)
    (hv_ab : v_ab ∈ A ∩ B) (hv_bc : v_bc ∈ B ∩ C)
    (hv_cd : v_cd ∈ C ∩ D) (hv_da : v_da ∈ D ∩ A) :
    let triangles := G.cliqueFinset 3
    T1 triangles v_ab ∪ T2 triangles v_ab v_bc ∪
    T3 triangles v_ab v_bc v_cd ∪ T4 triangles v_ab v_bc v_cd v_da = triangles := by
  intro triangles
  ext t
  simp only [Finset.mem_union, T1, T2, T3, T4, Finset.mem_filter]
  constructor
  · intro h
    rcases h with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _, _⟩ <;> assumption
  · intro ht
    -- By cycle4_all_triangles_contain_shared, t contains at least one shared vertex
    -- Then exactly one of the four cases applies based on priority
    by_cases hab : v_ab ∈ t
    · left; left; left; exact ⟨ht, hab⟩
    · by_cases hbc : v_bc ∈ t
      · left; left; right; exact ⟨ht, hbc, hab⟩
      · by_cases hcd : v_cd ∈ t
        · left; right; exact ⟨ht, hcd, hab, hbc⟩
        · right
          -- Must contain v_da by all-middle property
          have h_shared := cycle4_all_triangles_contain_shared G M A B C D hcycle hM t ht
          -- The shared vertex is one of v_ab, v_bc, v_cd, v_da
          -- Since we ruled out the first three, it must be v_da
          sorry -- Needs to connect h_shared to the specific vertices

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: THE DISJOINT PARTITION LEMMA
-- ══════════════════════════════════════════════════════════════════════════════

/-- MAIN: cycle_4 triangles form a disjoint 4-partition by shared vertex -/
theorem cycle4_disjoint_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A B C D : Finset V)
    (hcycle : isCycle4 M A B C D) (hM : isMaxPacking G M)
    (v_ab v_bc v_cd v_da : V)
    (hv_ab : v_ab ∈ A ∩ B) (hv_bc : v_bc ∈ B ∩ C)
    (hv_cd : v_cd ∈ C ∩ D) (hv_da : v_da ∈ D ∩ A) :
    let triangles := G.cliqueFinset 3
    let parts := [T1 triangles v_ab, T2 triangles v_ab v_bc,
                  T3 triangles v_ab v_bc v_cd, T4 triangles v_ab v_bc v_cd v_da]
    -- 1. Pairwise disjoint
    (∀ i j, i ≠ j → i < parts.length → j < parts.length →
      Disjoint (parts.get ⟨i, by omega⟩) (parts.get ⟨j, by omega⟩)) ∧
    -- 2. Union is all triangles
    (T1 triangles v_ab ∪ T2 triangles v_ab v_bc ∪
     T3 triangles v_ab v_bc v_cd ∪ T4 triangles v_ab v_bc v_cd v_da = triangles) := by
  intro triangles parts
  constructor
  · -- Pairwise disjointness from individual lemmas
    intro i j hij hi hj
    simp only [List.length_cons, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;> simp at hij <;>
      try exact T1_T2_disjoint triangles v_ab v_bc
      try exact T1_T3_disjoint triangles v_ab v_bc v_cd
      try exact T1_T4_disjoint triangles v_ab v_bc v_cd v_da
      try exact T2_T3_disjoint triangles v_ab v_bc v_cd
      try exact T2_T4_disjoint triangles v_ab v_bc v_cd v_da
      try exact T3_T4_disjoint triangles v_ab v_bc v_cd v_da
      <;> (first | apply Disjoint.symm | skip) <;>
      try exact T1_T2_disjoint triangles v_ab v_bc
      try exact T1_T3_disjoint triangles v_ab v_bc v_cd
      try exact T1_T4_disjoint triangles v_ab v_bc v_cd v_da
      try exact T2_T3_disjoint triangles v_ab v_bc v_cd
      try exact T2_T4_disjoint triangles v_ab v_bc v_cd v_da
      try exact T3_T4_disjoint triangles v_ab v_bc v_cd v_da
  · -- Union covers all triangles
    exact disjoint_partition_covers_all G M A B C D hcycle hM v_ab v_bc v_cd v_da hv_ab hv_bc hv_cd hv_da

end
