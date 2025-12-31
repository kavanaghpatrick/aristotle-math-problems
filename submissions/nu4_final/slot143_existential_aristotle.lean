/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: aed6b1a3-1794-4cb0-a11d-799dc87791f4

The following was proved by Aristotle:

- lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2
-/

/-
Tuza ν=4 Cycle_4: τ ≤ 8 via Existential Proof

APPROACH 2: Existential Proof
==============================
Prove existence of 8-edge cover without explicit construction.
Use Classical.choice and cardinality arguments.

Key insight: We don't need to BUILD the cover, just prove one EXISTS.
This avoids constructive König machinery entirely.

From AI research (Dec 30, 2025):
- "Existential proof with modified lemma structure" - most promising bypass
- Estimated 60-100 lines, 50% success probability

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
-- TRIANGLES AT A VERTEX
-- ══════════════════════════════════════════════════════════════════════════════

/-- Triangles containing vertex v -/
def trianglesAt (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

/-- Every triangle shares edge with M (from slot139, proven) -/
lemma triangle_shares_edge_with_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ X ∈ M, (t ∩ X).card ≥ 2 := by
  have := hM.2;
  by_contra! h;
  -- If no triangle in $M$ shares an edge with $t$, then $t$ can be added to $M$ to form a larger packing.
  have h_add : isTrianglePacking G (insert t M) := by
    refine' ⟨ _, _ ⟩;
    · exact Finset.insert_subset ht ( hM.1.1 );
    · intro x hx y hy hxy; by_cases hx' : x = t <;> by_cases hy' : y = t <;> simp_all +decide [ Finset.inter_comm ] ;
      · exact Nat.le_of_lt_succ ( h y hy );
      · exact Nat.le_of_lt_succ ( h x hx );
      · have := hM.1.2; aesop;
  -- Since $M$ is a maximum packing, adding $t$ to $M$ should not increase the packing number.
  have h_max : (insert t M).card ≤ trianglePackingNumber G := by
    have h_max : ∀ S : Finset (Finset V), isTrianglePacking G S → S.card ≤ trianglePackingNumber G := by
      unfold trianglePackingNumber;
      intro S hS;
      have h_max : S.card ∈ Finset.image Finset.card (Finset.filter (isTrianglePacking G) (G.cliqueFinset 3).powerset) := by
        simp +zetaDelta at *;
        exact ⟨ S, ⟨ hS.1, hS ⟩, rfl ⟩;
      have := Finset.le_max h_max;
      cases h : Finset.max ( Finset.image Finset.card ( Finset.filter ( isTrianglePacking G ) ( G.cliqueFinset 3 |> Finset.powerset ) ) ) <;> aesop;
    exact h_max _ h_add;
  rw [ Finset.card_insert_of_notMem ] at h_max;
  · linarith;
  · intro H; specialize h t H; simp_all +decide ;
    exact h.not_le ( ht.card_eq.symm ▸ by decide )

/- Aristotle failed to find a proof. -/
-- PROVEN in slot139

-- ══════════════════════════════════════════════════════════════════════════════
-- EXISTENTIAL COVER AT EACH VERTEX
-- ══════════════════════════════════════════════════════════════════════════════

/-- For triangles at v, there exists a 2-edge cover through v -/
lemma exists_local_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (hM4 : M.card = 4)
    (v : V) (hv : ∃ X Y : Finset V, X ∈ M ∧ Y ∈ M ∧ X ≠ Y ∧ v ∈ X ∧ v ∈ Y) :
    ∃ E_v : Finset (Sym2 V), E_v.card ≤ 2 ∧ E_v ⊆ G.edgeFinset ∧
      ∀ t ∈ trianglesAt G v, ∃ e ∈ E_v, e ∈ t.sym2 := by
  -- Key insight: triangles at v either share edge with one of the 2 M-triangles at v,
  -- or they are "external" triangles that still go through v.
  -- By maximality and the ν=4 constraint, external triangles at v can be covered
  -- by at most 2 edges through v.
  --
  -- Proof sketch:
  -- 1. Let X, Y be the two M-triangles containing v
  -- 2. Any triangle t at v either shares edge with X, shares edge with Y,
  --    or is external (shares only v with X ∪ Y)
  -- 3. External triangles at v form a "star" structure through v
  -- 4. At most 2 edges through v can cover all such triangles
  --    (otherwise matching in link graph > 2, contradicting ν = 4)
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

typeclass instance problem is stuck, it is often due to metavariables
  DecidableEq ?m.5-/
-- Aristotle: existential proof via cardinality argument

/-- Shared vertices of cycle_4 -/
def sharedVertices (cfg : Cycle4 G M) : Finset V :=
  {cfg.v_ab, cfg.v_bc, cfg.v_cd, cfg.v_da}

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  sharedVertices
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  cfg
Tactic `generalize` failed: result is not type correct
  (∃ X ∈ M, (t ∩ X).card ≥ 2) → ∃ v ∈ ?m.26, v ∈ t

V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
x✝ : Sort u_2
sharedVertices : x✝
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
M : Finset (Finset V)
hM : isMaxPacking G M
cfg : Cycle4 G M
t : Finset V
ht : t ∈ G.cliqueFinset 3
⊢ ∃ v ∈ ?m.26, v ∈ t-/
/-- Every triangle contains a shared vertex -/
lemma triangle_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    ∃ v ∈ sharedVertices cfg, v ∈ t := by
  -- By maximality, t shares edge with some M-element
  -- In cycle_4, any edge of M contains a shared vertex
  obtain ⟨X, hX, hShare⟩ := triangle_shares_edge_with_packing G M hM t ht
  -- X is one of A, B, C, D
  -- Each has a shared vertex with adjacent elements
  sorry

-- Aristotle: case analysis on X

-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN EXISTENTIAL THEOREM
-- ══════════════════════════════════════════════════════════════════════════════

/-- There exists an 8-edge cover for cycle_4 -/
theorem exists_cover_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    ∃ E' : Finset (Sym2 V), isTriangleCover G E' ∧ E'.card ≤ 8 := by
  -- Get 2-edge covers at each shared vertex
  have h_vab : ∃ E₁ : Finset (Sym2 V), E₁.card ≤ 2 ∧ E₁ ⊆ G.edgeFinset ∧
      ∀ t ∈ trianglesAt G cfg.v_ab, ∃ e ∈ E₁, e ∈ t.sym2 := by
    apply exists_local_cover G M hM (by rw [cfg.hM_eq]; simp)
    exact ⟨cfg.A, cfg.B, cfg.hA, cfg.hB, by
      intro h
      have : cfg.A ∩ cfg.B = cfg.A ∩ cfg.A := by rw [h]
      simp [cfg.hAB] at this,
      by rw [← cfg.hAB]; simp,
      by rw [← cfg.hAB]; simp⟩

  have h_vbc : ∃ E₂ : Finset (Sym2 V), E₂.card ≤ 2 ∧ E₂ ⊆ G.edgeFinset ∧
      ∀ t ∈ trianglesAt G cfg.v_bc, ∃ e ∈ E₂, e ∈ t.sym2 := by
    apply exists_local_cover G M hM (by rw [cfg.hM_eq]; simp)
    exact ⟨cfg.B, cfg.C, cfg.hB, cfg.hC, by
      intro h
      have : cfg.B ∩ cfg.C = cfg.B ∩ cfg.B := by rw [h]
      simp [cfg.hBC] at this,
      by rw [← cfg.hBC]; simp,
      by rw [← cfg.hBC]; simp⟩

  have h_vcd : ∃ E₃ : Finset (Sym2 V), E₃.card ≤ 2 ∧ E₃ ⊆ G.edgeFinset ∧
      ∀ t ∈ trianglesAt G cfg.v_cd, ∃ e ∈ E₃, e ∈ t.sym2 := by
    apply exists_local_cover G M hM (by rw [cfg.hM_eq]; simp)
    exact ⟨cfg.C, cfg.D, cfg.hC, cfg.hD, by
      intro h
      have : cfg.C ∩ cfg.D = cfg.C ∩ cfg.C := by rw [h]
      simp [cfg.hCD] at this,
      by rw [← cfg.hCD]; simp,
      by rw [← cfg.hCD]; simp⟩

  have h_vda : ∃ E₄ : Finset (Sym2 V), E₄.card ≤ 2 ∧ E₄ ⊆ G.edgeFinset ∧
      ∀ t ∈ trianglesAt G cfg.v_da, ∃ e ∈ E₄, e ∈ t.sym2 := by
    apply exists_local_cover G M hM (by rw [cfg.hM_eq]; simp)
    exact ⟨cfg.D, cfg.A, cfg.hD, cfg.hA, by
      intro h
      have : cfg.D ∩ cfg.A = cfg.D ∩ cfg.D := by rw [h]
      simp [cfg.hDA] at this,
      by rw [← cfg.hDA]; simp,
      by rw [← cfg.hDA]; simp⟩

  -- Extract the covers
  obtain ⟨E₁, hE₁_card, hE₁_sub, hE₁_cov⟩ := h_vab
  obtain ⟨E₂, hE₂_card, hE₂_sub, hE₂_cov⟩ := h_vbc
  obtain ⟨E₃, hE₃_card, hE₃_sub, hE₃_cov⟩ := h_vcd
  obtain ⟨E₄, hE₄_card, hE₄_sub, hE₄_cov⟩ := h_vda

  -- Union of all covers
  use E₁ ∪ E₂ ∪ E₃ ∪ E₄
  constructor
  · -- It's a valid triangle cover
    constructor
    · -- Subset of edge set
      intro e he
      simp only [Finset.mem_union] at he
      rcases he with he | he | he | he
      · exact hE₁_sub he
      · exact hE₂_sub he
      · exact hE₃_sub he
      · exact hE₄_sub he
    · -- Covers all triangles
      intro t ht
      -- t contains some shared vertex
      obtain ⟨v, hv_shared, hv_mem⟩ := triangle_contains_shared G M hM cfg t ht
      simp only [sharedVertices, Finset.mem_insert, Finset.mem_singleton] at hv_shared
      rcases hv_shared with rfl | rfl | rfl | rfl
      · obtain ⟨e, he_mem, he_in⟩ := hE₁_cov t (by simp [trianglesAt, ht, hv_mem])
        exact ⟨e, by simp [he_mem], he_in⟩
      · obtain ⟨e, he_mem, he_in⟩ := hE₂_cov t (by simp [trianglesAt, ht, hv_mem])
        exact ⟨e, by simp [he_mem], he_in⟩
      · obtain ⟨e, he_mem, he_in⟩ := hE₃_cov t (by simp [trianglesAt, ht, hv_mem])
        exact ⟨e, by simp [he_mem], he_in⟩
      · obtain ⟨e, he_mem, he_in⟩ := hE₄_cov t (by simp [trianglesAt, ht, hv_mem])
        exact ⟨e, by simp [he_mem], he_in⟩
  · -- Cardinality bound
    calc (E₁ ∪ E₂ ∪ E₃ ∪ E₄).card
        ≤ E₁.card + E₂.card + E₃.card + E₄.card := by
          apply le_trans (Finset.card_union_le _ _)
          apply le_trans
          · apply Nat.add_le_add_right (Finset.card_union_le _ _)
          apply le_trans
          · apply Nat.add_le_add_right
            apply Nat.add_le_add_right (Finset.card_union_le _ _)
          omega
      _ ≤ 2 + 2 + 2 + 2 := by omega
      _ = 8 := by ring

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Membership ℕ (Finset (Finset (Sym2 V)))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
`simp` made no progress-/
/-- Main theorem: τ ≤ 8 for cycle_4 -/
theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Cycle4 G M) :
    triangleCoveringNumber G ≤ 8 := by
  obtain ⟨E', hE'_cover, hE'_card⟩ := exists_cover_8 G M hM cfg
  unfold triangleCoveringNumber
  -- E' is a valid cover with |E'| ≤ 8, so min ≤ 8
  have h_mem : E'.card ∈ G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card := by
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨E', ⟨hE'_cover.1, hE'_cover⟩, rfl⟩
  have h_min_le := Finset.min'_le _ E'.card h_mem
  simp only [Finset.min_eq_inf_withTop, Finset.inf_eq_min'] at h_min_le
  sorry

-- Aristotle: conclude from h_min_le and hE'_card

end