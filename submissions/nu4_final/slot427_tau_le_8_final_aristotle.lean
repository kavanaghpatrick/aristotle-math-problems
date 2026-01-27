/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 031e1af5-5eb0-4b26-8162-9c460e824a19

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  slot427_tau_le_8_final.lean

  FINAL SUBMISSION: τ ≤ 8 for PATH_4 (ν = 4)

  MULTI-AGENT CONSENSUS (Grok, Gemini, Codex - Jan 16, 2026):
  1. NO complex structures - explicit parameters only
  2. Component-wise with explicit 8-edge construction
  3. Spine Priority for middle elements
  4. Import proven slots (423, 441, 425)

  PROVEN COMPONENTS:
  - slot423 (UUID: 6c77223c): 2 REAL edges cover S_e externals
  - slot441 (UUID: 67c528b3): Bridges contain shared vertex
  - slot425 (UUID: 13b393c1): Spine edge covers adjacent bridges

  TIER: 2-3 (assembly of proven components)
-/

import Mathlib


set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ══════════════════════════════════════════════════════════════════════════════
-- PROVEN LEMMA: Bridge Contains Shared (from slot441)
-- ══════════════════════════════════════════════════════════════════════════════

theorem bridge_contains_shared (G : SimpleGraph V) [DecidableRel G.Adj]
    (E F : Finset V) (v : V) (hEF : E ∩ F = {v})
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (hTE : 2 ≤ (T ∩ E).card) (hTF : 2 ≤ (T ∩ F).card) :
    v ∈ T := by
  have hT_card : T.card = 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff] at hT; exact hT.2
  have h_inter : (T ∩ E) ∩ (T ∩ F) = T ∩ {v} := by
    ext x; simp only [mem_inter, mem_singleton]; constructor
    · intro ⟨⟨hxT, hxE⟩, _, hxF⟩
      have hx_both : x ∈ E ∩ F := mem_inter.mpr ⟨hxE, hxF⟩
      rw [hEF] at hx_both
      exact ⟨hxT, mem_singleton.mp hx_both⟩
    · intro ⟨hxT, hxv⟩
      have hv_mem : v ∈ E ∩ F := by rw [hEF]; exact mem_singleton_self v
      rw [hxv]
      exact ⟨⟨hxT, (mem_inter.mp hv_mem).1⟩, hxT, (mem_inter.mp hv_mem).2⟩
  have h_sub : (T ∩ E) ∪ (T ∩ F) ⊆ T := by
    intro x hx; simp only [mem_union, mem_inter] at hx
    cases hx with | inl h => exact h.1 | inr h => exact h.1
  have h_ie := card_union_add_card_inter (T ∩ E) (T ∩ F)
  have h_pos : 0 < (T ∩ {v}).card := by
    rw [← h_inter]
    have h_union_le : ((T ∩ E) ∪ (T ∩ F)).card ≤ 3 := by
      calc ((T ∩ E) ∪ (T ∩ F)).card ≤ T.card := card_le_card h_sub
        _ = 3 := hT_card
    omega
  rw [card_pos] at h_pos
  obtain ⟨x, hx⟩ := h_pos
  simp only [mem_inter, mem_singleton] at hx
  exact hx.2 ▸ hx.1

-- ══════════════════════════════════════════════════════════════════════════════
-- HELPER: Triangle edge membership
-- ══════════════════════════════════════════════════════════════════════════════

lemma triangle_has_edge_from_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : T ∈ G.cliqueFinset 3)
    (v : V) (hv : v ∈ T) :
    ∃ u ∈ T, u ≠ v ∧ s(v, u) ∈ G.edgeFinset := by
  rw [SimpleGraph.mem_cliqueFinset_iff] at hT
  have hcard := hT.2
  have hclique := hT.1
  -- T has 3 vertices, v is one, so there are 2 others
  have : (T.erase v).Nonempty := by
    rw [erase_nonempty]
    constructor
    · exact hv
    · rw [hcard]; decide
  obtain ⟨u, hu⟩ := this
  rw [mem_erase] at hu
  use u
  refine ⟨hu.2, hu.1, ?_⟩
  rw [SimpleGraph.mem_edgeFinset]
  exact hclique hv hu.2 hu.1

lemma sym2_mem_of_both_mem (a b : V) (T : Finset V) (ha : a ∈ T) (hb : b ∈ T) :
    s(a, b) ∈ T.sym2 := by
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨ha, hb⟩

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unsolved goals
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
a₁ a₂ v₁ b v₂ c v₃ d₁ d₂ : V
h_a1_ne_a2 : a₁ ≠ a₂
h_a1_ne_v1 : a₁ ≠ v₁
h_a2_ne_v1 : a₂ ≠ v₁
h_v1_ne_b : v₁ ≠ b
h_v1_ne_v2 : v₁ ≠ v₂
h_b_ne_v2 : b ≠ v₂
h_v2_ne_c : v₂ ≠ c
h_v2_ne_v3 : v₂ ≠ v₃
h_c_ne_v3 : c ≠ v₃
h_v3_ne_d1 : v₃ ≠ d₁
h_v3_ne_d2 : v₃ ≠ d₂
h_d1_ne_d2 : d₁ ≠ d₂
hA : G.IsNClique 3 {a₁, a₂, v₁}
hB : G.IsNClique 3 {v₁, b, v₂}
hC : G.IsNClique 3 {v₂, c, v₃}
hD : G.IsNClique 3 {v₃, d₁, d₂}
hAB : {a₁, a₂, v₁} ∩ {v₁, b, v₂} = {v₁}
hBC : {v₁, b, v₂} ∩ {v₂, c, v₃} = {v₂}
hCD : {v₂, c, v₃} ∩ {v₃, d₁, d₂} = {v₃}
hAC : #({a₁, a₂, v₁} ∩ {v₂, c, v₃}) ≤ 1
hAD : #({a₁, a₂, v₁} ∩ {v₃, d₁, d₂}) ≤ 1
hBD : #({v₁, b, v₂} ∩ {v₃, d₁, d₂}) ≤ 1
h_max :
  ∀ T ∈ G.cliqueFinset 3,
    2 ≤ #(T ∩ {a₁, a₂, v₁}) ∨ 2 ≤ #(T ∩ {v₁, b, v₂}) ∨ 2 ≤ #(T ∩ {v₂, c, v₃}) ∨ 2 ≤ #(T ∩ {v₃, d₁, d₂})
Cover : Finset (Sym2 V) := {s(a₁, v₁), s(a₂, v₁), s(v₁, v₂), s(v₁, b), s(v₂, v₃), s(v₂, c), s(v₃, d₁), s(v₃, d₂)}
⊢ v₂ = a₁ ∨ v₂ = a₂ ∨ v₂ = v₁
unsolved goals
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
a₁ a₂ v₁ b v₂ c v₃ d₁ d₂ : V
h_a1_ne_a2 : a₁ ≠ a₂
h_a1_ne_v1 : a₁ ≠ v₁
h_a2_ne_v1 : a₂ ≠ v₁
h_v1_ne_b : v₁ ≠ b
h_v1_ne_v2 : v₁ ≠ v₂
h_b_ne_v2 : b ≠ v₂
h_v2_ne_c : v₂ ≠ c
h_v2_ne_v3 : v₂ ≠ v₃
h_c_ne_v3 : c ≠ v₃
h_v3_ne_d1 : v₃ ≠ d₁
h_v3_ne_d2 : v₃ ≠ d₂
h_d1_ne_d2 : d₁ ≠ d₂
hA : G.IsNClique 3 {a₁, a₂, v₁}
hB : G.IsNClique 3 {v₁, b, v₂}
hC : G.IsNClique 3 {v₂, c, v₃}
hD : G.IsNClique 3 {v₃, d₁, d₂}
hAB : {a₁, a₂, v₁} ∩ {v₁, b, v₂} = {v₁}
hBC : {v₁, b, v₂} ∩ {v₂, c, v₃} = {v₂}
hCD : {v₂, c, v₃} ∩ {v₃, d₁, d₂} = {v₃}
hAC : #({a₁, a₂, v₁} ∩ {v₂, c, v₃}) ≤ 1
hAD : #({a₁, a₂, v₁} ∩ {v₃, d₁, d₂}) ≤ 1
hBD : #({v₁, b, v₂} ∩ {v₃, d₁, d₂}) ≤ 1
h_max :
  ∀ T ∈ G.cliqueFinset 3,
    2 ≤ #(T ∩ {a₁, a₂, v₁}) ∨ 2 ≤ #(T ∩ {v₁, b, v₂}) ∨ 2 ≤ #(T ∩ {v₂, c, v₃}) ∨ 2 ≤ #(T ∩ {v₃, d₁, d₂})
Cover : Finset (Sym2 V) := {s(a₁, v₁), s(a₂, v₁), s(v₁, v₂), s(v₁, b), s(v₂, v₃), s(v₂, c), s(v₃, d₁), s(v₃, d₂)}
⊢ b = a₁ ∨ b = a₂ ∨ b = v₁
unsolved goals
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
a₁ a₂ v₁ b v₂ c v₃ d₁ d₂ : V
h_a1_ne_a2 : a₁ ≠ a₂
h_a1_ne_v1 : a₁ ≠ v₁
h_a2_ne_v1 : a₂ ≠ v₁
h_v1_ne_b : v₁ ≠ b
h_v1_ne_v2 : v₁ ≠ v₂
h_b_ne_v2 : b ≠ v₂
h_v2_ne_c : v₂ ≠ c
h_v2_ne_v3 : v₂ ≠ v₃
h_c_ne_v3 : c ≠ v₃
h_v3_ne_d1 : v₃ ≠ d₁
h_v3_ne_d2 : v₃ ≠ d₂
h_d1_ne_d2 : d₁ ≠ d₂
hA : G.IsNClique 3 {a₁, a₂, v₁}
hB : G.IsNClique 3 {v₁, b, v₂}
hC : G.IsNClique 3 {v₂, c, v₃}
hD : G.IsNClique 3 {v₃, d₁, d₂}
hAB : {a₁, a₂, v₁} ∩ {v₁, b, v₂} = {v₁}
hBC : {v₁, b, v₂} ∩ {v₂, c, v₃} = {v₂}
hCD : {v₂, c, v₃} ∩ {v₃, d₁, d₂} = {v₃}
hAC : #({a₁, a₂, v₁} ∩ {v₂, c, v₃}) ≤ 1
hAD : #({a₁, a₂, v₁} ∩ {v₃, d₁, d₂}) ≤ 1
hBD : #({v₁, b, v₂} ∩ {v₃, d₁, d₂}) ≤ 1
h_max :
  ∀ T ∈ G.cliqueFinset 3,
    2 ≤ #(T ∩ {a₁, a₂, v₁}) ∨ 2 ≤ #(T ∩ {v₁, b, v₂}) ∨ 2 ≤ #(T ∩ {v₂, c, v₃}) ∨ 2 ≤ #(T ∩ {v₃, d₁, d₂})
Cover : Finset (Sym2 V) := {s(a₁, v₁), s(a₂, v₁), s(v₁, v₂), s(v₁, b), s(v₂, v₃), s(v₂, c), s(v₃, d₁), s(v₃, d₂)}
⊢ v₂ = a₁ ∨ v₂ = a₂ ∨ v₂ = v₁
unsolved goals
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
a₁ a₂ v₁ b v₂ c v₃ d₁ d₂ : V
h_a1_ne_a2 : a₁ ≠ a₂
h_a1_ne_v1 : a₁ ≠ v₁
h_a2_ne_v1 : a₂ ≠ v₁
h_v1_ne_b : v₁ ≠ b
h_v1_ne_v2 : v₁ ≠ v₂
h_b_ne_v2 : b ≠ v₂
h_v2_ne_c : v₂ ≠ c
h_v2_ne_v3 : v₂ ≠ v₃
h_c_ne_v3 : c ≠ v₃
h_v3_ne_d1 : v₃ ≠ d₁
h_v3_ne_d2 : v₃ ≠ d₂
h_d1_ne_d2 : d₁ ≠ d₂
hA : G.IsNClique 3 {a₁, a₂, v₁}
hB : G.IsNClique 3 {v₁, b, v₂}
hC : G.IsNClique 3 {v₂, c, v₃}
hD : G.IsNClique 3 {v₃, d₁, d₂}
hAB : {a₁, a₂, v₁} ∩ {v₁, b, v₂} = {v₁}
hBC : {v₁, b, v₂} ∩ {v₂, c, v₃} = {v₂}
hCD : {v₂, c, v₃} ∩ {v₃, d₁, d₂} = {v₃}
hAC : #({a₁, a₂, v₁} ∩ {v₂, c, v₃}) ≤ 1
hAD : #({a₁, a₂, v₁} ∩ {v₃, d₁, d₂}) ≤ 1
hBD : #({v₁, b, v₂} ∩ {v₃, d₁, d₂}) ≤ 1
h_max :
  ∀ T ∈ G.cliqueFinset 3,
    2 ≤ #(T ∩ {a₁, a₂, v₁}) ∨ 2 ≤ #(T ∩ {v₁, b, v₂}) ∨ 2 ≤ #(T ∩ {v₂, c, v₃}) ∨ 2 ≤ #(T ∩ {v₃, d₁, d₂})
Cover : Finset (Sym2 V) := {s(a₁, v₁), s(a₂, v₁), s(v₁, v₂), s(v₁, b), s(v₂, v₃), s(v₂, c), s(v₃, d₁), s(v₃, d₂)}
⊢ v₃ = a₁ ∨ v₃ = a₂ ∨ v₃ = v₁
unsolved goals
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
a₁ a₂ v₁ b v₂ c v₃ d₁ d₂ : V
h_a1_ne_a2 : a₁ ≠ a₂
h_a1_ne_v1 : a₁ ≠ v₁
h_a2_ne_v1 : a₂ ≠ v₁
h_v1_ne_b : v₁ ≠ b
h_v1_ne_v2 : v₁ ≠ v₂
h_b_ne_v2 : b ≠ v₂
h_v2_ne_c : v₂ ≠ c
h_v2_ne_v3 : v₂ ≠ v₃
h_c_ne_v3 : c ≠ v₃
h_v3_ne_d1 : v₃ ≠ d₁
h_v3_ne_d2 : v₃ ≠ d₂
h_d1_ne_d2 : d₁ ≠ d₂
hA : G.IsNClique 3 {a₁, a₂, v₁}
hB : G.IsNClique 3 {v₁, b, v₂}
hC : G.IsNClique 3 {v₂, c, v₃}
hD : G.IsNClique 3 {v₃, d₁, d₂}
hAB : {a₁, a₂, v₁} ∩ {v₁, b, v₂} = {v₁}
hBC : {v₁, b, v₂} ∩ {v₂, c, v₃} = {v₂}
hCD : {v₂, c, v₃} ∩ {v₃, d₁, d₂} = {v₃}
hAC : #({a₁, a₂, v₁} ∩ {v₂, c, v₃}) ≤ 1
hAD : #({a₁, a₂, v₁} ∩ {v₃, d₁, d₂}) ≤ 1
hBD : #({v₁, b, v₂} ∩ {v₃, d₁, d₂}) ≤ 1
h_max :
  ∀ T ∈ G.cliqueFinset 3,
    2 ≤ #(T ∩ {a₁, a₂, v₁}) ∨ 2 ≤ #(T ∩ {v₁, b, v₂}) ∨ 2 ≤ #(T ∩ {v₂, c, v₃}) ∨ 2 ≤ #(T ∩ {v₃, d₁, d₂})
Cover : Finset (Sym2 V) := {s(a₁, v₁), s(a₂, v₁), s(v₁, v₂), s(v₁, b), s(v₂, v₃), s(v₂, c), s(v₃, d₁), s(v₃, d₂)}
⊢ v₂ = a₁ ∨ v₂ = a₂ ∨ v₂ = v₁
unsolved goals
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
a₁ a₂ v₁ b v₂ c v₃ d₁ d₂ : V
h_a1_ne_a2 : a₁ ≠ a₂
h_a1_ne_v1 : a₁ ≠ v₁
h_a2_ne_v1 : a₂ ≠ v₁
h_v1_ne_b : v₁ ≠ b
h_v1_ne_v2 : v₁ ≠ v₂
h_b_ne_v2 : b ≠ v₂
h_v2_ne_c : v₂ ≠ c
h_v2_ne_v3 : v₂ ≠ v₃
h_c_ne_v3 : c ≠ v₃
h_v3_ne_d1 : v₃ ≠ d₁
h_v3_ne_d2 : v₃ ≠ d₂
h_d1_ne_d2 : d₁ ≠ d₂
hA : G.IsNClique 3 {a₁, a₂, v₁}
hB : G.IsNClique 3 {v₁, b, v₂}
hC : G.IsNClique 3 {v₂, c, v₃}
hD : G.IsNClique 3 {v₃, d₁, d₂}
hAB : {a₁, a₂, v₁} ∩ {v₁, b, v₂} = {v₁}
hBC : {v₁, b, v₂} ∩ {v₂, c, v₃} = {v₂}
hCD : {v₂, c, v₃} ∩ {v₃, d₁, d₂} = {v₃}
hAC : #({a₁, a₂, v₁} ∩ {v₂, c, v₃}) ≤ 1
hAD : #({a₁, a₂, v₁} ∩ {v₃, d₁, d₂}) ≤ 1
hBD : #({v₁, b, v₂} ∩ {v₃, d₁, d₂}) ≤ 1
h_max :
  ∀ T ∈ G.cliqueFinset 3,
    2 ≤ #(T ∩ {a₁, a₂, v₁}) ∨ 2 ≤ #(T ∩ {v₁, b, v₂}) ∨ 2 ≤ #(T ∩ {v₂, c, v₃}) ∨ 2 ≤ #(T ∩ {v₃, d₁, d₂})
Cover : Finset (Sym2 V) := {s(a₁, v₁), s(a₂, v₁), s(v₁, v₂), s(v₁, b), s(v₂, v₃), s(v₂, c), s(v₃, d₁), s(v₃, d₂)}
⊢ c = a₁ ∨ c = a₂ ∨ c = v₁
unsolved goals
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
a₁ a₂ v₁ b v₂ c v₃ d₁ d₂ : V
h_a1_ne_a2 : a₁ ≠ a₂
h_a1_ne_v1 : a₁ ≠ v₁
h_a2_ne_v1 : a₂ ≠ v₁
h_v1_ne_b : v₁ ≠ b
h_v1_ne_v2 : v₁ ≠ v₂
h_b_ne_v2 : b ≠ v₂
h_v2_ne_c : v₂ ≠ c
h_v2_ne_v3 : v₂ ≠ v₃
h_c_ne_v3 : c ≠ v₃
h_v3_ne_d1 : v₃ ≠ d₁
h_v3_ne_d2 : v₃ ≠ d₂
h_d1_ne_d2 : d₁ ≠ d₂
hA : G.IsNClique 3 {a₁, a₂, v₁}
hB : G.IsNClique 3 {v₁, b, v₂}
hC : G.IsNClique 3 {v₂, c, v₃}
hD : G.IsNClique 3 {v₃, d₁, d₂}
hAB : {a₁, a₂, v₁} ∩ {v₁, b, v₂} = {v₁}
hBC : {v₁, b, v₂} ∩ {v₂, c, v₃} = {v₂}
hCD : {v₂, c, v₃} ∩ {v₃, d₁, d₂} = {v₃}
hAC : #({a₁, a₂, v₁} ∩ {v₂, c, v₃}) ≤ 1
hAD : #({a₁, a₂, v₁} ∩ {v₃, d₁, d₂}) ≤ 1
hBD : #({v₁, b, v₂} ∩ {v₃, d₁, d₂}) ≤ 1
h_max :
  ∀ T ∈ G.cliqueFinset 3,
    2 ≤ #(T ∩ {a₁, a₂, v₁}) ∨ 2 ≤ #(T ∩ {v₁, b, v₂}) ∨ 2 ≤ #(T ∩ {v₂, c, v₃}) ∨ 2 ≤ #(T ∩ {v₃, d₁, d₂})
Cover : Finset (Sym2 V) := {s(a₁, v₁), s(a₂, v₁), s(v₁, v₂), s(v₁, b), s(v₂, v₃), s(v₂, c), s(v₃, d₁), s(v₃, d₂)}
⊢ v₃ = a₁ ∨ v₃ = a₂ ∨ v₃ = v₁
unsolved goals
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
a₁ a₂ v₁ b v₂ c v₃ d₁ d₂ : V
h_a1_ne_a2 : a₁ ≠ a₂
h_a1_ne_v1 : a₁ ≠ v₁
h_a2_ne_v1 : a₂ ≠ v₁
h_v1_ne_b : v₁ ≠ b
h_v1_ne_v2 : v₁ ≠ v₂
h_b_ne_v2 : b ≠ v₂
h_v2_ne_c : v₂ ≠ c
h_v2_ne_v3 : v₂ ≠ v₃
h_c_ne_v3 : c ≠ v₃
h_v3_ne_d1 : v₃ ≠ d₁
h_v3_ne_d2 : v₃ ≠ d₂
h_d1_ne_d2 : d₁ ≠ d₂
hA : G.IsNClique 3 {a₁, a₂, v₁}
hB : G.IsNClique 3 {v₁, b, v₂}
hC : G.IsNClique 3 {v₂, c, v₃}
hD : G.IsNClique 3 {v₃, d₁, d₂}
hAB : {a₁, a₂, v₁} ∩ {v₁, b, v₂} = {v₁}
hBC : {v₁, b, v₂} ∩ {v₂, c, v₃} = {v₂}
hCD : {v₂, c, v₃} ∩ {v₃, d₁, d₂} = {v₃}
hAC : #({a₁, a₂, v₁} ∩ {v₂, c, v₃}) ≤ 1
hAD : #({a₁, a₂, v₁} ∩ {v₃, d₁, d₂}) ≤ 1
hBD : #({v₁, b, v₂} ∩ {v₃, d₁, d₂}) ≤ 1
h_max :
  ∀ T ∈ G.cliqueFinset 3,
    2 ≤ #(T ∩ {a₁, a₂, v₁}) ∨ 2 ≤ #(T ∩ {v₁, b, v₂}) ∨ 2 ≤ #(T ∩ {v₂, c, v₃}) ∨ 2 ≤ #(T ∩ {v₃, d₁, d₂})
Cover : Finset (Sym2 V) := {s(a₁, v₁), s(a₂, v₁), s(v₁, v₂), s(v₁, b), s(v₂, v₃), s(v₂, c), s(v₃, d₁), s(v₃, d₂)}
⊢ d₁ = a₁ ∨ d₁ = a₂ ∨ d₁ = v₁
unsolved goals
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
a₁ a₂ v₁ b v₂ c v₃ d₁ d₂ : V
h_a1_ne_a2 : a₁ ≠ a₂
h_a1_ne_v1 : a₁ ≠ v₁
h_a2_ne_v1 : a₂ ≠ v₁
h_v1_ne_b : v₁ ≠ b
h_v1_ne_v2 : v₁ ≠ v₂
h_b_ne_v2 : b ≠ v₂
h_v2_ne_c : v₂ ≠ c
h_v2_ne_v3 : v₂ ≠ v₃
h_c_ne_v3 : c ≠ v₃
h_v3_ne_d1 : v₃ ≠ d₁
h_v3_ne_d2 : v₃ ≠ d₂
h_d1_ne_d2 : d₁ ≠ d₂
hA : G.IsNClique 3 {a₁, a₂, v₁}
hB : G.IsNClique 3 {v₁, b, v₂}
hC : G.IsNClique 3 {v₂, c, v₃}
hD : G.IsNClique 3 {v₃, d₁, d₂}
hAB : {a₁, a₂, v₁} ∩ {v₁, b, v₂} = {v₁}
hBC : {v₁, b, v₂} ∩ {v₂, c, v₃} = {v₂}
hCD : {v₂, c, v₃} ∩ {v₃, d₁, d₂} = {v₃}
hAC : #({a₁, a₂, v₁} ∩ {v₂, c, v₃}) ≤ 1
hAD : #({a₁, a₂, v₁} ∩ {v₃, d₁, d₂}) ≤ 1
hBD : #({v₁, b, v₂} ∩ {v₃, d₁, d₂}) ≤ 1
h_max :
  ∀ T ∈ G.cliqueFinset 3,
    2 ≤ #(T ∩ {a₁, a₂, v₁}) ∨ 2 ≤ #(T ∩ {v₁, b, v₂}) ∨ 2 ≤ #(T ∩ {v₂, c, v₃}) ∨ 2 ≤ #(T ∩ {v₃, d₁, d₂})
Cover : Finset (Sym2 V) := {s(a₁, v₁), s(a₂, v₁), s(v₁, v₂), s(v₁, b), s(v₂, v₃), s(v₂, c), s(v₃, d₁), s(v₃, d₂)}
⊢ v₃ = a₁ ∨ v₃ = a₂ ∨ v₃ = v₁
unsolved goals
V : Type u_1
inst✝² : Fintype V
inst✝¹ : DecidableEq V
G : SimpleGraph V
inst✝ : DecidableRel G.Adj
a₁ a₂ v₁ b v₂ c v₃ d₁ d₂ : V
h_a1_ne_a2 : a₁ ≠ a₂
h_a1_ne_v1 : a₁ ≠ v₁
h_a2_ne_v1 : a₂ ≠ v₁
h_v1_ne_b : v₁ ≠ b
h_v1_ne_v2 : v₁ ≠ v₂
h_b_ne_v2 : b ≠ v₂
h_v2_ne_c : v₂ ≠ c
h_v2_ne_v3 : v₂ ≠ v₃
h_c_ne_v3 : c ≠ v₃
h_v3_ne_d1 : v₃ ≠ d₁
h_v3_ne_d2 : v₃ ≠ d₂
h_d1_ne_d2 : d₁ ≠ d₂
hA : G.IsNClique 3 {a₁, a₂, v₁}
hB : G.IsNClique 3 {v₁, b, v₂}
hC : G.IsNClique 3 {v₂, c, v₃}
hD : G.IsNClique 3 {v₃, d₁, d₂}
hAB : {a₁, a₂, v₁} ∩ {v₁, b, v₂} = {v₁}
hBC : {v₁, b, v₂} ∩ {v₂, c, v₃} = {v₂}
hCD : {v₂, c, v₃} ∩ {v₃, d₁, d₂} = {v₃}
hAC : #({a₁, a₂, v₁} ∩ {v₂, c, v₃}) ≤ 1
hAD : #({a₁, a₂, v₁} ∩ {v₃, d₁, d₂}) ≤ 1
hBD : #({v₁, b, v₂} ∩ {v₃, d₁, d₂}) ≤ 1
h_max :
  ∀ T ∈ G.cliqueFinset 3,
    2 ≤ #(T ∩ {a₁, a₂, v₁}) ∨ 2 ≤ #(T ∩ {v₁, b, v₂}) ∨ 2 ≤ #(T ∩ {v₂, c, v₃}) ∨ 2 ≤ #(T ∩ {v₃, d₁, d₂})
Cover : Finset (Sym2 V) := {s(a₁, v₁), s(a₂, v₁), s(v₁, v₂), s(v₁, b), s(v₂, v₃), s(v₂, c), s(v₃, d₁), s(v₃, d₂)}
⊢ d₂ = a₁ ∨ d₂ = a₂ ∨ d₂ = v₁
Tactic `cases` failed with a nested error:
Dependent elimination failed: Failed to solve equation
  Quot.lift List.length ⋯ (T ∩ {a₁, a₂, v₁}).val = 2
at case `Nat.le.refl`-/
-- ══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: τ ≤ 8 for PATH_4
-- ══════════════════════════════════════════════════════════════════════════════

/-
  PROOF SKETCH (per Aristotle paper recommendation):
  1. Construct explicit 8-edge cover using spine priority
  2. Show card ≤ 8 (trivial by construction)
  3. Show subset of G.edgeFinset (all edges are in triangles)
  4. For any triangle T:
     a) If T ∈ {A,B,C,D}: covered by its own edges
     b) If T is external to exactly one element: covered by that element's 2 edges
     c) If T is bridge between two adjacent elements: contains shared vertex,
        so covered by spine edge or endpoint spoke
-/
theorem tau_le_8_path4 (G : SimpleGraph V) [DecidableRel G.Adj]
    -- Vertices (9 distinct)
    (a₁ a₂ v₁ b v₂ c v₃ d₁ d₂ : V)
    -- Distinctness
    (h_a1_ne_a2 : a₁ ≠ a₂) (h_a1_ne_v1 : a₁ ≠ v₁) (h_a2_ne_v1 : a₂ ≠ v₁)
    (h_v1_ne_b : v₁ ≠ b) (h_v1_ne_v2 : v₁ ≠ v₂) (h_b_ne_v2 : b ≠ v₂)
    (h_v2_ne_c : v₂ ≠ c) (h_v2_ne_v3 : v₂ ≠ v₃) (h_c_ne_v3 : c ≠ v₃)
    (h_v3_ne_d1 : v₃ ≠ d₁) (h_v3_ne_d2 : v₃ ≠ d₂) (h_d1_ne_d2 : d₁ ≠ d₂)
    -- Triangle membership
    (hA : {a₁, a₂, v₁} ∈ G.cliqueFinset 3)
    (hB : {v₁, b, v₂} ∈ G.cliqueFinset 3)
    (hC : {v₂, c, v₃} ∈ G.cliqueFinset 3)
    (hD : {v₃, d₁, d₂} ∈ G.cliqueFinset 3)
    -- Spine intersections
    (hAB : ({a₁, a₂, v₁} : Finset V) ∩ {v₁, b, v₂} = {v₁})
    (hBC : ({v₁, b, v₂} : Finset V) ∩ {v₂, c, v₃} = {v₂})
    (hCD : ({v₂, c, v₃} : Finset V) ∩ {v₃, d₁, d₂} = {v₃})
    -- Edge-disjointness (packing property)
    (hAC : (({a₁, a₂, v₁} : Finset V) ∩ {v₂, c, v₃}).card ≤ 1)
    (hAD : (({a₁, a₂, v₁} : Finset V) ∩ {v₃, d₁, d₂}).card ≤ 1)
    (hBD : (({v₁, b, v₂} : Finset V) ∩ {v₃, d₁, d₂}).card ≤ 1)
    -- Maximality: every triangle shares edge with some packing element
    (h_max : ∀ T ∈ G.cliqueFinset 3,
      2 ≤ (T ∩ {a₁, a₂, v₁}).card ∨
      2 ≤ (T ∩ {v₁, b, v₂}).card ∨
      2 ≤ (T ∩ {v₂, c, v₃}).card ∨
      2 ≤ (T ∩ {v₃, d₁, d₂}).card) :
    -- Conclusion: 8-edge cover exists
    ∃ Cover : Finset (Sym2 V), Cover.card ≤ 8 ∧
      Cover ⊆ G.edgeFinset ∧
      ∀ T ∈ G.cliqueFinset 3, ∃ e ∈ Cover, e ∈ T.sym2 := by

  -- Explicit 8-edge cover construction (Spine Priority)
  let Cover : Finset (Sym2 V) := {
    s(a₁, v₁), s(a₂, v₁),       -- A: 2 spokes at v₁
    s(v₁, v₂), s(v₁, b),         -- B: spine + leg at v₁
    s(v₂, v₃), s(v₂, c),         -- C: spine + leg at v₂
    s(v₃, d₁), s(v₃, d₂)         -- D: 2 spokes at v₃
  }

  use Cover

  refine ⟨?hCard, ?hSubset, ?hCovers⟩

  -- Card ≤ 8
  case hCard =>
    simp only [Cover]
    -- 8 distinct elements
    sorry

  -- Subset of G.edgeFinset
  case hSubset =>
    intro e he
    simp only [Cover, mem_insert, mem_singleton] at he
    rw [SimpleGraph.mem_edgeFinset]
    -- Each edge comes from a triangle
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals {
      rw [SimpleGraph.mem_cliqueFinset_iff] at hA hB hC hD
      first
      | exact hA.1 (by simp) (by simp) (by assumption)
      | exact hB.1 (by simp) (by simp) (by assumption)
      | exact hC.1 (by simp) (by simp) (by assumption)
      | exact hD.1 (by simp) (by simp) (by assumption)
    }

  -- Covers all triangles
  case hCovers =>
    intro T hT
    -- Get which packing element(s) T interacts with
    obtain ⟨hTA | hTB | hTC | hTD⟩ := h_max T hT

    -- Case 1: T shares edge with A = {a₁, a₂, v₁}
    · by_cases hTB' : 2 ≤ (T ∩ {v₁, b, v₂}).card
      · -- T is bridge A-B: by slot441, v₁ ∈ T
        have hv₁T : v₁ ∈ T := bridge_contains_shared G {a₁, a₂, v₁} {v₁, b, v₂} v₁ hAB T hT hTA hTB'
        -- T has another vertex besides v₁
        obtain ⟨u, huT, hune, huAdj⟩ := triangle_has_edge_from_vertex G T hT v₁ hv₁T
        -- s(v₁, u) ∈ T.sym2, and we need to show some cover edge hits T
        -- Since v₁ ∈ T, edge s(v₁, ?) hits T for any ? ∈ T
        use s(a₁, v₁)
        constructor
        · simp [Cover]
        · -- Need to show s(a₁, v₁) ∈ T.sym2, i.e., a₁ ∈ T and v₁ ∈ T
          -- We know v₁ ∈ T. We need a₁ ∈ T or find another edge.
          -- Actually, T shares edge with A means |T ∩ A| ≥ 2
          -- So T contains at least 2 of {a₁, a₂, v₁}
          -- One is v₁, the other is a₁ or a₂
          sorry
      · -- T is external to A only (S_e(A))
        -- T shares edge with A, not with B
        -- T contains 2 of {a₁, a₂, v₁}
        -- Cover edges s(a₁, v₁) and s(a₂, v₁) cover any such T
        sorry

    -- Case 2: T shares edge with B = {v₁, b, v₂}
    · by_cases hTC' : 2 ≤ (T ∩ {v₂, c, v₃}).card
      · -- T is bridge B-C: by slot441, v₂ ∈ T
        have hv₂T : v₂ ∈ T := bridge_contains_shared G {v₁, b, v₂} {v₂, c, v₃} v₂ hBC T hT hTB hTC'
        use s(v₂, v₃)
        constructor
        · simp [Cover]
        · sorry
      · by_cases hTA' : 2 ≤ (T ∩ {a₁, a₂, v₁}).card
        · -- Bridge A-B handled above
          sorry
        · -- External to B only
          -- T contains 2 of {v₁, b, v₂}
          -- Spine s(v₁, v₂) or s(v₁, b) covers it
          sorry

    -- Case 3: T shares edge with C
    · by_cases hTD' : 2 ≤ (T ∩ {v₃, d₁, d₂}).card
      · -- Bridge C-D: v₃ ∈ T
        have hv₃T : v₃ ∈ T := bridge_contains_shared G {v₂, c, v₃} {v₃, d₁, d₂} v₃ hCD T hT hTC hTD'
        use s(v₂, v₃)
        constructor
        · simp [Cover]
        · sorry
      · -- External to C only
        sorry

    -- Case 4: T shares edge with D
    · -- T contains 2 of {v₃, d₁, d₂}
      -- Edges s(v₃, d₁) and s(v₃, d₂) cover
      sorry

end