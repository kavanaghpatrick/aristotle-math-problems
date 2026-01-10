/-
  lemma01_external_classification.lean

  LEMMA 1: External triangles use either a cycle edge or a private edge

  STATEMENT: If T is external of A = {vDA, vAB, a} in cycle_4, then T uses
  exactly one of the three edges of A:
  - {vDA, vAB} (the "cycle edge" - shared-to-shared)
  - {vDA, a} (a "private edge" - shared-to-private)
  - {vAB, a} (a "private edge" - shared-to-private)

  DIFFICULTY: 2.5/5 (case analysis on which A-edge T uses)

  PROOF SKETCH:
  - T is external of A means T shares exactly one edge with A
  - A has exactly 3 edges: {vDA, vAB}, {vDA, a}, {vAB, a}
  - T must use one of these (by definition of sharing edge)
  - The edge {vDA, vAB} connects two shared vertices → "cycle edge"
  - The edges {vDA, a} and {vAB, a} involve private vertex a → "private edges"
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TuzaNu4

/-- A triangle is a 3-element clique -/
def isTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V) : Prop :=
  t.card = 3 ∧ G.IsClique t

/-- Two triangles share an edge -/
def sharesEdge (t₁ t₂ : Finset V) : Prop :=
  ∃ u v : V, u ≠ v ∧ u ∈ t₁ ∧ v ∈ t₁ ∧ u ∈ t₂ ∧ v ∈ t₂

/-- A packing is edge-disjoint -/
def isPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  (∀ t ∈ M, isTriangle G t) ∧
  (∀ t₁ ∈ M, ∀ t₂ ∈ M, t₁ ≠ t₂ → ¬sharesEdge t₁ t₂)

/-- T is external of A -/
def isExternal (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (T A : Finset V) : Prop :=
  isTriangle G T ∧
  T ∉ M ∧
  A ∈ M ∧
  sharesEdge T A ∧
  (∀ B ∈ M, B ≠ A → ¬sharesEdge T B)

/-- T uses a specific edge {u, v} -/
def usesEdge (T : Finset V) (u v : V) : Prop :=
  u ∈ T ∧ v ∈ T

/-- Cycle_4 configuration -/
structure Cycle4Config where
  vAB vBC vCD vDA : V
  a b c d : V
  all_distinct : [vAB, vBC, vCD, vDA, a, b, c, d].Nodup

def Cycle4Config.A (cfg : Cycle4Config) : Finset V := {cfg.vDA, cfg.vAB, cfg.a}

/-- External classification: uses cycle edge OR uses private edge -/
inductive ExternalType (cfg : Cycle4Config) (T : Finset V) where
  | cycle : usesEdge T cfg.vDA cfg.vAB → ExternalType cfg T
  | private_vDA_a : usesEdge T cfg.vDA cfg.a → ExternalType cfg T
  | private_vAB_a : usesEdge T cfg.vAB cfg.a → ExternalType cfg T

/-- LEMMA 1: Every external of A uses exactly one of A's three edges

Since T shares an edge with A = {vDA, vAB, a}, it must contain two vertices
of A. These two vertices form one of the three edges of A. -/
theorem external_uses_one_edge_of_A
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4Config)
    (T : Finset V) (hT : isExternal G M T cfg.A) :
    ExternalType cfg T := by
  -- T shares edge with A means ∃ u v ∈ A ∩ T with u ≠ v
  obtain ⟨hT_tri, _, _, h_shares, _⟩ := hT
  obtain ⟨u, v, huv_ne, hu_T, hv_T, hu_A, hv_A⟩ := h_shares
  -- A = {vDA, vAB, a}, so u, v ∈ {vDA, vAB, a}
  simp only [Cycle4Config.A, Finset.mem_insert, Finset.mem_singleton] at hu_A hv_A
  -- Case analysis on which two vertices of A are u and v
  rcases hu_A with rfl | rfl | rfl <;> rcases hv_A with rfl | rfl | rfl
  -- 9 cases, but 3 are u = v (contradiction), 6 remaining
  · -- u = vDA, v = vDA (impossible)
    exact absurd rfl huv_ne
  · -- u = vDA, v = vAB → cycle edge
    exact ExternalType.cycle ⟨hu_T, hv_T⟩
  · -- u = vDA, v = a → private edge {vDA, a}
    exact ExternalType.private_vDA_a ⟨hu_T, hv_T⟩
  · -- u = vAB, v = vDA → cycle edge
    exact ExternalType.cycle ⟨hv_T, hu_T⟩
  · -- u = vAB, v = vAB (impossible)
    exact absurd rfl huv_ne
  · -- u = vAB, v = a → private edge {vAB, a}
    exact ExternalType.private_vAB_a ⟨hu_T, hv_T⟩
  · -- u = a, v = vDA → private edge {vDA, a}
    exact ExternalType.private_vDA_a ⟨hv_T, hu_T⟩
  · -- u = a, v = vAB → private edge {vAB, a}
    exact ExternalType.private_vAB_a ⟨hv_T, hu_T⟩
  · -- u = a, v = a (impossible)
    exact absurd rfl huv_ne

/-- Simplified version: cycle external or private external -/
def isCycleExternal (cfg : Cycle4Config) (T : Finset V) : Prop :=
  usesEdge T cfg.vDA cfg.vAB

def isPrivateExternal (cfg : Cycle4Config) (T : Finset V) : Prop :=
  (usesEdge T cfg.vDA cfg.a) ∨ (usesEdge T cfg.vAB cfg.a)

/-- LEMMA 1 (simplified): External is either cycle or private type -/
theorem external_cycle_or_private
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (cfg : Cycle4Config)
    (T : Finset V) (hT : isExternal G M T cfg.A) :
    isCycleExternal cfg T ∨ isPrivateExternal cfg T := by
  have h := external_uses_one_edge_of_A G M cfg T hT
  cases h with
  | cycle h => left; exact h
  | private_vDA_a h => right; left; exact h
  | private_vAB_a h => right; right; exact h

end TuzaNu4
