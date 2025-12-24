/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: db75d470-1424-4a23-bf9d-22467bc866fe
-/

/-
ITERATION 2 for Erdős #593 - 3-uniform hypergraph 2-colorability
Previous: 14271720-cb7a-4686-861f-5b0048d62d14

TRIVIAL FIX: Line 167 has exact? but the answer is IncidenceGraph_Bipartite H
(which is already proven at lines 82-94 of the same file!)

Fill line 167 with: exact IncidenceGraph_Bipartite H

Constraints:
- Do not modify theorem statements
- Replace exact? with exact IncidenceGraph_Bipartite H
-/

import Mathlib


set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

open Set Function

structure Hypergraph3 (V : Type*) where
  edges : Set (Set V)
  is_uniform : ∀ e ∈ edges, e.ncard = 3

def IsTwoColorable {V : Type*} (H : Hypergraph3 V) : Prop :=
  ∃ c : V → Bool, ∀ e ∈ H.edges, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

def IsColoring {V C : Type*} (H : Hypergraph3 V) (c : V → C) : Prop :=
  ∀ e ∈ H.edges, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

def EmbedsInto {V W : Type*} (H : Hypergraph3 V) (G : Hypergraph3 W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ e ∈ H.edges, (f '' e) ∈ G.edges

def HasChromaticNumberGtAleph0 {V : Type*} (G : Hypergraph3 V) : Prop :=
  ∀ (c : V → ℕ), ¬ IsColoring G c

def AppearsInAllUncountableChromatic {V : Type*} (H : Hypergraph3 V) : Prop :=
  Finite V ∧ ∀ (W : Type*) (G : Hypergraph3 W), HasChromaticNumberGtAleph0 G → EmbedsInto H G

def IsBergeCycle {V : Type*} (H : Hypergraph3 V) (k : ℕ) (v : ZMod k → V) (e : ZMod k → Set V) : Prop :=
  k ≥ 2 ∧
  Function.Injective v ∧
  Function.Injective e ∧
  (∀ i, e i ∈ H.edges) ∧
  (∀ i, v i ∈ e i) ∧
  (∀ i, v (i + 1) ∈ e i)

def IncidenceGraph {V : Type*} (H : Hypergraph3 V) : SimpleGraph (V ⊕ H.edges) where
  Adj u v :=
    match u, v with
    | Sum.inl x, Sum.inr e => x ∈ e.val
    | Sum.inr e, Sum.inl x => x ∈ e.val
    | _, _ => False
  symm := by
    intro u v h
    cases u <;> cases v <;> simp_all
  loopless := by
    intro u h
    cases u <;> simp_all

-- KEY LEMMA - already proven
lemma IncidenceGraph_Bipartite {V : Type*} (H : Hypergraph3 V) :
    (IncidenceGraph H).Colorable 2 := by
  let c : V ⊕ H.edges → Fin 2 := fun x => match x with
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  have h_valid : ∀ {u v : V ⊕ H.edges}, (IncidenceGraph H).Adj u v → c u ≠ c v := by
    intro u v h
    cases u <;> cases v
    · simp [IncidenceGraph] at h
    · simp [c]
    · simp [c]
    · simp [IncidenceGraph] at h
  exact ⟨SimpleGraph.Coloring.mk c h_valid⟩

lemma IncidenceGraph_NeighborSet_Card {V : Type*} (H : Hypergraph3 V) (e : H.edges) :
    ((IncidenceGraph H).neighborSet (Sum.inr e)).ncard = 3 := by
  bound
  have h_neighborSet : (IncidenceGraph H).neighborSet (Sum.inr ⟨val, property⟩) = Set.image (fun v => Sum.inl v) val := by
    ext; aesop
  rw [h_neighborSet, Set.ncard_image_of_injective _ fun x y => by aesop, H.is_uniform _ property]

lemma EmbedsInto_Transitive {U V W : Type*} (H1 : Hypergraph3 U) (H2 : Hypergraph3 V) (H3 : Hypergraph3 W) :
    EmbedsInto H1 H2 → EmbedsInto H2 H3 → EmbedsInto H1 H3 := by
  intro h1 h2
  obtain ⟨f, hf_inj, hf_edges⟩ := h1
  obtain ⟨g, hg_inj, hg_edges⟩ := h2
  use g ∘ f
  constructor
  · exact Function.Injective.comp hg_inj hf_inj
  · intro e he
    rw [Set.image_comp]
    apply hg_edges
    apply hf_edges
    exact he

def CompleteBipartiteGraph (n m : ℕ) : Hypergraph3 (Sum (Fin n) (Fin m)) :=
  { edges := { e | e.ncard = 3 ∧ (∃ x ∈ e, ∃ a, x = Sum.inl a) ∧ (∃ x ∈ e, ∃ b, x = Sum.inr b) },
    is_uniform := by intro e he; exact he.1 }

lemma EmbedsInto_CompleteBipartite_of_TwoColorable {V : Type*} [Finite V] (H : Hypergraph3 V) :
    IsTwoColorable H → ∃ (n m : ℕ), EmbedsInto H (CompleteBipartiteGraph n m) := by
  rintro ⟨c, hc⟩
  set n := Nat.card {v : V | c v = true}
  set m := Nat.card {v : V | c v = false}
  have h_partition : ∃ (f : V → Sum (Fin n) (Fin m)), Function.Injective f ∧ ∀ e ∈ H.edges, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y ∧ (f x).isLeft ∧ (f y).isRight := by
    have h_partition : ∃ (f : V → Sum (Fin n) (Fin m)), Function.Injective f ∧ ∀ v : V, (f v).isLeft = (c v = true) ∧ (f v).isRight = (c v = false) := by
      have h_partition : Nonempty ({v : V | c v = true} ≃ Fin n) ∧ Nonempty ({v : V | c v = false} ≃ Fin m) := by
        constructor
        · haveI := Fintype.ofFinite {v : V | c v = Bool.true}; exact ⟨Fintype.equivOfCardEq <| by simp +decide [n]⟩
        · have := Fintype.ofFinite {v : V | c v = Bool.false}
          exact ⟨Fintype.equivOfCardEq <| by aesop⟩
      obtain ⟨⟨f₁⟩, ⟨f₂⟩⟩ := h_partition
      refine' ⟨fun v => if hv : c v = Bool.true then Sum.inl (f₁ ⟨v, hv⟩) else Sum.inr (f₂ ⟨v, by simpa using hv⟩), _, _⟩ <;> intro v <;> aesop
    grind
  obtain ⟨f, hf₁, hf₂⟩ := h_partition
  refine' ⟨n, m, _, _⟩
  exact f
  refine' ⟨hf₁, fun e he => ⟨_, _, _⟩⟩
  · rw [Set.ncard_image_of_injective _ hf₁, H.is_uniform e he]
  · rcases hf₂ e he with ⟨x, hx, y, hy, hxy, hx', hy'⟩; use f x; aesop
    · use x
    · cases h : f x <;> aesop
  · obtain ⟨x, hx, y, hy, hxy, hx', hy'⟩ := hf₂ e he; use f y; aesop
    · exact ⟨y, hy, rfl⟩
    · cases h : f y <;> aesop

-- THE FIX: Use the already-proven IncidenceGraph_Bipartite lemma
lemma IncidenceGraph_No_Odd_Cycles {V : Type*} (H : Hypergraph3 V) :
    ∀ (u : V ⊕ H.edges) (p : (IncidenceGraph H).Walk u u), p.IsCycle → Even p.length := by
  have h_bipartite : (IncidenceGraph H).Colorable 2 := by
    exact IncidenceGraph_Bipartite H  -- THIS IS THE FIX!
  obtain ⟨f, hf⟩ := h_bipartite
  intros u p hp_cycle
  have h_alternating : ∀ (i : ℕ), i < p.length → f (p.getVert i) ≠ f (p.getVert (i + 1)) := by
    intro i hi
    exact hf (p.adj_getVert_succ hi)
  have h_even_length : ∀ (i : ℕ), i ≤ p.length → f (p.getVert i) = if Even i then f (p.getVert 0) else 1 - f (p.getVert 0) := by
    intro i hi
    induction' i with i ih
    · simp +decide
    · grind +ring
  specialize h_even_length p.length; aesop
  · grind
  · grind

lemma Exists_Cycle_Starting_At_Vertex {V : Type*} (H : Hypergraph3 V) :
    (∃ (u : V ⊕ H.edges) (p : (IncidenceGraph H).Walk u u), p.IsCycle) →
    ∃ (v : V) (p : (IncidenceGraph H).Walk (Sum.inl v) (Sum.inl v)), p.IsCycle := by
  rintro ⟨u, p, hp⟩
  obtain ⟨v, hv⟩ : ∃ v : V, Sum.inl v ∈ p.support := by
    rcases p with (_ | ⟨_, _, p⟩) <;> aesop
    · cases h
    · cases h
  refine' ⟨v, _⟩
  exact ⟨p.rotate hv, hp.rotate _⟩

lemma IncidenceGraph_Walk_Parity {V : Type*} (H : Hypergraph3 V) {u v : V ⊕ H.edges}
    (p : (IncidenceGraph H).Walk u v) (k : ℕ) (hk : k ≤ p.length) :
    (p.getVert k).isLeft ↔ (Even k ↔ u.isLeft) := by
  induction' p with u v p ih generalizing k
  · aesop
  · rcases k with (_ | k) <;> simp_all +decide [SimpleGraph.Walk.getVert]
    cases v <;> cases p <;> simp_all +decide [Nat.even_add_one]
    · tauto
    · exact absurd ‹_› (by rintro ⟨⟩)

lemma IncidenceGraph_Adj_Parity {V : Type*} (H : Hypergraph3 V) {u v : V ⊕ H.edges}
    (h : (IncidenceGraph H).Adj u v) : u.isLeft ≠ v.isLeft := by
  cases u <;> cases v <;> tauto

end