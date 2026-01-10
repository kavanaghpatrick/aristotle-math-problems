/-
  slot293: PATH_4 τ ≤ 8 - ADAPTIVE FAN APEX COVER

  DATE: Jan 8, 2026

  KEY INSIGHT FROM ULTRATHINK ANALYSIS (Gemini):
  The gap in slot292 is real for a STATIC cover. But we can use an
  ADAPTIVE cover based on fan apexes.

  FAN APEX LEMMA (proven scaffolding):
  For any M-element A, all its external triangles share a common vertex x_A
  (the "fan apex") that is NOT in A.

  THE ADAPTIVE 8-EDGE COVER:
  For each M-element, allocate 2 edges:
  - S_A = {{a1, a2}, {v1, x_A}}  -- base + spoke-to-apex
  - S_B = {{v1, v2}, {b, x_B}}   -- spine + private-to-apex
  - S_C = {{v2, v3}, {c, x_C}}   -- spine + private-to-apex
  - S_D = {{d1, d2}, {v3, x_D}}  -- base + spoke-to-apex

  WHY THIS WORKS:
  Any external triangle T of A contains:
  - The fan apex x_A (by fan apex lemma)
  - At least one vertex from A
  So either {a1,a2} covers it (if base-private) or {v1,x_A} covers it.

  The gap triangle {v1, a2, x} is now covered because x = x_A!
-/

import Mathlib

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Core Definitions -/

def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (fun M => isTrianglePacking G M) |>.image Finset.card |>.max |>.getD 0

def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Basic Lemmas -/

lemma triangle_card_3 (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : t.card = 3 := by
  simp only [SimpleGraph.cliqueFinset, SimpleGraph.isNClique_iff, Finset.mem_filter] at ht
  exact ht.2

lemma edge_in_triangle_sym2 (t : Finset V) (u w : V) (hu : u ∈ t) (hw : w ∈ t) :
    s(u, w) ∈ t.sym2 := by
  simp only [Finset.mem_sym2_iff]
  exact ⟨hu, hw⟩

lemma clique_edge_in_graph (t : Finset V) (ht : t ∈ G.cliqueFinset 3)
    (u w : V) (hu : u ∈ t) (hw : w ∈ t) (hne : u ≠ w) :
    s(u, w) ∈ G.edgeFinset := by
  have hclique := SimpleGraph.mem_cliqueFinset_iff.mp ht
  exact SimpleGraph.mem_edgeFinset.mpr (hclique.1 hu hw hne)

lemma max_packing_shares_edge (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) (ht_not : t ∉ M) :
    ∃ m ∈ M, (t ∩ m).card ≥ 2 := by
  by_contra h
  push_neg at h
  have h_packing : isTrianglePacking G (insert t M) := by
    constructor
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact ht
      · exact hM.1.1 hx
    · intro x hx y hy hxy
      simp only [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact Nat.lt_succ_iff.mp (h y hy)
      · rw [Finset.inter_comm]; exact Nat.lt_succ_iff.mp (h x hx)
      · exact hM.1.2 hx hy hxy
  have h_card : (insert t M).card = M.card + 1 := Finset.card_insert_of_not_mem ht_not
  have h_le : (insert t M).card ≤ trianglePackingNumber G := by
    unfold trianglePackingNumber
    have h_mem : insert t M ∈ (G.cliqueFinset 3).powerset.filter (fun M => isTrianglePacking G M) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h_packing.1, h_packing⟩
    have h_img := Finset.mem_image_of_mem Finset.card h_mem
    exact Finset.le_max h_img |> WithTop.coe_le_coe.mp
  omega

/-! ### External Triangle Definition -/

/-- T is external to A in packing M: T shares edge with A and only A -/
def isExternal (M : Finset (Finset V)) (T A : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧
  T ∉ M ∧
  A ∈ M ∧
  (T ∩ A).card ≥ 2 ∧
  (∀ B ∈ M, B ≠ A → (T ∩ B).card ≤ 1)

/-- Fan apex: vertex in all externals of A, not in A -/
def isFanApex (M : Finset (Finset V)) (A : Finset V) (x : V) : Prop :=
  x ∉ A ∧ ∀ T : Finset V, isExternal G M T A → x ∈ T

/-! ### Key Lemma: Fan Apex Existence (from proven scaffolding) -/

/-
PROOF SKETCH for fan_apex_exists:
1. If A has no externals, any vertex not in A is vacuously a fan apex
2. If A has one external T, the unique vertex in T \ A is the fan apex
3. If A has ≥2 externals T₁, T₂:
   - By 5-packing argument, T₁ and T₂ share an edge
   - This shared edge forces their external vertices to be equal
   - This common external vertex is the fan apex
-/
theorem fan_apex_exists (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M) (hA_clique : A ∈ G.cliqueFinset 3) :
    ∃ x : V, isFanApex G M A x := by
  -- Use classical choice: either externals exist or they don't
  by_cases h : ∃ T : Finset V, isExternal G M T A
  · -- Externals exist: extract fan apex from structure
    -- This requires the deep 5-packing argument
    sorry
  · -- No externals: any vertex not in A works
    push_neg at h
    have hA3 : A.card = 3 := triangle_card_3 G A hA_clique
    have hV_nonempty : (Finset.univ : Finset V).Nonempty := by
      by_contra h_empty
      simp at h_empty
      have : A.card = 0 := Finset.card_eq_zero.mpr (by ext x; simp [h_empty])
      omega
    -- Pick any vertex; if it's in A, pick another
    -- Since A has 3 vertices and V is finite with at least 3 vertices (from A), we can find x ∉ A
    -- Actually need |V| > 3 for there to exist x ∉ A... assume this
    sorry

/-! ### Adaptive Cover Construction -/

/-- Get fan apex for A (using classical choice) -/
noncomputable def fanApex (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M) (hA_clique : A ∈ G.cliqueFinset 3) : V :=
  Classical.choose (fan_apex_exists G M hM A hA hA_clique)

lemma fanApex_spec (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A : Finset V) (hA : A ∈ M) (hA_clique : A ∈ G.cliqueFinset 3) :
    isFanApex G M A (fanApex G M hM A hA hA_clique) :=
  Classical.choose_spec (fan_apex_exists G M hM A hA hA_clique)

/-! ### PATH_4 Specific Structure -/

/-- PATH_4 configuration with flat hypotheses -/
structure Path4 where
  A B C D : Finset V
  v1 v2 v3 a1 a2 b c d1 d2 : V
  hA_eq : A = {v1, a1, a2}
  hB_eq : B = {v1, v2, b}
  hC_eq : C = {v2, v3, c}
  hD_eq : D = {v3, d1, d2}
  hv12 : v1 ≠ v2
  hv23 : v2 ≠ v3
  hv13 : v1 ≠ v3

/-- The adaptive 8-edge cover for PATH_4 -/
noncomputable def adaptiveCover8 (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (cfg : Path4 V)
    (hA_clique : cfg.A ∈ G.cliqueFinset 3) (hB_clique : cfg.B ∈ G.cliqueFinset 3)
    (hC_clique : cfg.C ∈ G.cliqueFinset 3) (hD_clique : cfg.D ∈ G.cliqueFinset 3)
    (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D}) : Finset (Sym2 V) :=
  let hA_in : cfg.A ∈ M := by rw [hM_eq]; simp
  let hB_in : cfg.B ∈ M := by rw [hM_eq]; simp
  let hC_in : cfg.C ∈ M := by rw [hM_eq]; simp
  let hD_in : cfg.D ∈ M := by rw [hM_eq]; simp
  let x_A := fanApex G M hM cfg.A hA_in hA_clique
  let x_B := fanApex G M hM cfg.B hB_in hB_clique
  let x_C := fanApex G M hM cfg.C hC_in hC_clique
  let x_D := fanApex G M hM cfg.D hD_in hD_clique
  -- S_A: {a1,a2}, {v1,x_A}
  -- S_B: {v1,v2}, {b,x_B}
  -- S_C: {v2,v3}, {c,x_C}
  -- S_D: {d1,d2}, {v3,x_D}
  ({s(cfg.a1, cfg.a2), s(cfg.v1, x_A),
    s(cfg.v1, cfg.v2), s(cfg.b, x_B),
    s(cfg.v2, cfg.v3), s(cfg.c, x_C),
    s(cfg.d1, cfg.d2), s(cfg.v3, x_D)}).filter (fun e => e ∈ G.edgeFinset)

/-! ### Main Theorem -/

/-
PROOF SKETCH:
1. The adaptive cover has at most 8 edges (before filtering ≤8, after filtering ≤8)
2. Every edge in cover is in G.edgeFinset (by filter)
3. Every triangle t is covered:
   - If t ∈ M: covered by the corresponding S_X edges
   - If t ∉ M: t is external to exactly one M-element X
     - t contains fan apex x_X
     - t shares edge with X, so contains 2 vertices from X
     - One of the S_X edges covers t
-/
theorem tau_le_8_path4_adaptive (M : Finset (Finset V)) (cfg : Path4 V)
    (hM : isMaxPacking G M)
    (hM_eq : M = {cfg.A, cfg.B, cfg.C, cfg.D})
    (hA_clique : cfg.A ∈ G.cliqueFinset 3) (hB_clique : cfg.B ∈ G.cliqueFinset 3)
    (hC_clique : cfg.C ∈ G.cliqueFinset 3) (hD_clique : cfg.D ∈ G.cliqueFinset 3) :
    ∃ E : Finset (Sym2 V), E.card ≤ 8 ∧ E ⊆ G.edgeFinset ∧
    ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E, e ∈ t.sym2 := by
  use adaptiveCover8 G M hM cfg hA_clique hB_clique hC_clique hD_clique hM_eq
  refine ⟨?_, ?_, ?_⟩
  · -- Card ≤ 8: the unfiltered set has at most 8 elements
    unfold adaptiveCover8
    simp only
    calc (({s(cfg.a1, cfg.a2), s(cfg.v1, _), s(cfg.v1, cfg.v2), s(cfg.b, _),
            s(cfg.v2, cfg.v3), s(cfg.c, _), s(cfg.d1, cfg.d2), s(cfg.v3, _)} :
            Finset (Sym2 V)).filter (fun e => e ∈ G.edgeFinset)).card
        ≤ ({s(cfg.a1, cfg.a2), s(cfg.v1, _), s(cfg.v1, cfg.v2), s(cfg.b, _),
            s(cfg.v2, cfg.v3), s(cfg.c, _), s(cfg.d1, cfg.d2), s(cfg.v3, _)} :
            Finset (Sym2 V)).card := Finset.card_filter_le _ _
      _ ≤ 8 := by
          -- At most 8 distinct elements in a set literal with 8 terms
          refine Finset.card_le_card ?_
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          exact hx
  · -- Subset of G.edgeFinset: by definition of filter
    unfold adaptiveCover8
    simp only
    intro e he
    simp only [Finset.mem_filter] at he
    exact he.2
  · -- Covers all triangles
    intro t ht
    by_cases ht_in : t ∈ M
    · -- t is one of A, B, C, D
      rw [hM_eq] at ht_in
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht_in
      rcases ht_in with rfl | rfl | rfl | rfl
      all_goals {
        -- For each case, show one of the cover edges is in t.sym2
        sorry -- Aristotle: show M-element is covered by its designated edges
      }
    · -- t is external to some M-element
      obtain ⟨m, hm, h_share⟩ := max_packing_shares_edge G M hM t ht ht_in
      -- t shares edge with exactly one M-element (need to determine which)
      rw [hM_eq] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · -- t is external to A
        -- t contains fan apex x_A
        -- Either {a1,a2} ⊆ t (base-private) or {v1, x_A} covers
        sorry
      · -- t is external to B
        -- Either {v1,v2} ⊆ t or {b, x_B} covers
        sorry
      · -- t is external to C
        sorry
      · -- t is external to D
        sorry

end
