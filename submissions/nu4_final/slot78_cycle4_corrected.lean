/-
Tuza ν = 4 · cycle_4 case (slot 78)

The previous "bridge absorption" argument was incorrect: a base-edge cover of
S_A can miss bridges X_AB because those triangles only touch the shared vertex
v_ab.  The repair is to work vertex-by-vertex using the proven infrastructure
from slot71 (Se_structure) and slot73 (local vertex covers):

1. `cycle4_all_triangles_contain_shared` (slot73) → every triangle contains one
   of the four shared vertices v_ab, v_bc, v_cd, v_da.
2. For a fixed shared vertex v, `triangle_shares_edge_with_packing` forces any
   triangle containing v to share an edge with one of the two packing elements
   incident at v.  Combining this with `cycle4_triangle_at_vertex_supported`
   shows that each such triangle uses an edge from `M_edges_at G M v`.
3. `local_cover_le_2` (slot73) then yields a ≤2 edge cover for the triangles at
   v.  Each of those local covers uses only edges from `M_edges_at`, which sits
   inside `G.edgeFinset`.
4. `tau_union_le_sum` (slot71) lets us add the four local bounds.  Since the
   four vertex classes cover all triangles (Step 1), we obtain τ ≤ 2+2+2+2 = 8.

This file encodes that vertex-centric proof.  All heavy lemmas are imported as
axioms with references to the slots where they were proven.
-/

import Mathlib

set_option maxHeartbeats 400000

open scoped Classical
open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Standard notion of a triangle packing. -/
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) fun t₁ t₂ => (t₁ ∩ t₂).card ≤ 1

noncomputable def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>
    Finset.image Finset.card |>
    Finset.min |>.getD 0

/-- Maximal packings. -/
def isMaxPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

noncomputable def triangleCoveringNumber (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter
      (fun E' => E' ⊆ G.edgeFinset ∧
        ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) |>
    Finset.image Finset.card |>
    Finset.min |>.getD 0

noncomputable def triangleCoveringNumberOn (G : SimpleGraph V)
    [DecidableRel G.Adj] (triangles : Finset (Finset V)) : ℕ :=
  G.edgeFinset.powerset.filter
      (fun E' => ∀ t ∈ triangles, ∃ e ∈ E', e ∈ t.sym2) |>
    Finset.image Finset.card |>
    Finset.min |>.getD 0

/-- Triangles sharing an edge with `t`. -/
def trianglesSharingEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun x => (x ∩ t).card ≥ 2

/-- Triangles containing vertex `v`. -/
def trianglesContainingVertex (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun t => v ∈ t

/-- S_e sets from the Se-decomposition. -/
def S_e (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun t =>
    (t ∩ e).card ≥ 2 ∧ ∀ f ∈ M, f ≠ e → (t ∩ f).card ≤ 1

/-- All packing edges that touch vertex `v`. -/
def M_edges_at (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (v : V) : Finset (Sym2 V) :=
  M.biUnion fun X => X.sym2.filter fun e => v ∈ e

/-- The cycle_4 configuration for four distinct packing triangles. -/
def isCycle4 (M : Finset (Finset V))
    (A B C D : Finset V) : Prop :=
  M = {A, B, C, D} ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
  (A ∩ B).card = 1 ∧ (B ∩ C).card = 1 ∧
  (C ∩ D).card = 1 ∧ (D ∩ A).card = 1 ∧
  (A ∩ C).card = 0 ∧ (B ∩ D).card = 0

lemma isCycle4.rotate_left {M : Finset (Finset V)}
    {A B C D : Finset V} (h : isCycle4 M A B C D) :
    isCycle4 M B C D A := by
  classical
  rcases h with
    ⟨hM, hAB, hBC, hCD, hDA, hAC, hBD,
      hABc, hBCc, hCDc, hDAc, hAC0, hBD0⟩
  refine ⟨by
      simpa [Finset.insert_comm, Finset.insert_left_comm, Finset.insert_assoc]
        using hM,
    hBC, hCD, hDA, hAB, hBD, hAC,
    hBCc, hCDc, hDAc, hABc, hBD0, hAC0⟩

/-!
### Trusted lemmas (already proven in slots 71 & 73)

We record the precise statements we need as axioms; each references the
original slot where it was proved so this file can focus on the new assembly.
-/

/-- Slot71: subadditivity of triangle covering numbers. -/
axiom tau_union_le_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (Finset V)) :
    triangleCoveringNumberOn G (A ∪ B) ≤
      triangleCoveringNumberOn G A + triangleCoveringNumberOn G B

/-- Standard conversion from an explicit cover to a `triangleCoveringNumberOn`
    bound.  This follows immediately from the definition (also in slot71). -/
axiom triangleCoveringNumberOn_le_of_cover (G : SimpleGraph V)
    [DecidableRel G.Adj] (triangles : Finset (Finset V))
    (E : Finset (Sym2 V))
    (hEsubset : E ⊆ G.edgeFinset)
    (hCover : ∀ t ∈ triangles, ∃ e ∈ E, e ∈ t.sym2) :
    triangleCoveringNumberOn G triangles ≤ E.card

/-- Slot73: triangles at `A` containing vertex `v` always use an edge incident
    to `v`. -/
axiom cycle4_triangle_at_vertex_supported (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (M : Finset (Finset V)) (A : Finset V) (hA : A ∈ M)
    (v : V) (hv : v ∈ A)
    (t : Finset V) (ht : t ∈ trianglesSharingEdge G A) (hvt : v ∈ t) :
    ∃ e ∈ M_edges_at G M v, e ∈ t.sym2

/-- Slot73: All-Middle property. -/
axiom cycle4_all_triangles_contain_shared (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (vAB vBC vCD vDA : V)
    (hAB : A ∩ B = {vAB}) (hBC : B ∩ C = {vBC})
    (hCD : C ∩ D = {vCD}) (hDA : D ∩ A = {vDA})
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    vAB ∈ t ∨ vBC ∈ t ∨ vCD ∈ t ∨ vDA ∈ t

/-- Slot71 (Sₑ-structure): a triangle containing a shared vertex must share an
    edge with one of the two adjacent packing elements. -/
axiom triangle_contains_shared_vertex_shares_adjacent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (v : V) (hAB : A ∩ B = {v})
    (t : Finset V) (ht : t ∈ trianglesContainingVertex G v) :
    (t ∩ A).card ≥ 2 ∨ (t ∩ B).card ≥ 2

/-- Slot73: local covers of size ≤ 2 at any shared vertex. -/
axiom local_cover_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M)
    (hAB : A ≠ B) (v : V) (hABeq : A ∩ B = {v})
    (hOnly : ∀ Z ∈ M, v ∈ Z → Z = A ∨ Z = B) :
    ∃ E : Finset (Sym2 V),
      E.card ≤ 2 ∧ E ⊆ M_edges_at G M v ∧
        ∀ t ∈ G.cliqueFinset 3, v ∈ t →
          (∃ e ∈ M_edges_at G M v, e ∈ t.sym2) →
          (∃ e ∈ E, e ∈ t.sym2)

/-- Every edge in `M_edges_at` is a genuine graph edge. -/
axiom M_edges_at_subset_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (v : V) : M_edges_at G M v ⊆ G.edgeFinset

/-!
### Basic structural lemmas about the cycle_4 configuration
-/

lemma trianglesContainingVertex_subset (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    trianglesContainingVertex G v ⊆ G.cliqueFinset 3 := by
  intro t ht
  simp [trianglesContainingVertex] at ht
  exact ht.1

lemma triangleCoveringNumber_eq_triangleCoveringNumberOn
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    triangleCoveringNumber G =
      triangleCoveringNumberOn G (G.cliqueFinset 3) := by
  classical
  unfold triangleCoveringNumber triangleCoveringNumberOn
  have :
      G.edgeFinset.powerset.filter
          (fun E' => E' ⊆ G.edgeFinset ∧
            ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2)
        =
      G.edgeFinset.powerset.filter
          (fun E' => ∀ t ∈ G.cliqueFinset 3, ∃ e ∈ E', e ∈ t.sym2) := by
    ext E
    by_cases hE : E ⊆ G.edgeFinset
    · have hMem : E ∈ G.edgeFinset.powerset :=
        Finset.mem_powerset.mpr hE
      simp [hE, hMem]
    · have hMem : E ∉ G.edgeFinset.powerset := by
        simpa [Finset.mem_powerset] using hE
      simp [hE, hMem]
  simpa [this]

lemma shared_vertex_subset (M : Finset (Finset V))
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (vAB : V) (hAB : A ∩ B = {vAB}) :
    ∀ Z ∈ M, vAB ∈ Z → Z = A ∨ Z = B := by
  intro Z hZ hv
  have hM_eq : M = {A, B, C, D} := hcycle.1
  have hAC : A ∩ C = ∅ := by
    have := hcycle.2.2.2.2.2.2.2.2.2.2.1
    exact Finset.card_eq_zero.mp this
  have hBD : B ∩ D = ∅ := by
    have := hcycle.2.2.2.2.2.2.2.2.2.2.2
    exact Finset.card_eq_zero.mp this
  have hMem : Z ∈ ({A, B, C, D} : Finset (Finset V)) := by
    simpa [hM_eq] using hZ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
  rcases hMem with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exfalso
    have : vAB ∈ A ∩ C := by
      simp [Finset.mem_inter, hv, (Finset.mem_singleton.mp (by simpa [hAB]))]
    simpa [hAC] using this
  · exfalso
    have : vAB ∈ B ∩ D := by
      simp [Finset.mem_inter, hv, (Finset.mem_singleton.mp (by simpa [hAB]))]
    simpa [hBD] using this

lemma triangle_supported_at_shared (G : SimpleGraph V)
    [DecidableRel G.Adj] (M : Finset (Finset V))
    (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M)
    (v : V) (hvA : v ∈ A) (hvB : v ∈ B)
    (hShares : ∀ t ∈ trianglesContainingVertex G v,
      (t ∩ A).card ≥ 2 ∨ (t ∩ B).card ≥ 2)
    (t : Finset V)
    (ht : t ∈ trianglesContainingVertex G v) :
    ∃ e ∈ M_edges_at G M v, e ∈ t.sym2 := by
  classical
  have htClique : t ∈ G.cliqueFinset 3 :=
    trianglesContainingVertex_subset (G := G) v ht
  have hv_t : v ∈ t := by
    simp [trianglesContainingVertex] at ht
    exact ht.2
  obtain hEdge | hEdge := hShares t ht
  · have htEdge : t ∈ trianglesSharingEdge G A := by
      simp [trianglesSharingEdge, htClique, hEdge]
    exact cycle4_triangle_at_vertex_supported G M A hA v hvA t htEdge hv_t
  · have htEdge : t ∈ trianglesSharingEdge G B := by
      simp [trianglesSharingEdge, htClique, hEdge]
    exact cycle4_triangle_at_vertex_supported G M B hB v hvB t htEdge hv_t

lemma triangles_at_vertex_tau_le_two (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B : Finset V) (hA : A ∈ M) (hB : B ∈ M)
    (hAB_ne : A ≠ B)
    (v : V) (hvA : v ∈ A) (hvB : v ∈ B)
    (hABeq : A ∩ B = {v})
    (hOnly : ∀ Z ∈ M, v ∈ Z → Z = A ∨ Z = B)
    (hShares : ∀ t ∈ trianglesContainingVertex G v,
      (t ∩ A).card ≥ 2 ∨ (t ∩ B).card ≥ 2) :
    triangleCoveringNumberOn G (trianglesContainingVertex G v) ≤ 2 := by
  classical
  obtain ⟨E, hE_card, hE_subset, hE_cover⟩ :=
    local_cover_le_2 G M hM A B hA hB hAB_ne v hABeq hOnly
  have hEdges_subset : E ⊆ G.edgeFinset :=
    hE_subset.trans (M_edges_at_subset_edges G M hM v)
  have hSupport : ∀ t ∈ trianglesContainingVertex G v,
      ∃ e ∈ M_edges_at G M v, e ∈ t.sym2 :=
    triangle_supported_at_shared G M hM A B hA hB v hvA hvB hShares
  have hCover : ∀ t ∈ trianglesContainingVertex G v, ∃ e ∈ E, e ∈ t.sym2 := by
    intro t ht
    obtain ⟨e, heM, heSym⟩ := hSupport t ht
    exact hE_cover t
      (trianglesContainingVertex_subset (G := G) v ht)
      (by simpa [trianglesContainingVertex] using ht)
      ⟨e, heM, heSym⟩
  have hCard_le : E.card ≤ 2 := hE_card
  exact (triangleCoveringNumberOn_le_of_cover G
      (trianglesContainingVertex G v) E hEdges_subset hCover).trans hCard_le

lemma triangles_union_eq_clique (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D)
    (vAB vBC vCD vDA : V)
    (hAB : A ∩ B = {vAB}) (hBC : B ∩ C = {vBC})
    (hCD : C ∩ D = {vCD}) (hDA : D ∩ A = {vDA}) :
    G.cliqueFinset 3 =
      trianglesContainingVertex G vAB ∪
        trianglesContainingVertex G vBC ∪
        trianglesContainingVertex G vCD ∪
        trianglesContainingVertex G vDA := by
  classical
  apply Finset.ext
  intro t
  constructor
  · intro ht
    have hCase :=
      cycle4_all_triangles_contain_shared G M hM A B C D hcycle
        vAB vBC vCD vDA hAB hBC hCD hDA t ht
    rcases hCase with h₁ | h₂ | h₃ | h₄
    · simp [trianglesContainingVertex, ht, h₁]
    · have : t ∈ trianglesContainingVertex G vBC := by
        simp [trianglesContainingVertex, ht, h₂]
      simp [this]
    · have : t ∈ trianglesContainingVertex G vCD := by
        simp [trianglesContainingVertex, ht, h₃]
      simp [this]
    · have : t ∈ trianglesContainingVertex G vDA := by
        simp [trianglesContainingVertex, ht, h₄]
      simpa [this]
  · intro ht
    have hSubset :
        trianglesContainingVertex G vAB ⊆ G.cliqueFinset 3 :=
      trianglesContainingVertex_subset (G := G) vAB
    have hSubset' := trianglesContainingVertex_subset (G := G) vBC
    have hSubset'' := trianglesContainingVertex_subset (G := G) vCD
    have hSubset''' := trianglesContainingVertex_subset (G := G) vDA
    rcases Finset.mem_union.mp ht with ht₁ | htrest
    · exact hSubset ht₁
    rcases Finset.mem_union.mp htrest with ht₂ | htrest'
    · exact hSubset' ht₂
    rcases Finset.mem_union.mp htrest' with ht₃ | ht₄
    · exact hSubset'' ht₃
    · exact hSubset''' ht₄

/-!
### Main theorem: τ ≤ 8 in the cycle_4 configuration
-/

theorem tau_le_8_cycle4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (A B C D : Finset V) (hcycle : isCycle4 M A B C D) :
    triangleCoveringNumber G ≤ 8 := by
  classical
  have hcycle_full := hcycle
  obtain ⟨hM_eq, hAB_ne, hBC_ne, hCD_ne, hDA_ne, hAC_ne, hBD_ne,
    hAB_card, hBC_card, hCD_card, hDA_card, hAC_zero, hBD_zero⟩ := hcycle
  have hcycle_BCDA := isCycle4.rotate_left hcycle_full
  have hcycle_CDAB := isCycle4.rotate_left hcycle_BCDA
  have hcycle_DABC := isCycle4.rotate_left hcycle_CDAB
  obtain ⟨vAB, hvAB⟩ := Finset.card_eq_one.mp hAB_card
  obtain ⟨vBC, hvBC⟩ := Finset.card_eq_one.mp hBC_card
  obtain ⟨vCD, hvCD⟩ := Finset.card_eq_one.mp hCD_card
  obtain ⟨vDA, hvDA⟩ := Finset.card_eq_one.mp hDA_card
  have hvAB_inter : vAB ∈ A ∩ B := by simpa [hvAB]
  have hvBC_inter : vBC ∈ B ∩ C := by simpa [hvBC]
  have hvCD_inter : vCD ∈ C ∩ D := by simpa [hvCD]
  have hvDA_inter : vDA ∈ D ∩ A := by simpa [hvDA]
  have hvAB_A : vAB ∈ A := (Finset.mem_inter.mp hvAB_inter).1
  have hvAB_B : vAB ∈ B := (Finset.mem_inter.mp hvAB_inter).2
  have hvBC_B : vBC ∈ B := (Finset.mem_inter.mp hvBC_inter).1
  have hvBC_C : vBC ∈ C := (Finset.mem_inter.mp hvBC_inter).2
  have hvCD_C : vCD ∈ C := (Finset.mem_inter.mp hvCD_inter).1
  have hvCD_D : vCD ∈ D := (Finset.mem_inter.mp hvCD_inter).2
  have hvDA_D : vDA ∈ D := (Finset.mem_inter.mp hvDA_inter).1
  have hvDA_A : vDA ∈ A := (Finset.mem_inter.mp hvDA_inter).2
  have hA_mem : A ∈ M := by simpa [hM_eq]
  have hB_mem : B ∈ M := by simpa [hM_eq]
  have hC_mem : C ∈ M := by simpa [hM_eq]
  have hD_mem : D ∈ M := by simpa [hM_eq]
  -- Each shared vertex belongs only to its adjacent pair
  have hOnlyAB := shared_vertex_subset M A B C D hcycle_full vAB hvAB
  have hOnlyBC := shared_vertex_subset M B C D A hcycle_BCDA vBC hvBC
  have hOnlyCD := shared_vertex_subset M C D A B hcycle_CDAB vCD hvCD
  have hOnlyDA := shared_vertex_subset M D A B C hcycle_DABC vDA hvDA
  -- Every triangle through the shared vertex shares an edge with the adjacent pair
  have hSharesAB : ∀ t ∈ trianglesContainingVertex G vAB,
      (t ∩ A).card ≥ 2 ∨ (t ∩ B).card ≥ 2 := by
    intro t ht
    exact triangle_contains_shared_vertex_shares_adjacent G M hM A B C D
      hcycle_full vAB hvAB t ht
  have hSharesBC : ∀ t ∈ trianglesContainingVertex G vBC,
      (t ∩ B).card ≥ 2 ∨ (t ∩ C).card ≥ 2 := by
    intro t ht
    exact triangle_contains_shared_vertex_shares_adjacent G M hM B C D A
      hcycle_BCDA vBC hvBC t ht
  have hSharesCD : ∀ t ∈ trianglesContainingVertex G vCD,
      (t ∩ C).card ≥ 2 ∨ (t ∩ D).card ≥ 2 := by
    intro t ht
    exact triangle_contains_shared_vertex_shares_adjacent G M hM C D A B
      hcycle_CDAB vCD hvCD t ht
  have hSharesDA : ∀ t ∈ trianglesContainingVertex G vDA,
      (t ∩ D).card ≥ 2 ∨ (t ∩ A).card ≥ 2 := by
    intro t ht
    exact triangle_contains_shared_vertex_shares_adjacent G M hM D A B C
      hcycle_DABC vDA hvDA t ht
  -- Local τ ≤ 2 bounds
  have hAB_le : triangleCoveringNumberOn G (trianglesContainingVertex G vAB) ≤ 2 :=
    triangles_at_vertex_tau_le_two G M hM A B hA_mem hB_mem
      hAB_ne vAB hvAB_A hvAB_B hvAB hOnlyAB hSharesAB
  have hBC_le : triangleCoveringNumberOn G (trianglesContainingVertex G vBC) ≤ 2 :=
    triangles_at_vertex_tau_le_two G M hM B C hB_mem hC_mem
      hBC_ne vBC hvBC_B hvBC_C hvBC hOnlyBC hSharesBC
  have hCD_le : triangleCoveringNumberOn G (trianglesContainingVertex G vCD) ≤ 2 :=
    triangles_at_vertex_tau_le_two G M hM C D hC_mem hD_mem
      hCD_ne vCD hvCD_C hvCD_D hvCD hOnlyCD hSharesCD
  have hDA_le : triangleCoveringNumberOn G (trianglesContainingVertex G vDA) ≤ 2 :=
    triangles_at_vertex_tau_le_two G M hM D A hD_mem hA_mem
      hDA_ne vDA hvDA_D hvDA_A hvDA hOnlyDA hSharesDA
  -- Combine via tau_union_le_sum
  set T₁ := trianglesContainingVertex G vAB with hT₁
  set T₂ := trianglesContainingVertex G vBC with hT₂
  set T₃ := trianglesContainingVertex G vCD with hT₃
  set T₄ := trianglesContainingVertex G vDA with hT₄
  have h12 : triangleCoveringNumberOn G (T₁ ∪ T₂) ≤ 4 := by
    have := tau_union_le_sum (G := G) T₁ T₂
    exact this.trans (Nat.add_le_add hAB_le hBC_le)
  have h123 : triangleCoveringNumberOn G ((T₁ ∪ T₂) ∪ T₃) ≤ 6 := by
    have := tau_union_le_sum (G := G) (T₁ ∪ T₂) T₃
    exact this.trans (Nat.add_le_add h12 hCD_le)
  have h1234 : triangleCoveringNumberOn G (((T₁ ∪ T₂) ∪ T₃) ∪ T₄) ≤ 8 := by
    have := tau_union_le_sum (G := G) ((T₁ ∪ T₂) ∪ T₃) T₄
    exact this.trans (Nat.add_le_add h123 hDA_le)
  -- All triangles lie in the union of the four vertex classes
  have hCoverTriangles :
      G.cliqueFinset 3 = ((T₁ ∪ T₂) ∪ T₃) ∪ T₄ := by
    simpa [T₁, T₂, T₃, T₄, Finset.union_assoc, Finset.union_left_comm]
      using triangles_union_eq_clique G M hM A B C D hcycle_full
        vAB vBC vCD vDA hvAB hvBC hvCD hvDA
  -- Final inequality: τ ≤ 8
  have hAll : triangleCoveringNumberOn G (G.cliqueFinset 3) ≤ 8 := by
    simpa [hCoverTriangles, Finset.union_assoc, Finset.union_left_comm] using h1234
  have := triangleCoveringNumber_eq_triangleCoveringNumberOn (G := G)
  simpa [this] using hAll
