# Tuza Conjecture: Complete Lemma Database

**Last Updated**: December 21, 2025 (Added ν=4 building blocks from b0891cdd)
**Purpose**: All proven lemmas + key literature lemmas in one place for Aristotle context

---

## PART 1: OUR PROVEN LEMMAS (Aristotle-Verified)

### Definitions (Common to All Proofs)

```lean
-- Edge-disjoint triangle packing
def isTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) : Prop :=
  S ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (S : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

-- Maximum packing size
def trianglePackingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).powerset.filter (isTrianglePacking G) |>.image Finset.card |>.max |>.getD 0

-- Minimum edge cover size
def triangleCoveringNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.powerset.filter (isTriangleCover G) |>.image Finset.card |>.min |>.getD 0

-- T_e: triangles sharing edge with e
def trianglesSharingEdge (G : SimpleGraph V) (t : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun x => (x ∩ t).card ≥ 2)

-- S_e: triangles sharing edge ONLY with e (not other packing elements)
def S (G : SimpleGraph V) (t : Finset V) (M : Finset (Finset V)) : Finset (Finset V) :=
  (trianglesSharingEdge G t).filter (fun x => ∀ m ∈ M, m ≠ t → (x ∩ m).card ≤ 1)

-- Maximum packing
def isMaxPacking (G : SimpleGraph V) (M : Finset (Finset V)) : Prop :=
  isTrianglePacking G M ∧ M.card = trianglePackingNumber G

-- Two triangles share an edge
def shareEdge (t1 t2 : Finset V) : Prop := (t1 ∩ t2).card ≥ 2

-- Star structure (all triangles share common edge)
def isStar (S : Finset (Finset V)) : Prop :=
  ∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ S, e ⊆ t

-- K4 structure (all triangles in 4 vertices)
def isK4 (S : Finset (Finset V)) : Prop :=
  ∃ s : Finset V, s.card = 4 ∧ ∀ t ∈ S, t ⊆ s
```

---

### Core Parker Lemmas ✅ PROVEN

#### Lemma 2.2: S_e Pairwise Sharing
**Statement**: All triangles in S_e pairwise share edges
```lean
lemma lemma_2_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    ∀ t1 t2, t1 ∈ S G e M → t2 ∈ S G e M → shareEdge t1 t2
```
**Status**: ✅ PROVEN (UUID: 181fa406)
**Proof Technique**: Maximality contradiction - if t1, t2 don't share edge, M' = (M \ {e}) ∪ {t1, t2} is larger packing

---

#### Lemma 2.3: Packing Reduction
**Statement**: ν(G \ T_e) = ν(G) - 1
```lean
lemma lemma_2_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    trianglePackingNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e)) = trianglePackingNumber G - 1
```
**Status**: ✅ PROVEN (UUID: 181fa406)
**Proof Technique**: M \ {e} is valid packing in residual

---

#### Inductive Bound
**Statement**: τ(G) ≤ τ(T_e) + τ(G \ T_e)
```lean
lemma inductive_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumber G ≤ triangleCoveringNumberOn G (trianglesSharingEdge G e) +
                               triangleCoveringNumberOn G ((G.cliqueFinset 3) \ (trianglesSharingEdge G e))
```
**Status**: ✅ PROVEN (UUID: 181fa406)
**Proof Technique**: Union of covers for T_e and complement covers all

---

#### K4 Cover Bound
**Statement**: Triangles on ≤4 vertices have τ ≤ 2
```lean
lemma covering_number_le_two_of_subset_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (hU : U.card ≤ 4)
    (h_subset : ∀ t ∈ G.cliqueFinset 3, t ⊆ U) :
    triangleCoveringNumber G ≤ 2
```
**Status**: ✅ PROVEN (UUID: 181fa406)
**Proof Technique**: Case analysis on 0-4 vertices, explicit edge selection

---

#### Intersecting Family Structure
**Statement**: Pairwise intersecting triangles → star OR K4
```lean
lemma intersecting_family_structure_corrected (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS_nonempty : S.Nonempty) (hS : S ⊆ G.cliqueFinset 3)
    (h_pair : Set.Pairwise (S : Set (Finset V)) shareEdge) :
    isStar S ∨ isK4 S
```
**Status**: ✅ PROVEN (UUID: 181fa406)
**Proof Technique**: If 3 triangles don't share common edge, union has 4 vertices

---

#### Tau Star Bound
**Statement**: Star structure → τ ≤ 1
```lean
lemma tau_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hS : S ⊆ G.cliqueFinset 3) (h_star : isStar S) :
    triangleCoveringNumberOn G S ≤ 1
```
**Status**: ✅ PROVEN (UUID: 181fa406)
**Proof Technique**: Common edge covers all triangles in star

---

#### Tau S_e ≤ 2
**Statement**: τ(S_e) ≤ 2 always
```lean
lemma tau_S_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M) (e : Finset V) (he : e ∈ M) :
    triangleCoveringNumberOn G (S G e M) ≤ 2
```
**Status**: ✅ PROVEN (UUID: 181fa406, b0891cdd)
**Proof Technique**: Combines intersecting_family_structure with tau_star and K4 bound

---

### ν=4 Building Blocks ✅ PROVEN (NEW - Dec 21)

#### X(e,f) Definition
**Statement**: Triangles sharing edges with BOTH e and f
```lean
def X (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Finset V) : Finset (Finset V) :=
  (trianglesSharingEdge G e) ∩ (trianglesSharingEdge G f)
```
**Status**: ✅ DEFINED (UUID: b0891cdd)

---

#### Triangles in X(e,f) Contain Shared Vertex
**Statement**: When e ∩ f = {v}, all triangles in X(e,f) contain v
```lean
lemma mem_X_implies_v_in_t (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (he : e.card = 3) (hf : f.card = 3) (h_inter : e ∩ f = {v}) :
    ∀ t ∈ X G e f, v ∈ t
```
**Status**: ✅ PROVEN (UUID: b0891cdd)
**Proof Technique**: Intersection constraint forces v membership

---

#### τ(X(e,f)) ≤ 2
**Statement**: Triangles sharing edges with both e and f can be covered by 2 edges
```lean
lemma tau_X_le_2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : Finset V) (v : V) (he : G.IsNClique 3 e) (hf : G.IsNClique 3 f) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (X G e f) ≤ 2
```
**Status**: ✅ PROVEN (UUID: b0891cdd)
**Proof Technique**: All X(e,f) triangles contain v; cover with 2 edges from e incident to v

---

#### Packing Minus Pair
**Statement**: Removing two packing elements preserves ν - 2 in residual
```lean
lemma packing_minus_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (T_ef : Finset (Finset V)) (hT : T_ef = trianglesSharingEdge G e ∪ trianglesSharingEdge G f) :
    trianglePackingNumber G - 2 ≥ 0 →
    ∃ M' : Finset (Finset V), isTrianglePacking G M' ∧
      M' ⊆ (G.cliqueFinset 3) \ T_ef ∧ M'.card ≥ M.card - 2
```
**Status**: ✅ PROVEN (UUID: b0891cdd)
**Proof Technique**: M \ {e, f} is valid packing in residual

---

### Structural Helper Lemmas ✅ PROVEN (NEW - Dec 21)

#### Three Intersecting Triples Structure
```lean
lemma three_intersecting_triples_structure
    (t1 t2 t3 : Finset V) (h1 : t1.card = 3) (h2 : t2.card = 3) (h3 : t3.card = 3)
    (h12 : (t1 ∩ t2).card ≥ 2) (h13 : (t1 ∩ t3).card ≥ 2) (h23 : (t2 ∩ t3).card ≥ 2) :
    (∃ e : Finset V, e.card = 2 ∧ e ⊆ t1 ∧ e ⊆ t2 ∧ e ⊆ t3) ∨ (t1 ∪ t2 ∪ t3).card ≤ 4
```
**Status**: ✅ PROVEN (UUID: b0891cdd)

---

#### Common Edge of Three Distinct
```lean
lemma common_edge_of_three_distinct
    (t1 t2 t3 t4 : Finset V) (h_distinct : t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3)
    (h_sz : t1.card = 3 ∧ t2.card = 3 ∧ t3.card = 3 ∧ t4.card = 3)
    (e : Finset V) (he : e.card = 2) (h_sub : e ⊆ t1 ∧ e ⊆ t2 ∧ e ⊆ t3)
    (h_inter : (t4 ∩ t1).card ≥ 2 ∧ (t4 ∩ t2).card ≥ 2 ∧ (t4 ∩ t3).card ≥ 2) :
    e ⊆ t4
```
**Status**: ✅ PROVEN (UUID: b0891cdd)

---

#### Intersecting Triples → Star OR K4
```lean
lemma intersecting_triples_structure (F : Finset (Finset V))
    (h3 : ∀ t ∈ F, t.card = 3)
    (h_pair : ∀ t1 t2, t1 ∈ F → t2 ∈ F → (t1 ∩ t2).card ≥ 2) :
    (∃ e : Finset V, e.card = 2 ∧ ∀ t ∈ F, e ⊆ t) ∨ (F.biUnion id).card ≤ 4
```
**Status**: ✅ PROVEN (UUID: b0891cdd)

---

#### K4 Cover Lemmas
```lean
lemma lemma_K4_cover_small (S : Finset (Finset V)) (h3 : ∀ t ∈ S, t.card = 3) (hS : S.card ≤ 2) :
    ∃ E' : Finset (Finset V), E'.card ≤ 2 ∧ (∀ e ∈ E', e.card = 2 ∧ ∃ t ∈ S, e ⊆ t) ∧ (∀ t ∈ S, ∃ e ∈ E', e ⊆ t)

lemma lemma_K4_cover (S : Finset (Finset V)) (h_union : (S.biUnion id).card ≤ 4) (h3 : ∀ t ∈ S, t.card = 3) :
    ∃ E' : Finset (Finset V), E'.card ≤ 2 ∧ (∀ e ∈ E', e.card = 2 ∧ ∃ t ∈ S, e ⊆ t) ∧ (∀ t ∈ S, ∃ e ∈ E', e ⊆ t)
```
**Status**: ✅ PROVEN (UUID: b0891cdd)

---

#### Structural Cover
```lean
lemma structural_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (S_tris : Finset (Finset V)) (h_sub : S_tris ⊆ G.cliqueFinset 3)
    (h_pair : ∀ t1 t2, t1 ∈ S_tris → t2 ∈ S_tris → shareEdge t1 t2) :
    triangleCoveringNumberOn G S_tris ≤ 2
```
**Status**: ✅ PROVEN (UUID: b0891cdd)

---

### Case-Specific Theorems ✅ PROVEN

#### ν = 0 Case
```lean
lemma tuza_case_nu_0 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 0) : triangleCoveringNumber G = 0
```
**Status**: ✅ PROVEN
**Proof**: No triangles → no cover needed

---

#### ν = 2 Case (Full Theorem)
```lean
theorem tuza_nu2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G = 2) : coveringNumber G ≤ 4
```
**Status**: ✅ PROVEN (UUID: 0764be78)
**Proof Technique**: Dichotomy on vertex-disjoint vs shared vertex packing

**Supporting lemmas proven**:
- `nu2_all_triangles_share_edge`: Every triangle shares edge with e or f
- `vertex_disjoint_share_exclusive`: Vertex-disjoint triangles can't share edges with both
- `cover_through_vertex`: If all T_e triangles contain v, τ(T_e) ≤ 2

---

#### ν = 3 Case
```lean
lemma tau_Te_le_2_nu_3 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 3)
    (e : Finset V) (he : e ∈ M) :
    coveringNumberOn G (T_e G e) ≤ 2
```
**Status**: ✅ PROVEN (UUID: 89bfa298)
**Proof Technique**: At ν=3, bridges can attach to at most 2 elements

---

### Counterexamples Found ❌ (Rule Out Strategies)

#### K4 Counterexample
**Disproves**: "Cover pairwise-intersecting with 2 edges FROM e"
```lean
-- e = {0,1,2}, t1 = {0,1,3}, t2 = {1,2,3}, t3 = {0,2,3}
-- Need ALL 3 edges of e to cover {t1, t2, t3} using edges from e
lemma counterexample_lemma : ∃ (V : Type) ...
    ¬(∃ E ⊆ triangleEdges e, E.card ≤ 2 ∧ ∀ t ∈ S, ¬Disjoint (triangleEdges t) E)
```
**Status**: ✅ PROVEN (UUID: 8fd9def6)
**Implication**: Can't assume 2 edges of base triangle suffice

---

#### Fan Counterexample
**Disproves**: "|S_e| ≤ 4" assumption
```lean
-- Fin 7 graph with 5 triangles in S_e sharing edge {0,1}
-- |S_e| = 5, not ≤ 4
```
**Status**: ✅ PROVEN (UUID: 87299718)
**Implication**: Can't bound S_e size, must use structural properties

---

## PART 2: KEY LITERATURE LEMMAS (To Formalize)

### From Krivelevich 1995 (Fractional)

#### Fractional Duality
```lean
-- NOT YET FORMALIZED
theorem fractional_duality (G : SimpleGraph V) [DecidableRel G.Adj] :
    fractionalCoveringNumber G = fractionalPackingNumber G
```
**Source**: Krivelevich 1995, LP duality
**Implication**: Tuza ⟺ integrality gap ≤ 2

#### K₃,₃-Free
```lean
-- NOT YET FORMALIZED
theorem tuza_K33_free (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ¬ ∃ S : Finset V, S.card = 6 ∧ G.induce S ≃g completeEquipartiteGraph 2 3) :
    coveringNumber G ≤ 2 * packingNumber G
```
**Source**: Krivelevich 1995

---

### From Haxell 1999 (General Bound)

#### 66/23 Bound
```lean
-- NOT YET FORMALIZED
theorem haxell_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    coveringNumber G ≤ (66 * packingNumber G) / 23
```
**Source**: Haxell 1999
**Note**: First nontrivial bound, ≈ 2.87ν

---

### From Treewidth Paper 2002.07925

#### Treewidth 6 Result
```lean
-- NOT YET FORMALIZED
theorem tuza_treewidth_6 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : treewidth G ≤ 6) :
    coveringNumber G ≤ 2 * packingNumber G
```
**Source**: Botler et al. 2020

---

### From Dense Graphs 2405.11409

#### Complete 4-Partite
```lean
-- NOT YET FORMALIZED
theorem tuza_complete_4partite (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : isComplete4Partite G) :
    coveringNumber G ≤ (3 * packingNumber G) / 2
```
**Source**: 2405.11409
**Note**: This is OPTIMAL - tight examples exist

---

## PART 3: WHAT'S NEEDED FOR ν=4

### Current Gap Analysis

**What we have**:
- τ(S_e) ≤ 2 for ANY ν ✅
- τ(G) ≤ τ(T_e) + τ(G \ T_e) ✅
- ν(G \ T_e) = ν - 1 ✅

**What we need for ν=4**:
- Either: τ(T_e) ≤ 4 for some e
- Or: Compensating bound on residual
- Or: Alternative decomposition

### Key Lemma Candidates for ν=4

#### Strategy A: Bridge Limit
```lean
-- CONJECTURED, NOT PROVEN
lemma bridge_attachment_limit (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 4)
    (e : Finset V) (he : e ∈ M) :
    -- Bridge triangles attach to at most 2 other packing elements in "bad" way
    ∃ f ∈ M, f ≠ e ∧ ∀ b ∈ T_e G e \ S_e G M e, ¬shares_both_bad_edges b e f
```

#### Strategy B: Packing Pair
```lean
-- CONJECTURED, NOT PROVEN
lemma packing_pair_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 4) :
    ∃ e f ∈ M, e ≠ f ∧ coveringNumberOn G (T_e G e ∪ T_e G f) ≤ 4
```

#### Strategy C: Density Compensation
```lean
-- CONJECTURED, NOT PROVEN
lemma density_compensation (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 4)
    (h_bad : ∀ e ∈ M, coveringNumberOn G (T_e G e) ≥ 3) :
    ∃ e ∈ M, coveringNumberOn G ((G.cliqueFinset 3) \ (T_e G e)) ≤ 5
```

---

## PART 4: LEMMA DEPENDENCY GRAPH

```
                    tuza_nu4 (GOAL)
                         |
         ┌───────────────┼───────────────┐
         ↓               ↓               ↓
   inductive_bound   lemma_2_3     τ(T_e) ≤ 4?
         |               |               |
         ↓               ↓               ↓
  τ(T_e) + τ(rest)   ν(rest)=ν-1   NEED NEW LEMMA
                                        |
                    ┌───────────────────┼───────────────────┐
                    ↓                   ↓                   ↓
            bridge_limit?      density_compensation?   packing_pair?
```

---

## PART 5: ν=4 THEOREM STATUS

### Main Theorem Structure (Proven, pending cases)
```lean
theorem tuza_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : trianglePackingNumber G = 4) : triangleCoveringNumber G ≤ 8
```
**Status**: ⏳ SCAFFOLDED (UUID: b0891cdd)
**Splits into**:
- `nu4_case_isolated` - when ∃ isolated triangle ❌ PENDING
- `nu4_case_pairwise` - when all triangles share vertices ❌ PENDING

### Key Missing Lemma
```lean
lemma tau_union_le_4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : isMaxPacking G M)
    (e f : Finset V) (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f)
    (v : V) (h_inter : e ∩ f = {v}) :
    triangleCoveringNumberOn G (trianglesSharingEdge G e ∪ trianglesSharingEdge G f) ≤ 4
```
**Status**: ❌ PENDING (has `sorry`)
**Why it matters**: This is the key lemma for pairwise descent strategy

---

## SUMMARY STATISTICS

| Category | Proven | Pending | Total |
|----------|--------|---------|-------|
| Definitions | 9 | 0 | 9 |
| Universal Lemmas | 7 | 0 | 7 |
| ν=4 Building Blocks | 4 | 0 | 4 |
| Structural Helpers | 6 | 0 | 6 |
| ν-specific (0,1,2,3) | 4 | 0 | 4 |
| ν=4 Cases | 0 | 3 | 3 |
| Counterexamples | 2 | 0 | 2 |
| Literature Lemmas | 0 | 5 | 5 |
| **Total** | **32** | **8** | **40** |

**Progress**: 32/40 lemmas proven (80%)
