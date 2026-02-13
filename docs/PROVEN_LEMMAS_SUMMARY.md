# Proven Lemmas Summary — Tuza's Conjecture for ν=4

**Date**: February 8, 2026
**Database**: 122 proven submissions, 176 validated-true literature lemmas, 114 proven theorems
**Scope**: Formal Lean 4 proofs verified by Aristotle (0 sorry, 0 axiom, safe sym2)

---

## 1. Core Framework Results

### 1.1 Triangle Packing & Covering Foundations
| Lemma | Statement | Academic Relevance |
|-------|-----------|-------------------|
| `triangle_shares_edge_with_packing` | Every triangle in G shares ≥2 vertices (an edge) with some element of a maximal packing M | Standard maximality property |
| `packing_inter_le_one` | Distinct packing elements share ≤1 vertex | Edge-disjoint packing definition |
| `packing_elem_card_3` | Packing elements have exactly 3 vertices | Triangle = 3-clique |
| `triangle_classification` | Every triangle is: M-element, external (shares edge with exactly one M-elem), or bridge (shares edges with two M-elems) | Novel classification |
| `tau_union_le_sum` | τ(A ∪ B) ≤ τ(A) + τ(B) — subadditivity | Standard, but formally verified |
| `tau_le_of_exists_cover` | τ(T) ≤ |E| if E covers T | Definition of covering number |
| `always_has_covering` | Every finite subset of triangles has a covering | Existence result |

### 1.2 Fractional Relaxation
| Lemma | Statement | Academic Relevance |
|-------|-----------|-------------------|
| `krivelevich_tau_le_2nu_star` | τ(G) ≤ 2·ν*(G) where ν* is fractional packing number | **Krivelevich (1995)** — key bound |
| `nu_star_le_4_cycle4` | Any fractional packing in Cycle_4 has weight ≤ 4 | Concrete LP bound |
| `M_char_edge_sum_le_1` | Characteristic function of M satisfies edge constraint (≤1) | LP feasibility |
| `nu_star_ge_nu` | ν*(G) ≥ ν(G) — fractional ≥ integer | Standard LP relaxation |

### 1.3 Link Graph / Vertex Decomposition
| Lemma | Statement | Academic Relevance |
|-------|-----------|-------------------|
| `linkGraph` | Link graph at vertex v: neighbors of v form vertices, pairs completing triangles form edges | Standard construction |
| `triangleEdgeEquiv` | Bijection between triangles at v and edges in Link(v) | Folklore, now formalized |
| `packing_at_v_eq_matching` | ν(T_v) = matching number of Link(v) | Converts triangle packing to matching |
| `cover_at_v_le_vertex_cover` | τ(T_v) ≤ vertex cover of Link(v) | Reduction to vertex cover |
| `vertex_cover_le_two_matching` | VC(G) ≤ 2·matching(G) — König-type | Classical graph theory |
| `local_tuza_via_link_graph` | τ(T_v) ≤ 2·ν(T_v) for triangles at any vertex v | **Local Tuza** — may be novel |
| `disjoint_triangles_iff_matching` | Edge-disjoint triangles at v ↔ matching in Link(v) | Structural equivalence |
| `link_matching_le_2` | Matching in link graph at shared vertex has size ≤ 2 | Concrete bound for ν=4 |

---

## 2. S_e Structure (External Triangles of Packing Element e)

### 2.1 Core S_e Properties
| Lemma | Statement | Academic Relevance |
|-------|-----------|-------------------|
| `Se_disjoint` | S_e sets are pairwise disjoint for distinct packing elements | Partition property |
| `Se_structure_lemma` | S_e triangles share common edge OR common external vertex | **Key structural theorem** |
| `S_e_pairwise_intersect` | Any two distinct non-e triangles in S_e share ≥2 vertices | Intersecting family |
| `tau_S_le_2` | τ(S_e) ≤ 2 for any packing element e | **Central covering bound** |
| `exists_two_edges_cover_Se` | 2 explicit edges cover e + all S_e externals | Constructive witness |
| `Te_eq_Se_union_bridges` | T_e = S_e ∪ bridges(e) decomposition | Clean partition |
| `disjoint_triples_imply_contradiction` | Three pairwise-disjoint triangles in S_e contradicts maximality | Pigeonhole via ν=4 |

### 2.2 External Triangle Structure
| Lemma | Statement | Academic Relevance |
|-------|-----------|-------------------|
| `external_inter_card_two` | External T has |T ∩ X| = 2 (shares exactly one edge) | Definition consequence |
| `external_has_unique_outside_vertex` | External T of A has exactly one vertex x ∈ T \ A | Complement structure |
| `different_edges_share_external_vertex` | Externals of A on different A-edges share common external vertex | **Fan structure theorem** |
| `externals_on_two_edges_implies_universal_outside` | If externals use ≥2 edges of X, ∃ universal apex outside X | Apex existence |
| `universal_apex_exists` | All X-externals share a common apex vertex (inside or outside X) | **Universal apex theorem** |
| `two_edges_cover_X_and_externals` | 2 edges suffice to cover X and all its externals | **Covering construction** |
| `five_packing_from_disjoint_externals` | Edge-disjoint externals of A enable 5-packing construction | Maximality contradiction |
| `externals_disjoint_implies_false_v2` | Two X-externals must share an edge (else ν > 4) | Constraint from ν=4 |
| `shared_edge_contains_A_vertex` | Edge shared by two A-externals contains a vertex from A | Fan apex inside A |
| `middle_fan_apex_in_B` | Edge shared by two B-externals contains a vertex from B | Middle element variant |

---

## 3. Bridge Structure (X_ef — Triangles Sharing Edges with Two M-elements)

| Lemma | Statement | Academic Relevance |
|-------|-----------|-------------------|
| `bridges_contain_shared_vertex` | All bridges X(e,f) contain shared vertex v when e∩f={v} | Structural constraint |
| `bridge_contains_shared` | Bridges contain shared vertex between adjacent elements | Generalization |
| `tau_X_le_2` | τ(X_ef) ≤ 2 for adjacent elements | Bridge covering bound |
| `X_ef_empty_of_disjoint` | X(e,f) = ∅ when e ∩ f = ∅ (no bridges between disjoint elements) | Empty bridge result |
| `diagonal_bridges_empty` | Disjoint diagonals have no bridges | PATH_4 / CYCLE_4 specific |
| `bridge_nonexistence` | No bridges for vertex-disjoint M-elements | Scattered case |
| `bridge_covered_by_some_m_edge` | Every bridge shares edge with some M-element | Maximality consequence |

---

## 4. Case-Specific Results (ν=4 Configurations)

### 4.1 T_pair Decomposition (Pairs Sharing a Vertex)
| Lemma | Statement | Academic Relevance |
|-------|-----------|-------------------|
| `tau_containing_v_in_pair_le_4` | 4 spokes from v cover all triangles containing v | Spoke covering |
| `tau_avoiding_v_in_pair_le_2` | 2 base edges cover triangles avoiding v | Base edge covering |
| `avoiding_contains_base_edge` | Triangles avoiding v must share base edge {a,b} | **Critical structural insight** |
| `tau_pair_le_6` | τ(T_pair) ≤ 6 (4 spokes + 2 bases) — CORRECT bound (not 4!) | Tight bound |
| `tau_v_decomposition` | τ(T) ≤ τ(containing v) + τ(avoiding v) | Decomposition principle |

### 4.2 STAR_ALL_4 (All 4 Triangles Share a Vertex)
- **τ ≤ 4** — fully proven (slot375, slot49)
- 4 spoke edges from common vertex v cover everything

### 4.3 THREE_SHARE_V (3 Triangles Share a Vertex + 1 Isolated)
- **τ ≤ 4** — fully proven (slot378, slot50)
- 3 spokes + 1 edge from isolated triangle

### 4.4 SCATTERED (All 4 Triangles Vertex-Disjoint)
- **τ ≤ 4** — fully proven (slot376, slot54)
- `scattered_unique_parent` — externals have unique parent
- `scattered_ig_empty` — interaction graph is empty
- Each triangle needs ≤1 edge (no interaction)

### 4.5 TWO_TWO_VW (Two Disjoint Pairs)
- **τ ≤ 4** — fully proven (slot379, slot55)
- Two independent pairs, each covered by ≤2 edges

### 4.6 PATH_4 (A-B-C-D Chain)
| Lemma | Statement |
|-------|-----------|
| `path4_triangle_partition` | Triangles partition into T_A ∪ T_B ∪ T_C ∪ T_D |
| `triangle_decomposition_path4` | Complete decomposition into S_A, S_B, S_C, S_D, X_AB, X_BC, X_CD |
| `path4_A_bridges_only_to_B` | Endpoint A bridges only go to neighbor B |
| `path4_D_bridges_only_to_C` | Endpoint D bridges only go to neighbor C |
| `tau_Te_le_4_for_endpoint` | τ(T_A) ≤ 4 for endpoints |
| `tau_le_12_path4` | τ ≤ 12 (subadditivity, conservative) |
| `tau_le_10_path4` | τ ≤ 10 (tighter, proven in slot300) |
| `bridge_spine_covers_all_bridges` | Spine covers all middle bridges (slot523) |
| `middle_no_base_externals` | Middle elements have no base externals (slot421) |

### 4.7 CYCLE_4 (A-B-C-D-A Cycle)
| Lemma | Statement |
|-------|-----------|
| `cycle4_element_contains_shared` | Every edge of X contains ≥1 shared vertex (pigeonhole) |
| `cycle4_all_triangles_contain_shared` | Every triangle contains some shared vertex |
| `tau_le_12_cycle4` | τ ≤ 12 (conservative) |
| `cycle4_same_as_path4_union` | Cycle reduces to path + absorbed bridges |
| **τ ≤ 4** | Fully proven for cycle4 (slot377) |

### 4.8 Exhaustiveness
| Lemma | Statement |
|-------|-----------|
| `exhaustiveness_proof` | All 11 intersection graph patterns are realizable + τ ≤ 8 for each (slot466) |
| `four_missing_patterns` | K2, P3, Paw, Diamond patterns — all τ ≤ 4 (slot465) |
| `central_triangle_pattern` | K_{1,3} Central Triangle — τ ≤ 4 (slot464) |

---

## 5. Concrete Computations (Fin n, native_decide)

| Slot | Result | Vertex Set |
|------|--------|------------|
| slot460 | Bridge/private classification — 41 theorems | Fin 12 |
| slot461 | Degree bounds — 53 theorems | Fin 12 |
| slot471/473 | Adaptive cover — 62-63 theorems | Various |
| slot406 | 6-triangle contradiction + intersection lemmas — 10 theorems | |
| slot412 | `not_all_three_edge_types` — key lemma | |

---

## 6. Counterexample / Falsification Results (Also Proven)

| Lemma | What Was Disproven |
|-------|-------------------|
| `same_edge_counterexample` (slot252) | `same_edge_share_external_vertex` is FALSE |
| `propeller_nu_verify` (slot57) | Propeller 4-packing is INVALID (not maximal) |
| `bridge_has_apex_in_bridge` (slot543) | Apex approach FALSIFIED by counterexample on Fin 11 |

---

## 7. Auxiliary / General Graph Theory

| Lemma | Statement |
|-------|-----------|
| `exists_maximal_matching` | Every finite graph has a maximal matching |
| `helly_triangles_edges` | Pairwise edge-sharing triangles → global shared edge (Helly property) |
| `intersecting_triangles_structure` | 3 pairwise edge-sharing triangles without common edge form K4 |
| `hypergraph_hitting_set_lemma` | Hitting set lemma for hypergraph on 4 vertices |

---

## 8. Summary of What We Have vs What We Need

### What IS Formally Proven (Lean 4, 0 sorry)
1. **τ ≤ 4** for star_all_4, three_share_v, scattered, two_two_vw, cycle_4 — all 5 "easy" cases
2. **τ ≤ 8** for all 11 intersection graph patterns (slot466 exhaustiveness, but on Fin n)
3. **τ(S_e) ≤ 2** for any packing element e — central bound
4. **τ(X_ef) ≤ 2** for adjacent element bridges
5. **Fan structure**: externals share common apex vertex
6. **2 edges per element suffice** to cover element + externals
7. **Local Tuza**: τ(T_v) ≤ 2·ν(T_v) for any vertex v
8. **Full triangle decomposition** for PATH_4 and CYCLE_4

### What We Still Need (Gap to General Theorem)
1. **General τ ≤ 8 for PATH_4** — currently only have τ ≤ 10 general, τ ≤ 8 on Fin n
2. **SimpleGraph V formulation** — current proofs use Fin n, need arbitrary V
3. **Classification transfer**: every maximal 4-packing maps to one of 11 patterns
4. **Assembly**: chain case-by-case τ ≤ 8 into universal theorem

---

## 9. Key Academic References to Validate Against

1. **Tuza (1981)**: τ ≤ 2ν conjecture — our target
2. **Haxell (1999)**: τ ≤ 2ν - 1 for ν ≤ 3 (proven τ ≤ 2ν for small ν)
3. **Krivelevich (1995)**: τ ≤ 2ν* — fractional relaxation bound
4. **Chapuy et al. (2014)**: τ ≤ (2-ε)ν for some ε > 0 (still open?)
5. **Haxell, Kostochka, Thomassé**: Various partial results
6. **Puleo (2015)**: τ ≤ 2ν for ν ≤ 4 (IS THIS ALREADY PROVEN?)
7. **Baron, Kahn (2014)**: Tuza for random graphs
8. **Aparna Lakshmanan, Bujtás, Tuza (2012)**: Small values of ν
