# Multi-Agent Debate Context: τ ≤ 8 for PATH_4 (ν = 4)

**Date**: Jan 17, 2026
**Goal**: Determine next steps to complete the proof of τ ≤ 2ν for PATH_4 configuration

---

## 1. PROBLEM STATEMENT

**Tuza's Conjecture**: For any graph G, τ(G) ≤ 2ν(G), where:
- ν(G) = maximum triangle packing number (edge-disjoint triangles)
- τ(G) = minimum triangle cover number (edges hitting all triangles)

**Our Target**: Prove τ ≤ 8 for PATH_4 configuration with ν = 4.

**PATH_4 Structure**:
```
A ——v1—— B ——v2—— C ——v3—— D

Where:
  A = {a1, a2, v1}  (endpoint)
  B = {v1, b, v2}   (middle)
  C = {v2, c, v3}   (middle)
  D = {v3, d1, d2}  (endpoint)

Intersections:
  A ∩ B = {v1}, B ∩ C = {v2}, C ∩ D = {v3}
  Non-adjacent pairs are disjoint
```

---

## 2. BREAKTHROUGH: slot447 (ALL 17 PROVEN)

On Fin 9 with "full conflict" edges (worst-case graph), Aristotle proved:

### Key Theorems (native_decide):
```lean
-- ν = 4 confirmed
theorem full_conflict_nu_eq_4 :
    (∃ S, isPackingProp S ∧ S.card = 4) ∧
    (∀ S, isPackingProp S → S.card ≤ 4)

-- CRITICAL: No S_e external on C's spine edge {4,6}
theorem Se_C_spine_empty :
    ∀ T, isSeExternal T C_elem → usesSpineC T → False

-- τ ≤ 8 achieved with explicit cover
theorem tau_le_8_full_conflict :
    ∃ C : Finset (Sym2 (Fin 9)),
      C.card ≤ 8 ∧ ∀ T ∈ allTriangles, coverHitsTriangle C T
```

### The 8-Edge Cover That Works:
```lean
def cover8 : Finset (Sym2 (Fin 9)) :=
  { e 0 2, e 1 2,     -- A: both spokes
    e 2 4, e 2 3,     -- B: spine + left leg
    e 4 5, e 5 6,     -- C: both legs (NOT spine!)
    e 6 7, e 6 8 }    -- D: both spokes
```

### Why This Works:
- On Fin 9, all 9 vertices are in packing elements
- No external vertex exists to form S_e(C, spine)
- Therefore C can use both legs instead of spine
- Edge s(4,5) = s(v2,c) covers the B-C bridge {3,4,5}

---

## 3. NEGATION: slot446 (FALSE LEMMA #32)

Aristotle **negated** `endpoint_adaptive_cover` and proved key insights:

### The False Theorem:
```lean
-- THIS IS FALSE:
theorem endpoint_adaptive_cover ... :
    ∃ e₁ e₂ : Sym2 V,
      (e₁ ∈ A's edges) ∧ (e₂ ∈ A's edges) ∧
      ∀ T sharing edge with A, e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2
```

### Why False - Key Discovery:
```lean
-- PROVEN: 6-packing implies at least one edge is MISSING
lemma six_packing_implies_missing_edge ... :
    ¬(G.Adj a₁ a₂ ∧ G.Adj a₁ v₁ ∧ G.Adj a₂ v₁)
```

If 6-packing holds (at most 2 of 3 S_e types nonempty), then the triangle A = {a₁, a₂, v₁} is NOT a complete clique in G - at least one edge is missing!

### Corrected Approach (PROVEN):
```lean
-- If base edge missing, use both spokes
lemma endpoint_adaptive_cover_of_missing_base ... (h_missing : ¬G.Adj a₁ a₂) :
    ∃ e₁ e₂, ... ∀ T, e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2

-- If right spoke missing, use base + left spoke
lemma endpoint_adaptive_cover_of_missing_right ... (h_missing : ¬G.Adj a₂ v₁) :
    ∃ e₁ e₂, ... ∀ T, e₁ ∈ T.sym2 ∨ e₂ ∈ T.sym2
```

---

## 4. ALL PROVEN LEMMAS (Scaffolding)

### From slot441/443/444 - Bridge Structure:
```lean
-- Bridge contains shared vertex
theorem bridge_contains_shared (hEF : E ∩ F = {v}) (hTE : 2 ≤ (T ∩ E).card) (hTF : 2 ≤ (T ∩ F).card) :
    v ∈ T

-- Bridge structure: T = {v, x, y} with x ∈ E, y ∈ F
lemma bridge_edge_structure ... :
    ∃ x y, x ∈ E ∧ x ≠ v ∧ y ∈ F ∧ y ≠ v ∧ T = {v, x, y}
```

### From slot443 - Two Edges Cover:
```lean
-- Two distinct edges from triangle cover all 3 vertices
lemma two_edges_cover_all_vertices ...

-- Triangle sharing edge hit by two edges
lemma sharing_triangle_hit_by_two_edges ...
```

### From slot412 - 6-Packing Constraint:
```lean
-- At most 2 of 3 S_e types can be nonempty
theorem six_packing_constraint (E ∈ M) :
    ¬((S_e_edge spine).Nonempty ∧ (S_e_edge left).Nonempty ∧ (S_e_edge right).Nonempty)
```

### From slot447 - Fin 9 Specifics:
```lean
-- All S_e types enumerated
lemma Se_B_spine_nonempty : isSeExternal {2, 4, 7} B
lemma Se_B_left_nonempty : isSeExternal {2, 3, 5} B
lemma Se_C_right_nonempty : isSeExternal {0, 5, 6} C_elem

-- Bridge uniqueness
lemma BC_bridge_unique : ∀ T, isBridgeBC T ↔ T = {3, 4, 5}
```

---

## 5. FALSE LEMMAS (Do NOT Use)

| # | Lemma | Why False |
|---|-------|-----------|
| 31 | vertex_coverage_implies_triangle_coverage | Covering v ≠ covering triangles containing v |
| 32 | endpoint_adaptive_cover (without missing edge) | 6-packing forces missing edge |
| 29 | sym2_cover_cardinality | A.sym2 includes self-loops! |
| 8 | link_graph_bipartite | König approach invalid |

---

## 6. CURRENT GAP

### What's Proven:
- τ ≤ 8 on Fin 9 (minimal case) ✓
- Bridge structure lemmas ✓
- 6-packing constraint ✓
- Endpoint covers when edge is missing ✓

### What's Missing:
1. **Generalization from Fin 9 to arbitrary V**
   - On Fin 9, Se_C_spine_empty because no external vertex
   - For |V| > 9, external vertices could exist

2. **Middle element cover coordination**
   - If both B and C have S_e on their shared-facing edges, how to cover B-C bridge?
   - slot447 shows this is impossible on Fin 9, but what about larger V?

3. **Combining endpoint and middle covers**
   - Endpoint: use missing edge insight
   - Middle: use 6-packing + bridge coordination

---

## 7. QUESTIONS FOR DEBATE

1. **Can we prove S_e(C, spine) is always "manageable"?**
   - Either empty (Fin 9 case)
   - Or if nonempty, 6-packing frees up a leg for bridge coverage

2. **How to handle bridges in the general case?**
   - A-B bridges: endpoint A has spoke to v1, bridge contains v1
   - B-C bridges: this is the hard case - need coordination
   - C-D bridges: symmetric to A-B

3. **What's the minimal set of hypotheses needed?**
   - Do we need explicit coordination hypothesis?
   - Can we derive it from 6-packing alone?

4. **Strategy: Component-wise vs Global?**
   - Component-wise: prove each element contributes ≤2 edges
   - Global: construct explicit cover and verify

---

## 8. CANDIDATE NEXT STEPS

A. **Prove bc_bridge_always_coverable**:
   - If B-C bridge exists and S_e(C, spine) nonempty
   - Then by 6-packing, S_e(C, left) or S_e(C, right) empty
   - So C can use that free leg to cover bridge

B. **Prove middle_adaptive_cover**:
   - For middle element B with neighbors A, C
   - 6-packing ensures ≤2 S_e types nonempty
   - Show 2 edges suffice for S_e AND bridge coverage

C. **Induction on |V|**:
   - Base: Fin 9 proven
   - Step: larger graphs reduce to simpler case?

D. **Direct construction**:
   - Define explicit cover selection algorithm
   - Prove it produces ≤8 edges that hit all triangles

---

## 9. FILES FOR REFERENCE

- `slot447_BC_conflict_fixed_aristotle.lean` - BREAKTHROUGH (17/17 proven)
- `slot446_proven_scaffolding.lean` - Extracted lemmas from negated slot446
- `slot444_tau_le_8_coordinated_aristotle.lean` - Bridge structure lemmas
- `slot443_tau_le_8_path4_aristotle.lean` - Two edges cover lemmas

---

## 10. SUCCESS CRITERIA

A proof is complete when we have:
1. 0 sorry statements
2. 0 axioms
3. Main theorem: `∃ Cover, Cover.card ≤ 8 ∧ Cover ⊆ G.edgeFinset ∧ ∀ T ∈ triangles, ∃ e ∈ Cover, e ∈ T.sym2`
4. Applies to all PATH_4 configurations (not just Fin 9)
