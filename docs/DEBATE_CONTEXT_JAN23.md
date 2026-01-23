# Multi-Agent Debate Context: Tuza ν=4
## Date: 2026-01-23

---

## THE PROBLEM

**Tuza's Conjecture**: For any graph G, τ(G) ≤ 2ν(G)
- τ(G) = minimum number of edges needed to cover all triangles
- ν(G) = maximum number of edge-disjoint triangles

**Our Goal**: Prove the ν=4 case: If G has a maximum packing of 4 edge-disjoint triangles, then τ ≤ 8.

---

## CURRENT STATE SUMMARY

| Metric | Value |
|--------|-------|
| Total Aristotle submissions | 692 |
| Fully proven (0 sorry, 0 axiom) | 41+ files |
| Total theorems proven | 800+ |
| False lemmas documented | 47 |
| τ ≤ 12 proven | ALL 7 cases |
| τ ≤ 8 proven | PATH_4 only (specific Fin patterns) |

---

## THE 7 INTERSECTION GRAPH CASES

The 4 packing triangles M = {A, B, C, D} have intersection graph based on shared vertices:

| Case | Structure | τ Proven | τ Target | Status |
|------|-----------|----------|----------|--------|
| **PATH_4** | A-B-C-D chain | **8** | 8 | **COMPLETE** (107 theorems) |
| CYCLE_4 | A-B-C-D-A cycle | 12 | 8 | Fan apex proven, assembly pending |
| STAR_ALL_4 | All 4 share vertex | 12 | 4 | 2 sorry in triple_apex |
| THREE_SHARE_V | 3 share vertex + isolated | 12 | 5 | Same blocker |
| TWO_TWO_VW | Two pairs share vertices | 12 | 8 | Infrastructure only |
| SCATTERED | No shared vertices | 12 | 12 | τ = 2ν is TIGHT here |
| MATCHING_2 | Same as TWO_TWO_VW | 12 | 8 | Infrastructure only |

---

## KEY BREAKTHROUGH #1: THE 6-PACKING CONSTRAINT (slot412)

**Theorem `not_all_three_edge_types`** (PROVEN, 0 sorry):

For any packing element E = {a, b, c} with other elements B, C, D ∈ M:

> **At most 2 of the 3 edge-types can have S_e externals.**

**Why?** If all 3 edge-types have externals T₁, T₂, T₃ (with distinct fourth vertices w₁, w₂, w₃):
- T₁ = {a, b, w₁} (uses edge {a,b})
- T₂ = {b, c, w₂} (uses edge {b,c})
- T₃ = {a, c, w₃} (uses edge {a,c})

Then {T₁, T₂, T₃, B, C, D} would form **6 edge-disjoint triangles**, contradicting ν = 4.

**Proven via intersection bounds:**
- T₁ ∩ T₂ ⊆ {b} → (T₁ ∩ T₂).card ≤ 1 ✓
- T₁ ∩ T₃ ⊆ {a} → (T₁ ∩ T₃).card ≤ 1 ✓
- T₂ ∩ T₃ ⊆ {c} → (T₂ ∩ T₃).card ≤ 1 ✓

**Consequence**: τ(S_e) ≤ 2 for any M-element E (just cover the 2 populated edge-types).

---

## KEY BREAKTHROUGH #2: PATH_4 COMPLETE (slots 451-453)

PATH_4 structure: A --- B --- C --- D (chain of shared vertices)

**Three-case proof:**

| Case | Scenario | Result | File |
|------|----------|--------|------|
| **Case 1** | No bridges exist | τ = 4 (just M-edges) | slot453 |
| **Case 2a** | Bridge exists, covered by adaptive selection | τ ≤ 8 | slot452 |
| **Case 2b** | Bridge exists, NOT covered | **IMPOSSIBLE** (5-packing) | slot451 |

**Case 2b impossibility** (slot451, 39 theorems on Fin 10):
If bridge T between B and C exists AND forcing externals E_B, E_C exist that don't cover T, then {A, D, T, E_B, E_C} form a 5-packing, contradicting ν = 4.

---

## CRITICAL DISCOVERY TODAY (slot505): BRIDGES BREAK S_e

**Aristotle NEGATED lemma `triangle_in_some_Se_or_M`**

**Counterexample on K₅:**
```
M = {{0,1,2}, {2,3,4}}  (packing of 2 triangles sharing vertex 2)
T_bridge = {1, 2, 3}
```

**Why T_bridge is NOT in any S_e:**
- T_bridge shares edge {1,2} with {0,1,2}
- T_bridge shares edge {2,3} with {2,3,4}
- S_e definition requires: "edge-disjoint from OTHER M-elements"
- T_bridge shares edges with BOTH → excluded from BOTH S_e sets!

**Impact**: The partition "every triangle is in M or some S_e" is FALSE. Bridges escape!

---

## THE S_e DECOMPOSITION APPROACH

**Definition**: For M-element e = {a, b, c}:
```
S_e = { triangles T : T shares edge with e,
                      T ≠ e,
                      T is edge-disjoint from all other M-elements }
```

**The Plan Was**:
1. Partition all triangles: M ∪ ⋃_{e∈M} S_e
2. Each S_e covered by ≤2 edges (via 6-packing constraint)
3. Total: 4 × 2 = 8 edges

**The Problem**: Bridges don't fit in any S_e!

**Proposed Fix**: Define S_e' to include bridges via minimum-index assignment:
```
S_e' = S_e ∪ { bridges T : e = argmin_{f∈M : T shares edge with f} index(f) }
```

---

## KEY FALSE LEMMAS (PROVEN IMPOSSIBLE)

### Aristotle-Verified (🔴 - counterexamples found)

| Lemma | Why False | Impact |
|-------|-----------|--------|
| `triangle_in_some_Se_or_M` | Bridges share with multiple M-elements | Breaks partition |
| `bridge_absorption` | Cover of S_e ∪ S_f doesn't auto-hit bridges | Need explicit bridge handling |
| `two_externals_share_edge` | Two externals can be vertex-disjoint | Can't assume shared structure |

### AI-Verified (🟠 - multi-agent consensus)

| Lemma | Why False | Impact |
|-------|-----------|--------|
| `local_cover_le_2` | At shared vertex: need 3+ edges, not 2 | 4×2=8 fails |
| `external_share_common_vertex` | Externals from different M-elements don't share | No common apex |
| `bridge_auto_covered_by_pigeonhole` | Pigeonhole covers vertices, not edge-sets | Bridges need explicit coverage |
| `fan_apex_outside_A` | Fan apex can be IN A (e.g., shared vertex) | Apex selection more complex |

---

## THE PHASE 1 / PHASE 2 GAP

### Phase 1 (Current - WORKING)
- Prove τ ≤ 8 for 11 concrete patterns on Fin 12
- Use `native_decide` for computational verification
- Set-theoretic: triangles as `Finset (Fin n)` with `.card = 3`

### Phase 2 (Needed - NOT STARTED)
- Prove τ ≤ 8 for ANY graph G with ν(G) = 4
- Use `SimpleGraph V` with actual graph structure
- Need transfer lemma: any 4-packing embeds into one of 11 patterns

**The Gap**: We prove "For these 11 patterns, τ ≤ 8" but NOT "For any graph with ν=4, τ ≤ 8"

---

## NEAR-MISS ANALYSIS (13 files with 1 sorry, 10+ helpers)

### Blocking Issues:

| Issue | Files Blocked | Quick Fix? |
|-------|---------------|------------|
| `triangle_in_some_Se` pigeonhole | 4 files | Needs bridge handling |
| Externals pairwise disjoint | 4 files | May be false in some cases |
| Main τ ≤ 8 assembly | 5 files | Mechanical once #1 fixed |

### Highest Priority:
- **slot477**: `triangle_in_some_Se` - If fixed, unblocks 4+ other files
- **slot430**: Has 12+ proven helpers from slot429, just needs assembly
- **slot408**: Coverage assembly with 18 proven helpers

---

## PROVEN TACTICS (What Works for Aristotle)

| Tier | Success Rate | Pattern | Example |
|------|--------------|---------|---------|
| 1 | 95%+ | `native_decide` on Fin n | Cardinality facts, membership |
| 2 | 70%+ | `simp` + `exact` + `rw` | Structural proofs, case lemmas |
| 3 | 10-20% | `simp_all` + `aesop` | General τ bounds |

**Critical Rule**: 10+ scaffolding lemmas → 4× success rate

---

## DEBATE QUESTIONS

1. **Bridge Handling**: How should we modify S_e' to include bridges? Is minimum-index assignment correct, or is there a better approach?

2. **6-Packing Still Central?**: The 6-packing constraint (slot412) is proven. Does it still provide the τ ≤ 2 bound per element even with bridges included?

3. **Phase 1 → Phase 2 Path**: What's the fastest route?
   - Option A: Prove transfer lemma (any 4-packing → one of 11 patterns)
   - Option B: Direct general proof using SimpleGraph V
   - Option C: More concrete patterns until general structure emerges

4. **Remaining Cases**: Should we:
   - Focus on CYCLE_4 (fan apex proven, just need assembly)
   - Attack all cases uniformly
   - Jump to Phase 2 general theorem

5. **False Lemma Risk**: Are our near-miss files (13 with 1 sorry) likely blocked by false lemmas we haven't discovered yet?

6. **Scattered Case**: τ = 2ν is TIGHT for scattered (propeller counterexample). Does this affect the general approach?

---

## WHAT EACH AGENT SHOULD ADDRESS

- **Strategy**: Which path forward? Case-by-case vs. general theorem?
- **Bridge Problem**: Concrete solution for S_e' definition
- **False Lemma Risk**: Which near-miss assumptions might be false?
- **Actionable Next Steps**: Specific files/lemmas to work on
