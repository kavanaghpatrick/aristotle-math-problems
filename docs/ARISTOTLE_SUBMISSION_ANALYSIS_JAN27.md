# Aristotle Submission Analysis: Tuza's Conjecture (ν=4)

**Date**: January 27, 2026
**Total Submissions**: 690+
**Time Period Analyzed**: Slots 375-520 (last ~50 active submissions)
**Purpose**: Context for multi-agent debate on proof strategy

---

## Executive Summary

Over the past month, we submitted 150+ Lean files to Aristotle targeting τ ≤ 8 for ν = 4 graphs. Key findings:

| Metric | Value |
|--------|-------|
| Fully proven (0 sorry) | 108 submissions |
| Near-misses (1-2 sorry) | 62 submissions |
| Negated lemmas discovered | 39 false lemmas catalogued |
| Highest theorem count | 44 theorems (slot452) |
| Critical breakthrough | slot451: 5-packing impossibility proven |

**Bottom line**: We've proven τ ≤ 8 for 6 concrete graph patterns via `native_decide`, but the **general theorem remains unproven** due to bridge assignment complexity.

---

## Part 1: What We've Proven

### Tier 1: Fully Verified (0 sorry, ≥20 theorems)

| Slot | Theorems | Key Results |
|------|----------|-------------|
| 452 | 44 | `tau_le_8_case2a` - bridge with ≤1 external |
| 451 | 39 | **5-packing impossibility** on Fin 10 - if bridge + 2 externals exist, ν ≥ 5 |
| 382 | 37 | τ ≤ 8 on graph with 4 bridge triangles |
| 454 | 37 | Assembly theorem: τ ≤ 8 for 6 concrete patterns |
| 381 | 33 | `external_has_other_home` + `tau_le_8_hard_mode` |
| 380 | 32 | `external_shares_edge_with_other` theorem |
| 375-379 | 24-28 each | τ ≤ 4 for star_all_4, scattered, cycle4, three_share_v, two_two_vw |
| 453 | 24 | Case 1 (no bridges): `tau_le_8_case1`, `tuza_ratio_optimal` |

### Tier 2: Critical Structural Lemmas

```
✓ two_edges_cover_Se - 2 edges from e cover all EXCLUSIVE externals (slot512)
✓ external_uses_one_edge_type - each external uses exactly one edge-type
✓ S_e_subset_Se_prime - exclusive externals ⊆ min-index partition
✓ shared_edge_in_both_sym2 - shared edge exists when |T ∩ e| ≥ 2
✓ tau_le_8_assembly - modular assembly IF partition + cover hypotheses hold
✓ five_packing_from_bridge - bridge + both externals → 5-packing
```

### Concrete Graph Verifications (native_decide)

All 6 canonical ν = 4 patterns have τ ≤ 4 proven computationally:

1. **Star (all 4 share vertex)**: τ ≤ 4 via 4 spokes
2. **Scattered (pairwise disjoint)**: τ ≤ 4 via 1 edge each
3. **Three-share-v**: τ ≤ 4 via 3 spokes + 1 edge
4. **Two-two-vw**: τ ≤ 4 via 2 + 2 edges
5. **Cycle-4**: τ ≤ 4 via alternating edges
6. **Path-4**: τ ≤ 4 via spine + endpoints

---

## Part 2: What Aristotle Negated (Critical False Lemmas)

### Aristotle-Verified Counterexamples

| # | Lemma | Counterexample | Impact |
|---|-------|----------------|--------|
| 39 | `at_most_two_edge_types` | K4 with M={{0,1,2}}: S_e' uses all 3 edge-types | **Breaks 2-edges-per-element for bridges** |
| 38 | `triangle_in_some_Se_or_M` | K5 with M={{0,1,2},{2,3,4}}: bridge {1,2,3} excluded from all S_e | Must use S_e' with bridge assignment |
| 35 | `sym2_cover_cardinality` | A.sym2 has 6 elements (includes self-loops), not 3 | **Never use .sym2 for edge enumeration** |
| 34 | `fan_cover_le_2_self_loop` | Proof uses s(v,v) which is invalid | Self-loops are not graph edges |
| 33 | `Se_fan_apex` | K6 with e={0,1,2}: externals T1,T2,T3 have no common vertex | Externals don't form fans |
| 31 | `two_externals_share_edge` | T1={0,1,7}, T2={1,2,8} share vertex 1 but no edge | Externals can share just a vertex |
| 30 | `endpoint_D_external_contains_spine` | T={7,8,9} for D={6,7,8} avoids spine v3=6 | D-externals can avoid spine |

### AI-Verified False Lemmas (Multi-Agent Consensus)

| # | Lemma | Why False |
|---|-------|-----------|
| 36 | `bridge_auto_covered_by_pigeonhole` | Covering vertex v ≠ covering all triangles containing v |
| 32 | `tau_S_union_X_le_2` | Base triangles and bridges can be edge-disjoint (need 3 edges) |
| 29 | `externals_on_at_most_two_edges` | K4 externals can populate all 3 edges (share common external vertex) |

---

## Part 3: Approaches Tried and Why They Failed

### Failed Strategy 1: Local Apex Selection
**Idea**: For each M-element e, find apex x ∈ e contained in all S_e externals. Use 2 edges through x.

**Why Failed**:
- `Se_fan_apex` is FALSE - externals don't share common apex
- Counterexample: K6 with 3 externals using different edge-types

**Avoid**: Don't assume externals form fan structure

---

### Failed Strategy 2: Sym2 Edge Enumeration
**Idea**: Use `e.sym2` to enumerate edges of triangle e, then filter/select.

**Why Failed**:
- `Finset.sym2` includes self-loops s(x,x)
- |{a,b,c}.sym2| = 6, not 3
- Aristotle correctly negates cardinality bounds using this

**Avoid**: NEVER use .sym2 for edge enumeration. Use explicit sets like `{s(a,b), s(b,c), s(a,c)}`

---

### Failed Strategy 3: 2 Edges Per Element (Min-Index Partition)
**Idea**: Partition non-M triangles into S_e' sets using min-index assignment. Each S_e' uses ≤2 edge-types of e, so 2 edges suffice.

**Why Failed**:
- `at_most_two_edge_types` is FALSE for S_e' (slot518 negation)
- Bridges can use ANY edge-type of e, not constrained by 6-packing
- 6-packing constraint only applies to EXCLUSIVE externals (S_e)

**Avoid**: Don't assume min-index partition S_e' uses only 2 edge-types

---

### Failed Strategy 4: Bridges Auto-Covered by Pigeonhole
**Idea**: Any 2-edge selection covering all vertices automatically hits bridges containing shared vertex.

**Why Failed**:
- Covering vertex v means edge INCIDENT to v
- Does NOT mean all triangles containing v are hit
- Bridge T = {v, a, b} needs edge OF T, not just edge touching v

**Avoid**: Need explicit bridge coordination, not pigeonhole

---

### Failed Strategy 5: Link Graph Bipartiteness (König)
**Idea**: Link graph is bipartite → König's theorem gives τ = ν for matchings.

**Why Failed**:
- Link graph is NOT bipartite in general (false lemma #8)
- Helly property for triangle edge-sharing is FALSE

**Avoid**: Don't use König's theorem for triangle covering

---

### Failed Strategy 6: Pattern Exhaustiveness Without Verification
**Idea**: 6 patterns cover all ν=4 graphs.

**Why Failed**:
- Gemini+Grok audit found "Central Triangle" pattern missing
- A={0,1,2}, B={0,3,4}, C={1,5,6}, D={2,7,8} - triangle A shares DISTINCT vertices

**Avoid**: Never assume pattern list exhaustive without computational verification

---

## Part 4: What Aristotle Is Good At

### Tier 1: Excellent (70-90% success rate)

| Capability | Evidence | Key Tactics |
|------------|----------|-------------|
| **Counterexample finding** (Fin 5-8) | 6 negations in results folder | `native_decide`, `decide +revert` |
| **Cardinality bounds on finite sets** | slot375-379 all proven | `Finset.card_*`, `omega` |
| **Decidable predicates on Fin n** | slot451, 452, 453 | `native_decide +revert` |
| **Packing constructions** (with scaffolding) | slot451 - 39 theorems | `Disjoint.mono`, `card_union_of_disjoint` |
| **Set membership proofs** | Throughout | `simp +decide`, `aesop` |

### Tier 2: Good with Scaffolding (30-50% success rate)

| Capability | Evidence | Requirements |
|------------|----------|--------------|
| **Subadditivity arguments** | tau_le_8_assembly | Need partition lemma provided |
| **Simple case analysis** | external_uses_one_edge_type | 10+ helper lemmas |
| **Sym2 edge membership** | shared_edge_in_both_sym2 | Explicit mk_mem_sym2_iff |
| **Pigeonhole via disjoint unions** | slot347 patterns | card_union_of_disjoint chain |

### Aristotle's Winning Patterns

```lean
-- Pattern 1: Object construction for contradiction
let M' := M.erase X ∪ {T1, T2}
have h_larger : M'.card > M.card := ...
exact absurd h_larger (not_lt.mpr hM_max)

-- Pattern 2: Decidable finite type verification
theorem foo : P := by native_decide +revert

-- Pattern 3: Disjoint union cardinality
have h := card_union_of_disjoint hDisj
have h2 := card_erase_of_mem hMem
omega

-- Pattern 4: Case analysis via interval_cases
interval_cases (T ∩ e).card <;> simp_all +decide
```

---

## Part 5: What Aristotle Struggles With

### Tier 3: Difficult (10-20% success rate)

| Challenge | Why Hard | Evidence |
|-----------|----------|----------|
| **Deep combinatorics** | Search space explosion | Main tau_le_8 theorems have sorry |
| **Disjointness + pigeonhole** | Needs human proof structure | slot262: 30 lemmas but main sorry |
| **Coordinated selection** | Global optimization | Bridge assignment strategies fail |
| **Non-decidable predicates** | Can't use native_decide | General SimpleGraph V theorems |

### Tier 4: Very Difficult (<5% success rate)

| Challenge | Why Very Hard | Recommendation |
|-----------|---------------|----------------|
| **Asymptotics** | Infinite domain | Avoid entirely |
| **Optimal selection** | Requires choice axiom | Provide witness explicitly |
| **Global coordination** | Multiple constraints | Decompose into local lemmas |
| **General V theorems** | No decidability | Prove on Fin n first, then transfer |

### Specific Failure Modes

1. **Escaping to finite types**: Aristotle sometimes "proves" by specializing to `Fin n` and using `simp +decide`, which doesn't prove the general theorem

2. **Self-loop exploitation**: Uses `s(v,v)` in covers, which is invalid for SimpleGraph

3. **Syntax errors on complex definitions**: `DecidablePred` not synthesized for nested predicates

4. **Timeout on unscaffolded submissions**: Files without 10+ helper lemmas often timeout or return incomplete proofs

---

## Part 6: The Current Gap

### What We Have
- τ ≤ 8 for 6 concrete ν=4 patterns (via native_decide)
- `tau_le_8_assembly` theorem (needs hypotheses)
- `two_edges_cover_Se` for exclusive externals
- `five_packing_from_bridge` showing bridge+2externals → ν≥5

### What We're Missing
1. **Partition lemma**: Prove S_e' partitions all non-M triangles
2. **Bridge coverage**: Strategy for covering bridges with ≤2 edges per element
3. **Transfer principle**: Lift Fin n proofs to general SimpleGraph V

### The Bridge Problem (Core Difficulty)

```
For exclusive externals (S_e):
- 6-packing constraint → at most 2 edge-types populated
- Therefore 2 edges suffice ✓

For bridges (shared with multiple M-elements):
- Can use ANY edge-type of e
- Not constrained by 6-packing (they're not exclusive)
- May need 3 edges to cover all bridges ✗
```

**Key insight from slot518**: The min-index partition S_e' can have triangles using all 3 edge-types of e. This breaks the "2 edges per element" strategy.

---

## Part 7: Recommended Approaches for Debate

### Option A: Revise Bridge Assignment
Instead of min-index, assign bridges to the M-element that CAN cover them with existing 2-edge selection.
- Requires: Hall's theorem or greedy assignment proof
- Risk: May not always be possible

### Option B: Prove Bridge Count Bounded
Show that at most 2 bridges are assigned to each M-element via different argument.
- Approach: Use 5-packing contradiction differently
- Risk: slot519 attempt failed (at_most_two_bridges has sorry)

### Option C: Direct Case Analysis on Patterns
For each of ~15 pairwise interaction patterns, prove τ ≤ 8 directly.
- Evidence: slot462-466 attempted this
- Risk: Pattern enumeration may be incomplete

### Option D: Computational Verification on Large Fin n
Prove on Fin 12 (large enough for any ν=4 graph) via native_decide.
- Evidence: slot487 attempted Fin 10
- Risk: Decidability issues with complex predicates

---

## Part 8: Key Statistics

### Submission Outcomes (Last 50)
```
Status          Count
──────────────────────
proven          35
completed       10
near_miss        3
failed           2
```

### Aristotle Capabilities Demonstrated
```
Proven lemmas via native_decide:     44 (slot452 record)
Negated false lemmas:                6 in result files
False lemmas catalogued (all sources): 39
Failed approaches documented:         15
```

### Resource Usage
```
Average theorems per successful slot:  ~15
Minimum scaffolding for success:       10+ helper lemmas
Best success rate:                     safe_discard (100%)
Worst success rate:                    scaffolded (<10% without helpers)
```

---

## Appendix: Key Definitions

```lean
-- Triangle packing: edge-disjoint triangles
def isTrianglePacking (G : SimpleGraph V) (M : Finset (Finset V)) : Prop :=
  M ⊆ G.cliqueFinset 3 ∧
  Set.Pairwise (M : Set (Finset V)) (fun t1 t2 => (t1 ∩ t2).card ≤ 1)

-- Exclusive externals: share edge with e, disjoint from other M-elements
def S_e (G : SimpleGraph V) (M : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧ ∀ f ∈ M, f ≠ e → (T ∩ f).card ≤ 1)

-- Min-index partition (includes bridges)
def S_e' (G : SimpleGraph V) (M : Finset (Finset V)) (e : Finset V)
    (idx : Finset V → ℕ) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun T =>
    T ≠ e ∧ 2 ≤ (T ∩ e).card ∧
    (sharesEdgeWith M T).filter (fun f => idx f < idx e) = ∅)

-- Bridge: shares edges with 2+ M-elements
def isBridge (G : SimpleGraph V) (M : Finset (Finset V)) (T : Finset V) : Prop :=
  T ∈ G.cliqueFinset 3 ∧ T ∉ M ∧ 2 ≤ (sharesEdgeWith M T).card
```

---

*Document generated for multi-agent debate on Tuza's conjecture proof strategy.*
