# Tuza Conjecture: Master Database

**Last Updated**: December 21, 2025 (Added ν=4 building blocks from b0891cdd)
**Status**: Active tracking for ν=4 campaign - 32/40 lemmas proven (80%)

---

## Quick Reference

| Case | Status | Proof Method | Literature Match |
|------|--------|--------------|------------------|
| ν=0 | ✅ PROVEN | Trivial (no triangles) | - |
| ν=1 | ✅ PROVEN | T_e = S_e, τ(S_e) ≤ 2 | Parker Lemma 2.1 |
| ν=2 | ✅ PROVEN | `tuza_nu2` (0764be78) | Parker Lemma 2.2 |
| ν=3 | ✅ PROVEN | `tau_Te_le_2_nu_3` (89bfa298) | Parker Theorem 1.1 |
| ν=4+ | **OPEN** | See strategies below | **No published proof** |

**Our ν ≤ 3 formalization matches [Parker arXiv:2406.06501](https://arxiv.org/abs/2406.06501) (EJC May 2025).**

---

## Complete Literature Survey (Dec 2025)

### Tier 1: Cutting-Edge Results (2024-2025)

| Paper | Authors | Result | Implications for ν=4 |
|-------|---------|--------|---------------------|
| [Parker 2406.06501](https://arxiv.org/abs/2406.06501) | A. Parker | Tuza for ν ≤ 3, Aharoni-Zerbib for ν^(k-1) ≤ 3 | ✅ Our formalization matches. ν=4 is genuinely open |
| [Guruswami-Sandeep 2025](https://epubs.siam.org/doi/10.1137/23M1570351) | V. Guruswami, S. Sandeep | t/2 + O(√t log t) approximation via LP rounding | **Fractional version nearly solved; LP techniques available** |
| [Dense Graphs 2405.11409](https://arxiv.org/abs/2405.11409) | Multiple | τ ≤ (3/2)ν for complete 4-partite (optimal) | **"Bad" ν=4 graphs must resemble 4-partite → better bounds** |
| [Co-chain Graphs 2211.07766](https://arxiv.org/abs/2211.07766) | Chahua, Gutierrez | Tuza for co-chain graphs (subclass of interval) | New graph class proven, techniques may transfer |
| [Basit-Galvin 2024](https://arxiv.org/abs/2007.04478) | A. Basit, D. Galvin | Generalized Tuza for random hypergraphs | Probabilistic techniques |

### Tier 2: Foundational Results (Used in Our Proofs)

| Result | Authors/Year | Bound | Used By Us |
|--------|--------------|-------|------------|
| Haxell | P. Haxell 1993 | τ ≤ (66/23)ν ≈ 2.87ν | Best general bound, reference |
| Tripartite | Haxell 1993 | τ ≤ 2ν | For tripartite graphs |
| Planar | Tuza 1985 | τ ≤ 2ν | Original structural result |
| No K₃,₃ | Krivelevich | τ ≤ 2ν | Subdivision-free |
| Fractional | Krivelevich 1995 | τ* = ν* | LP duality, key insight |

### Tier 3: Graph Class Results (Identify Gaps)

| Graph Class | Status | Reference | Notes |
|-------------|--------|-----------|-------|
| Planar | ✅ PROVEN | Tuza 1985 | degeneracy ≤ 5 |
| Tripartite | ✅ PROVEN | Haxell 1993 | - |
| Degeneracy ≤ 6 | ✅ PROVEN | Multiple | Generalizes planar |
| Treewidth ≤ 6 | ✅ PROVEN | [arXiv:2002.07925](https://arxiv.org/abs/2002.07925) | Tree decomposition |
| Threshold | ✅ PROVEN | Bonamy et al. | Split + cograph |
| Co-chain | ✅ PROVEN | Chahua-Gutierrez 2024 | Subclass of interval |
| K₈-free chordal | ✅ PROVEN | Botler et al. | Bounded clique |
| **General chordal** | ❌ OPEN | - | **Key gap!** |
| **Split graphs** | ❌ OPEN | - | Only dense case proven |
| **Interval graphs** | ❌ OPEN | - | Co-chain is subclass |
| Random G(n,p) | ✅ PROVEN | Kahn-Park | Probabilistic |
| Complete 4-partite | ✅ PROVEN | 2405.11409 | τ ≤ (3/2)ν |

### What This Means for ν=4

1. **No published ν=4 proof exists** - We're on genuinely open ground
2. **Chordal graphs still open** - Even simpler classes aren't solved
3. **Dense graphs are easier** - If ν=4 is "bad", it has good structure
4. **LP techniques available** - Guruswami-Sandeep fractional approach
5. **Minimal counterexamples structured** - Not random, has dense edge cuts

---

## Proof Techniques Observed in Literature

### Technique 1: Parker's T_e/S_e Decomposition (We Use This)
- Split triangles by edge sharing with packing
- τ(G) ≤ τ(T_e) + τ(G \ T_e)
- Works when τ(T_e) ≤ 2 is guaranteed
- **Limitation**: Fails at ν=4 when bridges attach to 3 elements

### Technique 2: Reducible Sets (Sparse Graphs)
- Identify substructures that can't occur in minimal counterexample
- Used for degeneracy ≤ 6 and treewidth ≤ 6
- **Application**: Could identify reducible configurations for ν=4

### Technique 3: LP Rounding (Guruswami-Sandeep)
- Solve fractional relaxation
- Round to integer solution
- Gets t/2 + O(√t log t) approximation
- **Application**: Bridge gap between τ* = ν* and τ ≤ 2ν

### Technique 4: Minimal Counterexample Structure
- Any minimal counterexample has:
  - Dense edge cuts
  - Minimum degree > n/2
  - Every edge in a triangle ("triangular graph")
- **Application**: Search for counterexamples in structured graphs

### Technique 5: Fractional-to-Integer
- τ* = ν* by LP duality (proven)
- τ ≤ 2τ* would give τ ≤ 2ν
- Need to bound integrality gap
- **Application**: Show integrality gap ≤ 2 for specific cases

---

## Formalization Status

### Formal Conjectures Repo
**No Tuza conjecture formalization exists** in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures).

This is an **opportunity**: If we solve ν=4, we could contribute the formalization.

### Our Formalized Results
We have the most complete Lean 4 formalization of Tuza for small ν:
- Full ν ≤ 3 proof matching Parker
- Universal lemmas (work for all ν)
- Counterexamples to flawed strategies

---

## Proven Lemmas

### Universal Lemmas (Work for ALL ν)

These are the building blocks for ν=4. Include as context in submissions.

| Lemma | Description | Why Universal | File |
|-------|-------------|---------------|------|
| `lemma_2_2` | S_e triangles pairwise share edges | Maximality argument, no ν bound | f9473ebd:70-124 |
| `lemma_2_3` | ν(G \ T_e) = ν(G) - 1 | Pure decomposition | f9473ebd:130-198 |
| `inductive_bound` | τ(G) ≤ τ(T_e) + τ(G \ T_e) | Pure decomposition | f9473ebd:199-260 |
| `k4_cover` | Triangles on ≤4 vertices have τ ≤ 2 | 4-vertex exhaustion | f9473ebd:241-313 |
| `intersecting_triangles_structure` | Pairwise intersecting → star OR K4 | Combinatorial | f9473ebd:385-457 |
| `pairwise_sharing_implies_tau_le_2` | Any pairwise edge-sharing set has τ ≤ 2 | **KEY for ν=4** | 94407c27 |
| `S_e_pairwise_share_edges` | S_e triangles pairwise share edges | Works for any M | 8fd9def6 |
| `bridge_shares_vertex` | Bridges contain shared vertex | Structural | 94407c27 |

### ν=4 Building Block Lemmas (NEW - Dec 21)

| Lemma | Description | Why Important | File/UUID |
|-------|-------------|---------------|-----------|
| `tau_X_le_2` | τ(X(e,f)) ≤ 2 when e∩f={v} | Covers triangles in both T_e and T_f | b0891cdd |
| `mem_X_implies_v_in_t` | Triangles in X(e,f) contain shared vertex | Structural for union bound | b0891cdd |
| `packing_minus_pair` | ν(G \ T_ef) ≥ ν - 2 | Pair decomposition | b0891cdd |
| `structural_cover` | Pairwise sharing → τ ≤ 2 | Universal covering bound | b0891cdd |
| `three_intersecting_triples_structure` | 3 intersecting → common edge OR K4 | Star/K4 dichotomy | b0891cdd |
| `lemma_K4_cover` | Triangles in ≤4 vertices → τ ≤ 2 | K4 case | b0891cdd |

### ν-Specific Lemmas

| Lemma | ν | Description | File |
|-------|---|-------------|------|
| `tau_Te_le_2_nu_1` | 1 | T_e = S_e when ν=1 | 2b21c426 |
| `tuza_nu2` | 2 | Complete ν=2 proof | 0764be78 |
| `tau_Te_le_2_nu_3` | 3 | τ(T_e) ≤ 2 when ν=3 | 89bfa298 |
| `Te_eq_Se_of_vertex_disjoint` | any | When packing is vertex-disjoint | eb165e0f |
| `cover_with_v_edges` | any | All T_e contain v → τ(T_e) ≤ 2 | eb165e0f |

### ν=4 Theorem Status (In Progress)

| Lemma | Status | Description | UUID |
|-------|--------|-------------|------|
| `tuza_nu4` | ⏳ SCAFFOLDED | τ ≤ 8 when ν = 4 | b0891cdd |
| `tau_union_le_4` | ❌ PENDING | τ(T_e ∪ T_f) ≤ 4 when e∩f={v} | b0891cdd |
| `nu4_case_isolated` | ❌ PENDING | Isolated triangle case | b0891cdd |
| `nu4_case_pairwise` | ❌ PENDING | All share vertices case | b0891cdd |

---

## Counterexamples (What They Rule Out)

Each counterexample eliminates a proof strategy. **Critical for ν=4 planning.**

### K4 Counterexample (8fd9def6)

```lean
let e := {0, 1, 2}
let t1 := {0, 1, 3}; let t2 := {1, 2, 3}; let t3 := {0, 2, 3}
-- Need ALL 3 edges of e to cover {t1, t2, t3}
```

| What it rules out | Why |
|-------------------|-----|
| "Cover S_e with 2 edges FROM e" | K4 needs all 3 edges of e |
| "Pairwise sharing → 2 edges of base suffice" | False for K4 structure |

**What it DOESN'T rule out**: τ(S_e) ≤ 2 using edges NOT from e (still true via `pairwise_sharing_implies_tau_le_2`)

### Fan Counterexample (87299718)

```lean
-- Fin 7 graph: e shares edge {0,1} with 5 triangles
-- S_e = {e, {0,1,3}, {0,1,4}, {0,1,5}, {0,1,6}}
-- |S_e| = 5, not ≤ 4
```

| What it rules out | Why |
|-------------------|-----|
| "\|S_e\| ≤ 4" assumption | Fan has 5 triangles in S_e |
| Bounds based on \|S_e\| | S_e can be arbitrarily large |

**What it DOESN'T rule out**: τ(S_e) ≤ 2 (they all share edge {0,1}, so 1 edge covers all)

### FlowerGraph Counterexample

| What it rules out | Why |
|-------------------|-----|
| "τ(T_e) ≤ 2 for all e" | Central triangle needs 3 edges |
| Naive Parker extension to ν=4 | Can't guarantee τ(T_e) ≤ 2 |

**Key insight**: FlowerGraph has ν=1, so τ(T_e) > 2 is OK (Tuza still holds: τ ≤ 2).

---

## ν=4 Strategy (With Rationale)

### Why Parker Fails

For ν=4 with M = {e, f₁, f₂, f₃}:
- Bridges (T_e \ S_e) can attach to f₁, f₂, AND f₃
- Each bridge attachment potentially adds covering requirement
- Can't guarantee any e has τ(T_e) ≤ 2

### Strategy A: Compensating Density (Gemini + Literature)

**Rationale**: If τ(T_e) ≥ 3 for ALL e, the graph must be extremely dense. Dense graphs have structural constraints that force the residual to be sparse.

**Literature Support**: [arXiv:2405.11409](https://arxiv.org/abs/2405.11409) shows τ ≤ (3/2)ν = 6 for complete 4-partite. "Bad" graphs resemble these and have BETTER bounds.

**Target Lemma**:
```lean
lemma density_compensation (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 4)
    (h_bad : ∀ e ∈ M, coveringNumberOn G (T_e G e) ≥ 3) :
    ∃ e ∈ M, coveringNumberOn G ((G.cliqueFinset 3) \ (T_e G e)) ≤ 5
```

**Why it works**: τ(G) ≤ 3 + 5 = 8 ✓

### Strategy B: Packing-Pair Decomposition (Grok-4)

**Rationale**: Instead of single T_e, consider pairs. Among 6 pairs in M, at least one should have bounded joint covering.

**Target Lemma**:
```lean
lemma packing_pair_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 4) :
    ∃ e f ∈ M, e ≠ f ∧ coveringNumberOn G (T_e G e ∪ T_e G f) ≤ 4
```

**Why it works**: Apply to G' = G \ (T_e ∪ T_f) where ν(G') ≤ 2. Since ν=2 proven: τ(G) ≤ 4 + 4 = 8 ✓

**Evidence**: Even FlowerGraph doesn't break pairs - the "bad" triangle is isolated.

### Strategy C: Bridge Classification

**Rationale**: Bridges are the problem. Classify how they attach to M \ {e}.

**Literature Connection**: Reducible sets technique from treewidth proofs.

**Target Lemma**:
```lean
lemma bridge_limited_attachment (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset V)) (hM : IsMaxPacking G M) (hnu : M.card = 4)
    (e : Finset V) (he : e ∈ M) :
    -- Each bridge attaches to at most 2 of {f₁, f₂, f₃}
    ∀ b ∈ T_e G e \ S_e G M e,
    (#{f ∈ M | f ≠ e ∧ shares_edge b f}).card ≤ 2
```

**Why it works**: Limited attachment → controlled bridge structure → τ(T_e) ≤ 3 with structured bridges.

### Strategy D: Direct/Minimal (Boris Pattern)

**Rationale**: Let Aristotle explore freely without strategic constraints.

**Approach**: Just state the theorem, include universal lemmas, no comments.

```lean
theorem tuza_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : packingNumber G = 4) : coveringNumber G ≤ 8 := by
  sorry
```

### Strategy E: LP Rounding (NEW - from Guruswami-Sandeep)

**Rationale**: Use fractional relaxation. We know τ* = ν*, need to bound integrality gap.

**Literature**: [Guruswami-Sandeep 2025](https://arxiv.org/abs/2008.07344) achieves t/2 + O(√t log t) via LP rounding.

**Target Lemma**:
```lean
lemma integrality_gap_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnu : packingNumber G = 4) :
    coveringNumber G ≤ 2 * fractionalCoveringNumber G
```

### Strategy F: Minimal Counterexample Contradiction

**Rationale**: Show no minimal counterexample can exist by exploiting structure.

**Literature**: Minimal counterexamples have min degree > n/2, dense edge cuts.

**Target Lemma**:
```lean
lemma no_minimal_counterexample_nu4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnu : packingNumber G = 4)
    (h_counter : coveringNumber G > 8) :
    ∃ e : Sym2 V, e ∈ G.edgeSet ∧
      (packingNumber (G.deleteEdge e) < 4 ∨ coveringNumber (G.deleteEdge e) > 8)
```

---

## Planned Submission Portfolio (Updated)

| Slot | Strategy | File | Rationale | Priority |
|------|----------|------|-----------|----------|
| 1 | Compensating | `nu4_compensating.lean` | Exploit density constraint, literature support | HIGH |
| 2 | Packing-Pair | `nu4_pair.lean` | Grok's pair decomposition insight | HIGH |
| 3 | Bridge Classification | `nu4_bridges.lean` | Attack the actual failure point | HIGH |
| 4 | Direct/Minimal | `nu4_direct.lean` | Boris pattern - let Aristotle explore | HIGH |
| 5 | LP Rounding | `nu4_lp.lean` | New - use Guruswami-Sandeep technique | MEDIUM |
| 6 | Min Counterexample | `nu4_minimal.lean` | Structural constraints | MEDIUM |
| 7 | Counterexample Hunt | `nu4_negation.lean` | Find obstruction if τ > 8 exists | LOW |

---

## Open Problems We Could Attack (Beyond ν=4)

Based on literature review, these are tractable open problems:

| Problem | Status | Why Tractable |
|---------|--------|---------------|
| **ν=4 Tuza** | Our focus | No one has tried formalization |
| General chordal | OPEN | K₈-free solved, gap is small |
| Split graphs | OPEN | Only dense case proven |
| Interval graphs | OPEN | Co-chain (subclass) solved |
| Improve 66/23 bound | OPEN | No progress since Haxell 1993 |

---

## File References

### Proven Files (Include as Context)

| File | UUID | Content | Use For |
|------|------|---------|---------|
| `proven/tuza/nu2/tuza_nu2_PROVEN.lean` | 0764be78 | Complete ν=2 | Base case reference |
| `aristotle_parker_core_PROVEN_f9473ebd.lean` | f9473ebd | Universal lemmas | **Context folder** |
| `aristotle_parker_proven.lean` | 55d1ec45 | Same as above | Duplicate |

### Output Files (Analysis Sources)

| UUID | Content | Key Finding |
|------|---------|-------------|
| 89bfa298 | ν=3 proof | `tau_Te_le_2_nu_3` PROVEN |
| eb165e0f | Dichotomy | Vertex-disjoint lemmas |
| 87299718 | Free edge | Fan counterexample |
| 8fd9def6 | Bridge | K4 counterexample + `S_e_pairwise_share_edges` |
| 94407c27 | Informal | `pairwise_sharing_implies_tau_le_2` |
| 0f604116 | Failed | Only trivial helper |

---

## Key Insights Summary

### What Works for ALL ν
- τ(S_e) ≤ 2 (pairwise sharing)
- τ(G) ≤ τ(T_e) + τ(G \ T_e) (decomposition)
- ν(G \ T_e) = ν - 1 (reduction)
- K4 structure → τ ≤ 2 (bounded vertices)

### What Fails at ν=4
- τ(T_e) ≤ 2 guarantee (bridges to 3 targets)
- |S_e| bounds (can be arbitrarily large)
- Cover from edges of e only (K4 counterexample)

### The Gap
**Known**: τ(S_e) ≤ 2
**Unknown**: τ(T_e \ S_e) bound when bridges attach to 3 packing elements
**Target**: Show τ(T_e) ≤ 4 OR compensate with sparse residual

### Literature Gaps We Can Exploit
1. **No formalization exists** - We have the only Lean 4 Tuza formalization
2. **ν=4 unexplored** - No one has published formal attempts
3. **Chordal still open** - Even "easier" classes aren't done
4. **LP techniques available** - Fractional version is well-understood

---

## References

### Primary Sources
- [Parker 2406.06501](https://arxiv.org/abs/2406.06501) - Tuza for ν ≤ 3, our main match
- [Guruswami-Sandeep 2025](https://arxiv.org/abs/2008.07344) - LP techniques
- [Dense graphs 2405.11409](https://arxiv.org/abs/2405.11409) - 4-partite bounds
- [Aharoni-Zerbib 2020](https://arxiv.org/abs/1611.07497) - Hypergraph generalization
- [Haxell 1993](https://www.semanticscholar.org/paper/Packing-and-Covering-Triangles-in-Tripartite-Graphs-Haxell-Kohayakawa/6faa42887bc4e9396f6590475b76fdcc5ce4987a) - 66/23 bound

### Wikipedia
- [Tuza's conjecture](https://en.wikipedia.org/wiki/Tuza's_conjecture) - Overview

### Repositories
- [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) - No Tuza formalization (opportunity!)
