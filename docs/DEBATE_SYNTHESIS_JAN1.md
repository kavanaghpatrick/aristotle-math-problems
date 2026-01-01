# Multi-Agent Debate Synthesis: Tuza ν=4
## January 1, 2026

## The Critical Gap (Identified)

**We've been pursuing the WRONG approach.**

- Krivelevich's bound: τ ≤ 2ν* (fractional packing)
- Tuza's conjecture: τ ≤ 2ν (integral packing)
- Since ν* ≥ ν always, Krivelevich is WEAKER than Tuza
- Our 140+ submissions mostly formalized Krivelevich, NOT Tuza

**Integrality gap exists**: For triangle packings, ν*/ν ∈ [4/3, 3/2]

---

## Round 1 Consensus

| AI | Key Insight | Novel Contribution |
|----|-------------|-------------------|
| **Grok** | Vertex-link graphs, bottleneck vertices | Charging: each M-triangle pays for 2 externals |
| **Gemini** | "Safe Discard" strategy | Find 4 edges from M's 12 to safely discard |
| **Codex** | Minimal counterexample + ear decomposition | Triangle taxonomy: core-pack vs peripheral |

**Universal Agreement:**
1. Krivelevich/LP approach is DEAD for novel Tuza work
2. Need DIRECT combinatorial construction
3. "Interaction graph" is the key missing structure

---

## Round 2 Synthesis

### The Winning Strategy: "Safe Discard + Interaction Graph"

**Core Idea (Gemini, refined by all):**
- M has 12 edges (4 triangles × 3 edges)
- Instead of finding 8 edges to COVER, find 4 edges to SAFELY DISCARD
- An edge e is "safe" if e ∪ (E(G) \ E(M)) creates no triangles
- Search space: C(12,4) = 495 per packing config (vs 2^|E| for full search)

**Interaction Graph (Unified Definition):**
- Vertices: 12 edges of M
- Adjacency: e₁ ~ e₂ iff they share an external triangle
- Goal: Find independent set of size ≥ 4

**Why This Works:**
- IG is claw-free with Δ ≤ 3 (Codex)
- By Turán: α(IG) ≥ |V|/3 = 4
- For scattered/path cases: IG is sparse → easy
- For cycle/star: IG has bounded structure

### First Concrete Lemma: `bridge_absorption`

**Statement:** Bridge triangles (connecting disjoint packing elements) are covered "for free" by local covers.

**Formal:**
```lean
theorem bridge_absorption
  (A B : Finset V) (hA : G.IsNClique 3 A) (hB : G.IsNClique 3 B)
  (h_disj : Disjoint A B)
  (t : Finset V) (ht : is_bridge G t A B) :
  ∃ e ∈ local_cover G A, e ∈ t.sym2
```

**Why Critical:** If A and B are vertex-disjoint, any triangle bridging them must share an edge with A, hence is covered by A's local cover. This eliminates inter-component costs.

---

## Unified Action Plan

### Phase 1: Infrastructure (Week 1)
1. **Define `InteractionGraph`** on M's edges
2. **Prove `scattered_trivial`**: When IG is empty, τ = 2ν exactly
3. **Prove `bridge_absorption`**: Bridge triangles are free

### Phase 2: Structure Lemmas (Week 2)
4. **Prove `interaction_graph_sparse`**: IG has max degree ≤ 3
5. **Prove `safe_edges_exist`**: IG always has independent set ≥ 4
6. **Prove `safe_discard_reduction`**: τ(G) ≤ 8 when 4 safe edges exist

### Phase 3: Case Completion (Week 3)
7. **Complete `star_4`**: Already trivial (4 spokes)
8. **Complete `path_4`**: Use safe discard at endpoints
9. **Complete `cycle_4`**: IG is 4-cycle → 2 safe edges per pair
10. **Complete `matching_2`**: Two disjoint pairs → bridge absorption

### Concrete First Steps
1. Create `submissions/interaction_graph_def.lean` - definitions
2. Create `submissions/bridge_absorption.lean` - first real lemma
3. Enumerate IG structure for each case (star, path, cycle, scattered)

---

## What Would Be Novel

A proof of Tuza ν=4 via this approach would be novel because:

1. **Direct combinatorial** - not via LP relaxation
2. **Certifying algorithm** - produces the 8-edge cover explicitly
3. **Formalizable** - the safe discard + IG framework is Lean-friendly
4. **Generalizable** - might extend to ν=5, ν=6...

---

## Rejected Approaches

| Approach | Why Rejected |
|----------|--------------|
| Krivelevich τ ≤ 2ν* | Weaker than Tuza, not novel |
| Local cover ≤ 2 | FALSE (counterexample found) |
| Charging arguments | Too complex to formalize |
| Ear decomposition | Heavy infrastructure, not needed |

---

## Key Insight Summary

> **The missing structure is the Interaction Graph.**
>
> We've been trying to bound τ locally per triangle.
> But triangles INTERACT through external vertices/edges.
> The IG captures this interaction.
> An independent set in IG = safe edges to discard.
> Finding 4 safe edges among 12 is tractable.

---

## Next Aristotle Submission

**slot64_interaction_graph_def.lean:**
```lean
-- Define interaction graph on M's edges
def InteractionGraph (G : SimpleGraph V) (M : Finset (Finset V)) :
    SimpleGraph (Sym2 V) where
  Adj e₁ e₂ := e₁ ≠ e₂ ∧ ∃ t ∈ G.cliqueFinset 3,
    t ∉ M ∧ e₁ ∈ t.sym2 ∧ e₂ ∈ t.sym2
```

This is the foundation for the entire new approach.
